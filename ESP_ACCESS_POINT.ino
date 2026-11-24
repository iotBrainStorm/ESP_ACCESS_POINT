#include "esp_sntp.h"
#include "esp_timer.h"
#include "time.h"
#include <Arduino.h>
#include <Ticker.h>
#include <WiFi.h>
#include <WiFiManager.h>
#include <new>

#include <ArduinoJson.h>
#include <ESPAsyncWebServer.h>
#include <ESPmDNS.h>
#include <Preferences.h>
#include <SPIFFS.h>
#include <math.h>

// Explicit ESPAsyncWebServer method bitmasks (avoids collision with WebServer.h included by WiFiManager.h)
static constexpr WebRequestMethod ASYNC_GET = AsyncWebRequestMethod::HTTP_GET;
static constexpr WebRequestMethod ASYNC_POST = AsyncWebRequestMethod::HTTP_POST;
static constexpr WebRequestMethod ASYNC_OPTIONS = AsyncWebRequestMethod::HTTP_OPTIONS;

// ============================================================================
// 1. HARDWARE PINS & SYSTEM LIMITS
// ============================================================================
#define LED_PIN 16
#define BUILTIN_LED_PIN 2
#define BUZZER_PIN 17
#define BOOT_BUTTON 0

static const char *CONFIG_PATH = "/config.json";
static const char *CONFIG_TMP_PATH = "/config.tmp";
static const char *DESIGN_PATH = "/design.json";
static const char *DESIGN_TMP_PATH = "/design.tmp";

static const size_t MAX_CONFIG_BYTES = 20480;     // 16 KB UI limit + safety margin
static const size_t MAX_DESIGN_BYTES = 69632;     // 64 KB UI limit + safety margin
static const size_t MAX_SMALL_JSON_BYTES = 1024;  // For /api/time/sync & /api/wifi/portal
static const uint32_t MIN_FREE_HEAP_FOR_FILES = 12000;
static const uint32_t MIN_FREE_HEAP_FOR_UPLOAD = 16000;
static const uint32_t CRITICAL_LOW_HEAP_BYTES = 8000;

static const int WIFI_BOOT_MAX_ATTEMPTS = 12;                 // 12 * 500ms = 6s max boot wait
static const unsigned long WIFI_RETRY_INTERVAL_MS = 15000UL;  // Silent reconnect every 15s
static const unsigned long NTP_RETRY_UNSYNCED_MS = 60000UL;   // Retry every 60s until synced
static const unsigned long NTP_PERIODIC_SYNC_MS = 3600000UL;  // Hourly background sync
static const unsigned long FORGET_BOOT_WINDOW_MS = 5000UL;    // Matches 5.0s UI progress bar
static const unsigned long BOOT_HOLD_PREARM_MS = 5000UL;
static const unsigned long BOOT_HOLD_VALID_MS = 15000UL;
static const unsigned long FORGET_HOLD_CONFIRM_MS = 350UL;  // Stable press during 5s window

// ============================================================================
// 2. GLOBAL OBJECTS & THREAD SAFETY
// ============================================================================
AsyncWebServer server(80);
Preferences prefs;
Ticker apLedTicker;

SemaphoreHandle_t fsMutex = nullptr;
SemaphoreHandle_t asyncReqMutex = nullptr;

// Unique per-boot token so frontend resets lockout state after ESP32 restart
static char bootIdStr[12] = "00000000";

// ============================================================================
// 3. RUNTIME CONFIGURATION STATE (PERSISTED IN NVS FOR FAST BOOT)
// ============================================================================
struct HubNetworkConfig {
  bool dhcp = true;
  String staticIp = "";
  String subnet = "255.255.255.0";
  String gateway = "192.168.0.1";
  String dns = "8.8.8.8";
  String apName = "HOME ACCESS";
  String apPass = "";
  int apTimeout = 180;
  bool mdnsEnabled = true;
  String mdnsHost = "homeaccess";  // Stored WITHOUT ".local"
};
HubNetworkConfig netCfg;

// Time / NTP State (static buffer required by lwIP SNTP!)
static char ntpServerBuf[64] = "pool.ntp.org";
float tzOffsetHours = 5.5f;
long gmtOffsetSec = 19800L;
String lastSyncTimeStr = "Never";

// ============================================================================
// 4. VOLATILE FLAGS & NON-BLOCKING STATE MACHINES
// ============================================================================
volatile bool wifiGotIpFlag = false;
volatile bool wifiDisconnectedFlag = false;
volatile bool timeSynced = false;
volatile bool syncTimestampPending = false;
volatile bool apLedState = false;

bool webServerRunning = false;
bool mdnsRunning = false;
bool pendingMdnsRefresh = false;
bool pendingNtpResync = false;
bool pendingIpReapply = false;
unsigned long ipReapplyAt = 0;

bool portalPending = false;
bool portalForgetWifi = false;
unsigned long portalStartAt = 0;

bool restartPending = false;
unsigned long restartAt = 0;
bool factoryWifiWipePending = false;

unsigned long lastWifiRetryMs = 0;
unsigned long lastNtpSyncAttemptMs = 0;
unsigned long lowHeapSinceMs = 0;
unsigned long notifyStorageOffAt = 0;

// BOOT button state
unsigned long bootPressedAt = 0;
unsigned long bootHoldSatisfiedAt = 0;
bool bootHoldSatisfied = false;

// Deferred Async Request: POST /api/auth/forget-boot
AsyncWebServerRequest *pendingForgetBootReq = nullptr;
unsigned long forgetBootDeadlineMs = 0;
unsigned long forgetBootHoldStart = 0;

// Deferred Async Request: GET /api/scan
AsyncWebServerRequest *pendingScanReq = nullptr;
bool scanIotOnly = true;
bool scanWantMqtt = false;
char scanGateway[20] = "";
char scanTld[16] = ".local";

// Zero-RAM-Buffer Streaming Upload Session (for /api/config & /api/design)
struct StreamUploadSession {
  bool active = false;
  AsyncWebServerRequest *owner = nullptr;
  File file;
  const char *tmpPath = nullptr;
  const char *finalPath = nullptr;
  size_t maxBytes = 0;
  size_t bytesWritten = 0;
  bool failed = false;
  int errorCode = 500;
  char errorMsg[48] = "";
  char firstNonWs = 0;
  char lastNonWs = 0;
  bool isConfig = false;
};
StreamUploadSession uploadSession;

// Lightweight fixed buffer for tiny JSON POSTs (/api/time/sync, /api/wifi/portal)
struct SmallJsonBody {
  char data[MAX_SMALL_JSON_BYTES + 1];
  size_t len = 0;
  bool overflow = false;
};

// ============================================================================
// 5. FORWARD DECLARATIONS
// ============================================================================
void setupWebServer();
bool syncTime();
void startOrRefreshMdns();

// ============================================================================
// 6. CRASH GUARD & HARDWARE FEEDBACK
// ============================================================================
static void oomNewHandler() {
  ets_printf("[OOM] Heap allocation failed - restarting cleanly\n");
  esp_restart();
}

void notifyStorage() {
  digitalWrite(LED_PIN, HIGH);
  digitalWrite(BUZZER_PIN, HIGH);
  notifyStorageOffAt = millis() + 90;
  if (notifyStorageOffAt == 0) notifyStorageOffAt = 1;
}

void serviceNotifyStorage() {
  if (notifyStorageOffAt && (int32_t)(millis() - notifyStorageOffAt) >= 0) {
    notifyStorageOffAt = 0;
    digitalWrite(BUZZER_PIN, LOW);
    digitalWrite(LED_PIN, LOW);
  }
}

void beepShort(uint8_t count = 1) {
  for (uint8_t i = 0; i < count; i++) {
    digitalWrite(BUZZER_PIN, HIGH);
    delay(80);
    digitalWrite(BUZZER_PIN, LOW);
    if (i + 1 < count) delay(80);
  }
}

// ============================================================================
// 7. STRING, HOSTNAME & TIME UTILITIES
// ============================================================================
String sanitizeMdnsHost(String raw) {
  raw.trim();
  raw.toLowerCase();
  if (raw.startsWith("http://")) raw.remove(0, 7);
  if (raw.startsWith("https://")) raw.remove(0, 8);
  while (raw.endsWith("/")) raw.remove(raw.length() - 1);
  if (raw.endsWith(".local")) raw.remove(raw.length() - 6);

  String clean;
  clean.reserve(32);
  for (size_t i = 0; i < raw.length() && clean.length() < 32; i++) {
    char c = raw[i];
    if ((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-') {
      clean += c;
    }
  }
  while (clean.startsWith("-")) clean.remove(0, 1);
  while (clean.endsWith("-")) clean.remove(clean.length() - 1);
  return clean.isEmpty() ? String("homeaccess") : clean;
}

void formatUptimeStr(char *out, size_t outSize) {
  uint64_t totalSec = (uint64_t)(esp_timer_get_time() / 1000000ULL);
  uint32_t days = (uint32_t)(totalSec / 86400ULL);
  uint32_t hours = (uint32_t)((totalSec % 86400ULL) / 3600ULL);
  uint32_t mins = (uint32_t)((totalSec % 3600ULL) / 60ULL);
  uint32_t secs = (uint32_t)(totalSec % 60ULL);

  if (days > 0) {
    snprintf(out, outSize, "%lud %02luh %02lum", (unsigned long)days,
             (unsigned long)hours, (unsigned long)mins);
  } else if (hours > 0) {
    snprintf(out, outSize, "%luh %02lum %02lus", (unsigned long)hours,
             (unsigned long)mins, (unsigned long)secs);
  } else {
    snprintf(out, outSize, "%lum %02lus", (unsigned long)mins,
             (unsigned long)secs);
  }
}

bool readCurrentLocalTime(struct tm *ti) {
  if (!ti) return false;
  time_t nowEpoch = time(nullptr);
  if (nowEpoch <= 1577836800L) return false;  // Must be >= 2020-01-01
  localtime_r(&nowEpoch, ti);
  return (ti->tm_year + 1900) >= 2020;
}

void formatSyncTimestamp(const struct tm *ti, char *buf, size_t bufSize) {
  static const char *MONTHS[12] = { "Jan", "Feb", "Mar", "Apr", "May", "Jun",
                                    "Jul", "Aug", "Sep", "Oct", "Nov", "Dec" };
  int mon = (ti->tm_mon >= 0 && ti->tm_mon < 12) ? ti->tm_mon : 0;
  snprintf(buf, bufSize, "%02d %s %04d %02d:%02d:%02d",
           ti->tm_mday, MONTHS[mon], ti->tm_year + 1900,
           ti->tm_hour, ti->tm_min, ti->tm_sec);
}

void updateLastSyncTimestamp() {
  struct tm ti;
  if (readCurrentLocalTime(&ti)) {
    char buf[32];
    formatSyncTimestamp(&ti, buf, sizeof(buf));
    timeSynced = true;
    lastSyncTimeStr = String(buf);
    Preferences p;
    p.begin("hubtime", false);
    p.putString("lastSync", lastSyncTimeStr);
    p.end();
    Serial.printf("[TIME] Synced: %s (UTC%+.2fh)\n", buf, tzOffsetHours);
  }
}

// Keep SNTP callback strictly lock-free & lightweight
void sntpTimeAvailableCallback(struct timeval *tv) {
  (void)tv;
  timeSynced = true;
  syncTimestampPending = true;
}

bool syncTime() {
  if (WiFi.status() != WL_CONNECTED) return false;

  lastNtpSyncAttemptMs = millis();
  gmtOffsetSec = (long)lroundf(tzOffsetHours * 3600.0f);

  sntp_set_time_sync_notification_cb(sntpTimeAvailableCallback);
  configTime(gmtOffsetSec, 0, ntpServerBuf, "pool.ntp.org", "time.nist.gov");
  return true;
}

// ============================================================================
// 8. NVS PERSISTENCE (NETWORK, WIFI & TIME SETTINGS)
// ============================================================================
void loadNetworkAndTimeFromNvs() {
  Preferences p;

  p.begin("hubnet", true);
  netCfg.dhcp = p.getBool("dhcp", true);
  netCfg.staticIp = p.getString("sip", "");
  netCfg.subnet = p.getString("mask", "255.255.255.0");
  netCfg.gateway = p.getString("gw", "192.168.0.1");
  netCfg.dns = p.getString("dns", "8.8.8.8");
  netCfg.apName = p.getString("apName", "HOME ACCESS");
  netCfg.apPass = p.getString("apPass", "");
  netCfg.apTimeout = p.getInt("apTo", 180);
  netCfg.mdnsEnabled = p.getBool("mdnsEn", true);
  netCfg.mdnsHost = sanitizeMdnsHost(p.getString("mdns", "homeaccess"));
  p.end();

  if (netCfg.apName.isEmpty()) netCfg.apName = "HOME ACCESS";
  if (netCfg.apTimeout < 30 || netCfg.apTimeout > 600) netCfg.apTimeout = 180;

  p.begin("hubtime", true);
  String storedNtp = p.getString("ntp", "pool.ntp.org");
  tzOffsetHours = p.getFloat("tz", 5.5f);
  lastSyncTimeStr = p.getString("lastSync", "Never");
  p.end();

  storedNtp.trim();
  if (storedNtp.isEmpty()) storedNtp = "pool.ntp.org";
  strncpy(ntpServerBuf, storedNtp.c_str(), sizeof(ntpServerBuf) - 1);
  ntpServerBuf[sizeof(ntpServerBuf) - 1] = '\0';
  gmtOffsetSec = (long)lroundf(tzOffsetHours * 3600.0f);
}

void saveNetworkToNvs() {
  Preferences p;
  p.begin("hubnet", false);
  p.putBool("dhcp", netCfg.dhcp);
  p.putString("sip", netCfg.staticIp);
  p.putString("mask", netCfg.subnet);
  p.putString("gw", netCfg.gateway);
  p.putString("dns", netCfg.dns);
  p.putString("apName", netCfg.apName);
  p.putString("apPass", netCfg.apPass);
  p.putInt("apTo", netCfg.apTimeout);
  p.putBool("mdnsEn", netCfg.mdnsEnabled);
  p.putString("mdns", netCfg.mdnsHost);
  p.end();
}

void saveTimeToNvs() {
  Preferences p;
  p.begin("hubtime", false);
  p.putString("ntp", (const char *)ntpServerBuf);
  p.putFloat("tz", tzOffsetHours);
  p.putString("lastSync", lastSyncTimeStr);
  p.end();
}

bool getSavedWifiCredentials(String &ssid, String &pass) {
  Preferences p;
  p.begin("wfcfg", true);
  ssid = p.getString("ssid", "");
  pass = p.getString("pass", "");
  p.end();
  return !ssid.isEmpty();
}

void saveCurrentWifiCredentials() {
  String curSsid = WiFi.SSID();
  if (curSsid.isEmpty()) return;
  Preferences p;
  p.begin("wfcfg", false);
  p.putString("ssid", curSsid);
  p.putString("pass", WiFi.psk());
  p.end();
}

void clearSavedWifiCredentials() {
  Preferences p;
  p.begin("wfcfg", false);
  p.remove("ssid");
  p.remove("pass");
  p.end();
}

// Extracts ONLY `network` and `admin.time` from /config.tmp using ArduinoJson Filter (< 1.5 KB RAM)
bool syncRuntimeFromConfigFile(const char *path) {
  File f = SPIFFS.open(path, "r");
  if (!f) return false;

  JsonDocument filter;
  filter["network"] = true;
  filter["admin"]["time"] = true;

  JsonDocument doc;
  DeserializationError err = deserializeJson(doc, f, DeserializationOption::Filter(filter));
  f.close();

  if (err) {
    Serial.printf("[CFG] JSON validation failed: %s\n", err.c_str());
    return false;
  }

  bool ipChanged = false;
  bool mdnsChanged = false;
  bool timeChanged = false;

  if (doc["network"].is<JsonObject>()) {
    JsonObject net = doc["network"].as<JsonObject>();

    bool newDhcp = strcmp(net["mode"] | "dhcp", "static") != 0;
    String newSip = String(net["staticIp"] | "");
    String newMask = String(net["subnet"] | "255.255.255.0");
    String newGw = String(net["gateway"] | "192.168.0.1");
    String newDns = String(net["dns"] | "8.8.8.8");
    String newApName = String(net["apName"] | "HOME ACCESS");
    String newApPass = String(net["apPass"] | "");
    int newApTo = net["apTimeout"] | 180;
    bool newMdnsEn = net["mdnsEnabled"].is<bool>() ? net["mdnsEnabled"].as<bool>() : true;
    String newMdns = sanitizeMdnsHost(String(net["mdns"] | "homeaccess.local"));

    newSip.trim();
    newMask.trim();
    newGw.trim();
    newDns.trim();
    newApName.trim();
    if (newApName.isEmpty()) newApName = "HOME ACCESS";
    if (newApTo < 30 || newApTo > 600) newApTo = 180;

    if (newDhcp != netCfg.dhcp || (!newDhcp && (newSip != netCfg.staticIp || newMask != netCfg.subnet || newGw != netCfg.gateway || newDns != netCfg.dns))) {
      ipChanged = true;
    }

    if (newMdnsEn != netCfg.mdnsEnabled || newMdns != netCfg.mdnsHost) {
      mdnsChanged = true;
    }

    netCfg.dhcp = newDhcp;
    netCfg.staticIp = newSip;
    netCfg.subnet = newMask;
    netCfg.gateway = newGw;
    netCfg.dns = newDns;
    netCfg.apName = newApName;
    netCfg.apPass = newApPass;
    netCfg.apTimeout = newApTo;
    netCfg.mdnsEnabled = newMdnsEn;
    netCfg.mdnsHost = newMdns;

    saveNetworkToNvs();
  }

  if (doc["admin"]["time"].is<JsonObject>()) {
    JsonObject tmObj = doc["admin"]["time"].as<JsonObject>();
    String newNtp = String(tmObj["ntpServer"] | (const char *)ntpServerBuf);
    newNtp.trim();
    if (newNtp.isEmpty()) newNtp = "pool.ntp.org";

    float newTz = tzOffsetHours;
    if (!tmObj["tzOffset"].isNull()) {
      newTz = tmObj["tzOffset"].as<String>().toFloat();
    }

    if (strcmp(ntpServerBuf, newNtp.c_str()) != 0 || fabsf(newTz - tzOffsetHours) > 0.01f) {
      strncpy(ntpServerBuf, newNtp.c_str(), sizeof(ntpServerBuf) - 1);
      ntpServerBuf[sizeof(ntpServerBuf) - 1] = '\0';
      tzOffsetHours = newTz;
      gmtOffsetSec = (long)lroundf(tzOffsetHours * 3600.0f);
      saveTimeToNvs();
      timeChanged = true;
    }
  }

  if (mdnsChanged) pendingMdnsRefresh = true;
  if (timeChanged) pendingNtpResync = true;
  if (ipChanged) {
    pendingIpReapply = true;
    ipReapplyAt = millis() + 900;  // Wait for HTTP 200 to flush first
  }

  return true;
}

// ============================================================================
// 9. WIFI, STATIC IP, mDNS & CONFIG PORTAL MANAGEMENT
// ============================================================================
bool applyStationIpConfig() {
  WiFi.mode(WIFI_STA);
  WiFi.setHostname(netCfg.mdnsHost.c_str());

  if (!netCfg.dhcp) {
    IPAddress ip, gw, mask, dns;
    if (ip.fromString(netCfg.staticIp) && gw.fromString(netCfg.gateway) && mask.fromString(netCfg.subnet) && dns.fromString(netCfg.dns)) {
      WiFi.config(ip, gw, mask, dns);
      return true;
    }
    Serial.println("[WIFI] Static IP invalid - falling back to DHCP");
  }

  IPAddress zero(0, 0, 0, 0);
  WiFi.config(zero, zero, zero, zero);
  return true;
}

void startOrRefreshMdns() {
  if (mdnsRunning) {
    MDNS.end();
    mdnsRunning = false;
  }
  if (!netCfg.mdnsEnabled || WiFi.status() != WL_CONNECTED) return;

  if (MDNS.begin(netCfg.mdnsHost.c_str())) {
    MDNS.addService("http", "tcp", 80);
    mdnsRunning = true;
    Serial.printf("[MDNS] Active: http://%s.local\n", netCfg.mdnsHost.c_str());
  } else {
    Serial.println("[MDNS] Failed to start");
  }
}

bool runWifiConfigPortal(bool forgetBeforeStart = false, bool restartOnSuccess = true) {
  Serial.println("[WIFI] Launching Configuration Portal...");

  if (webServerRunning) {
    server.end();
    webServerRunning = false;
  }
  if (mdnsRunning) {
    MDNS.end();
    mdnsRunning = false;
  }

  if (forgetBeforeStart) {
    clearSavedWifiCredentials();
    WiFi.disconnect(true, true);
  } else {
    WiFi.disconnect(false, false);
  }
  delay(200);
  WiFi.softAPdisconnect(true);
  delay(100);
  WiFi.mode(WIFI_AP_STA);
  delay(100);

  WiFiManager wm;
  wm.setConfigPortalTimeout(netCfg.apTimeout);
  wm.setConnectTimeout(15);
  wm.setBreakAfterConfig(true);

  apLedState = false;
  apLedTicker.attach_ms(250, []() {
    apLedState = !apLedState;
    digitalWrite(BUILTIN_LED_PIN, apLedState ? HIGH : LOW);
    digitalWrite(LED_PIN, apLedState ? HIGH : LOW);
  });

  bool connected = false;
  if (netCfg.apPass.length() >= 8 && netCfg.apPass.length() <= 63) {
    connected = wm.startConfigPortal(netCfg.apName.c_str(), netCfg.apPass.c_str());
  } else {
    connected = wm.startConfigPortal(netCfg.apName.c_str());
  }

  apLedTicker.detach();
  apLedState = false;
  digitalWrite(BUILTIN_LED_PIN, LOW);
  digitalWrite(LED_PIN, LOW);

  if (connected && WiFi.status() == WL_CONNECTED) {
    Serial.printf("[WIFI] Connected via Portal: %s (%s)\n",
                  WiFi.SSID().c_str(), WiFi.localIP().toString().c_str());
    WiFi.setSleep(false);
    saveCurrentWifiCredentials();
    notifyStorage();
    if (restartOnSuccess) {
      delay(400);
      ESP.restart();
    }
    return true;
  }

  Serial.println("[WIFI] Portal closed/timed out - restoring Station & Server");
  WiFi.softAPdisconnect(true);
  WiFi.mode(WIFI_STA);
  delay(150);

  // Smoothly relaunch STA connection and Web Server without rebooting
  String ssid, pass;
  if (getSavedWifiCredentials(ssid, pass)) {
    applyStationIpConfig();
    WiFi.setAutoReconnect(true);
    WiFi.begin(ssid.c_str(), pass.c_str());
  }
  setupWebServer();
  return false;
}

bool connectToSavedWiFi() {
  String ssid, pass;
  if (!getSavedWifiCredentials(ssid, pass)) {
    Serial.println("[WIFI] No saved credentials - opening AP Portal");
    return runWifiConfigPortal(false, true);
  }

  Serial.printf("[WIFI] Connecting to %s...\n", ssid.c_str());
  applyStationIpConfig();
  WiFi.setAutoReconnect(true);
  WiFi.setSleep(false);
  WiFi.begin(ssid.c_str(), pass.c_str());

  for (int i = 0; i < WIFI_BOOT_MAX_ATTEMPTS; i++) {
    if (WiFi.status() == WL_CONNECTED) {
      Serial.printf("[WIFI] Connected! IP: %s  GW: %s\n",
                    WiFi.localIP().toString().c_str(),
                    WiFi.gatewayIP().toString().c_str());
      WiFi.setSleep(false);
      return true;
    }
    delay(500);
  }

  Serial.println("[WIFI] Router not ready yet - continuing in background");
  return false;
}

// ============================================================================
// 10. SAFE STREAMING UPLOAD HELPERS (ZERO-LEAK, ZERO-BUFFER)
// ============================================================================
void abortUploadIfOwner(AsyncWebServerRequest *req) {
  if (!fsMutex) return;
  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
    if (uploadSession.active && uploadSession.owner == req) {
      if (uploadSession.file) uploadSession.file.close();
      if (uploadSession.tmpPath && SPIFFS.exists(uploadSession.tmpPath)) {
        SPIFFS.remove(uploadSession.tmpPath);
      }
      uploadSession.active = false;
      uploadSession.owner = nullptr;
    }
    xSemaphoreGive(fsMutex);
  }
}

void handleStreamBody(AsyncWebServerRequest *req, uint8_t *data, size_t len,
                      size_t index, size_t total, const char *tmpPath,
                      const char *finalPath, size_t maxBytes, bool isConfig) {
  if (!fsMutex) return;

  if (index == 0) {
    if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(500)) != pdTRUE) return;

    if (uploadSession.active) {
      xSemaphoreGive(fsMutex);
      return;  // onRequest will return 503 Busy
    }

    uploadSession.active = true;
    uploadSession.owner = req;
    uploadSession.tmpPath = tmpPath;
    uploadSession.finalPath = finalPath;
    uploadSession.maxBytes = maxBytes;
    uploadSession.bytesWritten = 0;
    uploadSession.failed = false;
    uploadSession.errorCode = 200;
    uploadSession.errorMsg[0] = '\0';
    uploadSession.firstNonWs = 0;
    uploadSession.lastNonWs = 0;
    uploadSession.isConfig = isConfig;

    req->onDisconnect([req]() {
      abortUploadIfOwner(req);
    });

    if (ESP.getFreeHeap() < MIN_FREE_HEAP_FOR_UPLOAD) {
      uploadSession.failed = true;
      uploadSession.errorCode = 503;
      strncpy(uploadSession.errorMsg, "Low memory", sizeof(uploadSession.errorMsg) - 1);
    } else if (total == 0 || total > maxBytes) {
      uploadSession.failed = true;
      uploadSession.errorCode = 413;
      strncpy(uploadSession.errorMsg, "Payload exceeds storage limit", sizeof(uploadSession.errorMsg) - 1);
    } else {
      if (SPIFFS.exists(tmpPath)) SPIFFS.remove(tmpPath);
      uploadSession.file = SPIFFS.open(tmpPath, "w");
      if (!uploadSession.file) {
        uploadSession.failed = true;
        uploadSession.errorCode = 500;
        strncpy(uploadSession.errorMsg, "Failed to open flash file", sizeof(uploadSession.errorMsg) - 1);
      }
    }
    xSemaphoreGive(fsMutex);
  }

  if (len == 0) return;

  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(500)) != pdTRUE) return;
  if (uploadSession.active && uploadSession.owner == req && !uploadSession.failed) {
    if (uploadSession.bytesWritten + len > uploadSession.maxBytes) {
      uploadSession.failed = true;
      uploadSession.errorCode = 413;
      strncpy(uploadSession.errorMsg, "Payload exceeds storage limit", sizeof(uploadSession.errorMsg) - 1);
    } else {
      for (size_t i = 0; i < len; i++) {
        char c = (char)data[i];
        if (c != ' ' && c != '\t' && c != '\r' && c != '\n') {
          if (uploadSession.firstNonWs == 0) uploadSession.firstNonWs = c;
          uploadSession.lastNonWs = c;
        }
      }
      size_t written = uploadSession.file.write(data, len);
      uploadSession.bytesWritten += written;
      if (written != len) {
        uploadSession.failed = true;
        uploadSession.errorCode = 507;
        strncpy(uploadSession.errorMsg, "SPIFFS write failed (storage full)", sizeof(uploadSession.errorMsg) - 1);
      }
    }
  }
  xSemaphoreGive(fsMutex);
}

void finalizeStreamUpload(AsyncWebServerRequest *req) {
  if (!fsMutex) {
    req->send(500, "application/json", "{\"ok\":false,\"error\":\"Mutex error\"}");
    return;
  }

  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) != pdTRUE) {
    req->send(503, "application/json", "{\"ok\":false,\"error\":\"Storage busy\"}");
    return;
  }

  if (!uploadSession.active || uploadSession.owner != req) {
    xSemaphoreGive(fsMutex);
    req->send(503, "application/json", "{\"ok\":false,\"error\":\"Another save in progress\"}");
    return;
  }

  if (uploadSession.file) {
    uploadSession.file.flush();
    uploadSession.file.close();
  }

  bool ok = !uploadSession.failed && uploadSession.bytesWritten > 0;
  int errCode = uploadSession.errorCode;
  String errMsg = uploadSession.errorMsg;
  const char *tmpPath = uploadSession.tmpPath;
  const char *finalPath = uploadSession.finalPath;
  bool isConfig = uploadSession.isConfig;

  if (ok) {
    bool validFraming = isConfig
                          ? (uploadSession.firstNonWs == '{' && uploadSession.lastNonWs == '}')
                          : ((uploadSession.firstNonWs == '[' && uploadSession.lastNonWs == ']') || (uploadSession.firstNonWs == '{' && uploadSession.lastNonWs == '}'));
    if (!validFraming) {
      ok = false;
      errCode = 400;
      errMsg = "Malformed JSON payload";
    }
  }

  if (ok && isConfig) {
    if (!syncRuntimeFromConfigFile(tmpPath)) {
      ok = false;
      errCode = 400;
      errMsg = "Invalid configuration JSON";
    }
  }

  if (ok) {
    if (SPIFFS.exists(finalPath)) SPIFFS.remove(finalPath);
    if (!SPIFFS.rename(tmpPath, finalPath)) {
      ok = false;
      errCode = 500;
      errMsg = "Atomic file commit failed";
    }
  }

  if (!ok && tmpPath && SPIFFS.exists(tmpPath)) {
    SPIFFS.remove(tmpPath);
  }

  uploadSession.active = false;
  uploadSession.owner = nullptr;
  xSemaphoreGive(fsMutex);

  if (!ok) {
    JsonDocument d;
    d["ok"] = false;
    d["error"] = errMsg.isEmpty() ? "Save failed" : errMsg;
    AsyncResponseStream *res = req->beginResponseStream("application/json");
    res->setCode(errCode >= 400 ? errCode : 500);
    serializeJson(d, *res);
    req->send(res);
    return;
  }

  notifyStorage();
  req->send(200, "application/json", "{\"ok\":true}");
}

// Helper for small JSON POSTs (/api/time/sync & /api/wifi/portal)
void handleSmallJsonBody(AsyncWebServerRequest *req, uint8_t *data, size_t len,
                         size_t index, size_t total) {
  if (index == 0) {
    SmallJsonBody *buf = new (std::nothrow) SmallJsonBody();
    req->_tempObject = buf;
    req->onDisconnect([req]() {
      if (req->_tempObject) {
        delete static_cast<SmallJsonBody *>(req->_tempObject);
        req->_tempObject = nullptr;
      }
    });
    if (buf && total > MAX_SMALL_JSON_BYTES) {
      buf->overflow = true;
    }
  }

  SmallJsonBody *buf = static_cast<SmallJsonBody *>(req->_tempObject);
  if (!buf || buf->overflow) return;

  if (buf->len + len > MAX_SMALL_JSON_BYTES) {
    buf->overflow = true;
    return;
  }

  memcpy(buf->data + buf->len, data, len);
  buf->len += len;
  buf->data[buf->len] = '\0';
}

// ============================================================================
// 11. STATIC FILE & JSON STREAMING HELPERS
// ============================================================================
void sendWebFile(AsyncWebServerRequest *req, const char *path,
                 const char *contentType, bool cacheStatic = false) {
  if (ESP.getFreeHeap() < MIN_FREE_HEAP_FOR_FILES) {
    req->send(503, "text/plain", "Low memory - retry shortly");
    return;
  }

  char gzPath[48];
  snprintf(gzPath, sizeof(gzPath), "%s.gz", path);

  if (SPIFFS.exists(gzPath)) {
    File f = SPIFFS.open(gzPath, "r");
    uint8_t magic[2] = { 0, 0 };
    size_t sz = 0;
    if (f) {
      sz = f.size();
      f.read(magic, 2);
      f.close();
    }
    Serial.printf("[HTTP] 200 %s -> %s (%u B, magic=%02X %02X)\n",
                  req->url().c_str(), gzPath, (unsigned)sz, magic[0], magic[1]);

    // Pass uncompressed `path` so ESPAsyncWebServer auto-serves `.gz` with ONE Content-Encoding header
    AsyncWebServerResponse *res = req->beginResponse(SPIFFS, String(path), contentType, false);
    res->addHeader("Cache-Control", cacheStatic ? "public, max-age=86400" : "no-store");
    req->send(res);
    return;
  }

  if (SPIFFS.exists(path)) {
    AsyncWebServerResponse *res = req->beginResponse(SPIFFS, String(path), contentType, false);
    res->addHeader("Cache-Control", cacheStatic ? "public, max-age=86400" : "no-store");
    req->send(res);
    return;
  }

  Serial.printf("[HTTP] 404 Missing: %s\n", path);
  req->send(404, "text/plain", "File not found in SPIFFS");
}

void sendStoredJsonFile(AsyncWebServerRequest *req, const char *path,
                        const char *emptyFallback) {
  if (ESP.getFreeHeap() < MIN_FREE_HEAP_FOR_FILES) {
    req->send(503, "application/json", "{\"error\":\"Low memory\"}");
    return;
  }

  if (SPIFFS.exists(path)) {
    AsyncWebServerResponse *res = req->beginResponse(SPIFFS, path, "application/json");
    res->addHeader("Cache-Control", "no-store");
    req->send(res);
    return;
  }

  AsyncWebServerResponse *res = req->beginResponse(200, "application/json", emptyFallback);
  res->addHeader("Cache-Control", "no-store");
  req->send(res);
}

// ============================================================================
// 12. BACKGROUND SERVICERS (BOOT BUTTON, FORGET-BOOT & NATIVE mDNS SCANNER)
// ============================================================================
void serviceBootButtonAndForgetAuth() {
  unsigned long now = millis();
  bool pressed = (digitalRead(BOOT_BUTTON) == LOW);

  // Track general 5-second pre-hold gesture
  if (pressed) {
    if (bootPressedAt == 0) bootPressedAt = now;
    if (!bootHoldSatisfied && (now - bootPressedAt >= BOOT_HOLD_PREARM_MS)) {
      bootHoldSatisfied = true;
      bootHoldSatisfiedAt = now;
      Serial.println("[BOOT] Pre-armed 5s hold detected");
    }
  } else {
    bootPressedAt = 0;
    if (bootHoldSatisfied && (now - bootHoldSatisfiedAt > BOOT_HOLD_VALID_MS)) {
      bootHoldSatisfied = false;
    }
  }

  // Service active POST /api/auth/forget-boot request cleanly in loop()
  if (!pendingForgetBootReq) return;

  bool confirmed = false;
  bool timedOut = false;

  if (bootHoldSatisfied) {
    bootHoldSatisfied = false;
    confirmed = true;
  } else if (pressed) {
    if (forgetBootHoldStart == 0) forgetBootHoldStart = now;
    if (now - forgetBootHoldStart >= FORGET_HOLD_CONFIRM_MS) {
      confirmed = true;
    }
  } else {
    forgetBootHoldStart = 0;
  }

  if (!confirmed && (int32_t)(now - forgetBootDeadlineMs) >= 0) {
    timedOut = true;
  }

  if (confirmed || timedOut) {
    if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      if (pendingForgetBootReq) {
        pendingForgetBootReq->send(
          200, "application/json",
          confirmed ? "{\"bootHeld\":true}" : "{\"bootHeld\":false}");
        pendingForgetBootReq = nullptr;
      }
      xSemaphoreGive(asyncReqMutex);
    }
    forgetBootHoldStart = 0;
    if (confirmed) notifyStorage();
  }
}

void serviceNativeMdnsScan() {
  if (!pendingScanReq) return;

  // Copy scan options locally before releasing mutex
  bool localIotOnly = true;
  bool localWantMqtt = false;
  char localGw[20] = "";
  char localTld[16] = ".local";

  if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
    localIotOnly = scanIotOnly;
    localWantMqtt = scanWantMqtt;
    strncpy(localGw, scanGateway, sizeof(localGw) - 1);
    strncpy(localTld, scanTld, sizeof(localTld) - 1);
    xSemaphoreGive(asyncReqMutex);
  }

  JsonDocument doc;
  JsonArray arr = doc.to<JsonArray>();

  if (WiFi.status() == WL_CONNECTED && mdnsRunning) {
    String selfIp = WiFi.localIP().toString();
    int added = 0;
    const int MAX_SCAN_RESULTS = 24;

    auto queryServiceType = [&](const char *service, const char *proto,
                                const char *defaultType) {
      int n = MDNS.queryService(service, proto);
      for (int i = 0; i < n && added < MAX_SCAN_RESULTS; i++) {
#if defined(ESP_ARDUINO_VERSION_MAJOR) && (ESP_ARDUINO_VERSION_MAJOR >= 3)
        String ip = MDNS.address(i).toString();
#else
        String ip = MDNS.IP(i).toString();
#endif
        if (ip.isEmpty() || ip == "0.0.0.0" || ip == selfIp) continue;
        if (localIotOnly && localGw[0] != '\0' && ip == localGw) continue;

        String host = MDNS.hostname(i);
        host.trim();
        if (host.isEmpty()) host = String("esp-") + ip.substring(ip.lastIndexOf('.') + 1);

        // Deduplicate by IP + port
        uint16_t port = MDNS.port(i);
        if (port == 0) port = 80;
        bool dup = false;
        for (JsonObject existing : arr) {
          if (existing["ip"].as<String>() == ip && existing["port"].as<uint16_t>() == port) {
            dup = true;
            break;
          }
        }
        if (dup) continue;

        JsonObject item = arr.add<JsonObject>();
        item["name"] = host;
        item["type"] = defaultType;
        item["ip"] = ip;
        item["mdns"] = host + String(localTld);
        item["port"] = port;
        item["pingMs"] = 10;
        added++;
      }
    };

    queryServiceType("http", "tcp", "ESP / HTTP Node");
    if (localWantMqtt && added < MAX_SCAN_RESULTS) {
      queryServiceType("mqtt", "tcp", "MQTT Broker");
    }
  }

  if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
    if (pendingScanReq) {
      AsyncResponseStream *res = pendingScanReq->beginResponseStream("application/json");
      res->addHeader("Cache-Control", "no-store");
      serializeJson(doc, *res);
      pendingScanReq->send(res);
      pendingScanReq = nullptr;
    }
    xSemaphoreGive(asyncReqMutex);
  }
}

// ============================================================================
// 13. WEB SERVER ROUTES (REGISTERED ONCE - SAFE RELAUNCH ON RECONNECT)
// ============================================================================
void setupWebServer() {
  static bool routesRegistered = false;

  if (routesRegistered) {
    if (!webServerRunning) {
      server.begin();
      webServerRunning = true;
      Serial.println("[SERVER] Web server relaunched");
    }
    return;
  }
  routesRegistered = true;

  // CORS headers (do NOT add Connection: close here; ESPAsyncWebServer manages Connection itself)
  DefaultHeaders::Instance().addHeader("Access-Control-Allow-Origin", "*");
  DefaultHeaders::Instance().addHeader("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
  DefaultHeaders::Instance().addHeader("Access-Control-Allow-Headers", "Content-Type, X-API-Key, X-Session-Token");

  // --- Health Check ---
  server.on("/ping", ASYNC_GET, [](AsyncWebServerRequest *req) {
    Serial.println("[HTTP] 200 /ping");
    req->send(200, "text/plain", "pong");
  });

  // --- 4 Core Web Pages ---
  server.on("/", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/index.html", "text/html", false);
  });
  server.on("/index.html", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/index.html", "text/html", false);
  });
  server.on("/config.html", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/config.html", "text/html", false);
  });
  server.on("/layout.html", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/layout.html", "text/html", false);
  });
  server.on("/design.html", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/design.html", "text/html", false);
  });

  // --- Favicons (Cached 24h to cut redundant traffic) ---
  server.on("/index.svg", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/index.svg", "image/svg+xml", true);
  });
  server.on("/config.svg", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/config.svg", "image/svg+xml", true);
  });
  server.on("/layout.svg", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/layout.svg", "image/svg+xml", true);
  });
  server.on("/design.svg", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendWebFile(req, "/design.svg", "image/svg+xml", true);
  });

  // --- GET /api/status (Telemetry for index.html, config.html, layout.html) ---
  server.on("/api/status", ASYNC_GET, [](AsyncWebServerRequest *req) {
    JsonDocument d;
    bool connected = (WiFi.status() == WL_CONNECTED);
    uint32_t totalHeap = ESP.getHeapSize();
    uint32_t freeHeap = ESP.getFreeHeap();
    uint32_t usedHeap = (totalHeap > freeHeap) ? (totalHeap - freeHeap) : 0;

    char uptimeBuf[24];
    formatUptimeStr(uptimeBuf, sizeof(uptimeBuf));

    d["wifiOk"] = connected;
    d["ssid"] = connected ? WiFi.SSID() : "";
    d["ip"] = connected ? WiFi.localIP().toString() : "0.0.0.0";
    d["gateway"] = connected ? WiFi.gatewayIP().toString() : netCfg.gateway;
    d["subnet"] = connected ? WiFi.subnetMask().toString() : netCfg.subnet;
    d["dns"] = connected ? WiFi.dnsIP().toString() : netCfg.dns;
    d["mac"] = WiFi.macAddress();
    d["rssi"] = connected ? WiFi.RSSI() : 0;
    d["mdns"] = netCfg.mdnsHost + ".local";
    d["bootId"] = (const char *)bootIdStr;
    d["uptime"] = (const char *)uptimeBuf;
    d["cpuTemp"] = roundf(temperatureRead() * 10.0f) / 10.0f;
    d["ramUsedKb"] = usedHeap / 1024;
    d["ramTotalKb"] = totalHeap / 1024;
    d["freeHeap"] = freeHeap;
    d["minHeap"] = ESP.getMinFreeHeap();
    d["maxBlock"] = ESP.getMaxAllocHeap();
    d["storageUsedKb"] = roundf((SPIFFS.usedBytes() / 1024.0f) * 10.0f) / 10.0f;
    d["storageTotalKb"] = roundf((SPIFFS.totalBytes() / 1024.0f) * 10.0f) / 10.0f;
    d["timeSynced"] = timeSynced;
    d["lastSync"] = lastSyncTimeStr;

    AsyncResponseStream *res = req->beginResponseStream("application/json");
    res->addHeader("Cache-Control", "no-store");
    serializeJson(d, *res);
    req->send(res);
  });

  // --- GET /api/config (Streams /config.json directly from flash) ---
  server.on("/api/config", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendStoredJsonFile(req, CONFIG_PATH, "{}");
  });

  // --- POST /api/config (Zero-RAM-buffer streaming write) ---
  server.on(
    "/api/config", ASYNC_POST,
    [](AsyncWebServerRequest *req) {
      finalizeStreamUpload(req);
    },
    nullptr,
    [](AsyncWebServerRequest *req, uint8_t *data, size_t len, size_t index, size_t total) {
      handleStreamBody(req, data, len, index, total, CONFIG_TMP_PATH,
                       CONFIG_PATH, MAX_CONFIG_BYTES, true);
    });

  // --- GET /api/design (Streams /design.json directly from flash) ---
  server.on("/api/design", ASYNC_GET, [](AsyncWebServerRequest *req) {
    sendStoredJsonFile(req, DESIGN_PATH, "[]");
  });

  // --- POST /api/design (Zero-RAM-buffer streaming write up to 64 KB) ---
  server.on(
    "/api/design", ASYNC_POST,
    [](AsyncWebServerRequest *req) {
      finalizeStreamUpload(req);
    },
    nullptr,
    [](AsyncWebServerRequest *req, uint8_t *data, size_t len, size_t index, size_t total) {
      handleStreamBody(req, data, len, index, total, DESIGN_TMP_PATH,
                       DESIGN_PATH, MAX_DESIGN_BYTES, false);
    });

  // --- POST /api/time/sync (Non-blocking NTP + Timezone sync) ---
  server.on(
    "/api/time/sync", ASYNC_POST,
    [](AsyncWebServerRequest *req) {
      SmallJsonBody *buf = static_cast<SmallJsonBody *>(req->_tempObject);
      if (buf && !buf->overflow && buf->len > 0) {
        JsonDocument doc;
        if (!deserializeJson(doc, buf->data)) {
          String srv = String(doc["ntpServer"] | (const char *)ntpServerBuf);
          srv.trim();
          if (!srv.isEmpty()) {
            strncpy(ntpServerBuf, srv.c_str(), sizeof(ntpServerBuf) - 1);
            ntpServerBuf[sizeof(ntpServerBuf) - 1] = '\0';
          }
          if (!doc["tzOffset"].isNull()) {
            tzOffsetHours = doc["tzOffset"].as<String>().toFloat();
            gmtOffsetSec = (long)lroundf(tzOffsetHours * 3600.0f);
          }
          saveTimeToNvs();
        }
      }
      if (buf) {
        delete buf;
        req->_tempObject = nullptr;
      }

      bool started = syncTime();
      char formatted[32] = "";
      struct tm ti;
      if (readCurrentLocalTime(&ti)) {
        formatSyncTimestamp(&ti, formatted, sizeof(formatted));
        lastSyncTimeStr = String(formatted);
        saveTimeToNvs();
      }

      JsonDocument out;
      out["ok"] = started;
      out["synced"] = timeSynced;
      out["formattedTime"] = (const char *)formatted;

      AsyncResponseStream *res = req->beginResponseStream("application/json");
      serializeJson(out, *res);
      req->send(res);
    },
    nullptr, handleSmallJsonBody);

  // --- POST /api/wifi/portal (Launch WiFiManager AP with UI parameters) ---
  server.on(
    "/api/wifi/portal", ASYNC_POST,
    [](AsyncWebServerRequest *req) {
      bool forget = false;
      SmallJsonBody *buf = static_cast<SmallJsonBody *>(req->_tempObject);
      if (buf && !buf->overflow && buf->len > 0) {
        JsonDocument doc;
        if (!deserializeJson(doc, buf->data)) {
          forget = doc["forget"] | false;
          String apN = String(doc["apName"] | netCfg.apName.c_str());
          apN.trim();
          if (!apN.isEmpty()) netCfg.apName = apN;
          if (doc["apPass"].is<const char *>()) {
            netCfg.apPass = String(doc["apPass"].as<const char *>());
          }
          int to = doc["apTimeout"] | netCfg.apTimeout;
          if (to >= 30 && to <= 600) netCfg.apTimeout = to;
          saveNetworkToNvs();
        }
      }
      if (buf) {
        delete buf;
        req->_tempObject = nullptr;
      }

      req->send(200, "application/json", "{\"ok\":true}");
      portalForgetWifi = forget;
      portalStartAt = millis() + 450;
      portalPending = true;
    },
    nullptr, handleSmallJsonBody);

  // --- POST /api/auth/forget-boot (Non-blocking 5s BOOT button verification) ---
  server.on("/api/auth/forget-boot", ASYNC_POST, [](AsyncWebServerRequest *req) {
    if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) != pdTRUE) {
      req->send(503, "application/json", "{\"bootHeld\":false}");
      return;
    }

    if (bootHoldSatisfied) {
      bootHoldSatisfied = false;
      xSemaphoreGive(asyncReqMutex);
      notifyStorage();
      req->send(200, "application/json", "{\"bootHeld\":true}");
      return;
    }

    if (pendingForgetBootReq != nullptr) {
      xSemaphoreGive(asyncReqMutex);
      req->send(409, "application/json", "{\"bootHeld\":false,\"error\":\"Already waiting\"}");
      return;
    }

    pendingForgetBootReq = req;
    forgetBootDeadlineMs = millis() + FORGET_BOOT_WINDOW_MS;
    forgetBootHoldStart = 0;

    req->onDisconnect([req]() {
      if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
        if (pendingForgetBootReq == req) {
          pendingForgetBootReq = nullptr;
        }
        xSemaphoreGive(asyncReqMutex);
      }
    });

    xSemaphoreGive(asyncReqMutex);
  });

  // --- GET /api/scan (Non-blocking mDNS service discovery in loop()) ---
  server.on("/api/scan", ASYNC_GET, [](AsyncWebServerRequest *req) {
    if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) != pdTRUE) {
      req->send(503, "application/json", "[]");
      return;
    }

    if (pendingScanReq != nullptr) {
      xSemaphoreGive(asyncReqMutex);
      req->send(503, "application/json", "[]");
      return;
    }

    scanIotOnly = !req->hasParam("iotOnly") || req->getParam("iotOnly")->value() != "0";
    String portsStr = req->hasParam("ports") ? req->getParam("ports")->value() : "";
    scanWantMqtt = (portsStr.indexOf("1883") >= 0);

    String gw = req->hasParam("gateway") ? req->getParam("gateway")->value() : "";
    gw.trim();
    strncpy(scanGateway, gw.c_str(), sizeof(scanGateway) - 1);
    scanGateway[sizeof(scanGateway) - 1] = '\0';

    String tld = req->hasParam("tld") ? req->getParam("tld")->value() : ".local";
    tld.trim();
    if (tld.isEmpty()) tld = ".local";
    strncpy(scanTld, tld.c_str(), sizeof(scanTld) - 1);
    scanTld[sizeof(scanTld) - 1] = '\0';

    pendingScanReq = req;
    req->onDisconnect([req]() {
      if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
        if (pendingScanReq == req) {
          pendingScanReq = nullptr;
        }
        xSemaphoreGive(asyncReqMutex);
      }
    });

    xSemaphoreGive(asyncReqMutex);
  });

  // --- POST /api/reboot ---
  server.on("/api/reboot", ASYNC_POST, [](AsyncWebServerRequest *req) {
    req->send(200, "application/json", "{\"ok\":true,\"msg\":\"Restarting...\"}");
    restartPending = true;
    restartAt = millis() + 600;
  });

  // --- POST /api/reset?mode=data|settings|factory ---
  server.on("/api/reset", ASYNC_POST, [](AsyncWebServerRequest *req) {
    String mode = req->hasParam("mode") ? req->getParam("mode")->value() : "factory";
    mode.trim();
    mode.toLowerCase();

    if (mode == "data") {
      // 1. RESET DATA: Erase 2D designs in SPIFFS
      //    (devices, shortcuts, groups, favorites are saved via /api/config)
      if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
        if (SPIFFS.exists(DESIGN_PATH)) SPIFFS.remove(DESIGN_PATH);
        if (SPIFFS.exists(DESIGN_TMP_PATH)) SPIFFS.remove(DESIGN_TMP_PATH);
        xSemaphoreGive(fsMutex);
      }
      notifyStorage();
      Serial.println("[RESET] Data reset complete (/design.json removed)");
      req->send(200, "application/json", "{\"ok\":true,\"mode\":\"data\"}");
      return;
    }

    if (mode == "settings") {
      // 2. RESET SETTINGS: Clear Network (hubnet) & Time (hubtime) NVS, keep WiFi & Designs
      bool wasStatic = !netCfg.dhcp;

      Preferences p;
      p.begin("hubnet", false);
      p.clear();
      p.end();

      p.begin("hubtime", false);
      p.clear();
      p.end();

      timeSynced = false;
      loadNetworkAndTimeFromNvs();
      pendingMdnsRefresh = true;
      pendingNtpResync = true;
      if (wasStatic) {
        pendingIpReapply = true;
        ipReapplyAt = millis() + 1500;  // Wait so /api/config POST finishes first
      }

      notifyStorage();
      Serial.println("[RESET] Settings reset complete (hubnet & hubtime NVS cleared)");
      req->send(200, "application/json", "{\"ok\":true,\"mode\":\"settings\"}");
      return;
    }

    if (mode == "factory") {
      // 3. FACTORY RESET: Erase SPIFFS files + hubnet + hubtime + WiFi (wfcfg) + Reboot
      if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
        if (SPIFFS.exists(CONFIG_PATH)) SPIFFS.remove(CONFIG_PATH);
        if (SPIFFS.exists(CONFIG_TMP_PATH)) SPIFFS.remove(CONFIG_TMP_PATH);
        if (SPIFFS.exists(DESIGN_PATH)) SPIFFS.remove(DESIGN_PATH);
        if (SPIFFS.exists(DESIGN_TMP_PATH)) SPIFFS.remove(DESIGN_TMP_PATH);
        xSemaphoreGive(fsMutex);
      }

      Preferences p;
      p.begin("hubnet", false);
      p.clear();
      p.end();

      p.begin("hubtime", false);
      p.clear();
      p.end();

      clearSavedWifiCredentials();  // Erases NVS "wfcfg" (SSID & Password)

      timeSynced = false;
      loadNetworkAndTimeFromNvs();
      notifyStorage();
      Serial.println("[RESET] Factory reset complete - wiping WiFi & rebooting...");

      // Send HTTP 200 BEFORE dropping WiFi so the browser receives confirmation
      req->send(200, "application/json", "{\"ok\":true,\"mode\":\"factory\",\"rebooting\":true}");

      factoryWifiWipePending = true;
      restartPending = true;
      restartAt = millis() + 800;
      return;
    }

    req->send(400, "application/json", "{\"ok\":false,\"error\":\"Invalid reset mode\"}");
  });

  // --- Fallback & CORS Preflight ---
  server.onNotFound([](AsyncWebServerRequest *req) {
    if (req->method() == ASYNC_OPTIONS) {
      req->send(204);
      return;
    }
    Serial.printf("[HTTP] 404 %s (method=%u)\n", req->url().c_str(), (unsigned)req->method());
    if (req->url().startsWith("/api/")) {
      req->send(404, "application/json", "{\"error\":\"API route not found\"}");
      return;
    }
    req->send(404, "text/plain", "Not found");
  });

  server.begin();
  webServerRunning = true;
  Serial.println("[SERVER] Web server listening on port 80");
}

// ============================================================================
// 14. SETUP
// ============================================================================
void setup() {
  std::set_new_handler(oomNewHandler);

  fsMutex = xSemaphoreCreateMutex();
  asyncReqMutex = xSemaphoreCreateMutex();

  pinMode(LED_PIN, OUTPUT);
  pinMode(BUILTIN_LED_PIN, OUTPUT);
  pinMode(BUZZER_PIN, OUTPUT);
  pinMode(BOOT_BUTTON, INPUT_PULLUP);
  digitalWrite(LED_PIN, LOW);
  digitalWrite(BUILTIN_LED_PIN, LOW);
  digitalWrite(BUZZER_PIN, LOW);

  snprintf(bootIdStr, sizeof(bootIdStr), "%08lX", (unsigned long)esp_random());

  Serial.begin(115200);
  Serial.println("\n==================================");
  Serial.println("  ESP32 Smart Hub Starting");
  Serial.printf("  Boot ID: %s | Heap: %lu B\n", bootIdStr, (unsigned long)ESP.getFreeHeap());
  Serial.println("==================================");

  beepShort(1);
  delay(1200);

  if (!SPIFFS.begin(true, "/spiffs", 10)) {
    Serial.println("[ERROR] SPIFFS mount failed!");
  } else {
    // Clean any incomplete temporary files left by an unexpected power loss
    if (SPIFFS.exists(CONFIG_TMP_PATH)) SPIFFS.remove(CONFIG_TMP_PATH);
    if (SPIFFS.exists(DESIGN_TMP_PATH)) SPIFFS.remove(DESIGN_TMP_PATH);
    Serial.printf("[OK] SPIFFS mounted (%lu / %lu B used)\n",
                  (unsigned long)SPIFFS.usedBytes(), (unsigned long)SPIFFS.totalBytes());

    File root = SPIFFS.open("/");
    if (root) {
      for (File f = root.openNextFile(); f; f = root.openNextFile()) {
        Serial.printf("  [SPIFFS] %s (%u B)\n", f.name(), (unsigned)f.size());
      }
      root.close();
    }
  }

  loadNetworkAndTimeFromNvs();

  // Hold BOOT at startup to recover WiFi / reset Static IP back to DHCP
  if (digitalRead(BOOT_BUTTON) == LOW) {
    beepShort(2);
    netCfg.dhcp = true;
    saveNetworkToNvs();
    runWifiConfigPortal(false, true);
  }

  // Event-driven WiFi state notifications (lock-free, handled safely in loop)
  WiFi.onEvent([](WiFiEvent_t event, WiFiEventInfo_t info) {
    (void)info;
    if (event == ARDUINO_EVENT_WIFI_STA_GOT_IP) {
      wifiGotIpFlag = true;
      wifiDisconnectedFlag = false;
    } else if (event == ARDUINO_EVENT_WIFI_STA_DISCONNECTED) {
      wifiDisconnectedFlag = true;
    }
  });

  // Connect WiFi FIRST so lwIP & port 80 are clean if WiFiManager portal runs
  connectToSavedWiFi();
  setupWebServer();
  lastWifiRetryMs = millis();

  if (WiFi.status() == WL_CONNECTED) {
    WiFi.setSleep(false);
    startOrRefreshMdns();
    syncTime();
    wifiGotIpFlag = false;  // Already initialized above
  }

  Serial.printf("[READY] Free Heap: %lu B | Min Heap: %lu B\n",
                (unsigned long)ESP.getFreeHeap(), (unsigned long)ESP.getMinFreeHeap());
}

// ============================================================================
// 15. MAIN LOOP (NON-BLOCKING & SELF-HEALING)
// ============================================================================
void loop() {
  unsigned long now = millis();

  // 1. Smooth Server, mDNS & Time Refresh whenever WiFi gets/regains an IP
  if (wifiGotIpFlag) {
    wifiGotIpFlag = false;
    WiFi.setSleep(false);
    Serial.printf("[WIFI] IP Ready: %s\n", WiFi.localIP().toString().c_str());

    setupWebServer();  // Safe: starts server if stopped, never duplicates routes
    startOrRefreshMdns();
    syncTime();
  }

  // 2. Apply newly saved Static IP / DHCP configuration after HTTP response flushed
  if (pendingIpReapply && (int32_t)(now - ipReapplyAt) >= 0) {
    pendingIpReapply = false;
    String ssid, pass;
    if (getSavedWifiCredentials(ssid, pass)) {
      Serial.println("[WIFI] Applying updated IP configuration...");
      WiFi.disconnect(false, false);
      delay(100);
      applyStationIpConfig();
      WiFi.begin(ssid.c_str(), pass.c_str());
    }
  }

  // 3. Silent background WiFi reconnection if router dropped or booted later
  if (!portalPending && !restartPending && WiFi.status() != WL_CONNECTED && (now - lastWifiRetryMs >= WIFI_RETRY_INTERVAL_MS)) {
    lastWifiRetryMs = now;
    String ssid, pass;
    if (getSavedWifiCredentials(ssid, pass)) {
      Serial.println("[WIFI] Reconnecting in background...");
      applyStationIpConfig();
      WiFi.disconnect(false, false);
      WiFi.begin(ssid.c_str(), pass.c_str());
    }
  }

  // 4. Refresh mDNS if hostname or toggle changed in config.html
  if (pendingMdnsRefresh) {
    pendingMdnsRefresh = false;
    startOrRefreshMdns();
  }

  // 5. Background Time Sync (on change, retry if unsynced, and hourly refresh)
  if (pendingNtpResync) {
    pendingNtpResync = false;
    syncTime();
  }

  if (syncTimestampPending) {
    syncTimestampPending = false;
    updateLastSyncTimestamp();
  }

  if (WiFi.status() == WL_CONNECTED) {
    unsigned long syncInterval = timeSynced ? NTP_PERIODIC_SYNC_MS : NTP_RETRY_UNSYNCED_MS;
    if (now - lastNtpSyncAttemptMs >= syncInterval) {
      syncTime();
    }
  }

  // 6. Hardware LED/Buzzer feedback, BOOT button auth & native mDNS scan
  serviceNotifyStorage();
  serviceBootButtonAndForgetAuth();
  serviceNativeMdnsScan();

  // 7. Launch WiFi Config Portal safely after HTTP response has flushed
  if (portalPending && (int32_t)(now - portalStartAt) >= 0) {
    portalPending = false;
    runWifiConfigPortal(portalForgetWifi, true);
  }

  // 8. Sustained critical low-heap self-recovery (avoids false triggers on brief spikes)
  if (ESP.getFreeHeap() < CRITICAL_LOW_HEAP_BYTES) {
    if (lowHeapSinceMs == 0) lowHeapSinceMs = now;
    if (!restartPending && (now - lowHeapSinceMs >= 5000UL)) {
      Serial.println("[MEM] Sustained critical low heap - restarting cleanly");
      restartPending = true;
      restartAt = now + 200;
    }
  } else {
    lowHeapSinceMs = 0;
  }

  // 9. Deferred clean reboot
  if (restartPending && (int32_t)(now - restartAt) >= 0) {
    restartPending = false;
    if (webServerRunning) server.end();
    if (mdnsRunning) MDNS.end();
    if (factoryWifiWipePending) {
      factoryWifiWipePending = false;
      WiFi.disconnect(true, true);  // Also erases ESP-IDF SDK WiFi flash credentials
      delay(150);
    }
    delay(50);
    ESP.restart();
  }

  delay(2);  // Yield cleanly to IDLE/WDT & async_tcp task
}