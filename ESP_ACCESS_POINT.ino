#include "esp_heap_caps.h"
#include "esp_partition.h"
#include "esp_sntp.h"
#include "esp_timer.h"
#include "time.h"
#include <Arduino.h>
#include <WiFi.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <WiFiManager.h>
#include <Wire.h>
#include <new>

#include <ArduinoJson.h>
#include <ESPAsyncWebServer.h>
#include <ESPmDNS.h>
#include <FFat.h>
#include <FS.h>
#include <Preferences.h>
#include <SPIFFS.h>
#include <math.h>
#include "mbedtls/sha256.h"

// Explicit ESPAsyncWebServer method bitmasks (avoids collision with WebServer.h included by WiFiManager.h)
static constexpr WebRequestMethod ASYNC_GET = AsyncWebRequestMethod::HTTP_GET;
static constexpr WebRequestMethod ASYNC_POST = AsyncWebRequestMethod::HTTP_POST;
static constexpr WebRequestMethod ASYNC_OPTIONS = AsyncWebRequestMethod::HTTP_OPTIONS;

// ============================================================================
// 1. BOARD AUTO-DETECTION, HARDWARE PINS & SYSTEM LIMITS
// ============================================================================
#if defined(CONFIG_IDF_TARGET_ESP32S3)
#define HUB_BOARD_NAME "ESP32-S3"
#define HAS_BUILTIN_RGB_LED 1
// Standard ESP32-S3 N16R8 DevKitC-1 uses GPIO 48 for onboard WS2812B RGB LED.
// (Change to 38 only if your board silkscreen/revision specifies GPIO 38.)
#define S3_RGB_LED_PIN 48

// Safe GPIOs on ESP32-S3 N16R8:
#define LED_PIN 16
#define BUZZER_PIN 17
#define BOOT_BUTTON 0

static constexpr size_t MAX_CONFIG_BYTES = 524288;    // 512 KB on S3 (use 1048576 for 1 MB)
static constexpr size_t MAX_DESIGN_BYTES = 2097152;   // 2 MB on S3 (use 3145728 for 3 MB)
static constexpr size_t MAX_SMALL_JSON_BYTES = 4096;  // 4 KB
static constexpr uint8_t FS_MAX_OPEN_FILES = 16;
static constexpr int MAX_MDNS_SCAN_RESULTS = 64;
static constexpr uint8_t MAX_TRACKED_DEVICES = 128;  // Track up to 128 devices on S3
#else
#define HUB_BOARD_NAME "ESP32-Dev"
#define HAS_BUILTIN_RGB_LED 0
#define BUILTIN_LED_PIN 2

// Safe GPIOs on Classic ESP32 Dev Module:
#define LED_PIN 16
#define BUZZER_PIN 17
#define BOOT_BUTTON 0

static constexpr size_t MAX_CONFIG_BYTES = 20480;     // 20 KB (16 KB UI + margin)
static constexpr size_t MAX_DESIGN_BYTES = 69632;     // 68 KB (64 KB UI + margin)
static constexpr size_t MAX_SMALL_JSON_BYTES = 1024;  // 1 KB
static constexpr uint8_t FS_MAX_OPEN_FILES = 10;
static constexpr int MAX_MDNS_SCAN_RESULTS = 24;
static constexpr uint8_t MAX_TRACKED_DEVICES = 32;
#endif

// - Classic ESP32 Dev Module: SDA = 21, SCL = 22
// - ESP32-S3 N16R8 Module:    SDA = 8,  SCL = 9
static constexpr uint8_t I2C_SDA_PIN = SDA;
static constexpr uint8_t I2C_SCL_PIN = SCL;
static constexpr uint32_t I2C_CLOCK_HZ = 400000UL;

static const char *CONFIG_PATH = "/config.json";
static const char *CONFIG_TMP_PATH = "/config.tmp";
static const char *DESIGN_PATH = "/design.json";
static const char *DESIGN_TMP_PATH = "/design.tmp";

static const uint32_t MIN_FREE_HEAP_FOR_FILES = 12000;
static const uint32_t MIN_FREE_HEAP_FOR_UPLOAD = 16000;
static const uint32_t CRITICAL_LOW_HEAP_BYTES = 8000;

static const int WIFI_BOOT_MAX_ATTEMPTS = 12;                 // 12 * 500ms = 6s max boot wait
static const unsigned long WIFI_RETRY_INTERVAL_MS = 15000UL;  // Silent reconnect every 15s
static const unsigned long NTP_RETRY_UNSYNCED_MS = 60000UL;   // Retry every 60s until synced
static const unsigned long NTP_PERIODIC_SYNC_MS = 3600000UL;  // Hourly background sync
// Shared Auth Salt (matches KEY_SALT in index.html, config.html, layout.html, design.html)
static const char *HUB_AUTH_SALT = "esp32_nvs_hub_v1_secret";

// Uploader & Hub Security / 5s+10s Forget-BOOT Constants
static constexpr uint8_t UPLOAD_AUTH_MAX_ATTEMPTS = 3;
static const char *UPLOAD_DEFAULT_ADMIN_USER = "esp";
static const char *UPLOAD_DEFAULT_ADMIN_PASS = "456456";
static const unsigned long UPLOAD_SESSION_TTL_MS = 900000UL;        // 15 min inactivity timeout
static const unsigned long UPLOAD_FORGET_PRESS_WINDOW_MS = 5000UL;  // 5s window to press BOOT
static const unsigned long UPLOAD_FORGET_HOLD_MS = 10000UL;         // 10s continuous hold
static const unsigned long UPLOAD_FORGET_DEBOUNCE_MS = 120UL;       // Switch bounce tolerance

// ============================================================================
// 2. PSRAM ALLOCATOR (ARDUINOJSON v7) & PSRAM STATIC ASSET CACHE
// ============================================================================
bool hasPsram = false;

struct PsramAllocator : ArduinoJson::Allocator {
  void *allocate(size_t size) override {
    if (hasPsram) {
      void *ptr = heap_caps_malloc(size, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
      if (ptr) return ptr;
    }
    return malloc(size);
  }
  void deallocate(void *pointer) override {
    free(pointer);
  }
  void *reallocate(void *ptr, size_t new_size) override {
    if (hasPsram) {
      void *newPtr = heap_caps_realloc(ptr, new_size, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
      if (newPtr) return newPtr;
    }
    return realloc(ptr, new_size);
  }
};
static PsramAllocator psramAllocator;

// Static web file cache in 8 MB OPI PSRAM (eliminates repeated flash reads on S3)
static constexpr size_t MAX_PSRAM_CACHE_ENTRIES = 12;
static constexpr size_t MAX_PSRAM_CACHE_FILE_BYTES = 524288;  // 512 KB per asset

struct PsramCacheEntry {
  char path[40] = "";
  uint8_t *data = nullptr;
  size_t len = 0;
  bool isGzip = false;
  bool valid = false;
};
static PsramCacheEntry psramCache[MAX_PSRAM_CACHE_ENTRIES];
static size_t psramCacheTotalBytes = 0;

// Must be called ONLY while holding fsMutex
void clearPsramCacheLocked() {
  for (size_t i = 0; i < MAX_PSRAM_CACHE_ENTRIES; i++) {
    if (psramCache[i].data) {
      free(psramCache[i].data);
      psramCache[i].data = nullptr;
    }
    psramCache[i].path[0] = '\0';
    psramCache[i].len = 0;
    psramCache[i].isGzip = false;
    psramCache[i].valid = false;
  }
  psramCacheTotalBytes = 0;
}

// ============================================================================
// 3. UNIFIED FILESYSTEM ABSTRACTION (SPIFFS / 16MB FFat AUTO-DETECT)
// ============================================================================
fs::FS *hubFS = nullptr;
bool fsIsFFat = false;
const char *fsTypeName = "NONE";

uint64_t fsUsedBytes() {
  if (!hubFS) return 0;
  return fsIsFFat ? (uint64_t)FFat.usedBytes() : (uint64_t)SPIFFS.usedBytes();
}

uint64_t fsTotalBytes() {
  if (!hubFS) return 0;
  return fsIsFFat ? (uint64_t)FFat.totalBytes() : (uint64_t)SPIFFS.totalBytes();
}

bool initStorage() {
  const esp_partition_t *spiffsPart = esp_partition_find_first(
    ESP_PARTITION_TYPE_DATA, ESP_PARTITION_SUBTYPE_DATA_SPIFFS, nullptr);
  const esp_partition_t *fatPart = esp_partition_find_first(
    ESP_PARTITION_TYPE_DATA, ESP_PARTITION_SUBTYPE_DATA_FAT, nullptr);

  // Prefer FATFS when a large FAT partition is selected (e.g., 16M Flash 9.9MB/12.5MB FATFS),
  if (fatPart && !spiffsPart) {
    Serial.println("[FS] Detected FAT partition - mounting FFat (first-time format may take ~15s)...");
    if (FFat.begin(true, "/ffat", FS_MAX_OPEN_FILES)) {
      hubFS = &FFat;
      fsIsFFat = true;
      fsTypeName = "FFat";
      return true;
    }
    Serial.println("[ERROR] FFat mount failed!");
    return false;
  }

  if (spiffsPart) {
    if (SPIFFS.begin(true, "/spiffs", FS_MAX_OPEN_FILES)) {
      hubFS = &SPIFFS;
      fsIsFFat = false;
      fsTypeName = "SPIFFS";
      return true;
    }
    Serial.println("[ERROR] SPIFFS mount failed!");
  }

  // Fallback if both or custom partition labels exist
  if (fatPart && FFat.begin(true, "/ffat", FS_MAX_OPEN_FILES)) {
    hubFS = &FFat;
    fsIsFFat = true;
    fsTypeName = "FFat";
    return true;
  }

  return false;
}

// ============================================================================
// 4. BUILT-IN /upload FILE MANAGER UI (PASSWORD PROTECTED + IN-BOX FILE LIST)
// ============================================================================
static const char UPLOAD_HTML[] PROGMEM = R"rawliteral(<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Smart Hub Flash Uploader</title>
<style>
  :root{--bg:#0d1117;--card:#161b22;--bd:#30363d;--tx:#e6edf3;--mut:#8b949e;--acc:#2f81f7;--ok:#3fb950;--warn:#d29922;--err:#f85149}
  *{box-sizing:border-box;font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
  body{margin:0;background:var(--bg);color:var(--tx);padding:20px}
  .wrap{max-width:720px;margin:0 auto}
  .card{background:var(--card);border:1px solid var(--bd);border-radius:12px;padding:18px;margin-bottom:16px}
  .hidden{display:none!important}
  h1{margin:0 0 6px;font-size:20px;display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap}
  .sub{color:var(--mut);font-size:13px;margin:0 0 14px}
  .field{margin-bottom:12px}
  .field label{display:block;font-size:12px;color:var(--mut);margin-bottom:5px;font-weight:600}
  .field input{width:100%;background:#0d1117;border:1px solid var(--bd);border-radius:8px;padding:10px 12px;color:var(--tx);font-size:14px;outline:none}
  .field input:focus{border-color:var(--acc)}
  .alert{padding:10px 12px;border-radius:8px;font-size:13px;margin-bottom:12px;border:1px solid var(--bd);background:#0d1117}
  .alert.err{border-color:rgba(248,81,73,.5);background:rgba(248,81,73,.1);color:#ffa198}
  .alert.ok{border-color:rgba(63,185,80,.5);background:rgba(63,185,80,.1);color:#7ee787}
  .alert.warn{border-color:rgba(210,153,34,.5);background:rgba(210,153,34,.1);color:#f2cc60}
  .stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:10px;margin-bottom:12px}
  .stat{background:#0d1117;border:1px solid var(--bd);border-radius:8px;padding:10px}
  .stat b{display:block;font-size:15px;margin-top:2px}
  .stat span{font-size:11px;color:var(--mut);text-transform:uppercase}
  .bar{height:8px;background:#21262d;border-radius:99px;overflow:hidden}
  .bar>div{height:100%;background:var(--acc);width:0%;transition:width .18s}
  .drop{border:2px dashed var(--bd);border-radius:10px;padding:24px 16px;text-align:center;cursor:pointer;transition:.15s}
  .drop.over{border-color:var(--acc);background:rgba(47,129,247,.08)}
  .drop.has-files{border-color:var(--ok);background:rgba(63,185,80,.04);text-align:left;padding:16px}
  .dz-head{display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;gap:8px;flex-wrap:wrap}
  .dz-list{display:flex;flex-direction:column;gap:6px;max-height:220px;overflow:auto}
  .dz-item{display:flex;align-items:center;justify-content:space-between;gap:10px;background:#0d1117;border:1px solid var(--bd);border-radius:8px;padding:7px 10px;font-size:13px}
  .dz-name{font-family:ui-monospace,Consolas,monospace;word-break:break-all}
  .dz-meta{display:flex;align-items:center;gap:8px;flex-shrink:0}
  .dz-sz{font-family:ui-monospace,Consolas,monospace;font-size:12px;color:var(--mut)}
  .dz-rm{background:transparent;border:1px solid rgba(248,81,73,.4);color:var(--err);border-radius:6px;padding:2px 7px;font-size:12px;cursor:pointer}
  .row{display:flex;gap:10px;flex-wrap:wrap;margin-top:12px;align-items:center}
  button,a.btn{background:var(--acc);color:#fff;border:0;border-radius:8px;padding:9px 14px;font-size:14px;font-weight:600;cursor:pointer;text-decoration:none;display:inline-flex;align-items:center;gap:6px}
  button.sec,a.sec{background:#21262d;border:1px solid var(--bd);color:var(--tx)}
  button.warn{background:rgba(210,153,34,.18);border:1px solid rgba(210,153,34,.5);color:#f2cc60}
  button.del{background:transparent;border:1px solid rgba(248,81,73,.4);color:var(--err);padding:4px 9px;font-size:12px}
  button:disabled{opacity:.5;cursor:not-allowed}
  #log{margin-top:12px;font-family:ui-monospace,Consolas,monospace;font-size:12px;background:#0d1117;border:1px solid var(--bd);border-radius:8px;padding:10px;max-height:160px;overflow:auto;white-space:pre-wrap;display:none}
  table{width:100%;border-collapse:collapse;font-size:13px}
  th,td{text-align:left;padding:8px 6px;border-bottom:1px solid var(--bd)}
  th{color:var(--mut);font-weight:600;font-size:12px}
  td.sz{font-family:ui-monospace,Consolas,monospace;color:var(--mut);white-space:nowrap}
  td.act{text-align:right;white-space:nowrap}
</style>
</head>
<body>
<div class="wrap">
  <!-- AUTH GATE -->
  <div class="card" id="authCard" style="max-width:440px;margin:32px auto">
    <h1><span>Protected Flash Uploader</span></h1>
    <p class="sub">Sign in with an <b>Admin</b>. Maximum 3 failed attempts before hardware restart is required.</p>
    <div id="authMsg" class="alert hidden"></div>
    <form id="loginForm" onsubmit="doLogin(event)">
      <div class="field">
        <label for="uName">Admin Username</label>
        <input id="uName" type="text" autocomplete="username" required>
      </div>
      <div class="field">
        <label for="uPass">Password</label>
        <input id="uPass" type="password" autocomplete="current-password" required>
      </div>
      <div class="row" style="justify-content:space-between">
        <button id="loginBtn" type="submit">Unlock</button>
        <button id="forgetBtn" type="button" class="warn" onclick="startForgetFlow()">Forget</button>
      </div>
    </form>

    <div id="forgetBox" class="hidden" style="margin-top:14px;padding-top:14px;border-top:1px solid var(--bd)">
      <div id="forgetText" style="font-size:13px;font-weight:600;margin-bottom:8px"></div>
      <div class="bar"><div id="forgetBar"></div></div>
    </div>
  </div>

  <!-- UPLOADER WORKSPACE (ONLY SHOWN AFTER SERVER VERIFIES TOKEN) -->
  <div id="uploaderApp" class="hidden">
    <div class="card">
      <h1>
        <span>Flash Storage Uploader</span>
        <span style="display:flex;gap:8px;flex-wrap:wrap">
          <a class="btn sec" href="/">Open Hub</a>
          <button class="sec" onclick="rebootHub()">Reboot</button>
          <button class="del" onclick="doLogout()">Logout</button>
        </span>
      </h1>
      <p class="sub">Drop all <b>.gz</b> / web files from your <code>data/</code> folder here to upload directly into flash.</p>
      <div class="stats">
        <div class="stat"><span>Board / FS</span><b id="stBoard">-</b></div>
        <div class="stat"><span>Storage Used</span><b id="stUsed">-</b></div>
        <div class="stat"><span>Storage Free</span><b id="stFree">-</b></div>
        <div class="stat"><span>PSRAM</span><b id="stPsram">-</b></div>
      </div>
      <div class="bar"><div id="stBar"></div></div>
    </div>

    <div class="card">
      <div class="drop" id="dropZone" onclick="fileInput.click()">
        <div id="dzEmpty">
          <div style="font-size:15px;font-weight:600">Drag &amp; drop the files here</div>
          <div style="font-size:12px;color:var(--mut);margin-top:4px">Supports multiple files (index.html.gz, config.html.gz, layout.html.gz, design.html.gz, *.svg.gz)</div>
        </div>
        <div id="dzFilled" class="hidden">
          <div class="dz-head">
            <span style="font-size:13px;font-weight:600;color:var(--ok)" id="dzSummary">0 files ready to upload</span>
            <span style="font-size:12px;color:var(--mut)">Click or drop more files to add</span>
          </div>
          <div id="dropFileList" class="dz-list"></div>
        </div>
        <input id="fileInput" type="file" multiple style="display:none">
      </div>
      <div class="row">
        <button id="upBtn" onclick="uploadQueued()" disabled>Upload (0)</button>
        <button id="clrBtn" class="sec" onclick="clearQueue()" disabled>Clear Queue</button>
        <button class="sec" onclick="loadList()">Refresh List</button>
        <span id="upStatus" style="font-size:13px;color:var(--mut)"></span>
      </div>
      <div class="bar" style="margin-top:10px"><div id="upBar"></div></div>
      <div id="log"></div>
    </div>

    <div class="card">
      <h1 style="font-size:16px;margin-bottom:10px"><span>Files in Flash (<span id="fCount">0</span>)</span></h1>
      <table>
        <thead><tr><th>Path</th><th>Size</th><th style="text-align:right">Action</th></tr></thead>
        <tbody id="fBody"><tr><td colspan="3" style="color:var(--mut)">Loading...</td></tr></tbody>
      </table>
    </div>
  </div>
</div>
<script>
let authToken = '';
let queued = [];
let forgetTimer = null;

const authCard = document.getElementById('authCard');
const authMsg = document.getElementById('authMsg');
const loginBtn = document.getElementById('loginBtn');
const forgetBtn = document.getElementById('forgetBtn');
const forgetBox = document.getElementById('forgetBox');
const forgetText = document.getElementById('forgetText');
const forgetBar = document.getElementById('forgetBar');
const uploaderApp = document.getElementById('uploaderApp');

const dropZone = document.getElementById('dropZone');
const dzEmpty = document.getElementById('dzEmpty');
const dzFilled = document.getElementById('dzFilled');
const dzSummary = document.getElementById('dzSummary');
const dropFileList = document.getElementById('dropFileList');
const fileInput = document.getElementById('fileInput');
const upBtn = document.getElementById('upBtn');
const clrBtn = document.getElementById('clrBtn');
const upStatus = document.getElementById('upStatus');
const upBar = document.getElementById('upBar');
const logEl = document.getElementById('log');

function escHtml(s){
  return String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}
function fmtBytes(b){
  if(b >= 1048576) return (b/1048576).toFixed(2)+' MB';
  if(b >= 1024) return (b/1024).toFixed(1)+' KB';
  return b+' B';
}
function showAuthAlert(type, msg){
  authMsg.className = 'alert ' + type;
  authMsg.textContent = msg;
  authMsg.classList.remove('hidden');
}
function authHeaders(){
  return authToken ? { 'X-Upload-Token': authToken } : {};
}
function lockUiToAuth(msg){
  authToken = '';
  uploaderApp.classList.add('hidden');
  authCard.classList.remove('hidden');
  if(msg) showAuthAlert('err', msg);
}
function addLog(msg){
  logEl.style.display='block';
  logEl.textContent += msg + '\n';
  logEl.scrollTop = logEl.scrollHeight;
}

// --- IN-DROPZONE QUEUE RENDERER ---
function renderDropZone(){
  upBtn.textContent = 'Upload (' + queued.length + ')';
  upBtn.disabled = queued.length === 0;
  clrBtn.disabled = queued.length === 0;
  if(!queued.length){
    dropZone.classList.remove('has-files');
    dzEmpty.classList.remove('hidden');
    dzFilled.classList.add('hidden');
    dropFileList.innerHTML = '';
    return;
  }
  const totalBytes = queued.reduce((s, f) => s + f.size, 0);
  dropZone.classList.add('has-files');
  dzEmpty.classList.add('hidden');
  dzFilled.classList.remove('hidden');
  dzSummary.textContent = queued.length + ' file' + (queued.length > 1 ? 's' : '') + ' ready (' + fmtBytes(totalBytes) + ')';
  dropFileList.innerHTML = queued.map((f, idx) =>
    '<div class="dz-item" onclick="event.stopPropagation()">' +
      '<span class="dz-name">' + escHtml(f.name) + '</span>' +
      '<span class="dz-meta"><span class="dz-sz">' + fmtBytes(f.size) + '</span>' +
      '<button type="button" class="dz-rm" title="Remove" onclick="removeQueued(' + idx + ',event)">&times;</button></span>' +
    '</div>'
  ).join('');
}
function addFilesToQueue(fileList){
  const incoming = Array.from(fileList || []);
  for(const f of incoming){
    const existingIdx = queued.findIndex(x => x.name === f.name);
    if(existingIdx >= 0) queued[existingIdx] = f;
    else queued.push(f);
  }
  fileInput.value = '';
  renderDropZone();
}
function removeQueued(idx, ev){
  if(ev) ev.stopPropagation();
  queued.splice(idx, 1);
  renderDropZone();
}
function clearQueue(){
  queued = [];
  fileInput.value = '';
  renderDropZone();
}

fileInput.addEventListener('change', e => addFilesToQueue(e.target.files));
dropZone.addEventListener('dragover', e => { e.preventDefault(); dropZone.classList.add('over'); });
dropZone.addEventListener('dragleave', () => dropZone.classList.remove('over'));
dropZone.addEventListener('drop', e => {
  e.preventDefault();
  dropZone.classList.remove('over');
  addFilesToQueue(e.dataTransfer.files);
});

// --- AUTH & FORGET FLOW ---
async function checkAuthStatus(){
  try{
    const r = await fetch('/api/upload-auth/status', { cache:'no-store' });
    const d = await r.json();
    if(d.locked){
      loginBtn.disabled = true;
      showAuthAlert('err', 'LOCKED: Maximum 3 failed attempts reached. A fresh hardware restart of the ESP32 is required (or use Forget with physical BOOT button).');
    } else {
      loginBtn.disabled = false;
      if(d.failedAttempts > 0){
        showAuthAlert('warn', 'Failed attempts: ' + d.failedAttempts + '/3. Remaining: ' + d.remainingAttempts);
      }
    }
  }catch(e){}
}

async function doLogin(ev){
  ev.preventDefault();
  const username = document.getElementById('uName').value.trim();
  const password = document.getElementById('uPass').value;
  loginBtn.disabled = true;
  try{
    const r = await fetch('/api/upload-auth/login', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ username, password })
    });
    const d = await r.json();
    if(r.ok && d.ok && d.token){
      authToken = d.token;
      document.getElementById('uPass').value = '';
      authMsg.classList.add('hidden');
      authCard.classList.add('hidden');
      uploaderApp.classList.remove('hidden');
      await loadList();
      return;
    }
    if(d.locked){
      loginBtn.disabled = true;
      showAuthAlert('err', d.error || 'LOCKED after 3 failed attempts. Fresh hardware restart required.');
    } else {
      loginBtn.disabled = false;
      showAuthAlert('err', (d.error || 'Invalid credentials') + ' (' + d.remainingAttempts + ' attempt(s) left)');
    }
  }catch(e){
    loginBtn.disabled = false;
    showAuthAlert('err', 'Connection error: ' + e.message);
  }
}

async function doLogout(){
  try{ await fetch('/api/upload-auth/logout', { method:'POST', headers: authHeaders() }); }catch(e){}
  clearQueue();
  lockUiToAuth('');
  showAuthAlert('ok', 'Logged out securely.');
}

async function startForgetFlow(){
  if(forgetTimer){ clearInterval(forgetTimer); forgetTimer = null; }
  forgetBtn.disabled = true;
  forgetBox.classList.remove('hidden');
  forgetBar.style.width = '0%';
  forgetBar.style.background = 'var(--warn)';
  forgetText.textContent = 'Arming hardware reset...';
  try{
    const r = await fetch('/api/upload-auth/forget/start', { method:'POST' });
    const d = await r.json();
    if(!r.ok || !d.ok){
      forgetBtn.disabled = false;
      forgetText.textContent = d.error || 'Could not start forget process.';
      return;
    }
    forgetTimer = setInterval(pollForgetStatus, 250);
    pollForgetStatus();
  }catch(e){
    forgetBtn.disabled = false;
    forgetText.textContent = 'Request failed: ' + e.message;
  }
}

async function pollForgetStatus(){
  try{
    const r = await fetch('/api/upload-auth/forget/status', { cache:'no-store' });
    const d = await r.json();
    if(d.state === 'wait_press'){
      const rem = (d.remainingMs / 1000).toFixed(1);
      forgetBar.style.background = 'var(--warn)';
      forgetBar.style.width = Math.min(100, ((5000 - d.remainingMs) / 5000) * 100) + '%';
      forgetText.textContent = 'Step 1/2: Press & hold onboard BOOT button within ' + rem + 's...';
    } else if(d.state === 'holding'){
      const held = (d.heldMs / 1000).toFixed(1);
      forgetBar.style.background = 'var(--acc)';
      forgetBar.style.width = Math.min(100, (d.heldMs / 10000) * 100) + '%';
      forgetText.textContent = 'Step 2/2: Keep holding BOOT button... ' + held + 's / 10.0s';
    } else {
      clearInterval(forgetTimer);
      forgetTimer = null;
      forgetBtn.disabled = false;
      if(d.state === 'done'){
        forgetBar.style.background = 'var(--ok)';
        forgetBar.style.width = '100%';
        forgetText.textContent = 'Reset complete!';
        loginBtn.disabled = false;
        document.getElementById('uName').value = 'esp';
        document.getElementById('uPass').value = '';
        showAuthAlert('ok', 'All saved users erased! Default admin created: esp / 456456');
      } else {
        forgetBar.style.background = 'var(--err)';
        forgetText.textContent = d.message || 'Reset cancelled.';
        showAuthAlert('err', d.message || 'Hardware verification failed. Try again.');
      }
    }
  }catch(e){}
}

// --- PROTECTED FILE OPERATIONS ---
async function uploadQueued(){
  if(!queued.length || !authToken) return;
  upBtn.disabled = true;
  clrBtn.disabled = true;
  logEl.textContent = '';
  let okCount = 0;
  for(let i=0;i<queued.length;i++){
    const f = queued[i];
    upStatus.textContent = 'Uploading ' + (i+1) + '/' + queued.length + ': ' + f.name;
    upBar.style.width = Math.round((i / queued.length) * 100) + '%';
    const fd = new FormData();
    fd.append('file', f, f.name);
    try{
      const r = await fetch('/api/fs/upload', { method:'POST', headers: authHeaders(), body:fd });
      if(r.status === 401){ lockUiToAuth('Session expired. Please login again.'); return; }
      const j = await r.json();
      if(r.ok && j.ok){
        okCount++;
        addLog('[OK] ' + j.path + ' (' + fmtBytes(j.bytes) + ')');
      } else {
        addLog('[ERR] ' + f.name + ': ' + (j.error || r.status));
      }
    }catch(err){
      addLog('[ERR] ' + f.name + ': ' + err.message);
    }
  }
  upBar.style.width = '100%';
  upStatus.textContent = 'Done: ' + okCount + '/' + queued.length + ' uploaded.';
  clearQueue();
  await loadList();
}

async function delFile(path){
  if(!confirm('Delete ' + path + '?')) return;
  const r = await fetch('/api/fs/delete?path=' + encodeURIComponent(path), { method:'POST', headers: authHeaders() });
  if(r.status === 401){ lockUiToAuth('Session expired. Please login again.'); return; }
  if(r.ok) await loadList();
}

async function rebootHub(){
  if(!confirm('Reboot device now?')) return;
  const r = await fetch('/api/fs/reboot', { method:'POST', headers: authHeaders() });
  if(r.status === 401){ lockUiToAuth('Session expired. Please login again.'); return; }
  upStatus.textContent = 'Rebooting...';
}

async function loadList(){
  try{
    const r = await fetch('/api/fs/list', { cache:'no-store', headers: authHeaders() });
    if(r.status === 401){ lockUiToAuth('Session expired. Please login again.'); return; }
    const d = await r.json();
    document.getElementById('stBoard').textContent = d.board + ' / ' + d.fsType;
    document.getElementById('stUsed').textContent = fmtBytes(d.usedBytes) + ' / ' + fmtBytes(d.totalBytes);
    document.getElementById('stFree').textContent = fmtBytes(d.freeBytes);
    document.getElementById('stPsram').textContent = d.psramOk ? fmtBytes(d.psramTotalBytes) : 'Off';
    const pct = d.totalBytes ? Math.min(100, (d.usedBytes / d.totalBytes) * 100) : 0;
    document.getElementById('stBar').style.width = pct.toFixed(1) + '%';
    document.getElementById('fCount').textContent = d.files.length;
    const tb = document.getElementById('fBody');
    if(!d.files.length){
      tb.innerHTML = '<tr><td colspan="3" style="color:var(--mut)">No files in flash yet. Upload your data/ files above.</td></tr>';
      return;
    }
    d.files.sort((a,b)=>a.name.localeCompare(b.name));
    tb.innerHTML = d.files.map(f =>
      '<tr><td>' + escHtml(f.name) + '</td><td class="sz">' + fmtBytes(f.size) +
      '</td><td class="act"><button class="del" onclick="delFile(\'' + f.name.replace(/\\/g,'\\\\').replace(/'/g,"\\'") + '\')">Delete</button></td></tr>'
    ).join('');
  }catch(e){
    document.getElementById('fBody').innerHTML = '<tr><td colspan="3" style="color:var(--err)">Failed to read flash list</td></tr>';
  }
}

checkAuthStatus();
</script>
</body>
</html>)rawliteral";

// ============================================================================
// 5. GLOBAL OBJECTS, I2C DISPLAY HOOK & THREAD SAFETY
// ============================================================================
AsyncWebServer server(80);
Preferences prefs;

SemaphoreHandle_t fsMutex = nullptr;
SemaphoreHandle_t asyncReqMutex = nullptr;

// 128x64 I2C OLED Object & State
uint8_t detectedI2cDisplayAddr = 0;
#define OLED_WIDTH 128
#define OLED_HEIGHT 64
#define OLED_RESET -1
Adafruit_SSD1306 display(OLED_WIDTH, OLED_HEIGHT, &Wire, OLED_RESET);
bool oledReady = false;

// Emergency / Priority Alert State (thread-safe via asyncReqMutex)
struct OledAlertState {
  bool active = false;
  bool critical = false;
  char title[22] = "";
  char line1[22] = "";
  char line2[22] = "";
  char line3[22] = "";
  unsigned long expiresAt = 0;  // 0 = persistent until cleared
};
OledAlertState oledAlert;
volatile bool oledForceRedraw = false;
unsigned long lastOledDrawMs = 0;

// Boot Console Rolling Log (3 lines)
static char oledBootLog[3][22] = { "", "", "" };

// Automatic Device Online/Offline Tracker (reads /config.json)
static constexpr unsigned long DEVICE_CHECK_INTERVAL_MS = 4000UL;  // Check 1 device every 4s
struct TrackedDevice {
  char host[48];
  uint16_t port;
  bool online;
  bool checked;
};
TrackedDevice trackedDevices[MAX_TRACKED_DEVICES];
uint8_t trackedDeviceCount = 0;
uint8_t trackedCheckIdx = 0;
uint8_t devicesOnlineCount = 0;
uint8_t devicesOfflineCount = 0;
bool deviceListReloadPending = false;
unsigned long lastDeviceCheckMs = 0;

// Optional: live override if index.html pushes counts to /api/oled/devices
bool webDeviceOverrideActive = false;
unsigned long webDeviceOverrideUntil = 0;
uint8_t webDevicesOnline = 0;
uint8_t webDevicesOffline = 0;

// Unique per-boot token so frontend resets lockout state after ESP32 restart
static char bootIdStr[12] = "00000000";

// ============================================================================
// 6. RUNTIME CONFIGURATION STATE (PERSISTED IN NVS FOR FAST BOOT)
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
// 7. VOLATILE FLAGS & NON-BLOCKING STATE MACHINES
// ============================================================================
volatile bool wifiGotIpFlag = false;
volatile bool wifiDisconnectedFlag = false;
volatile bool timeSynced = false;
volatile bool syncTimestampPending = false;
volatile bool apLedBlinkActive = false;
volatile bool notifyRgbPulsePending = false;
TaskHandle_t apLedTaskHandle = nullptr;

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

// Streaming Multipart Upload Session (for /api/fs/upload)
struct FsFileUploadSession {
  bool active = false;
  AsyncWebServerRequest *owner = nullptr;
  File file;
  char path[64] = "";
  size_t bytesWritten = 0;
  bool ok = false;
  char errorMsg[64] = "";
};
FsFileUploadSession fsUploadSession;

// Lightweight fixed buffer for tiny JSON POSTs (/api/time/sync, /api/wifi/portal)
struct SmallJsonBody {
  char data[MAX_SMALL_JSON_BYTES + 1];
  size_t len = 0;
  bool overflow = false;
};

// ============================================================================
// UPLOADER HIGH-SECURITY AUTH & HARDWARE FORGET-BOOT STATE
// ============================================================================
uint8_t uploadAuthFailedAttempts = 0;
bool uploadAuthLocked = false;          // Resets ONLY on fresh hardware restart or BOOT Forget
char uploadSessionToken[65] = "";       // 256-bit random hex token (64 chars + NUL)
IPAddress uploadSessionIp(0, 0, 0, 0);  // Token bound to client IP
unsigned long uploadSessionLastSeenMs = 0;

enum UploadForgetState : uint8_t {
  UF_IDLE = 0,
  UF_WAIT_PRESS,
  UF_HOLDING,
  UF_DONE,
  UF_TIMEOUT,
  UF_RELEASED_EARLY
};

UploadForgetState ufState = UF_IDLE;
bool ufResetUsersOnDone = true;  // true = Forget (erase users), false = BOOT hold confirm for Reset Data/Settings/Factory
unsigned long ufWindowDeadlineMs = 0;
unsigned long ufHoldStartMs = 0;
unsigned long ufReleaseSinceMs = 0;
char ufStatusMsg[96] = "";

// ============================================================================
// 8. FORWARD DECLARATIONS
// ============================================================================
void setupWebServer();
bool syncTime();
void startOrRefreshMdns();
bool readCurrentLocalTime(struct tm *ti);
bool getSavedWifiCredentials(String &ssid, String &pass);

// ============================================================================
// 9. CRASH GUARD, BOARD-SAFE BUILT-IN LED, I2C BUS & HARDWARE FEEDBACK
// ============================================================================
static void oomNewHandler() {
  ets_printf("[OOM] Heap allocation failed - restarting cleanly\n");
  esp_restart();
}

// Safely drives either the classic ESP32 GPIO 2 LED or the ESP32-S3 WS2812B RGB LED
void setBuiltinLed(bool on, uint8_t r = 0, uint8_t g = 18, uint8_t b = 48) {
#if HAS_BUILTIN_RGB_LED
  uint8_t rv = on ? r : 0;
  uint8_t gv = on ? g : 0;
  uint8_t bv = on ? b : 0;
#if defined(ESP_ARDUINO_VERSION_MAJOR) && (ESP_ARDUINO_VERSION_MAJOR >= 3)
  rgbLedWrite(S3_RGB_LED_PIN, rv, gv, bv);
#else
  neopixelWrite(S3_RGB_LED_PIN, rv, gv, bv);
#endif
#else
  (void)r;
  (void)g;
  (void)b;
  digitalWrite(BUILTIN_LED_PIN, on ? HIGH : LOW);
#endif
}

// FreeRTOS task for AP portal blinking (100% RMT/NeoPixel-safe on ESP32-S3)
void apLedBlinkTask(void *param) {
  (void)param;
  bool state = false;
  while (apLedBlinkActive) {
    state = !state;
    setBuiltinLed(state, 0, 18, 48);  // Soft cyan-blue on S3 RGB, solid ON on classic ESP32
    digitalWrite(LED_PIN, state ? HIGH : LOW);
    vTaskDelay(pdMS_TO_TICKS(250));
  }
  setBuiltinLed(false);
  digitalWrite(LED_PIN, LOW);
  apLedTaskHandle = nullptr;
  vTaskDelete(nullptr);
}

void startApLedBlink() {
  if (apLedTaskHandle != nullptr) return;
  apLedBlinkActive = true;
  xTaskCreate(apLedBlinkTask, "apLedBlink", 2048, nullptr, 1, &apLedTaskHandle);
}

void stopApLedBlink() {
  apLedBlinkActive = false;
  unsigned long deadline = millis() + 600;
  while (apLedTaskHandle != nullptr && millis() < deadline) {
    delay(10);
  }
  setBuiltinLed(false);
  digitalWrite(LED_PIN, LOW);
}

void notifyStorage() {
  digitalWrite(LED_PIN, HIGH);
  digitalWrite(BUZZER_PIN, HIGH);
  notifyRgbPulsePending = true;
  notifyStorageOffAt = millis() + 90;
  if (notifyStorageOffAt == 0) notifyStorageOffAt = 1;
}

void serviceNotifyStorage() {
  if (notifyRgbPulsePending) {
    notifyRgbPulsePending = false;
#if HAS_BUILTIN_RGB_LED
    setBuiltinLed(true, 0, 36, 0);  // Brief subtle green confirmation pulse on S3
#endif
  }

  if (notifyStorageOffAt && (int32_t)(millis() - notifyStorageOffAt) >= 0) {
    notifyStorageOffAt = 0;
    digitalWrite(BUZZER_PIN, LOW);
    digitalWrite(LED_PIN, LOW);
#if HAS_BUILTIN_RGB_LED
    setBuiltinLed(false);
#endif
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
// 9.5. 128x64 I2C OLED DISPLAY MANAGER & DEVICE ONLINE/OFFLINE MONITOR
// ============================================================================
void oledShowBoot(const char *msg, uint8_t progressPct = 0) {
  if (!oledReady) return;

  // Scroll rolling 3-line setup log upward
  strncpy(oledBootLog[0], oledBootLog[1], sizeof(oledBootLog[0]) - 1);
  strncpy(oledBootLog[1], oledBootLog[2], sizeof(oledBootLog[1]) - 1);
  strncpy(oledBootLog[2], msg, sizeof(oledBootLog[2]) - 1);
  oledBootLog[2][sizeof(oledBootLog[2]) - 1] = '\0';

  display.clearDisplay();
  display.setTextSize(1);
  display.setTextColor(SSD1306_WHITE);

  // Header (Y=0..15)
  display.setCursor(0, 2);
  display.printf("HUB SETUP [%s]", HUB_BOARD_NAME);
  display.drawFastHLine(0, 14, 128, SSD1306_WHITE);

  // Rolling 3 setup messages
  for (int i = 0; i < 3; i++) {
    if (oledBootLog[i][0] != '\0') {
      display.setCursor(0, 18 + (i * 11));
      display.print(i == 2 ? ">" : " ");
      display.print(oledBootLog[i]);
    }
  }

  // Progress bar at bottom
  if (progressPct > 100) progressPct = 100;
  display.drawRect(0, 54, 128, 9, SSD1306_WHITE);
  int fillW = (int)((124UL * progressPct) / 100UL);
  if (fillW > 0) display.fillRect(2, 56, fillW, 5, SSD1306_WHITE);

  display.display();
}

// Thread-safe alert trigger (safe to call from HTTP routes or WiFi callbacks)
void oledPostAlert(const char *title, const char *l1, const char *l2 = "",
                   const char *l3 = "", unsigned long durationMs = 4000, bool critical = false) {
  if (!asyncReqMutex) return;
  if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(100)) == pdTRUE) {
    oledAlert.active = true;
    oledAlert.critical = critical;
    strncpy(oledAlert.title, title ? title : "", sizeof(oledAlert.title) - 1);
    oledAlert.title[sizeof(oledAlert.title) - 1] = '\0';
    strncpy(oledAlert.line1, l1 ? l1 : "", sizeof(oledAlert.line1) - 1);
    oledAlert.line1[sizeof(oledAlert.line1) - 1] = '\0';
    strncpy(oledAlert.line2, l2 ? l2 : "", sizeof(oledAlert.line2) - 1);
    oledAlert.line2[sizeof(oledAlert.line2) - 1] = '\0';
    strncpy(oledAlert.line3, l3 ? l3 : "", sizeof(oledAlert.line3) - 1);
    oledAlert.line3[sizeof(oledAlert.line3) - 1] = '\0';
    oledAlert.expiresAt = (durationMs == 0) ? 0 : (millis() + durationMs);
    oledForceRedraw = true;
    xSemaphoreGive(asyncReqMutex);
  }
}

void oledClearAlert() {
  if (!asyncReqMutex) return;
  if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(100)) == pdTRUE) {
    oledAlert.active = false;
    oledForceRedraw = true;
    xSemaphoreGive(asyncReqMutex);
  }
}

// Immediate screen drawn right before blocking WiFiManager AP portal starts
void oledShowApMode() {
  if (!oledReady) return;
  display.clearDisplay();
  display.fillRect(0, 0, 128, 14, SSD1306_WHITE);
  display.setTextSize(1);
  display.setTextColor(SSD1306_BLACK);
  display.setCursor(14, 3);
  display.print("!! AP SETUP MODE !!");

  display.setTextColor(SSD1306_WHITE);
  display.setCursor(0, 18);
  display.print("SSID: ");
  display.print(netCfg.apName.substring(0, 15));

  display.setCursor(0, 29);
  display.print("PASS: ");
  if (netCfg.apPass.length() >= 8) display.print(netCfg.apPass.substring(0, 15));
  else display.print("(OPEN)");

  display.setCursor(0, 41);
  display.print("OPEN: 192.168.4.1");

  display.setCursor(0, 53);
  display.printf("Timeout: %ds", netCfg.apTimeout);
  display.display();
}

void initI2cDisplayBus() {
  Wire.begin(I2C_SDA_PIN, I2C_SCL_PIN);
  Wire.setClock(I2C_CLOCK_HZ);

  const uint8_t probeAddrs[2] = { 0x3C, 0x3D };
  detectedI2cDisplayAddr = 0;
  for (uint8_t addr : probeAddrs) {
    Wire.beginTransmission(addr);
    if (Wire.endTransmission() == 0) {
      detectedI2cDisplayAddr = addr;
      break;
    }
  }

  if (detectedI2cDisplayAddr) {
    // Last two 'false' args keep our custom SDA/SCL pins intact on ESP32-S3
    if (display.begin(SSD1306_SWITCHCAPVCC, detectedI2cDisplayAddr, false, false)) {
      oledReady = true;
      display.cp437(true);
      display.setTextWrap(false);
      display.clearDisplay();
      display.display();
      Serial.printf("[I2C] 128x64 OLED ACTIVE at 0x%02X (SDA=%u, SCL=%u)\n",
                    detectedI2cDisplayAddr, I2C_SDA_PIN, I2C_SCL_PIN);
      oledShowBoot("OLED Ready", 5);
    } else {
      Serial.println("[I2C] Display found but SSD1306 init failed!");
    }
  } else {
    Serial.printf("[I2C] No OLED detected (SDA=%u, SCL=%u)\n", I2C_SDA_PIN, I2C_SCL_PIN);
  }
}

// Helper: extracts host/IP & port from a device JSON object in /config.json
bool extractDeviceEndpoint(JsonObjectConst obj, char *outHost, size_t hostSz, uint16_t &outPort) {
  if (obj["enabled"].is<bool>() && !obj["enabled"].as<bool>()) return false;

  String raw = obj["ip"] | (obj["host"] | (obj["address"] | (obj["mdns"] | (obj["url"] | ""))));
  raw.trim();
  if (raw.isEmpty()) return false;

  if (raw.startsWith("http://")) raw.remove(0, 7);
  else if (raw.startsWith("https://")) raw.remove(0, 8);

  int slashIdx = raw.indexOf('/');
  if (slashIdx >= 0) raw = raw.substring(0, slashIdx);

  uint16_t port = obj["port"] | 80;
  int colonIdx = raw.lastIndexOf(':');
  if (colonIdx > 0) {
    int p = raw.substring(colonIdx + 1).toInt();
    if (p > 0 && p <= 65535) port = (uint16_t)p;
    raw = raw.substring(0, colonIdx);
  }
  raw.trim();
  if (raw.isEmpty() || raw == "0.0.0.0") return false;

  strncpy(outHost, raw.c_str(), hostSz - 1);
  outHost[hostSz - 1] = '\0';
  outPort = (port == 0) ? 80 : port;
  return true;
}

// Loads all configured devices from /config.json so the OLED tracks ON/OFF counts
void reloadDevicesFromConfig() {
  trackedDeviceCount = 0;
  trackedCheckIdx = 0;
  devicesOnlineCount = 0;
  devicesOfflineCount = 0;

  if (!hubFS || !fsMutex) return;
  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) != pdTRUE) return;

  if (hubFS->exists(CONFIG_PATH)) {
    File f = hubFS->open(CONFIG_PATH, "r");
    if (f) {
      JsonDocument doc(&psramAllocator);
      if (!deserializeJson(doc, f)) {
        auto addFromArray = [&](JsonArrayConst arr) {
          for (JsonVariantConst v : arr) {
            if (trackedDeviceCount >= MAX_TRACKED_DEVICES) break;
            if (!v.is<JsonObjectConst>()) continue;
            char host[48];
            uint16_t port = 80;
            if (extractDeviceEndpoint(v.as<JsonObjectConst>(), host, sizeof(host), port)) {
              // Skip duplicates
              bool dup = false;
              for (uint8_t i = 0; i < trackedDeviceCount; i++) {
                if (strcmp(trackedDevices[i].host, host) == 0 && trackedDevices[i].port == port) {
                  dup = true;
                  break;
                }
              }
              if (!dup) {
                strncpy(trackedDevices[trackedDeviceCount].host, host, sizeof(trackedDevices[0].host) - 1);
                trackedDevices[trackedDeviceCount].host[sizeof(trackedDevices[0].host) - 1] = '\0';
                trackedDevices[trackedDeviceCount].port = port;
                trackedDevices[trackedDeviceCount].online = false;
                trackedDevices[trackedDeviceCount].checked = false;
                trackedDeviceCount++;
              }
            }
          }
        };

        // Supports flat arrays or grouped/roomed arrays in /config.json
        if (doc["devices"].is<JsonArrayConst>()) addFromArray(doc["devices"].as<JsonArrayConst>());
        if (doc["nodes"].is<JsonArrayConst>()) addFromArray(doc["nodes"].as<JsonArrayConst>());
        if (doc["groups"].is<JsonArrayConst>()) {
          for (JsonVariantConst g : doc["groups"].as<JsonArrayConst>()) {
            if (g["devices"].is<JsonArrayConst>()) addFromArray(g["devices"].as<JsonArrayConst>());
          }
        }
        if (doc["rooms"].is<JsonArrayConst>()) {
          for (JsonVariantConst r : doc["rooms"].as<JsonArrayConst>()) {
            if (r["devices"].is<JsonArrayConst>()) addFromArray(r["devices"].as<JsonArrayConst>());
          }
        }
      }
      f.close();
    }
  }
  xSemaphoreGive(fsMutex);

  devicesOfflineCount = trackedDeviceCount;
  Serial.printf("[OLED] Loaded %u devices from %s for status tracking\n", trackedDeviceCount, CONFIG_PATH);
  oledForceRedraw = true;
}

// Checks 1 device per interval (non-intrusive; skipped during uploads/resets)
void serviceDeviceHealthCheck() {
  if (deviceListReloadPending) {
    deviceListReloadPending = false;
    reloadDevicesFromConfig();
  }

  if (trackedDeviceCount == 0 || WiFi.status() != WL_CONNECTED) return;
  if (uploadSession.active || fsUploadSession.active || ufState != UF_IDLE || portalPending || restartPending) return;

  unsigned long now = millis();
  if (now - lastDeviceCheckMs < DEVICE_CHECK_INTERVAL_MS) return;
  lastDeviceCheckMs = now;

  TrackedDevice &dev = trackedDevices[trackedCheckIdx];
  WiFiClient probe;
  IPAddress ip;
  bool ok = false;
  if (ip.fromString(dev.host)) {
    ok = probe.connect(ip, dev.port, 250);
  } else {
    ok = probe.connect(dev.host, dev.port, 350);
  }
  if (ok) probe.stop();

  dev.online = ok;
  dev.checked = true;

  trackedCheckIdx = (trackedCheckIdx + 1) % trackedDeviceCount;

  // Recalculate totals
  uint8_t onCnt = 0, offCnt = 0;
  for (uint8_t i = 0; i < trackedDeviceCount; i++) {
    if (trackedDevices[i].online) onCnt++;
    else offCnt++;
  }
  if (onCnt != devicesOnlineCount || offCnt != devicesOfflineCount) {
    devicesOnlineCount = onCnt;
    devicesOfflineCount = offCnt;
    oledForceRedraw = true;
  }
}

void drawWifiSignalBars(int x, int y, int rssi) {
  int bars = 0;
  if (rssi >= -55) bars = 4;
  else if (rssi >= -67) bars = 3;
  else if (rssi >= -77) bars = 2;
  else if (rssi >= -88) bars = 1;

  for (int i = 0; i < 4; i++) {
    int h = (i + 1) * 2 + 1;  // heights: 3, 5, 7, 9 px
    int bx = x + (i * 4);
    int by = y + (9 - h);
    if (i < bars) display.fillRect(bx, by, 3, h, SSD1306_WHITE);
    else display.drawRect(bx, by, 3, h, SSD1306_WHITE);
  }
}

void drawOledAlertBox(const char *title, const char *l1, const char *l2, const char *l3, bool invertedHeader) {
  display.clearDisplay();
  display.setTextSize(1);
  if (invertedHeader) {
    display.fillRect(0, 0, 128, 14, SSD1306_WHITE);
    display.setTextColor(SSD1306_BLACK);
  } else {
    display.setTextColor(SSD1306_WHITE);
    display.drawFastHLine(0, 14, 128, SSD1306_WHITE);
  }
  display.setCursor(3, 3);
  display.print(title);

  display.setTextColor(SSD1306_WHITE);
  display.setCursor(0, 19);
  display.print(l1);
  display.setCursor(0, 32);
  display.print(l2);
  display.setCursor(0, 46);
  display.print(l3);
  display.display();
}

// Main OLED renderer (MUST ONLY BE CALLED FROM loop())
void serviceOledDisplay() {
  if (!oledReady) return;

  unsigned long now = millis();
  unsigned long refreshPeriod = (ufState == UF_WAIT_PRESS || ufState == UF_HOLDING) ? 200UL : 1000UL;
  if (!oledForceRedraw && (now - lastOledDrawMs < refreshPeriod)) return;
  oledForceRedraw = false;
  lastOledDrawMs = now;

  // --- PRIORITY 1: Explicit Emergency / Timed Alert ---
  OledAlertState localAlert;
  bool showLocalAlert = false;
  if (asyncReqMutex && xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(50)) == pdTRUE) {
    if (oledAlert.active) {
      if (oledAlert.expiresAt != 0 && (int32_t)(now - oledAlert.expiresAt) >= 0) {
        oledAlert.active = false;
      } else {
        localAlert = oledAlert;
        showLocalAlert = true;
      }
    }
    xSemaphoreGive(asyncReqMutex);
  }
  if (showLocalAlert) {
    drawOledAlertBox(localAlert.title, localAlert.line1, localAlert.line2, localAlert.line3, localAlert.critical);
    return;
  }

  // --- PRIORITY 2: Physical BOOT Button Hold Flow ---
  if (ufState == UF_WAIT_PRESS || ufState == UF_HOLDING) {
    display.clearDisplay();
    display.fillRect(0, 0, 128, 14, SSD1306_WHITE);
    display.setTextSize(1);
    display.setTextColor(SSD1306_BLACK);
    display.setCursor(10, 3);
    display.print("HARDWARE VERIFY");
    display.setTextColor(SSD1306_WHITE);

    if (ufState == UF_WAIT_PRESS) {
      uint32_t rem = ((int32_t)(ufWindowDeadlineMs - now) > 0) ? (uint32_t)(ufWindowDeadlineMs - now) : 0;
      display.setCursor(0, 20);
      display.print("Press & Hold BOOT");
      display.setCursor(0, 33);
      display.printf("Window: %.1fs left", rem / 1000.0f);
      int w = (int)((124UL * (UPLOAD_FORGET_PRESS_WINDOW_MS - rem)) / UPLOAD_FORGET_PRESS_WINDOW_MS);
      display.drawRect(0, 50, 128, 10, SSD1306_WHITE);
      if (w > 0) display.fillRect(2, 52, w, 6, SSD1306_WHITE);
    } else {
      uint32_t held = (uint32_t)(now - ufHoldStartMs);
      if (held > UPLOAD_FORGET_HOLD_MS) held = UPLOAD_FORGET_HOLD_MS;
      display.setCursor(0, 20);
      display.print("KEEP HOLDING BOOT...");
      display.setCursor(0, 33);
      display.printf("Held: %.1fs / 10.0s", held / 1000.0f);
      int w = (int)((124UL * held) / UPLOAD_FORGET_HOLD_MS);
      display.drawRect(0, 50, 128, 10, SSD1306_WHITE);
      if (w > 0) display.fillRect(2, 52, w, 6, SSD1306_WHITE);
    }
    display.display();
    return;
  }

  // --- PRIORITY 3: Persistent Emergency Conditions ---
  if (uploadAuthLocked) {
    drawOledAlertBox("!! AUTH LOCKED !!", "3 Failed Logins!", "Restart ESP32 or", "use Forget + BOOT", true);
    return;
  }
  if (!hubFS) {
    drawOledAlertBox("!! STORAGE ERROR !!", "Filesystem failed!", "Check Flash/FFat", "partition settings", true);
    return;
  }
  if (!webServerRunning) {
    drawOledAlertBox("!! SERVER ERROR !!", "Web server stopped", "Port 80 offline", "Check WiFi / Reboot", true);
    return;
  }
  if (WiFi.status() != WL_CONNECTED) {
    String ssid, pass;
    char l2[22] = "No saved WiFi";
    if (getSavedWifiCredentials(ssid, pass)) {
      snprintf(l2, sizeof(l2), "SSID: %.15s", ssid.c_str());
    }
    drawOledAlertBox("! WIFI DISCONNECTED !", "Reconnecting...", l2, "Retry every 15s", true);
    return;
  }

  // --- PRIORITY 4: NORMAL DASHBOARD SCREEN ---
  display.clearDisplay();
  display.setTextSize(1);
  display.setTextColor(SSD1306_WHITE);

  // Header (Y=0..15): Time + Date + WiFi Bars
  struct tm ti;
  if (readCurrentLocalTime(&ti)) {
    static const char *MON[12] = { "Jan", "Feb", "Mar", "Apr", "May", "Jun",
                                   "Jul", "Aug", "Sep", "Oct", "Nov", "Dec" };
    display.setCursor(0, 3);
    display.printf("%02d:%02d:%02d", ti.tm_hour, ti.tm_min, ti.tm_sec);
    display.setCursor(55, 3);
    display.printf("%02d %s", ti.tm_mday, MON[ti.tm_mon % 12]);
  } else {
    display.setCursor(0, 3);
    display.print("--:--:-- NTP WAIT");
  }
  drawWifiSignalBars(112, 2, WiFi.RSSI());
  display.drawFastHLine(0, 15, 128, SSD1306_WHITE);

  // Middle Body (Y=19..41): IP Address & mDNS Address
  display.setCursor(0, 19);
  display.print("IP: ");
  display.print(WiFi.localIP().toString());

  display.setCursor(0, 31);
  display.print("MD: ");
  if (netCfg.mdnsEnabled && mdnsRunning) {
    String md = netCfg.mdnsHost + ".local";
    display.print(md.substring(0, 17));
  } else {
    display.print("Disabled");
  }
  display.drawFastHLine(0, 43, 128, SSD1306_WHITE);

  // Bottom Bar (Y=48..63): Online / Offline Devices
  if (webDeviceOverrideActive && (int32_t)(now - webDeviceOverrideUntil) >= 0) {
    webDeviceOverrideActive = false;
  }
  uint8_t onCnt = webDeviceOverrideActive ? webDevicesOnline : devicesOnlineCount;
  uint8_t offCnt = webDeviceOverrideActive ? webDevicesOffline : devicesOfflineCount;
  uint8_t totCnt = onCnt + offCnt;

  display.setCursor(0, 50);
  if (totCnt == 0) {
    display.print("DEV: No devices");
  } else {
    // Inverted badge for ON count
    display.fillRoundRect(0, 48, 44, 13, 2, SSD1306_WHITE);
    display.setTextColor(SSD1306_BLACK);
    display.setCursor(4, 51);
    display.printf("ON:%u", onCnt);

    // Outlined badge for OFF count
    display.setTextColor(SSD1306_WHITE);
    display.drawRoundRect(48, 48, 48, 13, 2, SSD1306_WHITE);
    display.setCursor(52, 51);
    display.printf("OFF:%u", offCnt);

    // Total count on the right
    display.setCursor(100, 51);
    display.printf("T:%u", totCnt);
  }

  display.display();
}

// ============================================================================
// 10. STRING, HOSTNAME & TIME UTILITIES
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

String sanitizeUploadPath(String raw) {
  raw.trim();
  int slash = raw.lastIndexOf('/');
  int bslash = raw.lastIndexOf('\\');
  int cut = (slash > bslash) ? slash : bslash;
  if (cut >= 0) raw = raw.substring(cut + 1);
  raw.trim();
  if (raw.isEmpty() || raw.indexOf("..") >= 0 || raw.length() > 56) return "";
  return String("/") + raw;
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
// 11. NVS PERSISTENCE (NETWORK, WIFI & TIME SETTINGS)
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

// Extracts ONLY `network` and `admin.time` from /config.tmp using ArduinoJson Filter (PSRAM-backed on S3)
bool syncRuntimeFromConfigFile(const char *path) {
  if (!hubFS) return false;
  File f = hubFS->open(path, "r");
  if (!f) return false;

  JsonDocument filter(&psramAllocator);
  filter["network"] = true;
  filter["admin"]["time"] = true;

  JsonDocument doc(&psramAllocator);
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

  deviceListReloadPending = true;
  return true;
}

// ============================================================================
// 12. WIFI, STATIC IP, mDNS & CONFIG PORTAL MANAGEMENT
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
    oledPostAlert("WIFI WARNING", "Static IP invalid!", "Fallback to DHCP", "", 4000, true);
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

  startApLedBlink();
  oledShowApMode();

  bool connected = false;
  if (netCfg.apPass.length() >= 8 && netCfg.apPass.length() <= 63) {
    connected = wm.startConfigPortal(netCfg.apName.c_str(), netCfg.apPass.c_str());
  } else {
    connected = wm.startConfigPortal(netCfg.apName.c_str());
  }

  stopApLedBlink();

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

  oledShowBoot(("WiFi:" + ssid.substring(0, 14)).c_str(), 70);

  for (int i = 0; i < WIFI_BOOT_MAX_ATTEMPTS; i++) {
    if (WiFi.status() == WL_CONNECTED) {
      Serial.printf("[WIFI] Connected! IP: %s  GW: %s\n",
                    WiFi.localIP().toString().c_str(),
                    WiFi.gatewayIP().toString().c_str());
      oledShowBoot(("IP:" + WiFi.localIP().toString()).c_str(), 82);
      WiFi.setSleep(false);
      return true;
    }
    delay(500);
  }

  Serial.println("[WIFI] Router not ready yet - continuing in background");
  return false;
}

// ============================================================================
// 12.5. UPLOADER AUTHENTICATION, CONSTANT-TIME CHECK & 5s+10s BOOT FORGET
// ============================================================================
bool secureEquals(const char *a, const char *b) {
  if (!a || !b) return false;
  size_t la = strlen(a);
  size_t lb = strlen(b);
  size_t maxLen = (la > lb) ? la : lb;
  uint8_t diff = (uint8_t)(la ^ lb);
  for (size_t i = 0; i < maxLen; i++) {
    uint8_t ca = (i < la) ? (uint8_t)a[i] : 0;
    uint8_t cb = (i < lb) ? (uint8_t)b[i] : 0;
    diff |= (uint8_t)(ca ^ cb);
  }
  return diff == 0;
}

void sha256HexLower(const char *input, char outHex[65]) {
  uint8_t hash[32];
  mbedtls_sha256_context ctx;
  mbedtls_sha256_init(&ctx);
  mbedtls_sha256_starts(&ctx, 0);
  mbedtls_sha256_update(&ctx, reinterpret_cast<const uint8_t *>(input), strlen(input));
  mbedtls_sha256_finish(&ctx, hash);
  mbedtls_sha256_free(&ctx);
  static const char HEX_CHARS[] = "0123456789abcdef";
  for (int i = 0; i < 32; i++) {
    outHex[i * 2] = HEX_CHARS[(hash[i] >> 4) & 0x0F];
    outHex[i * 2 + 1] = HEX_CHARS[hash[i] & 0x0F];
  }
  outHex[64] = '\0';
}

// Exact C++ match for hashCredential() in index.html, config.html, layout.html & design.html
void hubHashCredential(const String &username, const String &password, char outBuf[21]) {
  String cleanUser = username;
  cleanUser.trim();
  String raw = cleanUser + ":" + password + ":" + HUB_AUTH_SALT;

  uint32_t h1 = 0xdeadbeefUL ^ (uint32_t)raw.length();
  uint32_t h2 = 0x41c6ce57UL ^ (uint32_t)raw.length();

  for (size_t i = 0; i < raw.length(); i++) {
    uint32_t ch = (uint8_t)raw[i];
    h1 = (h1 ^ ch) * 2654435761UL;
    h2 = (h2 ^ ch) * 1597334677UL;
  }
  h1 = ((h1 ^ (h1 >> 16)) * 2246822507UL) ^ ((h2 ^ (h2 >> 13)) * 3266489909UL);
  h2 = ((h2 ^ (h2 >> 16)) * 2246822507UL) ^ ((h1 ^ (h1 >> 13)) * 3266489909UL);

  snprintf(outBuf, 21, "sha:%08lx%08lx", (unsigned long)h2, (unsigned long)h1);
}

bool passwordMatchesStored(const String &storedRaw, const String &provided) {
  if (storedRaw.isEmpty()) return false;
  if (secureEquals(storedRaw.c_str(), provided.c_str())) return true;

  // Also support SHA-256 hex hashes if config.html hashes passwords before saving
  if (storedRaw.length() == 64) {
    char computed[65];
    sha256HexLower(provided.c_str(), computed);
    String storedLower = storedRaw;
    storedLower.toLowerCase();
    if (secureEquals(storedLower.c_str(), computed)) return true;
  }
  return false;
}

bool isAdminRoleEntry(JsonObjectConst u) {
  if (u["isAdmin"].is<bool>() && u["isAdmin"].as<bool>()) return true;
  if (u["role"].is<const char *>()) {
    String r = u["role"].as<const char *>();
    r.trim();
    r.toLowerCase();
    return (r == "admin" || r == "superadmin" || r == "administrator");
  }
  return false;
}

bool verifyUploadAdminCredentials(const String &user, const String &pass) {
  String cleanUser = user;
  cleanUser.trim();
  if (cleanUser.isEmpty() || pass.isEmpty()) return false;

  char computedHubHash[21];
  hubHashCredential(cleanUser, pass, computedHubHash);

  bool anyAdminInConfig = false;
  bool matched = false;

  if (hubFS && fsMutex && xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
    if (hubFS->exists(CONFIG_PATH)) {
      File f = hubFS->open(CONFIG_PATH, "r");
      if (f) {
        JsonDocument doc(&psramAllocator);
        if (!deserializeJson(doc, f)) {
          auto checkUserArray = [&](JsonArrayConst arr) {
            for (JsonVariantConst item : arr) {
              if (!item.is<JsonObjectConst>()) continue;
              JsonObjectConst u = item.as<JsonObjectConst>();
              if (!isAdminRoleEntry(u)) continue;

              const char *uName = u["username"] | (u["user"] | (u["name"] | ""));
              const char *uHash = u["passHash"] | "";
              const char *uPass = u["password"] | (u["pass"] | (u["pin"] | ""));
              if (uName[0] != '\0' && (uHash[0] != '\0' || uPass[0] != '\0')) {
                anyAdminInConfig = true;
                if (secureEquals(uName, cleanUser.c_str())) {
                  if (uHash[0] != '\0' && secureEquals(uHash, computedHubHash)) {
                    matched = true;
                  } else if (uPass[0] != '\0' && passwordMatchesStored(String(uPass), pass)) {
                    matched = true;
                  }
                }
              }
            }
          };

          if (doc["admin"]["users"].is<JsonArrayConst>()) checkUserArray(doc["admin"]["users"].as<JsonArrayConst>());
          if (doc["users"].is<JsonArrayConst>()) checkUserArray(doc["users"].as<JsonArrayConst>());
          if (doc["auth"]["users"].is<JsonArrayConst>()) checkUserArray(doc["auth"]["users"].as<JsonArrayConst>());
        }
        f.close();
      }
    }
    xSemaphoreGive(fsMutex);
  }

  // First boot (or no admin users defined yet): allow default admin esp / 456456
  if (!anyAdminInConfig) {
    return secureEquals(cleanUser.c_str(), UPLOAD_DEFAULT_ADMIN_USER) && secureEquals(pass.c_str(), UPLOAD_DEFAULT_ADMIN_PASS);
  }
  return matched;
}

void generateUploadSessionToken(IPAddress clientIp) {
  uint8_t raw[32];
  esp_fill_random(raw, sizeof(raw));
  static const char HEX_CHARS[] = "0123456789abcdef";
  for (int i = 0; i < 32; i++) {
    uploadSessionToken[i * 2] = HEX_CHARS[(raw[i] >> 4) & 0x0F];
    uploadSessionToken[i * 2 + 1] = HEX_CHARS[raw[i] & 0x0F];
  }
  uploadSessionToken[64] = '\0';
  uploadSessionIp = clientIp;
  uploadSessionLastSeenMs = millis();
}

void invalidateUploadSession() {
  memset(uploadSessionToken, 0, sizeof(uploadSessionToken));
  uploadSessionIp = IPAddress(0, 0, 0, 0);
  uploadSessionLastSeenMs = 0;
}

bool isUploadRequestAuthorized(AsyncWebServerRequest *req) {
  if (!req || !asyncReqMutex) return false;
  if (!req->hasHeader("X-Upload-Token")) return false;
  String hdr = req->getHeader("X-Upload-Token")->value();
  if (hdr.length() != 64) return false;

  bool ok = false;
  if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
    if (!uploadAuthLocked && uploadSessionToken[0] != '\0') {
      bool expired = (millis() - uploadSessionLastSeenMs) > UPLOAD_SESSION_TTL_MS;
      bool ipMatch = (req->client() && req->client()->remoteIP() == uploadSessionIp);
      if (!expired && ipMatch && secureEquals(uploadSessionToken, hdr.c_str())) {
        uploadSessionLastSeenMs = millis();
        ok = true;
      } else if (expired) {
        invalidateUploadSession();
      }
    }
    xSemaphoreGive(asyncReqMutex);
  }
  return ok;
}

// Erases ALL saved admin & normal users in /config.json and creates ONLY default admin (esp / 456456)
bool resetAllUsersToDefaultAdmin() {
  if (!hubFS || !fsMutex) return false;
  bool saved = false;

  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1500)) == pdTRUE) {
    JsonDocument doc(&psramAllocator);

    // Preserve existing non-user settings (network, relays, schedules, etc.) if /config.json exists
    if (hubFS->exists(CONFIG_PATH)) {
      File rf = hubFS->open(CONFIG_PATH, "r");
      if (rf) {
        DeserializationError err = deserializeJson(doc, rf);
        rf.close();
        if (err || !doc.is<JsonObject>()) {
          doc.clear();
          doc.to<JsonObject>();
        }
      }
    } else {
      doc.to<JsonObject>();
    }

    // 1. Erase every saved user list (admin + normal users)
    doc.remove("users");
    if (doc["auth"].is<JsonObject>()) doc["auth"].remove("users");
    if (doc["admin"].is<JsonObject>()) {
      doc["admin"].remove("users");
      doc["admin"].remove("username");
      doc["admin"].remove("password");
    }

    // 2. Create default admin user using exact passHash expected by all HTML pages
    char defaultHash[21];
    hubHashCredential(UPLOAD_DEFAULT_ADMIN_USER, UPLOAD_DEFAULT_ADMIN_PASS, defaultHash);

    JsonArray users = doc["admin"]["users"].to<JsonArray>();
    JsonObject defAdmin = users.add<JsonObject>();
    defAdmin["username"] = UPLOAD_DEFAULT_ADMIN_USER;  // "esp"
    defAdmin["passHash"] = (const char *)defaultHash;  // 100% synced with index/config/layout/design.html
    defAdmin["role"] = "admin";

    // 3. Atomic write via /config.tmp -> /config.json
    if (hubFS->exists(CONFIG_TMP_PATH)) hubFS->remove(CONFIG_TMP_PATH);
    File wf = hubFS->open(CONFIG_TMP_PATH, "w");
    if (wf) {
      size_t written = serializeJson(doc, wf);
      wf.flush();
      wf.close();
      if (written > 0) {
        if (hubFS->exists(CONFIG_PATH)) hubFS->remove(CONFIG_PATH);
        saved = hubFS->rename(CONFIG_TMP_PATH, CONFIG_PATH);
      }
      if (!saved && hubFS->exists(CONFIG_TMP_PATH)) hubFS->remove(CONFIG_TMP_PATH);
    }
    clearPsramCacheLocked();
    xSemaphoreGive(fsMutex);
  }

  // Clear lockout & invalidate old tokens on success
  if (saved && asyncReqMutex && xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(300)) == pdTRUE) {
    uploadAuthFailedAttempts = 0;
    uploadAuthLocked = false;
    invalidateUploadSession();
    snprintf(bootIdStr, sizeof(bootIdStr), "%08lX", (unsigned long)esp_random());
    xSemaphoreGive(asyncReqMutex);
  }

  Serial.printf("[AUTH] Hardware Forget Reset %s -> default admin '%s'\n",
                saved ? "OK" : "FAILED", UPLOAD_DEFAULT_ADMIN_USER);
  return saved;
}

void serviceUploadForgetButton() {
  if (ufState != UF_WAIT_PRESS && ufState != UF_HOLDING) return;

  unsigned long now = millis();
  bool pressed = (digitalRead(BOOT_BUTTON) == LOW);

  if (ufState == UF_WAIT_PRESS) {
    if (pressed) {
      ufState = UF_HOLDING;
      ufHoldStartMs = now;
      ufReleaseSinceMs = 0;
      digitalWrite(LED_PIN, HIGH);
      setBuiltinLed(true, 40, 24, 0);  // Amber indicator while holding
      Serial.println("[AUTH] BOOT pressed in 5s window -> hold 10s to erase users");
    } else if ((int32_t)(now - ufWindowDeadlineMs) >= 0) {
      ufState = UF_TIMEOUT;
      strncpy(ufStatusMsg, "Timed out: BOOT button was not pressed within 5 seconds.", sizeof(ufStatusMsg) - 1);
      oledPostAlert("RESET TIMEOUT", "BOOT not pressed", "within 5 seconds", "", 4000, false);
      digitalWrite(LED_PIN, LOW);
      setBuiltinLed(false);
    }
    return;
  }

  if (ufState == UF_HOLDING) {
    if (!pressed) {
      if (ufReleaseSinceMs == 0) ufReleaseSinceMs = now;
      if (now - ufReleaseSinceMs >= UPLOAD_FORGET_DEBOUNCE_MS) {
        ufState = UF_RELEASED_EARLY;
        strncpy(ufStatusMsg, "Cancelled: BOOT button was released before 10 seconds.", sizeof(ufStatusMsg) - 1);
        oledPostAlert("RESET CANCELLED", "BOOT released", "before 10 seconds", "", 4000, false);
        digitalWrite(LED_PIN, LOW);
        setBuiltinLed(false);
        return;
      }
    } else {
      ufReleaseSinceMs = 0;
    }

    if (now - ufHoldStartMs >= UPLOAD_FORGET_HOLD_MS) {
      digitalWrite(LED_PIN, LOW);
      setBuiltinLed(false);
      if (ufResetUsersOnDone) {
        bool ok = resetAllUsersToDefaultAdmin();
        if (ok) {
          ufState = UF_DONE;
          strncpy(ufStatusMsg, "All users erased. Default admin esp / 456456 created.", sizeof(ufStatusMsg) - 1);
          ufStatusMsg[sizeof(ufStatusMsg) - 1] = '\0';
          notifyStorage();
          oledPostAlert("RESET COMPLETE", ufResetUsersOnDone ? "Default: esp/456456" : "BOOT Verified OK", "", "", 5000, false);
        } else {
          ufState = UF_RELEASED_EARLY;
          strncpy(ufStatusMsg, "Flash write error while resetting users.", sizeof(ufStatusMsg) - 1);
          ufStatusMsg[sizeof(ufStatusMsg) - 1] = '\0';
        }
      } else {
        ufState = UF_DONE;
        strncpy(ufStatusMsg, "BOOT button verified. Proceeding with reset...", sizeof(ufStatusMsg) - 1);
        ufStatusMsg[sizeof(ufStatusMsg) - 1] = '\0';
        notifyStorage();
      }
    }
  }
}

// ============================================================================
// 13. SAFE STREAMING UPLOAD HELPERS (CONFIG/DESIGN + /api/fs/upload)
// ============================================================================
void abortUploadIfOwner(AsyncWebServerRequest *req) {
  if (!fsMutex) return;
  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
    if (uploadSession.active && uploadSession.owner == req) {
      if (uploadSession.file) uploadSession.file.close();
      if (hubFS && uploadSession.tmpPath && hubFS->exists(uploadSession.tmpPath)) {
        hubFS->remove(uploadSession.tmpPath);
      }
      uploadSession.active = false;
      uploadSession.owner = nullptr;
    }
    xSemaphoreGive(fsMutex);
  }
}

void abortFsFileUploadIfOwner(AsyncWebServerRequest *req) {
  if (!fsMutex) return;
  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
    if (fsUploadSession.active && fsUploadSession.owner == req) {
      if (fsUploadSession.file) fsUploadSession.file.close();
      fsUploadSession.active = false;
      fsUploadSession.owner = nullptr;
    }
    xSemaphoreGive(fsMutex);
  }
}

void handleFsFileUploadChunk(AsyncWebServerRequest *req, const String &filename,
                             size_t index, uint8_t *data, size_t len, bool final) {
  if (!fsMutex) return;

  if (index == 0) {
    if (!isUploadRequestAuthorized(req)) return;
    if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) != pdTRUE) return;

    if (fsUploadSession.active) {
      xSemaphoreGive(fsMutex);
      return;
    }

    fsUploadSession.active = true;
    fsUploadSession.owner = req;
    fsUploadSession.bytesWritten = 0;
    fsUploadSession.ok = false;
    fsUploadSession.path[0] = '\0';
    fsUploadSession.errorMsg[0] = '\0';

    req->onDisconnect([req]() {
      abortFsFileUploadIfOwner(req);
    });

    String cleanPath = sanitizeUploadPath(filename);
    if (!hubFS) {
      strncpy(fsUploadSession.errorMsg, "Filesystem not mounted", sizeof(fsUploadSession.errorMsg) - 1);
    } else if (cleanPath.isEmpty()) {
      strncpy(fsUploadSession.errorMsg, "Invalid filename", sizeof(fsUploadSession.errorMsg) - 1);
    } else {
      strncpy(fsUploadSession.path, cleanPath.c_str(), sizeof(fsUploadSession.path) - 1);
      if (hubFS->exists(fsUploadSession.path)) hubFS->remove(fsUploadSession.path);
      fsUploadSession.file = hubFS->open(fsUploadSession.path, "w");
      if (!fsUploadSession.file) {
        strncpy(fsUploadSession.errorMsg, "Failed to create file in flash", sizeof(fsUploadSession.errorMsg) - 1);
      } else {
        fsUploadSession.ok = true;
      }
    }
    xSemaphoreGive(fsMutex);
  }

  if (len > 0) {
    if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
      if (fsUploadSession.active && fsUploadSession.owner == req && fsUploadSession.ok && fsUploadSession.file) {
        size_t written = fsUploadSession.file.write(data, len);
        fsUploadSession.bytesWritten += written;
        if (written != len) {
          fsUploadSession.ok = false;
          strncpy(fsUploadSession.errorMsg, "Flash write failed (storage full)", sizeof(fsUploadSession.errorMsg) - 1);
        }
      }
      xSemaphoreGive(fsMutex);
    }
  }

  if (final) {
    if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
      if (fsUploadSession.active && fsUploadSession.owner == req) {
        if (fsUploadSession.file) {
          fsUploadSession.file.flush();
          fsUploadSession.file.close();
        }
        clearPsramCacheLocked();
        Serial.printf("[UPLOAD] %s -> %s (%u B)\n",
                      fsUploadSession.ok ? "OK" : "FAIL",
                      fsUploadSession.path,
                      (unsigned)fsUploadSession.bytesWritten);
      }
      xSemaphoreGive(fsMutex);
    }
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

    if (!hubFS) {
      uploadSession.failed = true;
      uploadSession.errorCode = 500;
      strncpy(uploadSession.errorMsg, "Filesystem not mounted", sizeof(uploadSession.errorMsg) - 1);
    } else if (ESP.getFreeHeap() < MIN_FREE_HEAP_FOR_UPLOAD) {
      uploadSession.failed = true;
      uploadSession.errorCode = 503;
      strncpy(uploadSession.errorMsg, "Low memory", sizeof(uploadSession.errorMsg) - 1);
    } else if (total == 0 || total > maxBytes) {
      uploadSession.failed = true;
      uploadSession.errorCode = 413;
      strncpy(uploadSession.errorMsg, "Payload exceeds storage limit", sizeof(uploadSession.errorMsg) - 1);
    } else {
      if (hubFS->exists(tmpPath)) hubFS->remove(tmpPath);
      uploadSession.file = hubFS->open(tmpPath, "w");
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
        strncpy(uploadSession.errorMsg, "Flash write failed (storage full)", sizeof(uploadSession.errorMsg) - 1);
      }
    }
  }
  xSemaphoreGive(fsMutex);
}

void finalizeStreamUpload(AsyncWebServerRequest *req) {
  if (!fsMutex || !hubFS) {
    req->send(500, "application/json", "{\"ok\":false,\"error\":\"Storage unavailable\"}");
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
    if (hubFS->exists(finalPath)) hubFS->remove(finalPath);
    if (!hubFS->rename(tmpPath, finalPath)) {
      ok = false;
      errCode = 500;
      errMsg = "Atomic file commit failed";
    }
  }

  if (!ok && tmpPath && hubFS->exists(tmpPath)) {
    hubFS->remove(tmpPath);
  }

  uploadSession.active = false;
  uploadSession.owner = nullptr;
  xSemaphoreGive(fsMutex);

  if (!ok) {
    JsonDocument d(&psramAllocator);
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
// 14. STATIC FILE (WITH S3 PSRAM CACHE) & JSON STREAMING HELPERS
// ============================================================================
bool getOrLoadPsramAsset(const char *path, const uint8_t *&outData,
                         size_t &outLen, bool &outIsGzip) {
  if (!hasPsram || !hubFS || !fsMutex) return false;

  if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(500)) != pdTRUE) return false;

  // 1. Cache hit check
  for (size_t i = 0; i < MAX_PSRAM_CACHE_ENTRIES; i++) {
    if (psramCache[i].valid && strcmp(psramCache[i].path, path) == 0) {
      outData = psramCache[i].data;
      outLen = psramCache[i].len;
      outIsGzip = psramCache[i].isGzip;
      xSemaphoreGive(fsMutex);
      return true;
    }
  }

  // 2. Find an empty slot
  int freeSlot = -1;
  for (size_t i = 0; i < MAX_PSRAM_CACHE_ENTRIES; i++) {
    if (!psramCache[i].valid) {
      freeSlot = (int)i;
      break;
    }
  }
  if (freeSlot < 0) {
    xSemaphoreGive(fsMutex);
    return false;
  }

  // 3. Locate .gz version first, else plain file
  char gzPath[48];
  snprintf(gzPath, sizeof(gzPath), "%s.gz", path);

  const char *actualPath = nullptr;
  bool isGz = false;
  if (hubFS->exists(gzPath)) {
    actualPath = gzPath;
    isGz = true;
  } else if (hubFS->exists(path)) {
    actualPath = path;
    isGz = false;
  } else {
    xSemaphoreGive(fsMutex);
    return false;
  }

  File f = hubFS->open(actualPath, "r");
  if (!f) {
    xSemaphoreGive(fsMutex);
    return false;
  }

  size_t sz = f.size();
  if (sz == 0 || sz > MAX_PSRAM_CACHE_FILE_BYTES || ESP.getFreePsram() < (sz + 262144UL)) {
    f.close();
    xSemaphoreGive(fsMutex);
    return false;
  }

  uint8_t *buf = static_cast<uint8_t *>(
    heap_caps_malloc(sz, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT));
  if (!buf) {
    f.close();
    xSemaphoreGive(fsMutex);
    return false;
  }

  size_t readBytes = f.read(buf, sz);
  f.close();

  if (readBytes != sz) {
    free(buf);
    xSemaphoreGive(fsMutex);
    return false;
  }

  strncpy(psramCache[freeSlot].path, path, sizeof(psramCache[freeSlot].path) - 1);
  psramCache[freeSlot].path[sizeof(psramCache[freeSlot].path) - 1] = '\0';
  psramCache[freeSlot].data = buf;
  psramCache[freeSlot].len = sz;
  psramCache[freeSlot].isGzip = isGz;
  psramCache[freeSlot].valid = true;
  psramCacheTotalBytes += sz;

  outData = buf;
  outLen = sz;
  outIsGzip = isGz;
  xSemaphoreGive(fsMutex);

  Serial.printf("[PSRAM] Cached %s (%u B, gzip=%d)\n", actualPath, (unsigned)sz, isGz ? 1 : 0);
  return true;
}

void sendWebFile(AsyncWebServerRequest *req, const char *path,
                 const char *contentType, bool cacheStatic = false) {
  if (!hubFS) {
    req->send(500, "text/plain", "Filesystem not mounted");
    return;
  }
  if (ESP.getFreeHeap() < MIN_FREE_HEAP_FOR_FILES) {
    req->send(503, "text/plain", "Low memory - retry shortly");
    return;
  }

  // Fast path on ESP32-S3 with 8 MB OPI PSRAM: serve directly from RAM
  if (hasPsram) {
    const uint8_t *data = nullptr;
    size_t len = 0;
    bool isGzip = false;
    if (getOrLoadPsramAsset(path, data, len, isGzip)) {
      AsyncWebServerResponse *res = req->beginChunkedResponse(
        contentType,
        [data, len](uint8_t *buffer, size_t maxLen, size_t index) -> size_t {
          if (index >= len) return 0;
          size_t toCopy = len - index;
          if (toCopy > maxLen) toCopy = maxLen;
          memcpy(buffer, data + index, toCopy);
          return toCopy;
        });
      if (isGzip) res->addHeader("Content-Encoding", "gzip");
      res->addHeader("Cache-Control", cacheStatic ? "public, max-age=86400" : "no-store");
      req->send(res);
      return;
    }
  }

  // Standard direct-from-flash streaming path (Classic ESP32 or PSRAM disabled)
  char gzPath[48];
  snprintf(gzPath, sizeof(gzPath), "%s.gz", path);

  if (hubFS->exists(gzPath)) {
    File f = hubFS->open(gzPath, "r");
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
    AsyncWebServerResponse *res = req->beginResponse(*hubFS, String(path), contentType, false);
    res->addHeader("Cache-Control", cacheStatic ? "public, max-age=86400" : "no-store");
    req->send(res);
    return;
  }

  if (hubFS->exists(path)) {
    AsyncWebServerResponse *res = req->beginResponse(*hubFS, String(path), contentType, false);
    res->addHeader("Cache-Control", cacheStatic ? "public, max-age=86400" : "no-store");
    req->send(res);
    return;
  }

  // Auto-open built-in /upload page when main dashboard files haven't been uploaded yet
  if (strcmp(path, "/index.html") == 0) {
    Serial.println("[HTTP] /index.html missing -> redirecting to /upload");
    req->redirect("/upload");
    return;
  }

  Serial.printf("[HTTP] 404 Missing: %s\n", path);
  req->send(404, "text/plain", "File not found in flash storage (open /upload to add files)");
}

void sendStoredJsonFile(AsyncWebServerRequest *req, const char *path,
                        const char *emptyFallback) {
  if (!hubFS) {
    req->send(500, "application/json", "{\"error\":\"Filesystem not mounted\"}");
    return;
  }
  if (ESP.getFreeHeap() < MIN_FREE_HEAP_FOR_FILES) {
    req->send(503, "application/json", "{\"error\":\"Low memory\"}");
    return;
  }

  if (hubFS->exists(path)) {
    AsyncWebServerResponse *res = req->beginResponse(*hubFS, path, "application/json");
    res->addHeader("Cache-Control", "no-store");
    req->send(res);
    return;
  }

  AsyncWebServerResponse *res = req->beginResponse(200, "application/json", emptyFallback);
  res->addHeader("Cache-Control", "no-store");
  req->send(res);
}

// ============================================================================
// 15. BACKGROUND SERVICERS (BOOT BUTTON, FORGET-BOOT & NATIVE mDNS SCANNER)
// ============================================================================
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

  JsonDocument doc(&psramAllocator);
  JsonArray arr = doc.to<JsonArray>();

  if (WiFi.status() == WL_CONNECTED && mdnsRunning) {
    String selfIp = WiFi.localIP().toString();
    int added = 0;

    auto queryServiceType = [&](const char *service, const char *proto,
                                const char *defaultType) {
      int n = MDNS.queryService(service, proto);
      for (int i = 0; i < n && added < MAX_MDNS_SCAN_RESULTS; i++) {
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
    if (localWantMqtt && added < MAX_MDNS_SCAN_RESULTS) {
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
// 16. WEB SERVER ROUTES (REGISTERED ONCE - SAFE RELAUNCH ON RECONNECT)
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
  DefaultHeaders::Instance().addHeader("Access-Control-Allow-Headers",
                                       "Content-Type, X-API-Key, X-Session-Token, X-Upload-Token");

  // --- Health Check ---
  server.on("/ping", ASYNC_GET, [](AsyncWebServerRequest *req) {
    Serial.println("[HTTP] 200 /ping");
    req->send(200, "text/plain", "pong");
  });

  // --- POST/GET /api/oled/devices?on=4&off=1 ---
  server.on("/api/oled/devices", ASYNC_GET, [](AsyncWebServerRequest *req) {
    if (req->hasParam("on") && req->hasParam("off")) {
      webDevicesOnline = (uint8_t)req->getParam("on")->value().toInt();
      webDevicesOffline = (uint8_t)req->getParam("off")->value().toInt();
      webDeviceOverrideActive = true;
      webDeviceOverrideUntil = millis() + 60000UL;  // Valid for 60s, then ESP32 auto-checker resumes
      oledForceRedraw = true;
      req->send(200, "application/json", "{\"ok\":true}");
      return;
    }
    req->send(400, "application/json", "{\"ok\":false}");
  });

  // --- Built-in Flash Uploader Page (/upload) ---
  server.on("/upload", ASYNC_GET, [](AsyncWebServerRequest *req) {
    size_t totalLen = sizeof(UPLOAD_HTML) - 1;
    AsyncWebServerResponse *res = req->beginChunkedResponse(
      "text/html",
      [totalLen](uint8_t *buffer, size_t maxLen, size_t index) -> size_t {
        if (index >= totalLen) return 0;
        size_t toCopy = totalLen - index;
        if (toCopy > maxLen) toCopy = maxLen;
        memcpy_P(buffer, UPLOAD_HTML + index, toCopy);
        return toCopy;
      });
    res->addHeader("Cache-Control", "no-store");
    req->send(res);
  });

  // --- GET /api/upload-auth/status ---
  server.on("/api/upload-auth/status", ASYNC_GET, [](AsyncWebServerRequest *req) {
    JsonDocument d(&psramAllocator);
    if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      d["locked"] = uploadAuthLocked;
      d["failedAttempts"] = uploadAuthFailedAttempts;
      d["remainingAttempts"] = (uploadAuthFailedAttempts >= UPLOAD_AUTH_MAX_ATTEMPTS)
                                 ? 0
                                 : (UPLOAD_AUTH_MAX_ATTEMPTS - uploadAuthFailedAttempts);
      xSemaphoreGive(asyncReqMutex);
    }
    AsyncResponseStream *res = req->beginResponseStream("application/json");
    res->addHeader("Cache-Control", "no-store");
    serializeJson(d, *res);
    req->send(res);
  });

  // --- POST /api/upload-auth/login (Max 3 failed attempts -> locked until fresh restart) ---
  server.on(
    "/api/upload-auth/login", ASYNC_POST,
    [](AsyncWebServerRequest *req) {
      SmallJsonBody *buf = static_cast<SmallJsonBody *>(req->_tempObject);
      String user, pass;
      if (buf && !buf->overflow && buf->len > 0) {
        JsonDocument in(&psramAllocator);
        if (!deserializeJson(in, buf->data)) {
          user = String(in["username"] | "");
          pass = String(in["password"] | "");
          user.trim();
        }
      }
      if (buf) {
        delete buf;
        req->_tempObject = nullptr;
      }

      // 1. Check lockout state first
      bool alreadyLocked = false;
      if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
        alreadyLocked = uploadAuthLocked;
        xSemaphoreGive(asyncReqMutex);
      }
      if (alreadyLocked) {
        req->send(423, "application/json",
                  "{\"ok\":false,\"locked\":true,\"remainingAttempts\":0,"
                  "\"error\":\"Locked after 3 failed attempts. Fresh hardware restart required.\"}");
        return;
      }

      // 2. Verify against admin users in /config.json (or esp/456456 on first boot)
      bool valid = verifyUploadAdminCredentials(user, pass);

      JsonDocument out(&psramAllocator);
      int httpCode = 401;

      if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(300)) == pdTRUE) {
        if (valid) {
          uploadAuthFailedAttempts = 0;
          IPAddress ip = req->client() ? req->client()->remoteIP() : IPAddress(0, 0, 0, 0);
          generateUploadSessionToken(ip);
          out["ok"] = true;
          out["token"] = (const char *)uploadSessionToken;
          httpCode = 200;
        } else {
          if (uploadAuthFailedAttempts < UPLOAD_AUTH_MAX_ATTEMPTS) uploadAuthFailedAttempts++;
          if (uploadAuthFailedAttempts >= UPLOAD_AUTH_MAX_ATTEMPTS) {
            uploadAuthLocked = true;
            invalidateUploadSession();
            oledForceRedraw = true;
          }
          uint8_t rem = (uploadAuthFailedAttempts >= UPLOAD_AUTH_MAX_ATTEMPTS)
                          ? 0
                          : (UPLOAD_AUTH_MAX_ATTEMPTS - uploadAuthFailedAttempts);
          out["ok"] = false;
          out["locked"] = uploadAuthLocked;
          out["remainingAttempts"] = rem;
          out["error"] = uploadAuthLocked
                           ? "Maximum attempts reached. Restart required."
                           : "Invalid admin username or password";
          httpCode = uploadAuthLocked ? 423 : 401;
        }
        xSemaphoreGive(asyncReqMutex);
      }

      AsyncResponseStream *res = req->beginResponseStream("application/json");
      res->setCode(httpCode);
      res->addHeader("Cache-Control", "no-store");
      serializeJson(out, *res);
      req->send(res);
    },
    nullptr, handleSmallJsonBody);

  // --- POST /api/upload-auth/logout ---
  server.on("/api/upload-auth/logout", ASYNC_POST, [](AsyncWebServerRequest *req) {
    if (isUploadRequestAuthorized(req) && xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      invalidateUploadSession();
      xSemaphoreGive(asyncReqMutex);
    }
    req->send(200, "application/json", "{\"ok\":true}");
  });

  // --- POST /api/upload-auth/forget/start (5s press window + 10s hold; ?mode=confirm for Danger Zone resets) ---
  server.on("/api/upload-auth/forget/start", ASYNC_POST, [](AsyncWebServerRequest *req) {
    if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) != pdTRUE) {
      req->send(503, "application/json", "{\"ok\":false,\"error\":\"Busy\"}");
      return;
    }
    bool confirmOnly = req->hasParam("mode") && req->getParam("mode")->value() == "confirm";
    ufResetUsersOnDone = !confirmOnly;
    ufState = UF_WAIT_PRESS;
    ufWindowDeadlineMs = millis() + UPLOAD_FORGET_PRESS_WINDOW_MS;
    ufHoldStartMs = 0;
    ufReleaseSinceMs = 0;
    ufStatusMsg[0] = '\0';
    xSemaphoreGive(asyncReqMutex);
    req->send(200, "application/json", "{\"ok\":true,\"pressWindowMs\":5000,\"holdMs\":10000}");
  });

  // --- GET /api/upload-auth/forget/status ---
  server.on("/api/upload-auth/forget/status", ASYNC_GET, [](AsyncWebServerRequest *req) {
    JsonDocument d(&psramAllocator);
    unsigned long now = millis();
    if (xSemaphoreTake(asyncReqMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      switch (ufState) {
        case UF_WAIT_PRESS:
          d["state"] = "wait_press";
          d["remainingMs"] = ((int32_t)(ufWindowDeadlineMs - now) > 0) ? (uint32_t)(ufWindowDeadlineMs - now) : 0;
          break;
        case UF_HOLDING:
          d["state"] = "holding";
          d["heldMs"] = (uint32_t)(now - ufHoldStartMs);
          break;
        case UF_DONE:
          d["state"] = "done";
          d["message"] = (const char *)ufStatusMsg;
          break;
        case UF_TIMEOUT:
          d["state"] = "timeout";
          d["message"] = (const char *)ufStatusMsg;
          break;
        case UF_RELEASED_EARLY:
          d["state"] = "released_early";
          d["message"] = (const char *)ufStatusMsg;
          break;
        default:
          d["state"] = "idle";
          break;
      }
      xSemaphoreGive(asyncReqMutex);
    }
    AsyncResponseStream *res = req->beginResponseStream("application/json");
    res->addHeader("Cache-Control", "no-store");
    serializeJson(d, *res);
    req->send(res);
  });

  // --- POST /api/fs/reboot (Authenticated reboot from /upload) ---
  server.on("/api/fs/reboot", ASYNC_POST, [](AsyncWebServerRequest *req) {
    if (!isUploadRequestAuthorized(req)) {
      req->send(401, "application/json", "{\"ok\":false,\"error\":\"Unauthorized\"}");
      return;
    }
    req->send(200, "application/json", "{\"ok\":true,\"msg\":\"Restarting...\"}");
    restartPending = true;
    oledPostAlert("REBOOTING HUB", "Restart requested", "Please wait...", "", 0, true);
    restartAt = millis() + 600;
  });

  // --- GET /api/fs/list (Lists flash storage & files for /upload) ---
  server.on("/api/fs/list", ASYNC_GET, [](AsyncWebServerRequest *req) {
    if (!isUploadRequestAuthorized(req)) {
      req->send(401, "application/json", "{\"ok\":false,\"error\":\"Unauthorized\"}");
      return;
    }
    JsonDocument doc(&psramAllocator);
    uint64_t totalB = fsTotalBytes();
    uint64_t usedB = fsUsedBytes();
    doc["board"] = HUB_BOARD_NAME;
    doc["fsType"] = fsTypeName;
    doc["usedBytes"] = usedB;
    doc["totalBytes"] = totalB;
    doc["freeBytes"] = (totalB > usedB) ? (totalB - usedB) : 0;
    doc["psramOk"] = hasPsram;
    doc["psramTotalBytes"] = hasPsram ? ESP.getPsramSize() : 0;

    JsonArray arr = doc["files"].to<JsonArray>();
    if (hubFS && xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
      File root = hubFS->open("/");
      if (root) {
        for (File f = root.openNextFile(); f; f = root.openNextFile()) {
          if (f.isDirectory()) continue;
          String name = String(f.name());
          if (!name.startsWith("/")) name = String("/") + name;
          JsonObject item = arr.add<JsonObject>();
          item["name"] = name;
          item["size"] = (uint32_t)f.size();
        }
        root.close();
      }
      xSemaphoreGive(fsMutex);
    }

    AsyncResponseStream *res = req->beginResponseStream("application/json");
    res->addHeader("Cache-Control", "no-store");
    serializeJson(doc, *res);
    req->send(res);
  });

  // --- POST /api/fs/upload (Streams uploaded files straight into FFat/SPIFFS) ---
  server.on(
    "/api/fs/upload", ASYNC_POST,
    [](AsyncWebServerRequest *req) {
      if (!isUploadRequestAuthorized(req)) {
        req->send(401, "application/json", "{\"ok\":false,\"error\":\"Unauthorized\"}");
        return;
      }
      bool ok = false;
      size_t bytes = 0;
      String path;
      String err;

      if (fsMutex && xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
        if (fsUploadSession.active && fsUploadSession.owner == req) {
          if (fsUploadSession.file) {
            fsUploadSession.file.flush();
            fsUploadSession.file.close();
          }
          ok = fsUploadSession.ok;
          bytes = fsUploadSession.bytesWritten;
          path = fsUploadSession.path;
          err = fsUploadSession.errorMsg;
          fsUploadSession.active = false;
          fsUploadSession.owner = nullptr;
        } else {
          err = "No file received or uploader busy";
        }
        xSemaphoreGive(fsMutex);
      } else {
        err = "Storage busy";
      }

      JsonDocument out(&psramAllocator);
      out["ok"] = ok;
      if (ok) {
        out["path"] = path;
        out["bytes"] = (uint32_t)bytes;
        notifyStorage();
      } else {
        out["error"] = err.isEmpty() ? "Upload failed" : err;
      }

      AsyncResponseStream *res = req->beginResponseStream("application/json");
      res->setCode(ok ? 200 : 500);
      res->addHeader("Cache-Control", "no-store");
      serializeJson(out, *res);
      req->send(res);
    },
    handleFsFileUploadChunk);

  // --- POST /api/fs/delete?path=/filename ---
  server.on("/api/fs/delete", ASYNC_POST, [](AsyncWebServerRequest *req) {
    if (!isUploadRequestAuthorized(req)) {
      req->send(401, "application/json", "{\"ok\":false,\"error\":\"Unauthorized\"}");
      return;
    }
    if (!hubFS || !req->hasParam("path")) {
      req->send(400, "application/json", "{\"ok\":false,\"error\":\"Missing path\"}");
      return;
    }
    String p = sanitizeUploadPath(req->getParam("path")->value());
    if (p.isEmpty()) {
      req->send(400, "application/json", "{\"ok\":false,\"error\":\"Invalid path\"}");
      return;
    }

    bool removed = false;
    if (xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
      if (hubFS->exists(p.c_str())) {
        removed = hubFS->remove(p.c_str());
      }
      clearPsramCacheLocked();
      xSemaphoreGive(fsMutex);
    }

    if (removed) {
      notifyStorage();
      req->send(200, "application/json", "{\"ok\":true}");
    } else {
      req->send(404, "application/json", "{\"ok\":false,\"error\":\"File not found\"}");
    }
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
    JsonDocument d(&psramAllocator);
    bool connected = (WiFi.status() == WL_CONNECTED);
    uint32_t totalHeap = ESP.getHeapSize();
    uint32_t freeHeap = ESP.getFreeHeap();
    uint32_t usedHeap = (totalHeap > freeHeap) ? (totalHeap - freeHeap) : 0;

    uint32_t psramTotal = hasPsram ? ESP.getPsramSize() : 0;
    uint32_t psramFree = hasPsram ? ESP.getFreePsram() : 0;
    uint32_t psramUsed = (psramTotal > psramFree) ? (psramTotal - psramFree) : 0;

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
    d["storageUsedKb"] = roundf((fsUsedBytes() / 1024.0f) * 10.0f) / 10.0f;
    d["storageTotalKb"] = roundf((fsTotalBytes() / 1024.0f) * 10.0f) / 10.0f;
    d["maxConfigBytes"] = MAX_CONFIG_BYTES;
    d["maxDesignBytes"] = MAX_DESIGN_BYTES;
    d["timeSynced"] = timeSynced;
    d["lastSync"] = lastSyncTimeStr;

    // Extended hardware & S3 PSRAM / 16MB flash telemetry (non-breaking)
    d["board"] = HUB_BOARD_NAME;
    d["chip"] = ESP.getChipModel();
    d["cpuMhz"] = ESP.getCpuFreqMHz();
    d["flashMb"] = ESP.getFlashChipSize() / (1024UL * 1024UL);
    d["fsType"] = fsTypeName;
    d["psramOk"] = hasPsram;
    d["psramTotalKb"] = psramTotal / 1024;
    d["psramUsedKb"] = psramUsed / 1024;
    d["psramFreeKb"] = psramFree / 1024;
    d["psramCacheKb"] = roundf((psramCacheTotalBytes / 1024.0f) * 10.0f) / 10.0f;
    d["i2cSda"] = I2C_SDA_PIN;
    d["i2cScl"] = I2C_SCL_PIN;
    d["displayAddr"] = detectedI2cDisplayAddr;

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

  // --- POST /api/design (Zero-RAM-buffer streaming write) ---
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
        JsonDocument doc(&psramAllocator);
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

      JsonDocument out(&psramAllocator);
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
        JsonDocument doc(&psramAllocator);
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
    if (uploadAuthLocked) {
      req->send(423, "application/json", "{\"ok\":false,\"error\":\"Locked - physical restart required\"}");
      return;
    }
    req->send(200, "application/json", "{\"ok\":true,\"msg\":\"Restarting...\"}");
    restartPending = true;
    oledPostAlert("REBOOTING HUB", "Restart requested", "Please wait...", "", 0, true);
    restartAt = millis() + 600;
  });

  // --- POST /api/reset?mode=data|settings|factory ---
  server.on("/api/reset", ASYNC_POST, [](AsyncWebServerRequest *req) {
    if (uploadAuthLocked) {
      req->send(423, "application/json", "{\"ok\":false,\"error\":\"Locked - physical restart required\"}");
      return;
    }
    String mode = req->hasParam("mode") ? req->getParam("mode")->value() : "factory";
    mode.trim();
    mode.toLowerCase();

    if (mode == "data") {
      // 1. RESET DATA: Erase 2D designs in flash storage
      if (hubFS && xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
        if (hubFS->exists(DESIGN_PATH)) hubFS->remove(DESIGN_PATH);
        if (hubFS->exists(DESIGN_TMP_PATH)) hubFS->remove(DESIGN_TMP_PATH);
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
      // 3. FACTORY RESET: Erase flash config/design + hubnet + hubtime + WiFi (wfcfg) + Reboot
      if (hubFS && xSemaphoreTake(fsMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
        if (hubFS->exists(CONFIG_PATH)) hubFS->remove(CONFIG_PATH);
        if (hubFS->exists(CONFIG_TMP_PATH)) hubFS->remove(CONFIG_TMP_PATH);
        if (hubFS->exists(DESIGN_PATH)) hubFS->remove(DESIGN_PATH);
        if (hubFS->exists(DESIGN_TMP_PATH)) hubFS->remove(DESIGN_TMP_PATH);
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
      oledPostAlert("!! FACTORY RESET !!", "Erasing all data", "Wiping WiFi...", "Rebooting now", 0, true);
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
  Serial.println("[SERVER] Web server listening on port 80 (Uploader: /upload)");
}

// ============================================================================
// 17. SETUP
// ============================================================================
void setup() {
  std::set_new_handler(oomNewHandler);
  setCpuFrequencyMhz(240);

  fsMutex = xSemaphoreCreateMutex();
  asyncReqMutex = xSemaphoreCreateMutex();

  pinMode(LED_PIN, OUTPUT);
  pinMode(BUZZER_PIN, OUTPUT);
  pinMode(BOOT_BUTTON, INPUT_PULLUP);
  digitalWrite(LED_PIN, LOW);
  digitalWrite(BUZZER_PIN, LOW);

#if !HAS_BUILTIN_RGB_LED
  pinMode(BUILTIN_LED_PIN, OUTPUT);
#endif
  setBuiltinLed(false);

  snprintf(bootIdStr, sizeof(bootIdStr), "%08lX", (unsigned long)esp_random());

  Serial.begin(115200);
#if defined(ARDUINO_USB_CDC_ON_BOOT) && ARDUINO_USB_CDC_ON_BOOT
  unsigned long serialWaitStart = millis();
  while (!Serial && (millis() - serialWaitStart < 1500)) {
    delay(10);
  }
#endif

  // Detect & activate full 8 MB OPI PSRAM on ESP32-S3 N16R8
  hasPsram = psramFound() && (ESP.getPsramSize() > 0);

  Serial.println("\n==========================================");
  Serial.printf("  ESP32 Smart Hub Starting (%s)\n", HUB_BOARD_NAME);
  Serial.printf("  Chip: %s @ %lu MHz | Flash: %lu MB\n",
                ESP.getChipModel(),
                (unsigned long)ESP.getCpuFreqMHz(),
                (unsigned long)(ESP.getFlashChipSize() / (1024UL * 1024UL)));
  Serial.printf("  Boot ID: %s | Internal Heap: %lu B\n",
                bootIdStr, (unsigned long)ESP.getFreeHeap());
  if (hasPsram) {
    Serial.printf("  PSRAM: ACTIVE (%lu KB free / %lu KB total)\n",
                  (unsigned long)(ESP.getFreePsram() / 1024UL),
                  (unsigned long)(ESP.getPsramSize() / 1024UL));
  } else {
    Serial.println("  PSRAM: Not present / disabled");
  }
  Serial.println("==========================================");

  initI2cDisplayBus();
  oledShowBoot(hasPsram ? "PSRAM: Active" : "PSRAM: Off", 15);

  beepShort(1);
  delay(1200);

  if (!initStorage()) {
    Serial.println("[ERROR] No usable SPIFFS or FFat partition mounted!");
    oledShowBoot("FS MOUNT FAILED!", 30);
  } else {
    // Clean any incomplete temporary files left by an unexpected power loss
    if (hubFS->exists(CONFIG_TMP_PATH)) hubFS->remove(CONFIG_TMP_PATH);
    if (hubFS->exists(DESIGN_TMP_PATH)) hubFS->remove(DESIGN_TMP_PATH);
    Serial.printf("[OK] %s mounted (%llu / %llu KB used)\n",
                  fsTypeName,
                  (unsigned long long)(fsUsedBytes() / 1024ULL),
                  (unsigned long long)(fsTotalBytes() / 1024ULL));
    oledShowBoot((String("FS: ") + fsTypeName + " OK").c_str(), 35);

    File root = hubFS->open("/");
    if (root) {
      for (File f = root.openNextFile(); f; f = root.openNextFile()) {
        Serial.printf("  [%s] %s (%u B)\n", fsTypeName, f.name(), (unsigned)f.size());
      }
      root.close();
    }
  }

  loadNetworkAndTimeFromNvs();
  oledShowBoot("NVS Config Loaded", 48);
  reloadDevicesFromConfig();
  oledShowBoot(("Devices: " + String(trackedDeviceCount)).c_str(), 55);

  // Hold BOOT at startup to recover WiFi / reset Static IP back to DHCP
  if (digitalRead(BOOT_BUTTON) == LOW) {
    oledShowBoot("BOOT Held -> AP", 60);
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
  oledShowBoot("Web Server: Port 80", 88);
  lastWifiRetryMs = millis();

  if (WiFi.status() == WL_CONNECTED) {
    WiFi.setSleep(false);
    startOrRefreshMdns();
    oledShowBoot(("mDNS:" + netCfg.mdnsHost).c_str(), 94);
    syncTime();
    oledShowBoot("System Ready!", 100);
    delay(1000);
    wifiGotIpFlag = false;  // Already initialized above
  } else {
    oledShowBoot("WiFi Pending...", 100);
    delay(500);
  }
  oledForceRedraw = true;

  Serial.printf("[READY] Free Heap: %lu B | Min Heap: %lu B | Free PSRAM: %lu KB\n",
                (unsigned long)ESP.getFreeHeap(),
                (unsigned long)ESP.getMinFreeHeap(),
                hasPsram ? (unsigned long)(ESP.getFreePsram() / 1024UL) : 0UL);
}

// ============================================================================
// 18. MAIN LOOP (NON-BLOCKING & SELF-HEALING)
// ============================================================================
void loop() {
  unsigned long now = millis();

  // 1. Smooth Server, mDNS & Time Refresh whenever WiFi gets/regains an IP
  if (wifiGotIpFlag) {
    wifiGotIpFlag = false;
    WiFi.setSleep(false);
    Serial.printf("[WIFI] IP Ready: %s (Uploader: http://%s/upload)\n",
                  WiFi.localIP().toString().c_str(),
                  WiFi.localIP().toString().c_str());
    oledPostAlert("WIFI CONNECTED", WiFi.SSID().c_str(), WiFi.localIP().toString().c_str(), "Server & mDNS OK", 3000, false);

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
      oledPostAlert("NETWORK UPDATE", "Applying new IP...", "Reconnecting WiFi", "", 4000, false);
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
  serviceUploadForgetButton();
  serviceNativeMdnsScan();
  serviceDeviceHealthCheck();
  serviceOledDisplay();

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
      char heapBuf[22];
      snprintf(heapBuf, sizeof(heapBuf), "Heap: %lu B", (unsigned long)ESP.getFreeHeap());
      oledPostAlert("!! LOW MEMORY !!", heapBuf, "Critical threshold", "Auto-restarting...", 0, true);
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