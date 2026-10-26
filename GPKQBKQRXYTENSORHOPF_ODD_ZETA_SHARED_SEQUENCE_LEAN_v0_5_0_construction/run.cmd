@echo off
echo RUNNER_ENTERED=ODD_ZETA_SHARED_SEQUENCE_v0_5_0
setlocal EnableExtensions DisableDelayedExpansion
rem Native Windows only. The authoring host has not executed this runner.
set "CSCRIPT=%SystemRoot%\System32\cscript.exe"
set "CERTUTIL=%SystemRoot%\System32\certutil.exe"
set "RUNNER_JS=%~dp0cache_runner.js"
set "EXPECTED_JS_SHA256=2f81a823bee30ef6b956252a27f236202b6f363f30b8d38d890eb9e20bb56482"
set "HASH_TEMP=%TEMP%\ZH_NATIVE_RUNNER_%RANDOM%_%RANDOM%.tmp"
set "ACTUAL_JS_SHA256="
if not exist "%CSCRIPT%" (
  echo BUILD=FAIL
  echo REASON=NATIVE_CSCRIPT_MISSING
  exit /b 10
)
if not exist "%CERTUTIL%" (
  echo BUILD=FAIL
  echo REASON=NATIVE_CERTUTIL_MISSING
  exit /b 11
)
if not exist "%RUNNER_JS%" (
  echo BUILD=FAIL
  echo REASON=CACHE_RUNNER_SCRIPT_MISSING
  exit /b 12
)
"%CERTUTIL%" -hashfile "%RUNNER_JS%" SHA256 >"%HASH_TEMP%" 2>&1
if errorlevel 1 (
  type "%HASH_TEMP%"
  del /q "%HASH_TEMP%" >nul 2>&1
  echo BUILD=FAIL
  echo REASON=RUNNER_SHA256_COMMAND_FAILED
  exit /b 13
)
for /f "usebackq skip=1 tokens=*" %%H in ("%HASH_TEMP%") do if not defined ACTUAL_JS_SHA256 set "ACTUAL_JS_SHA256=%%H"
del /q "%HASH_TEMP%" >nul 2>&1
set "ACTUAL_JS_SHA256=%ACTUAL_JS_SHA256: =%"
if /I not "%ACTUAL_JS_SHA256%"=="%EXPECTED_JS_SHA256%" (
  echo BUILD=FAIL
  echo REASON=CACHE_RUNNER_SHA256_MISMATCH
  exit /b 14
)
echo RUNNER_SCRIPT_INTEGRITY=PASS
"%CSCRIPT%" //nologo //E:JScript "%RUNNER_JS%" "%~dp0."
exit /b %ERRORLEVEL%
