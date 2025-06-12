@echo off
setlocal enabledelayedexpansion
echo ========================================
echo BPMN Test Execution Script
echo ========================================
echo.

REM set variables
set LOG_DIR=tests
REM use PowerShell to generate timestamp for compatibility
for /f "delims=" %%i in ('powershell -command "Get-Date -Format 'yyyyMMdd_HHmmss'"') do set TIMESTAMP=%%i
set LOG_FILE=%LOG_DIR%\test-execution-all-%TIMESTAMP%.log

REM ensure tests directory exists
if not exist "%LOG_DIR%" mkdir "%LOG_DIR%"

echo Starting BPMN Test Execution for ALL JSON files...
echo Timestamp: %date% %time%
echo Log file: %LOG_FILE%
echo.

REM initialize log file
echo ======================================== > "%LOG_FILE%"
echo BPMN Test Execution Log - ALL JSON FILES >> "%LOG_FILE%"
echo Timestamp: %date% %time% >> "%LOG_FILE%"
echo ======================================== >> "%LOG_FILE%"
echo. >> "%LOG_FILE%"

REM initialize counters
set /a success_count=0
set /a failed_count=0
set /a total_count=0

REM process each json file
for /f "delims=" %%F in ('powershell -command "Get-ChildItem -Path tests -Recurse -Name '*.json'"') do (
    set /a total_count+=1
    set INPUT_FILE=tests/%%F
    set TEST_NAME=%%~nF
    
    echo.
    echo ========================================
    echo Processing: %%F
    echo ========================================
    
    echo. >> "%LOG_FILE%"
    echo ======================================== >> "%LOG_FILE%"
    echo Processing: %%F >> "%LOG_FILE%"
    echo ======================================== >> "%LOG_FILE%"
    echo. >> "%LOG_FILE%"
    
    REM step 1: convert JSON model to test file
    echo [STEP 1] Converting JSON model to test file... >> "%LOG_FILE%"
    echo Command: node json-to-process.js !INPUT_FILE! >> "%LOG_FILE%"
    echo ---------------------------------------- >> "%LOG_FILE%"
    
    echo [STEP 1] Converting !INPUT_FILE!...
    node json-to-process.js !INPUT_FILE! >> "%LOG_FILE%" 2>&1
    
    REM check if step 1 is successful
    if !ERRORLEVEL! neq 0 (
        echo [ERROR] Step 1 failed with error code: !ERRORLEVEL! >> "%LOG_FILE%"
        echo [ERROR] Step 1 failed for !INPUT_FILE!
        set /a failed_count+=1
        echo ---------------------------------------- >> "%LOG_FILE%"
        goto :continue
    )
    
    echo [STEP 1] Conversion completed successfully. >> "%LOG_FILE%"
    echo. >> "%LOG_FILE%"
    
    REM step 2: run generated test file
    echo [STEP 2] Running generated test file... >> "%LOG_FILE%"
    echo Command: node tests/generated-!TEST_NAME!.js >> "%LOG_FILE%"
    echo ---------------------------------------- >> "%LOG_FILE%"
    
    echo [STEP 2] Running generated test file...
    node tests/generated-!TEST_NAME!.js >> "%LOG_FILE%" 2>&1
    
    REM check if step 2 is successful
    if !ERRORLEVEL! neq 0 (
        echo [ERROR] Step 2 failed with error code: !ERRORLEVEL! >> "%LOG_FILE%"
        echo [ERROR] Step 2 failed for !TEST_NAME!
        set /a failed_count+=1
    ) else (
        echo [STEP 2] Test execution completed successfully. >> "%LOG_FILE%"
        echo [SUCCESS] Test completed for !TEST_NAME!
        set /a success_count+=1
    )
    
    :continue
    echo ---------------------------------------- >> "%LOG_FILE%"
)

REM print summary
echo.
echo ========================================
echo Test Execution Summary
echo ========================================
echo Total files processed: !total_count!
echo Successful tests: !success_count!
echo Failed tests: !failed_count!
echo ========================================

echo. >> "%LOG_FILE%"
echo ======================================== >> "%LOG_FILE%"
echo Test Execution Summary >> "%LOG_FILE%"
echo Total files processed: !total_count! >> "%LOG_FILE%"
echo Successful tests: !success_count! >> "%LOG_FILE%"
echo Failed tests: !failed_count! >> "%LOG_FILE%"
echo Test execution finished at: %date% %time% >> "%LOG_FILE%"
echo ======================================== >> "%LOG_FILE%"

echo.
echo ========================================
echo All tests completed!
echo Log file saved to: %LOG_FILE%
echo ========================================
echo.

REM print last 15 lines of log file
echo Last 15 lines of log file:
echo ----------------------------------------
powershell -command "Get-Content '%LOG_FILE%' | Select-Object -Last 15"
echo ----------------------------------------

pause 