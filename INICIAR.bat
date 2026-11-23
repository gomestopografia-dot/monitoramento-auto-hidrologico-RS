@echo off
setlocal
cd /d "%~dp0"
title Dashboard Hidrologico - 3 DE
echo Iniciando Dashboard Hidrologico...
where py >nul 2>nul
if %errorlevel%==0 (
    py -3 server.py
) else (
    where python >nul 2>nul
    if %errorlevel%==0 (
        python server.py
    ) else (
        echo ERRO: Python nao encontrado. Instale Python 3 e marque Add Python to PATH.
    )
)
echo.
echo O servidor foi encerrado ou nao conseguiu iniciar.
pause
