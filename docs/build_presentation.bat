@echo off
REM Batch file to build and clean LaTeX Beamer presentation

set TEX=presentation.tex
set PDF=presentation.pdf
set AUXFILES="*.aux" "*.log" "*.nav" "*.out" "*.snm" "*.toc" "*.vrb" "*.fdb_latexmk" "*.fls"

if "%1"=="clean" goto clean
if "%1"=="cleanaux" goto cleanaux

echo Building %PDF% from %TEX% ...
pdflatex %TEX%
pdflatex %TEX%
goto end

:clean
  del /Q %AUXFILES% 
  goto end

:cleanaux
  del /Q %AUXFILES%
  goto end

:end
