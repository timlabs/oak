@echo off
where /q ruby
if %errorlevel% == 0 (
  ruby "%~dp0\src\oak.rb" %*
) else (
  echo error: could not find "ruby"
  echo Oak requires the Ruby programming language to be installed.
)