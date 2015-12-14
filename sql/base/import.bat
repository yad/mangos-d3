@echo off
mysql -u root -proot characters < characters.sql
mysql -u root -proot realmd < realmd.sql
pause