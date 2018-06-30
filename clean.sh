#!/bin/bash
find /home/papa/verified-algebra/ -name "*~" -delete
~/.cabal/bin/idris --clean verified-algebra.ipkg
