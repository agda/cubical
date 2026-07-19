#!/usr/bin/env sh

printf 'module Cubical.Everything where\n\n'
find Cubical/ -type f -name "*.agda" | sed -e 's/\//./g' -e 's/\.agda$//g' -e 's/^/import /'
