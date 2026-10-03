#!/bin/sh
# Fails if the library contains placeholders or kernel bypasses.
# `admit` is matched in tactic positions only, since prose may contain the English word.
cd "$(dirname "$0")/.." || exit 2
files=$(find ExoticSpheres8And10 RiemannianGeometry -name '*.lean'; echo ExoticSpheres8And10.lean RiemannianGeometry.lean)
if grep -nE '\b(sorry|native_decide|implemented_by)\b|^\s*admit\b|\b(by|:=|<;>|;|·)\s*admit\b|^\s*(axiom|unsafe)\b|set_option\s+debug\.skipKernelTC' $files; then
  echo "LEXICAL_SCAN=FAIL"; exit 1
fi
echo "LEXICAL_SCAN=CLEAN"
