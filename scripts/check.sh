#!/bin/sh
# Full check: build, lexical scan, axiom audit. Exit status 0 iff all pass.
cd "$(dirname "$0")/.." || exit 2
lake build || exit 1
sh scripts/lexical_scan.sh || exit 1
lake env lean audit/PrintAxioms.lean > audit/axioms.out 2>&1 || { cat audit/axioms.out; exit 1; }
python3 scripts/check_axioms.py audit/axioms.out
