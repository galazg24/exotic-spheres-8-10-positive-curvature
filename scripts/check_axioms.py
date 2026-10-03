#!/usr/bin/env python3
"""Checks the output of `lake env lean audit/PrintAxioms.lean`: every audited declaration may
depend only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`."""
import re, sys
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
text = open(sys.argv[1]).read()
entries = re.findall(r"'(.+?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.S)
bad = []
for name, _, axs in entries:
    used = {a.strip() for a in axs.replace('\n', ' ').split(',') if a.strip()}
    if not used <= ALLOWED:
        bad.append((name, sorted(used - ALLOWED)))
print(f'AUDITED={len(entries)} NONSTANDARD={len(bad)}')
for n, a in bad:
    print(f'  {n}: {a}')
if not entries or bad or 'error' in text:
    sys.exit(1)
