# Changelog

## Unreleased

Editorial and audit-list changes only; no definition, statement or proof changed.

- The paper citation key was standardised to [GG] throughout the README, documentation and
  Lean docstrings.
- `audit/PrintAxioms.lean`: removed a duplicate entry for `hly_general`. The audit now lists 774
  entries, one per declaration.
- README: provenance and trust-base wording; metadata affiliation given as Durham University.
- Lean file headers: `Authors: Fernando Galaz-García`, followed by the line "Developed with
  extensive assistance from Claude (Anthropic), used through Claude Code."
- `RiemannianGeometry` docstrings refer to modules and declarations by their current
  `RiemannianGeometry` names, not by the vendored library's former namespace.
- The paper's arXiv identifier, arXiv:2609.38126 [math.DG], in the README, `CITATION.cff` and
  `.zenodo.json`.

## v1.0.0-rc1 (2026-10-03)

Release candidate, for independent audit before the v1.0.0 release.

- Complete formalisation of the new arguments in [GG]. Five cited published results (Reiser–Wraith,
  Sperança, Kervaire–Milnor, Hitchin, orientation reversal in Θ₁₀) enter as explicit hypotheses.
- [HLY] Proposition 3.1 in full generality: compact base with boundary, frame-independent
  curvature norms, and two non-vacuity models.
- Axiom audit (775 entries covering 774 distinct declarations, standard axioms only), lexical
  scan, and continuous integration.
