# Changelog

## Unreleased (v1.0.0-rc3 candidate)

Repair of the smooth identification of `E/S³_⋆`, after the independent audit of
`v1.0.0-rc2-audit-source`.

- Theorems A and B now conclude positive sectional curvature on the smooth manifold `E/S³_⋆`:
  `theoremA`/`theoremB` apply to every smooth quotient `p : E → Q` of the star bundle by the star
  action (`StarBundle.IsSmoothStarQuotient`). Previously they concluded it on a polar model
  recorded only as homeomorphic to the topological orbit space.
- New: `IsSmoothStarQuotient` with `isSmoothStarQuotient_starQuotMap` (the polar model is a smooth
  star quotient) and `IsSmoothStarQuotient.diffeomorph` (any two are diffeomorphic), in
  `StarBundles.SmoothQuotient`; `HasPosCurvMetric.of_diffeomorph` (positive sectional curvature
  pulls back along diffeomorphisms), in `Geometry.DiffeoTransport`; `polarModelA`, `polarModelB`.
- Sperança's input in `SECc_of_theoremA`/`B` is now his Theorem 1 at its published strength:
  some smooth star quotient `p : E → Q` has `Rep Q g`. It replaces a hypothesis about every polar
  model homeomorphic to the orbit space, which was stronger than the published result.
- The RW hypothesis of `SECc_of_theoremA`/`B` is restricted to polar models with the given
  representation.
- `CITATION.cff`: version `1.0.0-rc3`.
- Axiom audit: 785 entries, 785 distinct declarations (11 new).

## v1.0.0-rc2-audit-source (2026-10-04)

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
