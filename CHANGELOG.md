# Changelog

## 1.0.0 — 2026-10-05

First scholarly release, accompanying [GG] (arXiv:2609.38126).

- Completed formalisation of the new arguments in [GG]; the five cited published input categories
  enter as explicit hypotheses.
- Revisions following the first independent cross-vendor audit (of `v1.0.0-rc2-audit-source`),
  made in `v1.0.0-rc3-audit-source`.
- A second independent audit of the revised candidate reported no remaining findings.
- Axiom audit: 785 audited declarations, standard axioms only (no nonstandard axioms).
- The sanitised cross-vendor audit reports are included under `audit/cross-vendor-v1.0.0-rc2/` and
  `audit/cross-vendor-v1.0.0-rc3/`.
- Citation metadata: version `1.0.0`, release date 2026-10-05.
- No definition, statement or proof changed from `v1.0.0-rc3-audit-source`.

## v1.0.0-rc3-audit-source (2026-10-05)

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
- `remark_general_bound` and `remark_general_bound_RW` ([GG] `rem:general_bound`) likewise record
  that their polar model is a smooth star quotient of `E`. They previously recorded only a
  homeomorphism with the orbit space.
- `CITATION.cff`: version `1.0.0-rc3`. `date-released` is not set for a release candidate; the
  candidate's freeze date is recorded by its annotated tag.
- [Sp] is cited from the published version, Proc. Amer. Math. Soc. 144 (2016), Theorem 1 on
  p. 3182 (doi:10.1090/proc/12945), with its wording for the 10-dimensional class.
- Citations: the standard quotient-manifold facts used to read Sperança's theorem are cited from
  [Lee] (Cor. 21.6, Thms 21.10, 4.29; Thm 4.31 for the uniqueness proved here).
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
