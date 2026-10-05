# Rc3 regression and hostile headline review

## Frozen identity

```text
RC3_AUDIT_SOURCE_TAG=v1.0.0-rc3-audit-source
RC3_AUDIT_SOURCE_COMMIT=95b467a0e0efbc95473ad2c5a918d499a7607fef
RC3_AUDIT_SOURCE_TREE=8d7805b9b0a4ad5307e611b44b47fc5da9f99239
RC3_AUDIT_TAG_OBJECT=21992edc4fb8e80ca32e4a52237bc389c2b4dcde
MANIFEST_VERIFICATION=15/15 MATCH
PREVIOUS_RC2_AUDIT_SOURCE_COMMIT=ad7a77f4b6619cd160090095211fbc001939a540
PREVIOUS_RC2_AUDIT_HANDOFF_COMMIT=fde484d6ead04b84b799aa5e5388d9066ce0e857
PAPER_ARXIV=2609.38126v2
```

Fresh authenticated GitHub clone, detached frozen tag, initially clean. Commit, tree, tag object and peeled commit match the task exactly. All 15 supplied SHA-256 values match. Final source verification: clean status, unchanged HEAD/tree, all 219 tracked-file hashes unchanged. Builds and probes used disposable snapshots; no candidate repair or source edit occurred. The complete manifest is in CROSS_VENDOR_RC3_REPRODUCIBILITY.md.

## Pass B: occurrence classification

The complete tracked Lean repository was searched for Homeomorph, ≃ₜ, homeomorphism/homeomorphic wording and topological-equivalence wording. Source uses and consumers were inspected, especially around HasPosCurvMetric, sectionalCurvatureAt, Rep, StarBundle, QuotSpace, PolarData and RWGluing. Raw matches are preserved in the raw audit record (kept privately). The table groups repeated occurrences sharing one interface; it does not classify a smooth-chart implementation by its type name alone.

| Occurrences / interface | Classification | Evidence |
|---|---|---|
| StarBundles/Equivariant.lean prop_polar; NormalForm.lean starQuotientHomeo, starQuotientManifold; Model.lean and PolarBundles/Summary.lean examples | TOPOLOGICAL USE IS SUFFICIENT | Topological orbit descriptions; bundle diffeomorphism and canonical quotient smooth/descent proofs are separately present. Headline geometry now consumes the smooth witness. |
| PolarBundles/Attaching.lean orbitSpaceHomeo, DNHomeo, DSHomeo, diskGluingHomeo, orbitSpaceDiskGluing | TOPOLOGICAL USE IS SUFFICIENT | Underlying quotient/disk topology and compactness. No metric or smooth-class transfer is justified from an arbitrary one of these maps. |
| PolarBundles/AttachingDiffeo.lean fullN/fullS, partial charts, xModel, lem_attaching_3_smooth | SMOOTH BRIDGE PRESENT | Explicit chart smoothness and inverse smoothness; smooth collar-gluing model and diffeomorphism to every such model. |
| PolarBundles/PolarBundle.lean ΦPh/κP; StarQuotient.lean ΦSh/κS | SMOOTH BRIDGE PRESENT | Smoothness in both directions and hκ/hκs; the smooth glued atlas requires these proofs. |
| PolarBundles/PolarCoordinates.lean disk/cap homeomorphism | TOPOLOGICAL USE IS SUFFICIENT | Cap topology; smooth attaching/collar charts are established elsewhere on the actual model. |
| Geometry/Gluing.lean partial-homeomorphism atlas and opensPH | SMOOTH BRIDGE PRESENT | transitions_mem and hasGroupoid_smooth use both transition and inverse smoothness; opensPH smoothness lemmas require smooth maps, not mere continuity. |
| Geometry/Boundary/DiskGluing.lean ψN/ψS | SMOOTH BRIDGE PRESENT | DiskGluingModel includes four smoothness fields, source/cover/overlap/glue conditions; glueDiffeo proves both maps smooth and inverse. |
| Geometry/Boundary/RegularDomain.lean AdmChart; translated charts | SMOOTH BRIDGE PRESENT | Explicit smooth/inverse-smooth fields, regular-domain compatibility; ordinary translations are smooth. |
| Geometry/Boundary/Radial.lean radialLoc/radialPH | SMOOTH BRIDGE PRESENT | Smooth derivative/invertibility and inverse-function construction, not a topological upgrade without differential hypotheses. |
| Geometry/PullbackMetric.lean extChartAt/OpenPartialHomeomorph bookkeeping | SMOOTH BRIDGE PRESENT | Pullback section proof uses smooth local manifold coordinates and derivative formulas. |
| SmoothQuotient.lean and DiffeoTransport.lean explanatory homeomorphism warnings | TOPOLOGICAL USE IS SUFFICIENT | Comments explaining the distinction; no homeomorphism-based theorem premise. |
| Old theoremA/B, SEC bridges and both general-bound wrappers | POTENTIAL ANALOGUE OF F01 investigated; SMOOTH BRIDGE PRESENT in rc3 | Independent rc2→rc3 comparison verifies these are the six repaired interfaces; no old universal class premise remains. |

No occurrence was classified ACTUAL DEFECT in rc3. The search was followed by inspection of geometric interfaces and proof dependencies; an absence of a word match alone was not treated as proof of absence of a defect.

## General-bound remarks

Curvature/RemarkGeneralBound.lean:123 and Curvature/DHZ.lean:101 now choose B.equivSections.polarData and retain ∃ p, B.IsSmoothStarQuotient p. The first identifies that exact datum with polarOf θ⁻¹ and its attaching map with Jβ; curvature is transferred through equality of data, not homeomorphism. The second constructs RWData and curvature on that same D using its finite infinitesimal operator-norm bound. Both therefore identify the curved smooth model with the fixed star action's smooth quotient. If another smooth quotient is specified, the internally proved quotient diffeomorphism and metric transport apply. No unchanged homeomorphism-only representative loophole remains here.

```text
GENERAL_BOUND_ANALOGUE_STATUS=CLOSED
REGRESSION_SEARCH=NO_ACTUAL_DEFECT_ESTABLISHED
```

## Pass C: hostile models and assumptions

| Attack | Independent assessment |
|---|---|
| Empty E or Q makes positivity vacuous | StarBundle local sections over the nonempty base give E points; quotient surjectivity gives Q points. Canonical construction supplies an actual quotient. |
| Arbitrary charted structure or pathological target topology | Theorems require an IsManifold instance; smooth descent plus the canonical quotient forces a genuine smooth equivalence. The target cannot escape merely by sharing the underlying set or topology. |
| D.ρ equality hides wrong clutching or exotic class | Equality is sufficient for the norm estimate. Identification/class information is separately tied to fixed B and a smooth quotient p; no arbitrary-D homeomorphism class premise remains. |
| RW asks too much or is vacuous | Universal fixed-representation RW is broader than the single application but follows from the general compact smooth gluing theorem; each canonical model has explicit RWData. Model dimensions 8 and 10 are appropriate. |
| Representation/pole/index mismatch | rep8 uses R⊕H⊕H and fixed (1,0,0); rep10 uses R³⊕H⊕H with pole in the real axis of the last H. Quaternion conjugation fixes that pole; base actions match published equations. m=7/9 gives quotient dimensions 8/10 and total dimensions 11/13. |
| A metric exists but not strict sectional positivity | HasPosCurvMetric stores a C∞ symmetric positive-definite metric and a strict inequality on every independent tangent pair. Transport proves sectional curvature equality and independent-pair preservation. |
| Imported Rep relation is arbitrary | True and openly documented: the paper interpretation is supplied by KM/smooth class semantics. The repaired bridge proves curvature on the same Q with Rep Q g and needs no unjustified Rep invariance axiom. Product/round satisfiability is not exotic construction. |
| Orientation or generator lost | Existential orientation in Rep permits hneg on the same smooth manifold and metric. Sperança need not fix which of the two oriented order-three generators is chosen. |
| False Corollary C converse smuggled in | Dimension 10 PSC→α=0 restricts to {0,2,4}; round zero and ±g supply SEC there. No external PSC existence converse is assumed. Dimension 8 zero and the nonzero class exhaust Z/2. |

No model satisfying the actual repaired assumptions and falsifying their formal geometric conclusion was identified. The paper-level exotic interpretation remains conditional on the explicit external inputs; a freely reinterpreted arbitrary Rep is not that interpretation.

## Trust and declaration regression

Source inventory adds 16 named declarations, removes none, and changes only the expected six types/proofs. Independent elaborated environments change exactly the same six dependency sets, with no kind change. The 65 raw added constants comprise those 16 and 49 generated auxiliaries/structure constants under IsSmoothStarQuotient, its diffeomorph, and pullbackForm. Both final geometric Corollary C declarations are unchanged in all inspected fingerprints and dependencies.

The 11 new direct audit targets are isSymm_pullbackForm, isPosDef_pullbackForm, mpullback_symm_apply_self, isContMDiffMetricSection_pullbackForm, HasPosCurvMetric.of_diffeomorph, isSmoothStarQuotient_starQuotMap, lift_comp, diffeomorph, diffeomorph_comp, polarModelA, polarModelB (with their source namespaces).

Actual exported dependency paths from audited theoremA cover the other five:

| Helper | Audited path |
|---|---|
| StarBundle.IsSmoothStarQuotient | theoremA → IsSmoothStarQuotient |
| IsSmoothStarQuotient.lift | theoremA → diffeomorph → lift |
| pullbackForm | theoremA → HasPosCurvMetric.of_diffeomorph → pullbackForm |
| pullbackForm_apply | theoremA → HasPosCurvMetric.of_diffeomorph → isSymm_pullbackForm → pullbackForm_apply |
| infty_ne_zero_ω | theoremA → HasPosCurvMetric.of_diffeomorph → infty_ne_zero_ω |

```text
RC3_NEW_PROJECT_AXIOMS=0
RC3_NEW_TRUST_ESCAPES=0
RC3_UNAUDITED_LOAD_BEARING_DECLARATIONS=0
AUDITED=785
AUDIT_DISTINCT=785
NONSTANDARD=0
```

## Lighter overall completeness pass

| Paper item | Rechecked interpretation |
|---|---|
| Theorems A/B | Canonical polar metric → actual smooth quotient via proved diffeomorphism; faithful modulo RW and special-bundle input. |
| Corollary C | Same group/Rep/Hitchin/orientation interfaces; repaired SEC bridge now supplies the required class legitimately. |
| thm:HLYgeneral | Smooth polar quotient, actual northern/southern RWData and positive sectional curvature, conditional on RW. Upstream geometry unchanged. |
| prop:polar | Smooth equivariant bundle diffeomorphism remains intact; repaired wrapper preserves the needed smooth quotient consequence. |
| lem:attaching | Smooth disk/collar identification established by AttachingDiffeo and diskGluing_unique in addition to topological descriptions. |
| lem:K | Fixed-representation closed-unit-ball bound; still supplies the canonical model's curvature hypothesis. |
| rem:general_bound | Same finite-bound geometry, now smoothly connected to fixed bundle quotient. |
| HLY Prop.3.1 | Existing intrinsic connection-metric estimates and frame/gauge regularity unchanged; smaller algebraic Λ threshold remains a documented strengthening, not an extra input. |
| DHZ Prop.5.1 | Smooth β, arbitrary orthogonal representation and exact Jβ attaching remain; basic RWData has sufficient semidefinite seam, separate StrictCompat proves strict seam. |

Primary comparisons revisited [HLY Prop.3.1](https://arxiv.org/pdf/2609.29426v1), [DHZ Prop.5.1](https://arxiv.org/pdf/2609.32680v1), and [RW Theorem A(i), k=1](https://arxiv.org/pdf/2308.06996v2). No repair-induced change in their previously accepted mathematical interpretation was found. This pass detects regressions; it does not claim a new exhaustive derivation of every unchanged curvature estimate.

## Reconciliation

Pass A's repair closure, Pass B's repository-wide interface review, Pass C's hostile headline checks, and independent dynamic trust results agree. No candidate mathematical repair was made. Remaining limits are openly external mathematics, warm Mathlib cache, scanner coverage limitations and non-exhaustive semantic review; none is a new severity-classified defect.
