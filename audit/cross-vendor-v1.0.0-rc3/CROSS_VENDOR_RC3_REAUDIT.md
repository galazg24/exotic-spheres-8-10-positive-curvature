# Independent cross-vendor re-audit of rc3

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

## Disposition and scope

F01 and F02 are closed. No new BLOCKING, MAJOR, MINOR or NOTE finding was established. The repaired candidate supports the advertised geometric conclusions **conditional on the five documented substantive input categories**, with the openly documented standard smooth-quotient background used to interpret Sperança. This is not an unconditional Lean construction of Sperança's exotic bundles, the homotopy-sphere classification, Hitchin's obstruction, or RW gluing.

The formal implications were independently rebuilt and axiom-checked (LEAN_VERIFIED). Their repaired statement fidelity and dependency interfaces were independently reviewed (INDEPENDENTLY_AUDITED within this audit's scope). No HUMAN_VERIFIED label is asserted. Confidence is high in closure of the identified smooth-structure defect; the review is not an exhaustive independent proof of every library definition or every analytic estimate.

## Method: three distinct passes

Pass A reconstructed the old defect and examined the repair, smooth-quotient interface, metric transport, published Sperança theorem and Lee accounting. Pass B began separately from the complete repository topology search, the actual geometric predicate definitions, chart/collar interfaces and audit coverage; it did not clear sites by borrowing Pass A's adjudication. Pass C challenged the headline quantifiers, dimensions, non-vacuity, RW and representation assumptions, class semantics and Corollary C arithmetic. Separate source-review notes were saved before reconciliation with dynamic results. These were sequential passes by the same referee, not three separate agents or three blinded reviewers.

The five specified previous-audit documents were retrieved with git show from the verified handoff commit without merging. They identify F01 as the homeomorphism-only smooth-class bridge and F02 as the rc1 version in rc2's CITATION.cff. No Claude rc3 repair verdict or reasoning report was used. Candidate comments, correspondence, release metadata and commit messages were inspected as claims to verify, not as verdicts.

## Toolchain, checks and trust regression

The build ran on a Linux x86_64 build host. Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6; Lake 5.0.0-src+819816b. All nine dependency revisions match the frozen manifest, including Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

```text
CHECK_SH_EXIT=0
RIEMANNIAN_GEOMETRY_BUILD_EXIT=0
GIT_DIFF_CHECK_EXIT=0
LEXICAL_SCAN=CLEAN
AUDITED=785
AUDIT_DISTINCT=785
NONSTANDARD=0
RC3_NEW_PROJECT_AXIOMS=0
RC3_NEW_TRUST_ESCAPES=0
RC3_UNAUDITED_LOAD_BEARING_DECLARATIONS=0
```

The full check took 12m27.07s; the separate root build 2.73s. Independent parsing matched every footprint to the 785 distinct source targets, with no missing or additional names and axiom union exactly {propext, Classical.choice, Quot.sound}. Inspection of the scripts confirmed that the candidate parser alone does not enforce count or distinctness; the independent check did. A separate scanner stripped nested comments and strings and checked all 202 tracked Lean files for placeholders, native_decide, implemented_by, unsafe, axiom, custom elaboration/macro/extern and listed kernel bypasses; it found no code occurrence.

Eleven new declarations are directly audited. The five other handwritten helpers are reached through audited dependency closures: IsSmoothStarQuotient, lift, pullbackForm, pullbackForm_apply and infty_ne_zero_ω. The exported proof/type constant graph establishes those paths, rather than relying on module imports. Existing curvature naturality is also explicitly audited. Computational limitations and failed orchestration attempts are recorded in the reproducibility report.

## Independent rc2 → rc3 comparison

```text
ADDED=16
REMOVED=0
TYPE_CHANGES=6
DEPENDENCY_CHANGES=6
KIND_CHANGES=0
PROOF_CHANGES=6
UNEXPECTED=0
```

These counts refer to handwritten named declarations. Independent nested-comment-stripped source inventory and separately elaborated rc2/rc3 environments agree on the changed existing declarations:

| Declaration | Change |
|---|---|
| theoremA, theoremB | Curvature on any supplied smooth star quotient, via canonical polar model and diffeomorphism transport |
| SECc_of_theoremA, SECc_of_theoremB | Existential smooth quotient with Rep Q g replaces universal homeomorphism-based class premise |
| remark_general_bound, remark_general_bound_RW | Canonical smooth quotient witness replaces homeomorphism-only packaging |

Raw elaborated project-namespace counts are 5895 → 5960: 65 constants added, none removed; the extra 49 are generated structure constructors/projections/recursors and auxiliaries under the new definitions. Exactly the same six existing constants change structural type/proof fingerprints and dependency sets; no kind changes. Both corollaryC_dim8_geom and corollaryC_dim10_geom retain their source types and elaborated type fingerprints, proof fingerprints, dependencies and kinds. The additional root imports, audit targets and documentation/metadata changes explain the rest of the Git diff.

## F01: reconstruction and adjudication

Rc2 prop_polar provided a smooth principal- and star-equivariant bundle diffeomorphism. Its headline wrappers discarded that witness and retained a fixed representation, a topological orbit-space homeomorphism and conditional curvature on an existential polar model. The old SECc_of_theoremA/B premise then assigned the exotic class to every polar model with the same representation and underlying homeomorphism.

For constant β=1, polarOf retains the representation and sigmaV_eq_J makes the attaching map the identity. Identity gluing of smooth disks is the standard smooth sphere. Exoticity supplies a homeomorphism to that standard sphere, while forbidding a diffeomorphism. Thus the old premise falsely assigned a nonzero exotic smooth class to the standard smooth model. A homeomorphism cannot retain the smooth structure that distinguishes these spheres.

Rc3 instead uses the canonical B.equivSections.polarData, its smooth starQuotMap and the descent property already proved in Equivariant.lean. polarModelA/B retain that quotient witness on the same model on which hly_general builds curvature. theoremA/B compare it smoothly to the supplied quotient and pull back the metric. The SEC bridges put the metric directly on Q satisfying Rep Q g; they do not transfer Rep through a topological equivalence.

Exact repaired sites: StarBundles/SmoothQuotient.lean:58,69,83,86,93,113; Main/TheoremsAB.lean:52,67,85,99; Main/CorollaryC.lean:109,124.

```text
F01_STATUS=CLOSED
F01_CONSTANT_CLUTCHING_COUNTEREXAMPLE=CLOSED
```

The fresh scratch probe reproduces the constant representation and identity attaching map and proves that a repaired premise yields Nonempty(Q ≃ₘ canonical polar quotient). Its contrapositive rejects any target known not to be diffeomorphic to that quotient, including the constant-clutching standard model for a genuinely exotic fixed bundle. All five probe declarations checked with only the standard axioms, exit 0, 5.53s initially and again in the successful retry. The exotic-versus-standard non-diffeomorphism remains the external mathematical classification/exoticity input; no formal contradiction for arbitrary RepRel is claimed.

## Smooth quotient and diffeomorphism verdicts

IsSmoothStarQuotient has precisely four fields: smoothness of p, surjectivity, equality of fibres with star orbits, and smooth descent for maps to smooth manifolds of the same target dimension. The target's IsManifold instance is not an internal field: it is supplied explicitly at all headline use sites and at diffeomorph. The interface therefore meets the required smooth-manifold obligation in those theorems. Its restricted descent quantification is weaker than Lee's full characteristic property and sufficient to compare the two same-dimensional quotient targets.

There is no curvature, class identification, desired-model diffeomorphism or hidden exotic-sphere conclusion in these fields. The canonical inhabitant is obtained from existing quotient/normal-form proofs independently of any curvature conclusion. Surjectivity and the fixed bundle's local sections prevent an empty-target escape. Arbitrary alternate atlases or non-Hausdorff targets cannot defeat the headlines: the proved smooth equivalence forces them to have the canonical smooth/topological structure.

The uniqueness proof chooses a representative of each fibre using surjInv, maps it with p', and proves lift(p x)=p' x using the two exact-fibre properties. Reversing the roles gives the inverse. Surjectivity reduces both inverse equations to these commuting equations. Descent applied to the opposing target proves both maps smooth from smoothness of p and p'. Thus the result is an actual C∞ diffeomorphism, not a renamed homeomorphism. Any other map commuting with the projections equals this one by surjectivity; the relevant uniqueness principle follows internally. No Lee 4.31 axiom or hypothesis is used.

Verdicts: IsSmoothStarQuotient ACCEPTED; diffeomorphism uniqueness ACCEPTED. Attempts to construct an unintended smooth quotient with the same topology fail at smooth descent/inverse smoothness unless it is actually diffeomorphic to the canonical model.

## Positive-curvature transport verdict

Geometry/DiffeoTransport.lean:48 defines φ* g at x by g at φ(x) applied to dφ_x in each argument; :56 verifies the formula. Symmetry follows from symmetry of g (:63), and positive definiteness from invertibility of dφ (:66). The inverse tangent-map identity in mpullback_symm_apply_self (:77) follows from the derivative chain rule for φ⁻¹∘φ=id. It pushes vector fields along φ by pulling them back along φ⁻¹, in the correct direction.

The smooth metric-section proof (:94) uses the existing double-frame scalar test and smooth pairing of the pushed fields, then composes back with φ. It establishes C∞ regularity, not just continuity or pointwise existence of a metric. HasPosCurvMetric.of_diffeomorph (:115) uses the actual kernel-checked sectionalCurvatureAt_pullback in Geometry/Naturality.lean:228. That theorem derives Riemann-tensor invariance through naturality of Koszul terms, Levi-Civita connection and curvature, and preserves the Gram denominator. Invertibility maps independent tangent pairs to independent pairs, so the resulting sectional inequalities remain strict. Both metrics' required regularity and positivity hypotheses are supplied. In theoremA/B, φ goes from Q to the curved polar model, so pullback places the metric on Q.

Verdict: positive-curvature transport ACCEPTED; no direction, inverse, definiteness, smoothness or curvature-invariance gap established.

## Sperança fidelity and Lee accounting

The supplied published PAMS PDF, SHA-256 5e5c19e3d36a174ccd68ea78ff059da41b81ce79c5f89bcf593d4da1b6e3c135, was checked directly. Theorem 1, p.3182, supplies the free commuting actions and the required exotic quotient classes. Equations (2.6) and (2.8), p.3185, match the implemented representations after the stated Euclidean coordinate identification; inversion converts the principal left convention to the right convention. Section 3, Corollary 3.5 and the proof of Theorem 1, p.3190, identify differentiable structures through plumbing, not merely homeomorphism. [Published reference](https://doi.org/10.1090/proc/12945).

For its specific bundle, this supplies a genuine smooth quotient Q and Rep Q g. Properness, quotient smooth structure and descent justify the interface. Rc3 asks only for this existential quotient; it does not ask that every homeomorphic manifold have that smooth class, nor import positive curvature as Sperança data. The order-three generator may be either orientation; the downstream argument only needs a nonzero subgroup element and its negative. Verdict: Sperança interface FAITHFUL to the published input, with the documented standard background.

The actual supplied Lee second edition (SHA-256 67802551192afabbf43661c5886db33d5f152bb0cfaf1f422a23f3a004d36066) confirms Cor.21.6 (p.544), Thm21.10 (pp.544–545), Thm4.29 (p.90), and Thm4.31 (pp.90–91), with the accounting claimed in the candidate. The first three are standard unformalised background for interpreting the free smooth action quotient; the relevant fourth principle is proved internally. Verdict: Lee accounting ACCURATE.

```text
EXTERNAL_INPUT_COUNT=5
```

This is justified as five **substantive named input categories**, not five individual hypotheses or a claim that all background mathematics is formalised: RW; Sperança's special bundles/smooth identification; Kervaire–Milnor classification/Rep semantics; Hitchin; orientation reversal. Lee background is disclosed, not smuggled in as a new project axiom. Ordinary manifold/bundle data, bibliographic justification of the input's interpretation, standard background, and the internally proved smooth bridge must remain distinct. The repaired bridge needs no additional independent smooth-class invariance hypothesis on arbitrary homeomorphisms.

## F02, regression, remarks and headlines

CITATION.cff:5 now reads version: "1.0.0-rc3", consistent with this frozen candidate. The preferred paper citation remains the accompanying paper. F02_STATUS=CLOSED.

The entire candidate topology search and geometric dependency review found no new F01 analogue. Detailed occurrence classification is in CROSS_VENDOR_RC3_REGRESSION.md. Both repaired general-bound remarks retain IsSmoothStarQuotient on the same D carrying the metric; positive curvature on any other smooth quotient then follows by the proved diffeomorphism layer. GENERAL_BOUND_ANALOGUE_STATUS=CLOSED. Regression-search verdict: NO ACTUAL DEFECT ESTABLISHED.

Theorem A/B quantifiers require RW for all polar models with the fixed representation. This is broader than the single canonical application needed by the proof, but the general RW gluing theorem justifies each instance on the compact smooth polar models; it is not an additional curvature assumption unsupported by RW. RWData is actually constructed, so this implication does not rely on an empty input type. D.ρ equality is used for the infinitesimal action estimate; smooth quotient identity is separately enforced. Dimensions are 8/10 for Q and 11/13 for E, with the intended fixed axes and representations. No falsifying model satisfying the actual hypotheses was found. Verdicts: Theorem A ACCEPTED MODULO INPUTS; Theorem B ACCEPTED MODULO INPUTS.

Corollary C's dimension-eight argument exhausts Z/2 by zero and the nonzero quotient class. In dimension ten, a nonzero homomorphism Z/6→Z/2 has kernel {0,2,4}; the order-three classes are 2 and 4, which are negatives. Round zero and Sperança's generator with orientation reversal give sectional curvature on that kernel. Hitchin excludes the other classes from positive scalar curvature, and the proved sectional-to-scalar implication yields the iff. Primary KM p.504 and Hitchin pp.41–44 were independently revisited; the finite arithmetic was independently enumerated. Rep remains an openly supplied smooth-class relation with an existential orientation; the repaired SEC bridges preserve the needed class on Q itself. Every smooth representative is handled mathematically by diffeomorphism invariance, now with a proved metric-transport theorem. Abstract satisfiability examples are not evidence constructing exotic spheres. Verdict: Corollary C ACCEPTED MODULO INPUTS.

The lighter completeness review found no regression in prop_polar, smooth lem_attaching, lem_K, hly_general, HLY Prop.3.1 or DHZ Prop.5.1. The geometry remains on actual smooth charts/collars and regular metrics; upstream repair changes only final quotient packaging and transport. Previously documented stronger/equivalent HLY/DHZ formulations remain explicit, including HLY's smaller algebraic threshold and the basic semidefinite seam versus separate strict-compatibility proof. These accepted areas were checked for dependency/interface regression, not reopened as a full independent analytic audit.

## Findings, investigated risks and final disposition

```text
BLOCKING_FINDINGS=0
MAJOR_FINDINGS=0
MINOR_FINDINGS=0
NOTE_FINDINGS=0
```

Investigated and cleared within scope: constant-clutching substitution, hidden curvature or exoticity in quotient fields, missing target smoothness, empty quotient, fake representation equality, wrong dimensions/fixed axis, excessively restricted RW application, loss of orientation/class information, homeomorphism-only metric transfer, metric regularity or inverse differential gaps, Gram/strict-positivity loss, unaudited repair helpers, new project axioms and kernel escapes. Computation/bootstrap/export limitations are operational evidence, not candidate mathematical findings.

What would change this verdict: a concrete countermodel to the repaired hypotheses, an invalid instantiated external input, an overlooked smoothness/curvature defect in a load-bearing dependency, or a mismatch in frozen source/build identities. No candidate source was repaired. The reports are the sole audit-branch changes; supporting raw records and scratch work remain outside candidate and outside the published five-file report directory.

CROSS_VENDOR_RC3_REAUDIT_PASS
