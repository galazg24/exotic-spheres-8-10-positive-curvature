# Cross-vendor audit of the frozen candidate

## Frozen identity

```text
GITHUB_REPOSITORY=https://github.com/galazg24/exotic-spheres-8-10-positive-curvature.git
AUDIT_SOURCE_TAG=v1.0.0-rc2-audit-source
AUDIT_SOURCE_COMMIT=ad7a77f4b6619cd160090095211fbc001939a540
AUDIT_SOURCE_TREE=7424f98ad372e2b6f12dd345d86c92975ebc3ffc
PAPER_ARXIV=2609.38126
```

Fresh authenticated clone, detached tagged commit; HEAD, peeled tag and tree matched exactly; initial worktree clean. Manifest hashes independently computed and matched all eight supplied values:

```text
2da3ea5bd0bb7d84ebb8c441ece8530480b9b54e6c08f7f8990140339053b060  README.md
df6203138cf41bf1698c6fed712ae2df1b541048a887420871c815d1f9510163  audit/PrintAxioms.lean
107777d42bde4d10a45725323e70dc19a4c3f020af93f77d6dc2515cf14dfd1c  CITATION.cff
0de548c5ca956fdc4f85c01767ddaa4409bb2ad7f42be791c121f7d6a67c48aa  .zenodo.json
25b194fb89f7b6771c0a44ff382bbf9feebb6fe9e7b27bbfe31400388aa88f85  NOTICE
392cdc2629b611495ce12b4beac7c26c4bd47e1ee90bce3fa8b8feb6464e1c49  lake-manifest.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
98e657c3375ed7279779568e070be491dc0a89ebd979b6b27630f02297c4bc1a  lakefile.toml
```

## Outcome and scope

Recommended disposition: **do not accept the advertised paper-level headline claims from this frozen formalisation**. F01 is a BLOCKING statement-fidelity defect in the exotic smooth-class bridge. F02 is a MINOR stale citation version. This is not a claim that the paper's mathematical theorems are false, nor that a Lean proof term is invalid. It is a claim that the advertised bridge hypotheses do not follow from the stated published inputs.

No source, theorem, proof, comment, configuration, audit machinery or metadata was repaired. Reports and experiments are outside the pristine candidate. No commit, tag, merge, push or remote mutation was performed. Builds were directed to disposable copies because the advertised script writes an output file. No pre-existing target checkout or separate formalisation/release-tooling repository was inspected or used.

## Method and three independent referee passes

**Referee A — fidelity/completeness:** independently read GG v2, HLY, DHZ, RW and Sperança, inspected Lean interfaces, reconstructed the argument before consulting repository correspondence/targets. Found that the smooth quotient identification is discarded in headline packaging and replaced by a universal homeomorphism premise. Paper-to-Lean comparisons, categories and limitations are in `CROSS_VENDOR_CORRESPONDENCE.md`.

**Referee B — trust/reproducibility:** independently checked Git identity, manifests, toolchain and Mathlib pins, check machinery, lexical escapes, axiom list/parser and static import cones. Confirmed 774 distinct selected declarations and subsequently774 standard-only recursive footprints. Initial fresh build dispatch on an independent compute node failed at dependency DNS; pinned dependency transfer enabled a successful full check/root build. Exact evidence and limitations are in `CROSS_VENDOR_REPRODUCIBILITY.md`.

**Referee C — hostile mathematical referee:** independently recomputed Z/2 and Z/6 arguments, inspected actual structure fields and models, challenged quotient and curvature meaning, and tested the bridge against constant-one clutching. Found the standard smooth sphere counterargument to the alleged Sp input. Abstract satisfiability examples were distinguished from faithful exotic-sphere examples.

These passes were reconciled after their separate investigations. Initial conclusions were formed before reading repository maps; initial note-writing failed due to an incorrect relative destination, so the saved pass notes postdate consultation of those maps. This is disclosed rather than claiming a stronger written blinding procedure. No Claude verdict/review/reasoning report was read. Candidate release claims and commit messages are candidate evidence, not an independent audit verdict.

Audit evidence is source inspection and independent mathematical derivation, with successful Git/hash/lexical commands. The full build on an independent compute node and recursive selected axiom checks completed successfully: LEAN_VERIFIED for the formal statements, assessed separately from paper fidelity. High confidence in F01; no exhaustive absence-of-other-defects claim, since every mathematical definition and every library declaration was not independently reviewed.

## Independently reconstructed external-input census

Inspection before reliance on the README finds five intended **classes** of external inputs. Each class contains multiple substantive hypotheses; five classes is not five individual propositions. There is no established sixth independent published mathematical input, but the Sp class contains an unsupported strengthening (F01), so “modulo exactly these five published results” is not justified.

| Source | Lean interface and exact substantive hypothesis | Headline use and assessment |
|---|---|---|
| RW Theorem A(i), k=1 | `RWGluing I X := RWData I X → HasPosCurvMetric I X`, under `CompactSpace X`. `RWData` stores smooth regular cut, north/south smooth positive-definite metrics, positive sectional curvature, matching boundary restriction, semidefinite outward SFF sum. Headline wrappers assume `∀ D : PolarData ..., RWGluing ... (QuotSpace D)`. | A/B and hence C. Actual model compact, smooth, Hausdorff and finite-dimensional. Outward convention corresponds to RW negative sum with inward normals. Lean asks only existence of a smooth positive metric, less than RW's preservation away from seam; enough for the paper. No proven RW gluing theorem is claimed. |
| Sperança Theorem 1 and special S³–S³ construction | `B : StarBundle (m:=7) rep8 E` or `(m:=9) rep10 E`, smooth total space `IsManifold (IP m) ∞ E`, `T2Space E`; then `hSp : ∀ D, D.ρ = repN.ρ → Nonempty (Quotient (starSetoid B) ≃ₜ QuotSpace D) → Rep (QuotSpace D) g`. Exact types in F01. | A/B/C. Existence and smooth identification of specific special bundles are external; not silently constructed by product examples. The displayed hSp assumes **more** than the cited smooth identification and is false for the intended exotic class when arbitrary homeomorphic polar models are allowed. Auxiliary smooth structures and correct representation/action identification must be provided. |
| Kervaire–Milnor | `[AddCommGroup Θ]`, `eΘ : Θ ≃+ ZMod 2` or `ZMod 6`; `Rep : RepRel n Θ`; `hround : Rep (Sph n) 0`; nonzero `g`, and in dimension10 `eΘ g ∈ zmod6Order3`, `g ≠ 0`. `RepRel n Θ := ∀ M [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M], Θ → Prop`. | C, and the interpretation of A/B as exotic classes. The relation is arbitrary; closedness, homotopy-sphere property and smooth-class invariance are not enforced by its type. A correct semantic interpretation is an external obligation. Group arithmetic itself is proved. KM original p.504 table independently visually checked: orders2 and6; abelianness gives these cyclic groups. Group deductions independently recomputed. |
| Hitchin | `α : Θ →+ ZMod 2`, `hα : α ≠ 0`, `hHitchin : ∀ x, PSCc Rep x → α x = 0`. | Dimension10 C. Nonzero α and PSC obstruction are separate inputs. For actual homotopy spheres spin existence/uniqueness is inherited from topology, but arbitrary Rep does not ensure it; cannot apply Hitchin to arbitrary manifolds satisfying only its Lean type. No converse Hitchin existence theorem is needed: SEC on all kernel classes supplies it. |
| Orientation reversal/negation | `∀ M [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] x, Rep M x → Rep M (-x)`. | B's second order-three class and dimension10 C. Meaningful because Rep forgets choice of orientation; same underlying smooth manifold and metric. Requires correct smooth interpretation, not topological equivalence. |

HLY and DHZ are not additional explicit external propositions in the inspected final curvature route: their needed geometric conclusions are implemented by repository curvature/block/epsilon/frame machinery. Linear ODE transport, Haar averaging, partition-of-unity and normal-form construction are repository proofs over Mathlib analytic infrastructure, not a bare existence hypothesis for the desired geometry. The 774 selected declarations were dynamically checked for recursive axiom dependencies; individual hypotheses remain outside that census.

## Verdicts on statements and completeness

**Statement fidelity:** fails at the final topology-to-smooth-class bridge, F01. Theorems named A/B prove conditional curvature existence on some smooth polar quotient homeomorphic to the star orbit space. That is not by itself positive curvature on the prescribed exotic smooth structure. Existing canonical smooth quotient machinery does not make arbitrary homeomorphisms preserve exotic class.

**Completeness:** the central local/global geometry has a substantial source-level route. The paper-derived obligation to identify the curved smooth model with the specific exotic smooth sphere remains unsupported by the advertised external premise. PARTIAL headline support for A/B/C, despite the successful advertised builds. Repository target coverage cannot settle this omitted semantic obligation.

**Trust/axioms:** static repository scan clean, list 774/774, parser's whitelist sound for recognized axiom footprints but count/coverage not enforced. Dynamic standard-only 774 footprint result independently reproduced and exact list match verified. Ordinary mathematical hypotheses never appear as nonstandard axioms merely because they are false or too strong. Therefore advertised NONSTANDARD=0 would not clear F01.

**Theorem A:** BLOCKING fidelity gap. Dimension8 geometry and action bound match; exotic smooth identification does not.

**Theorem B:** BLOCKING fidelity gap. Dimension10 geometry and representation indices match; order-three class identification does not follow from the bridge as written. Negation argument itself is correct.

**Corollary C:** correct conditional finite-group argument, BLOCKING geometric-class fidelity gap. From Θ8=Z/2, classes0 andg exhaust the group. From Θ10=Z/6, any nonzero homomorphism to Z/2 sends1 to1, so kernel={0,2,4}; classes2 and4 have order3 and are negatives. Hitchin excludes1,3,5 from PSC; SEC supplies0,2,4 and implies PSC. Hence the intended iff follows **if** the actual smooth-class curvature inputs are established. The arbitrary round-sphere Rep model does not establish them.

**HLY bridge:** substantive source-level proof rather than an extra external axiom. Published Prop3.1 concerns compact smooth base possibly boundary, positive base curvature, smooth S³ connection, Ω and DΩ bounds, sufficiently concave φ and r²=εexp(εφ), sufficiently smallε. Lean proves block estimates, uniform ε budget and intrinsic global version, with smaller Λ threshold (omits published +4). Frame and trivialisation invariance are proved; choice of frames justified by local existence. Interval×S³ model establishes a real compact boundary model, although its one-dimensional base sectional premise is vacuous; the closed round cap `CDisk 2 1`×S³ supplies a nonvacuous two-dimensional positively curved base with nonzero connection curvature at every point (`hly_prop31_model_disk`). Abstract examples do not establish exotic-bundle input. The formal package built successfully and selected recursive axiom footprints passed.

**DHZ bridge:** arbitrary smooth orthogonal S³ representation fixing e and smooth conjugation-equivariant β; compactness supplies derivative/operator-norm bound L. Attaching Jβ is exact. North/south metric construction with adjusted parameters gives positive curvature and compatible seam, then RW. Exponential profile is a valid alternative to DHZ's profile. Basic RWDatum semidefinite conclusion is enough for gluing; strict-compatibility theorem separately present. No additional representation restriction or published DHZ assumption was found hidden in the final interface. Formal build and selected recursive axiom checks passed.

**RiemannianGeometry:** inspected load-bearing interfaces in static cones, not every file line by line. LC is constructed from Koszul using symmetric nondegenerate smooth metric; uniqueness and required differentiability are explicit. Rm convention gives positive `Rm(u,v,v,u)` on round sphere. Sectional denominator is positive for independent planes. Pullback/naturality requires invertible derivative, not merely a homeomorphism. Submersion requires derivative surjectivity and horizontal isometry; horizontal/vertical split uses positive metric. A=half vertical bracket, `K_total = K_base − 3‖A‖²/Gram`, consistent with +3/4 bracket correction on the base. Germ congruence is used with eventual equality around the correct point; metrics C² and map C³ hypotheses are present in the inspected O'Neill theorem. SFF `g(∇ν v,w)` with outward normalized gradient matches boundary/RW sign. Mathlib supplies manifold/calculus/vector-bundle infrastructure; repository supplies these curvature interfaces. No actual sign/coercion/positivity defect established, but source inspection is not complete kernel certification.

**Reproducibility:** fresh GitHub source identity reproduced, pins and instructions coherent, independent lexical and Git diff checks succeeded. Initial dependency fetching on the build node failed because of DNS. All nine pinned sources were then freshly fetched on a separate host and transferred to the authorized snapshot. Existing Mathlib cache supplied 8689 files, then the full check passed in 12m27.23s and standalone root build in 2.73s. Probe passed in 5.02s. No-cache online bootstrap on the build node remains unverified; the cached candidate build is reproduced.

**Provenance consistency:** author/creator fields and Lean headers identify Fernando; Claude/Claude Code is assistance; Lean kernel is checker and Tláloc infrastructure. No production role for Codex inferred. NOTICE foundation origin is an internal claim only; prohibited origin repository not inspected. License/header Apache2 consistency found. CFF software type is not a contradiction; stale rc1 version is F02. Git AI coauthor trailer is disclosed separately from scholarly author fields.

## Findings, cleared risks, and disposition

Findings: **1 BLOCKING (F01), 0 MAJOR, 1 MINOR (F02)**. Notes and serious investigated risks are detailed in `CROSS_VENDOR_FINDINGS.md`. Cleared source-level risks include vacuous StarBundle local data, hidden positive curvature in PolarData, setoid collapse, dimension/action mismatch, homeomorphisms in local curvature pullback, scalar implication, round metric, O'Neill sign/coefficient, frame-dependent curvature norms, and group arithmetic. F01 is not cleared by those checks.

Confidence: high for the blocking bridge counterargument and independent finite-group deductions; qualified for exhaustive semantic validity of all definitions; successful kernel checking of the formal statements has been reproduced. A faithful canonical smooth-class bridge derivable from published inputs would change F01; no repair is part of this audit.

The successful build record, the independent footprint enumeration and the probe run record the completed verification (raw audit record, kept privately); the probe source is published as `ConstantClutchingProbe.lean`. Final frozen-tree evidence is recorded below before the terminal verdict. An operational handoff for the compute infrastructure was recorded separately (raw audit record, kept privately). No infrastructure changed and no commits/pushes.


## Final frozen-source verification

Final candidate `git status --porcelain`: empty; HEAD `ad7a77f4b6619cd160090095211fbc001939a540`; tree `7424f98ad372e2b6f12dd345d86c92975ebc3ffc`; `git diff --check`: exit 0. Independent comparison of all 217 tracked files to initial SHA-256 fingerprints:0 byte mismatches. The built snapshot on the compute node separately matched all 217 original file hashes and all 9 frozen dependency revisions, exit 0. Evidence: (raw audit record, kept privately). Candidate remained frozen; reports and scratch evidence are outside it. No commits or pushes.

CROSS_VENDOR_AUDIT_BLOCKED
