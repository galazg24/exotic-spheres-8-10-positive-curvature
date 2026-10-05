# Independent paper-to-Lean correspondence

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


Paper-derived map was constructed before consulting `docs/correspondence.md` and `docs/targets.md`. The first attempt to persist pass notes used an incorrect relative destination and failed without creating a candidate file; notes were saved after those documents were consulted. This timing is disclosed. No Claude audit verdict or reasoning report was consulted. The three passes have separate evidence notes (raw audit record, kept privately).

Sources: [GG v2](https://arxiv.org/pdf/2609.38126v2), [HLY v1](https://arxiv.org/pdf/2609.29426v1), [DHZ v1](https://arxiv.org/pdf/2609.32680v1), [Reiser–Wraith v2](https://arxiv.org/pdf/2308.06996v2), [Sperança preprint](https://arxiv.org/pdf/1010.6039), [Kervaire–Milnor scan](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/kervaire-milnor.pdf), [Hitchin, Harmonic Spinors](https://users.math.msu.edu/users/parker/GT/Harmonic%20Spinors.pdf). Downloaded readable texts are kept with the raw audit record. The KM PDF is scanned; independent rendered inspection of original p.504 verifies orders2 and6 in dimensions8 and10. Theorem1.1 gives abelianness, and a finite abelian group of order6 is cyclic. Original p.505 distinguishes homeomorphism from diffeomorphism; Lemma2.1 identifies the standard sphere as group identity. Hitchin was read through the web PDF reader after the direct download returned HTML; relevant discussion occurs on original pp.41–46. Sperança's preprint was used, not independently the final journal version.

| Paper item | Lean route | Classification and fidelity |
|---|---|---|
| Theorem A | `Main/TheoremsAB.theoremA`, `Main/CorollaryC.SECc_of_theoremA` | PARTIAL. Smooth 8-dimensional positive-curvature polar model is conditionally constructed, but transfer to the actual nonzero smooth class uses invalid stronger `hSp` (F01). |
| Theorem B | `theoremB`, `SECc_of_theoremB` | PARTIAL for the same reason in dimension 10. Does not itself identify either oriented order-three class. |
| Corollary C | `CorollaryCLogic`, `corollaryC_dim8_geom`, `corollaryC_dim10_geom` | PARTIAL. Conditional finite-group deduction is correct; substantive geometric class input and every-smooth-representative interpretation remain unsupported by the advertised bridges. Affects A/B/C. |
| `prop:polar`, §3.1 | `StarBundle.prop_polar`, `EquivSections`, `normalFormDiffeo`, canonical quotient universal property | FULLY FORMALISED. Smooth principal- and star-equivariant diffeomorphism over the sphere. Complete route uses invariant connection, smooth radial transport and compatible equivariant sections; intermediate skeleton modules alone are not the final proof. |
| `lem:attaching`, §2.4 | `lem_attaching_1`, `lem_attaching_3`, `sigmaV`, `DiskGluingModel`, `diskGluing_unique` | FULLY FORMALISED. Smooth disk charts and attaching diffeomorphism; inverse uses conjugation equivariance. Smooth category is preserved in this construction. |
| `lem:K`, §5.2 | `Main/Representations.lem_K` specialized to both representation models, action-field bounds | FORMALISED BY AN EQUIVALENT OR STRONGER RESULT. Closed unit-ball bound ≤2 includes unit sphere. Real+quaternion 8-model and imaginary-quaternion+quaternion+quaternion 10-model match fixed axes and dimensions. |
| `thm:HLYgeneral`, §4.1 | `hly_general`, `hly_general_L`, `exists_rwData_L` | FULLY FORMALISED conditional on RW. All smooth orthogonal representations satisfying the action bound, smooth conjugation-equivariant clutching, actual smooth quotient, positive north/south fillings and matching seam. Conditional metric existence is not unconditional RW proof. |
| `rem:general_bound`, §4.4 | `exists_K_bound`, `hly_general_L`, `dhz_prop51` | FORMALISED BY AN EQUIVALENT OR STRONGER RESULT. Finite operator-norm bound L replaces 2; profile parameters adjusted. |
| HLY Proposition 3.1, §4.2 | `prop31_pointwise`, `prop31_at_P`, `hly_prop31_global`, `hly_prop31_global_intrinsic` | FORMALISED BY AN EQUIVALENT OR STRONGER RESULT. Intrinsic norms are frame and gauge invariant; smaller Λ threshold than printed +4. Compact base possibly boundary; local models respect tangent/model-with-corners structures. |
| DHZ Proposition 5.1 | `Curvature/DHZ.dhz_prop51`, strict compatibility machinery | FORMALISED BY AN EQUIVALENT OR STRONGER RESULT for the curvature construction needed by GG. Arbitrary orthogonal representation and smooth conjugation-equivariant β. Basic statement gives semidefinite seam, separate result strict seam; exponential profile differs from DHZ's implicit polynomial profile. |
| sec>0⇒scalar>0 | `HasPosCurvMetric.hasPosScalMetric`, `SECc_PSCc` | FULLY FORMALISED for dimension≥2. Scalar is frame trace of Rm; independent off-diagonal planes positive, frames exist. |
| round sphere sec>0 | `hasPosCurvMetric_sphere` | FULLY FORMALISED: smooth pullback metric under inclusion, stereographic conformal calculation, both poles covered. |
| RW gluing | `RWGluing` | EXPLICIT EXTERNAL HYPOTHESIS. Semidefinite outward SFF sum; consistent with RW inward normal sign convention. |
| Sp exotic quotient | `StarBundle` parameter + `hSp` in geometric bridges | EXPLICIT EXTERNAL HYPOTHESIS **with incorrect strength**: F01. |
| KM classification | `Θ ≃+ ZMod 2/6`, arbitrary `RepRel`, standard zero | EXPLICIT EXTERNAL HYPOTHESIS. Meaningful smooth representation relation is not axiomatized by `RepRel`. |
| Hitchin obstruction | `α : Θ →+ ZMod 2`, `α ≠ 0`, `PSCc Rep x → α x = 0` | EXPLICIT EXTERNAL HYPOTHESIS. Intended spin homotopy spheres; arbitrary Rep does not enforce compactness/spin. |
| Orientation reversal | `Rep M x → Rep M (-x)` | EXPLICIT EXTERNAL HYPOTHESIS. With orientation existentially forgotten, underlying smooth metric is unchanged. |

Global comparison: sphere dimension n=m+1, equatorial V dimension m+1, W dimension m+2, principal total space n+3. Headline choices m=7 and m=9 give n=8 and n=10. Polar θ is smooth (∞), not merely continuous. Metric positivity is strict on independent two-planes. Quotient geometry is smooth in its own canonical atlas, compact and Hausdorff; ordinary topological equivalence is inadequate for its identification with a different smooth structure. Lean existence via classical choice is existential and acceptable; no computational construction is promised by the paper.

## Central mechanism and completeness beyond the target list

The paper-derived route is special smooth S³–S³ bundle → equivariant polar normal form → smooth star quotient model → northern/southern disk metrics → attaching map and common boundary metric → SFF compatibility → RW → sec>0 → correct exotic smooth class → classification/obstruction deduction. The source supports the middle geometric route. Its last smooth-class bridge is PARTIAL/MISSING as a legitimate consequence of published Sp input, affecting all three headlines. This obligation arises from the paper's smooth claim, irrespective of whether `docs/targets.md` lists it.

The north/south route includes the cutoff gauge transformation, regularity at poles, action-field norm, warped profile near the centre, boundary agreement, curvature transport and SFF signs. These are represented in the Connection, HLYModel/Prop31, Northern, Boundary, Gluing and Attaching files; their mere presence is not a line-by-line verification of every estimate. Smooth ODE parameter dependence and averaging are proved in repository Analysis machinery with Mathlib analytic infrastructure, rather than a substantive sixth external mathematics axiom. `Nonempty` packages genuine existence of diffeomorphisms/RW data; it does not add constructions for free.

Sections 1 motivation, descriptions of historical examples, alternative explanations and bibliographical discussion are EXPOSITORY / NON-LOAD-BEARING. The full special bundles and KM/Hitchin results are deliberately external. No independent proof of these is required by the advertised scope. No additional missing load-bearing argument was established from this source inspection apart from the smooth-class transfer. No exhaustive all-declaration correctness claim is made.

The repository's correspondence/targets documents agree on the intended geometric construction but understate the significance of the topological-versus-smooth identification in the headline packaging. The HLY and DHZ route differences are mathematical reformulations; F01 is an additional hypothesis with no valid source instantiation, not such a reformulation.

## Completed verification

The full advertised check and standalone RiemannianGeometry build subsequently passed on an independent compute node. Independently parsed774 entries, 774 distinct declarations, exact name-list match, no nonstandard axioms. The constant-one clutching scratch probe also passed and established representation equality and identity attaching. All FULLY FORMALISED labels concern the inspected Lean statements and their successful kernel checks, not an automatic certification of paper-level statement fidelity. F01 remains. Mathlib dependencies were freshly fetched at their pins; the node reused 8689 existing cache files. No cold-cache online bootstrap claim is made.

## Final frozen-source verification

Final candidate `git status --porcelain`: empty; HEAD `ad7a77f4b6619cd160090095211fbc001939a540`; tree `7424f98ad372e2b6f12dd345d86c92975ebc3ffc`; `git diff --check`: exit 0. Independent comparison of all 217 tracked files to initial SHA-256 fingerprints:0 byte mismatches. The built snapshot on the compute node separately matched all 217 original file hashes and all 9 frozen dependency revisions, exit 0. Evidence: (raw audit record, kept privately). Candidate remained frozen; reports and scratch evidence are outside it. No commits or pushes.
