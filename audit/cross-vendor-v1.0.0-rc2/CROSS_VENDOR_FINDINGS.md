# Cross-vendor findings

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


## F01 — smooth-class bridge assumes an invalid invariance principle

**CLAIM:** The hypotheses advertised as Sperança's input in the geometric headline bridges are substantially stronger than the published smooth identification. For the intended smooth-class representation relation and nonzero exotic class they cannot be supplied.

**SEVERITY:** BLOCKING.

**EXACT SOURCE LOCATION:** `ExoticSpheres8And10/Main/CorollaryC.lean:103–115`, especially 109–110; dimension-eight counterpart 118–130, especially 124–125. `RepRel`, `SECc`, `PSCc`: 46–60. `ExoticSpheres8And10/Main/TheoremsAB.lean`, statements `theoremA` and `theoremB`, retain a homeomorphism of orbit spaces. The smooth canonical quotient universal property is separately present in `StarBundles/Equivariant.lean` (`contMDiff_iff_comp_starQuotMap`); this finding does not allege that all smooth quotient machinery is missing.

**LEAN DECLARATIONS:** `SECc_of_theoremA`, `SECc_of_theoremB`, `theoremA`, `theoremB`, `corollaryC_dim8_geom`, `corollaryC_dim10_geom`, `StarRep.polarOf`, `sigmaV_eq_J`.

**PAPER LOCATION:** [GG] §§2.4, 3.1, 5.1, 5.3, Theorems A/B and Corollary C; [Sperança Theorem 1](https://arxiv.org/pdf/1010.6039), p.4; [Kervaire–Milnor](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/kervaire-milnor.pdf), original pp.504–505, distinguishes smooth classes from underlying topological spheres. Sperança identifies specific smooth quotients **diffeomorphically**, not every smooth polar manifold homeomorphic to their underlying orbit spaces.

**DEPENDENCY TRACE:** `StarBundle.prop_polar` → `theoremA/B` (existential polar model, fixed representation, orbit-space homeomorphism, conditional positive curvature) → `SECc_of_theoremA/B` (apply `hSp` to obtain `Rep (QuotSpace D) g`) → `corollaryC_dim8_geom` / `corollaryC_dim10_geom` via their `hSg` hypotheses. Curvature construction itself goes through `lem_K`, `hly_general`, `exists_rwData`, `RWGluing`.

**EXACT HYPOTHESIS:** dimension ten, after installing `rep10.factVs 9`:

```lean
∀ D : PolarData (m := 9) e10, D.ρ = rep10.ρ →
  Nonempty (Quotient (EquivSections.starSetoid B) ≃ₜ QuotSpace D) →
  Rep (QuotSpace D) g
```

Dimension eight substitutes `m := 7`, `e8`, `rep8`. This quantifies over all such `D`, not just the canonically constructed smooth normal form. No condition preserves the smooth structure of the actual star quotient.

**INDEPENDENT DERIVATION / COUNTERARGUMENT:** Choose the constant clutching map `β(y)=1` for the fixed orthogonal representation. It is smooth and conjugation equivariant. `R.polarOf β` has that representation; its attaching map is `ρ(β(y))⁻¹ y = y`, as explicitly expressed by `sigmaV_eq_J`. Gluing two standard smooth disks by this identity gives the standard smooth sphere. The orbit space of the actual exotic sphere is homeomorphic to the standard sphere. Thus `hSp` applies to this unrelated trivial-clutching polar model and forces its standard smooth sphere to represent the nonzero exotic `g`. For the intended Kervaire–Milnor relation this is false: the standard sphere represents zero, even after forgetting orientation up to sign. Nonzero exotic classes cannot become zero by orientation reversal. The counterargument uses smooth disk gluing and the definition of an exotic sphere; it does not assume that arbitrary homeomorphisms are smooth.

**WHY IT MATTERS:** A kernel-checked implication from this stronger antecedent does not establish the advertised exotic-sphere existence modulo the five published inputs. The arbitrary `RepRel` accepts misleading models: the repository's own `corollaryC_dim10_geom_satisfiable` assigns all even classes to the round standard sphere (lines 134–156). That demonstrates consistency of the abstract predicates, not fidelity to smooth homotopy-sphere classification. Likewise `SECc` expresses one representative with curvature; interpretation as every representative requires legitimate smooth-class identification and diffeomorphism transport.

**MINIMAL REPRODUCTION:** Inspect the quantified types at the locations above; substitute constant-one `β` into `StarRep.polarOf` and `sigmaV_eq_J`; use the two-disk standard sphere and the topological homeomorphism defining exoticity. The scratch-only [`ConstantClutchingProbe.lean`](ConstantClutchingProbe.lean) (published alongside this report) was executed successfully on an independent compute node: `auditConstantRepresentation` and `auditConstantAttaching` establish the fixed representation and identity attaching map. Both footprints contain only propext, Classical.choice and Quot.sound; run exit 0, 5.02s. Identity disk gluing as the standard smooth sphere and the topological equivalence of exotic spheres remain independent mathematical parts of the counterargument. No Lean contradiction is claimed for an arbitrary, unconstrained `RepRel`.

**CONFIDENCE:** High. What would change the finding: a frozen theorem interface tying the representative to the canonical smooth quotient, together with an explicit derivation of its external hypothesis from Sperança's published diffeomorphism. The existing canonical smooth quotient lemmas alone do not imply the universally quantified `hSp` above. No repair was attempted.

## F02 — stale citation version

**SEVERITY:** MINOR.

`CITATION.cff:5` specifies `version: "1.0.0-rc1"` in the immutable `v1.0.0-rc2-audit-source` release candidate. This gives readers the wrong release-candidate identifier. It does not affect Lean proof validity. Confidence: high.

## Notes, not defects

- The axiom parser does not enforce 774 entries or distinctness. Independent enumeration confirms **774 entries and 774 distinct declarations** in this candidate. Probe inputs containing one allowed entry or duplicated allowed entries both pass; `sorryAx` fails. Those probes do not prove a defect in the present list.
- HLY's published Λ threshold contains an additional `+4`; the Lean global theorem uses the smaller threshold. That is a strengthening, requiring its independent algebraic proof, rather than a quotation of the published proposition. It does not add an external input.
- The basic DHZ package states semidefinite rather than strictly positive boundary sum, sufficient for RW; separate `Boundary/StrictCompat` machinery proves strict positivity. No missing strictness finding is asserted.
- Scholarly creator/author fields name Fernando alone; Claude is credited as assistance. A Git commit trailer uses `Co-Authored-By: Claude Opus 5.5`, which is recorded as Git assistance credit, not treated as a bibliographic author listing. Schema-required software metadata is consistent with a Lean formalisation.
- Initial build failure before elaboration was an infrastructure limitation, not evidence that candidate proofs fail. The subsequent full check and standalone root build passed; independent parsing verified 774 distinct standard-only footprints. Mathlib cache artifacts were already available on the build node, and a no-cache bootstrap was not reproduced.

## Serious risks investigated and cleared at source-inspection level

No listed trust escape in independently scanned repository Lean code; no hidden topology conclusion in `StarBundle` or curvature conclusion in `PolarData`; no arbitrary quotient collapse in `starSetoid`; intended representation dimensions and fixed axes; action bound on the whole closed unit ball; canonical smooth normal-form quotient; actual smooth attaching diffeomorphisms; HLY frame/trivialisation invariance and compact boundary models; correct finite-group deduction; positive sectional implies positive scalar; genuine round-sphere metric; O'Neill coefficient and curvature signs; positive/nondegenerate metric hypotheses before inverse metrics and horizontal decompositions. These combine source inspection with successful build and selected recursive axiom checks; they do not claim an exhaustive independent verification of every mathematical definition.

## Final frozen-source verification

Final candidate `git status --porcelain`: empty; HEAD `ad7a77f4b6619cd160090095211fbc001939a540`; tree `7424f98ad372e2b6f12dd345d86c92975ebc3ffc`; `git diff --check`: exit 0. Independent comparison of all 217 tracked files to initial SHA-256 fingerprints:0 byte mismatches. The built snapshot on the compute node separately matched all 217 original file hashes and all 9 frozen dependency revisions, exit 0. Evidence: (raw audit record, kept privately). Candidate remained frozen; reports and scratch evidence are outside it. No commits or pushes.
