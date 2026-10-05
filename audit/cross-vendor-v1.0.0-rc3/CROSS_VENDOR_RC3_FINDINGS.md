# Rc3 re-audit findings and closure evidence

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

## Finding census

```text
BLOCKING_FINDINGS=0
MAJOR_FINDINGS=0
MINOR_FINDINGS=0
NOTE_FINDINGS=0
F01_STATUS=CLOSED
F01_CONSTANT_CLUTCHING_COUNTEREXAMPLE=CLOSED
F02_STATUS=CLOSED
GENERAL_BOUND_ANALOGUE_STATUS=CLOSED
```

No new finding meets BLOCKING, MAJOR, MINOR or NOTE severity. The original rc2 findings remain historically valid for rc2; this report closes them only for the immutable rc3 source identified above. No repair was performed by this referee.

## F01 closure: exact dependency trace

1. StarBundle.prop_polar (StarBundles/Equivariant.lean:249) retains the smooth equivariant bundle normal form.
2. StarBundle.starQuotMap, contMDiff_starQuotMap, starQuotMap_surjective, starQuotMap_eq_iff and contMDiff_iff_comp_starQuotMap (same file:263–305) supply the smooth canonical quotient.
3. isSmoothStarQuotient_starQuotMap (StarBundles/SmoothQuotient.lean:69) packages those independently established properties, without curvature or exoticity.
4. polarModelA/B (Main/TheoremsAB.lean:52,67) retain that package on the polar model and prove conditional positive curvature through norm_KY_le, lem_K and hly_general.
5. IsSmoothStarQuotient.diffeomorph (:93) gives smooth equivalence from any supplied quotient Q of the same fixed action to that polar model.
6. HasPosCurvMetric.of_diffeomorph (Geometry/DiffeoTransport.lean:115) pulls back the metric, with strict sectional positivity from sectionalCurvatureAt_pullback (Geometry/Naturality.lean:228).
7. theoremA/B (Main/TheoremsAB.lean:85,99) conclude curvature on Q; SECc_of_theoremA/B (Main/CorollaryC.lean:124,109) keep the same Q with its supplied Rep Q g.
8. corollaryC_dim8_geom and corollaryC_dim10_geom use that SECc input, standard zero, and the unchanged classification/obstruction/orientation argument.

The new Sperança premise is existential over a genuine smooth quotient map from the fixed E. Its published justification is Theorem 1 on PAMS p.3182 and the differentiable recognition argument in §3, culminating on p.3190, combined with Lee's standard free proper quotient/submersion facts. The old universal premise over merely homeomorphic polar models is gone.

## Counterexample re-adjudication

The archived rc2 probe was retrieved from the verified handoff as evidence, then extended and run against freshly built rc3. Constant β=1 still preserves ρ and yields σ=id; the standard model is therefore still a useful adversarial target. The repair does not make that calculation disappear.

It changes the premise required to use that target: B.IsSmoothStarQuotient p forces a C∞ diffeomorphism to B's canonical polar quotient. If the target is not diffeomorphic to that quotient, no such p can satisfy the repaired premise. The scratch declarations auditRepairedPremiseForcesSmoothModel, auditUnrelatedSmoothModelRejected and auditConstantTargetRejected verify that implication and contrapositive; they do not assume a metric and do not modify the candidate.

```text
'auditConstantRepresentation' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditConstantAttaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditRepairedPremiseForcesSmoothModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditUnrelatedSmoothModelRejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditConstantTargetRejected' depends on axioms: [propext, Classical.choice, Quot.sound]
LEAN_EXIT=0
```

The standard/exotic non-diffeomorphism is supplied by the intended smooth interpretation, not proved by this generic probe. For a product bundle the standard model can be a genuine smooth quotient; that does not make it a quotient of an unrelated exotic fixed bundle. Arbitrary RepRel consistency examples are not counterexamples to the conditional geometric theorem or evidence for exoticity.

Confidence in closure: high. Reopening F01 would require a target not diffeomorphic to the canonical quotient that nevertheless satisfies the actual four quotient fields and target manifold hypotheses, or a demonstrated failure of the metric transport/normal-form dependency. A homeomorphism alone supplies neither.

## F02 closure

The old finding was exactly the version mismatch in CITATION.cff, not a wrong edition of the Sperança reference. Verified rc3 location CITATION.cff:5 is version: "1.0.0-rc3"; SHA-256 4408b4e9d535e8c52ef2ebc9471657f970195bc4b451deaeabc93b5273365d52. Confidence: high. Frozen rc2 metadata was not altered.

## Trust, severity and limitations

785 selected declarations were independently matched and checked, all distinct, no nonstandard axiom. The 11 new direct targets and five helper dependency paths are documented in the regression/reproducibility reports. The target-list parser's lack of count enforcement was compensated for independently; it is a pre-existing limitation, not a new rc3 finding. Standard quotient background and the five substantive input categories remain explicit. No claim of an unconditional proof of the external mathematics or exhaustive semantic verification is made.

Because no BLOCKING or MAJOR finding was established, there is no serious-finding reproduction to list. The counterexample closure probe and exact source trace above provide positive adjudication evidence instead.
