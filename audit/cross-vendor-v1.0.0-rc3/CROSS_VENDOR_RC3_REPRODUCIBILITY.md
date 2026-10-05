# Rc3 re-audit reproducibility and immutable-source record

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

## Workspace and exact identity checks

Workspace: a fresh audit workspace with candidate, reports, scratch and previous-audit directories. It was created fresh; the rc2 audit clone and Claude checkout were not reused. The separate production/tooling repository was not inspected or used.

```sh
git clone https://github.com/galazg24/exotic-spheres-8-10-positive-curvature.git candidate
cd candidate
git fetch --tags --force
git checkout --detach v1.0.0-rc3-audit-source
git status --porcelain
git rev-parse HEAD 'HEAD^{tree}' v1.0.0-rc3-audit-source 'v1.0.0-rc3-audit-source^{}'
git show --no-patch --format=fuller HEAD
git remote -v
git fetch origin <rc2 audit handoff branch>     # raw audit branch, kept privately
git rev-parse origin/<rc2 audit handoff branch>
```

Outputs: empty status; HEAD 95b467a0e0efbc95473ad2c5a918d499a7607fef; tree 8d7805b9b0a4ad5307e611b44b47fc5da9f99239; tag object 21992edc4fb8e80ca32e4a52237bc389c2b4dcde; peeled tag equals HEAD; handoff fde484d6ead04b84b799aa5e5388d9066ce0e857. Origin fetch/push URL is the specified GitHub repository. Author and committer Fernando Galaz-García; commit date 2026-10-05T00:58:07+01:00, subject "docs: cite Sperança from the published PAMS version". Candidate commit credit/claims were not accepted as independent validation.

All five requested previous reports were extracted with git show <handoff>:audit/cross-vendor-v1.0.0-rc2/<file> into previous-audit/. No merge occurred.

## Supplied manifest, independently reproduced

```text
e23d5d51a23b67436b502afe29f204ebf0d6eb3d0295c61f9ce4ae2f4a6152a4  README.md
3ca740a3c192d0c2c87e7c2c648ec6675c1c39184beacac137a991c936ca6a11  audit/PrintAxioms.lean
4408b4e9d535e8c52ef2ebc9471657f970195bc4b451deaeabc93b5273365d52  CITATION.cff
0de548c5ca956fdc4f85c01767ddaa4409bb2ad7f42be791c121f7d6a67c48aa  .zenodo.json
25b194fb89f7b6771c0a44ff382bbf9feebb6fe9e7b27bbfe31400388aa88f85  NOTICE
392cdc2629b611495ce12b4beac7c26c4bd47e1ee90bce3fa8b8feb6464e1c49  lake-manifest.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
98e657c3375ed7279779568e070be491dc0a89ebd979b6b27630f02297c4bc1a  lakefile.toml
68a768422d1cdf1da8c1320e6dbbfd0e985448bf0d4b5bb11e0244fce90c9d14  docs/correspondence.md
09a12e918be73d5844064c8ffd9a6f5e4867086318dcf4b6a3261f8089a54dbc  ExoticSpheres8And10/Main/TheoremsAB.lean
ea29a56ec0c3c04b14545b11a29304b04d7ca087e6bebca53b732eb89cebb21b  ExoticSpheres8And10/Main/CorollaryC.lean
5f989d6d5d06c3ce87d9f6207d14280ad6b56a73630f4c419aae24870de7f5a0  ExoticSpheres8And10/StarBundles/SmoothQuotient.lean
501f53987ee5456e6cbbd10e830757b6317a61c8a2a322a5c909de3434355aca  ExoticSpheres8And10/Geometry/DiffeoTransport.lean
7c3b788108a920dc5bd605aee62981a93d5ccd9df7c9df34d6515c9d9294ff9c  ExoticSpheres8And10/Curvature/RemarkGeneralBound.lean
9ff243ee16919f1610df110903bb9609160f285b91b6015aeb26eba545d46385  ExoticSpheres8And10/Curvature/DHZ.lean
MANIFEST_VERIFICATION=15/15 MATCH
```

The initial SHA-256 census covers all 219 tracked files, not just these 15. Final recomputation found zero byte mismatches. Initial and final git diff --check in the actual clone exit 0. Candidate status stays clean and HEAD/tree retain the frozen identities.

## Environment and build isolation

Audit-host tools: Git 2.43.0; Python 3.12.3; Poppler pdftotext 24.02.0. Build host: Linux x86_64. Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6); Lake 5.0.0-src+819816b.

The check script writes audit/axioms.out and Lake writes build artifacts. Therefore sh scripts/check.sh and lake build RiemannianGeometry were executed on a disposable frozen-source snapshot, never in candidate/. A literal run in candidate/ would violate the task's stronger immutability instruction.

Snapshot: a fresh copy of the frozen clone on the build node.

```text
FILES=219
CONTENT_HASH=c57888741239287964af1f724be1549d2ed7e802693481af7cc02d9790670182
PACKAGES=NOT shared
RETENTION=skipped
```

No other campaign package tree or build was borrowed. All nine dependency repositories were freshly fetched on a separate host at the manifest's exact revisions using git -c http.version=HTTP/1.1 fetch --depth 1 <url> <revision> and detached checkout. The archive was transferred to the build node with SHA-256 verification; archive bf99f629e97d… (156241920 bytes). Matching pre-existing Mathlib cache was reused on the build node; no full Mathlib source rebuild or cold online bootstrap is claimed.

The build job used set -e and waited for exclusive use of the node. No peer job was cancelled or modified. The actual successful commands within the snapshot were:

```sh
tar -xf fresh-packages.tar -C .lake/packages
/usr/bin/time -v lake exe cache get
/usr/bin/time -v sh scripts/check.sh
/usr/bin/time -v lake build RiemannianGeometry
```

| Command | Exit | Wall time | Maximum RSS KiB |
|---|---:|---:|---:|
| lake exe cache get | 0 | 24.71s | 995804 |
| sh scripts/check.sh | 0 | 12m27.07s | 6928228 |
| lake build RiemannianGeometry | 0 | 2.73s | 2972036 |

Check stdout ends with successful build (8906 jobs), LEXICAL_SCAN=CLEAN and AUDITED=785 NONSTANDARD=0. The root reports successful build (2579 jobs). Routine deprecation/style/unused-variable warnings are preserved; no placeholder/kernel-bypass warning was used to justify completion.

## Failures and exact interpretation

1. The initial build job failed before candidate elaboration: GitHub DNS failure during Mathlib clone; Lake exit 1. Initial collection was also sandbox-refused, then explicitly escalated and collected. No network configuration was changed.
2. The retry job completed all three commands above with exit 0, then ended 129 because the audit runner appended git diff --check in a snapshot without Git metadata. That was an audit orchestration error. It does not mean check.sh or the root build failed, and the job is not reported as overall exit 0. git diff --check was independently run successfully in the actual pristine clone.
3. The probe/export job checked the five Lean probe declarations (exit 0, 5.53s), exported rc3's environment and rebuilt a fresh rc2 source reconstruction (exit 0, 43.72s), but terminated 143 during rc2's full-expression export. The first export wrote hundreds of MiB of expression representations; the precise cause of termination is not established. It was not a candidate proof failure. Structural-fingerprint/dependency export replaced unbounded expression text; a retry completed exit 0. An early scratch exporter API check had an ambiguous liftIO elaboration error; that scratch code was corrected before the successful export. No candidate change was involved.

## Axiom and lexical verification

The source target list has 785 entries and 785 distinct names. check_axioms.py accepts only propext, Classical.choice, Quot.sound in recognized footprints, but does not enforce cardinality/uniqueness. Independent line-anchored parsing of actual output required exact equality with the source target set:

```text
AUDITED=785
AUDIT_DISTINCT=785
NONSTANDARD=0
MISSING_TARGETS=0
UNEXPECTED_TARGETS=0
AXIOM_UNION={Classical.choice, Quot.sound, propext}
```

These outputs were separately collected by a read-only extraction job, exit 0, which shared the node with the independent environment job; it did not launch another build.

The independent lexical scanner strips nested block comments, line comments and string literals, then scans all 202 tracked Lean files. It includes sorry, admit, native_decide, implemented_by, unsafe, axiom, extern, elab, run_elab, macro and debug.skipKernelTC/proofAsSorry/byAsSorry/terminalTacticsAsSorry. No code hits. This repository-source scan and the selected recursive footprint check are complementary; neither proves the truth of ordinary mathematical hypotheses or independently rebuilds all Mathlib infrastructure.

## Declaration comparison and coverage reproduction

The rc2 source reconstruction came from git archive ad7a77f4b6619cd160090095211fbc001939a540 in the fresh clone, extracted into an audit-owned subdirectory of the assigned snapshot. It reused only audit-built cache artifacts, then Lake rebuilt the changed rc2 modules before importing its root. The repaired snapshot's source files were not replaced. Both environments were exported independently using Lean's ConstantInfo.type, value? true and getUsedConstantsAsSet. Kind, structural type/proof hashes and dependency name sets were compared; source inventory independently located the 16 new handwritten definitions and six changed statements/proofs. Structural hashes are fingerprints, not a cryptographic proof of expression equality; direct source comparison also confirms the unchanged Corollary C statements.

```text
HANDWRITTEN_ADDED=16
HANDWRITTEN_REMOVED=0
ELABORATED_PROJECT_CONSTANTS_RC2=5895
ELABORATED_PROJECT_CONSTANTS_RC3=5960
ELABORATED_ADDED=65
ELABORATED_REMOVED=0
GENERATED_ADDITIONS=49
TYPE_CHANGES=6
DEPENDENCY_CHANGES=6
PROOF_CHANGES=6
KIND_CHANGES=0
UNEXPECTED_MATHEMATICAL_CHANGES=0
```

The changed existing names are theoremA, theoremB, SECc_of_theoremA, SECc_of_theoremB, remark_general_bound and remark_general_bound_RW. Both corollaryC_dim8_geom and corollaryC_dim10_geom have unchanged source and type/proof/dependency/kind fingerprints. Generated additions are confined to the new quotient structure, its diffeomorphism and pullbackForm auxiliaries. No added project-namespace constant has kind axiom.

All five helpers without direct #print axioms targets are in audited theoremA's exported dependency closure; the paths are enumerated in the regression report. The new direct list adds exactly 11 targets. Thus RC3_NEW_PROJECT_AXIOMS=0, RC3_NEW_TRUST_ESCAPES=0, RC3_UNAUDITED_LOAD_BEARING_DECLARATIONS=0 for the repair surface.

## Constant-clutching probe

Commands in the freshly built snapshot:

```sh
lake env lean audit-probes/ConstantClutchingProbe.lean
python3 audit-probes/VerifyFrozen.py
```

The first two probe declarations are the archived constant-clutching test retrieved with git show from the rc2 handoff, rerun against rc3. The new rejection implication is:

```lean
theorem auditRepairedPremiseForcesSmoothModel (p : E → Q)
    (hp : B.IsSmoothStarQuotient p) :
    Nonempty (Q ≃ₘ^∞⟮𝓡 (m + 1), 𝓡 (m + 1)⟯
      QuotSpace B.equivSections.polarData) :=
  ⟨hp.diffeomorph B.isSmoothStarQuotient_starQuotMap⟩
```

With the actual manifold/bundle/dimension instances from the candidate, the contrapositive rejects any Q not diffeomorphic to that canonical quotient; specialization takes Q=QuotSpace(auditConstantPolar R). The five #print axioms outputs contain only the three standard axioms. This tests the repaired interface's exclusion mechanism; standard/exotic non-diffeomorphism is an external mathematical interpretation, not silently added as a proved classification theorem.

## Sources and audit records

Local supplied source hashes:

```text
5e5c19e3d36a174ccd68ea78ff059da41b81ce79c5f89bcf593d4da1b6e3c135  speranca-published.pdf
67802551192afabbf43661c5886db33d5f152bb0cfaf1f422a23f3a004d36066  lee_smooth_manifolds.pdf
```

The actual PAMS edition and Lee second edition were read via pdftotext -layout; exact original pages are identified in the main report. Internet primary sources were also revisited for GG v2, HLY, DHZ, RW, KM and Hitchin. The KM scan's PDF page numbering differs from printed pagination: PDF page 2 contains printed p.504. An initial render of PDF page 15 showed printed p.517; it was corrected before the table conclusion. Independently observed orders are 2 in dimension 8 and 6 in dimension 10. Independent finite enumeration gives kernel {0,2,4}, nonzero order-three classes {2,4} and negatives 2↔4.

Full exact commands, stdout/stderr, exit files and build telemetry are retained in the raw audit record (kept privately), together with the snapshot and transfer logs, static-audit results, source-declaration and kernel-constant deltas, environment exports, independent axiom and helper-coverage results, frozen-verification records and the three pass notes. Scratch includes the independent scanner, environment exporter, probe, source fingerprint verifier and fresh dependency/rc2 archives. These are audit artifacts, not candidate changes. The published handoff contains the requested four reports and report-hash manifest only.

## Final immutability, local commits and publication scope

Final candidate git status --porcelain is empty; HEAD and tree are the exact frozen rc3 identities; all 219 tracked SHA-256 values match the initial census. The built rc3 snapshot separately matched all 219 source files and all nine dependency pins both before and after probes/reconstruction. No frozen tag or candidate branch was changed.

Coordination records on the compute infrastructure were committed locally and not pushed (raw audit record, kept privately). The initial working directory is not a Git repository; the fresh candidate began clean. No old audit checkout was used. Remaining local evidence and scratch files are intentionally outside the pristine candidate and published report worktree.

The separate audit-report worktree is based exactly on the rc3 commit. Its commit message is "audit: independent cross-vendor re-audit of rc3"; only audit/cross-vendor-v1.0.0-rc3/ is staged. Only the audit-report branch (kept privately) is authorised for push. The resulting report commit and remote verification are supplied in the final handoff response, avoiding a self-referential hash inside these hashed reports.
