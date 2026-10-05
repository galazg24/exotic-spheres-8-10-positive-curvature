# Reproducibility and formal trust

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


## Commands and environment

Fresh `git clone` from the specified authenticated GitHub URL, `git fetch --tags --force`, detached checkout of the tag; exact requested identity commands and `git diff --check` recorded in the raw audit record (kept privately). Candidate `git diff --check` succeeded. Exact environment and outputs, rather than inferred machine facts, are retained in the raw audit record.

Lean pin `leanprover/lean4:v4.33.1`; Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Lake `5.0.0-src+819816b`. Mathlib manifest pin `0df444a360eaa60ab8c11dca51a86af692955474`; transitive Git revisions recorded in the frozen manifest. No dependency on Claude sessions, Tláloc files, uncommitted candidate files or the prohibited separate tooling repository was found in build configuration. CI installs elan, downloads Mathlib cache, then runs the check script. The standalone RiemannianGeometry root requires its separate target build.

A disposable local copy attempted `timeout --kill-after=5s 45s sh scripts/check.sh`; exit 124 while fetching Mathlib, before Lean checks. No prolonged local build was run. Full computation on an independent compute node was subsequently expressly authorised; no other job on that node was touched.

A fresh build snapshot received the 217 tracked files, snapshot content hash `0748a3568c5559c156135b092d6957f13aded13ad3999a6643a95f75620a8a1a`. No packages borrowed from another campaign; no retention sweep.

The authorized build job used `set -e` and intended commands:

```sh
uname -a
lscpu
free -h
df -h .
lean --version
lake --version
/usr/bin/time -v lake exe cache get
git -C .lake/packages/mathlib rev-parse HEAD
/usr/bin/time -v sh scripts/check.sh
/usr/bin/time -v lake build RiemannianGeometry
```

The first build job failed at cache dependency clone: `Could not resolve host: github.com`, Git exit 128, Lake exit 1, elapsed0.07s, peak RSS103536KiB. Neither advertised check nor RiemannianGeometry build was reached. The failure record, stdout, stderr, resource data and exit status were collected and preserved (raw audit record, kept privately); dispatch and snapshot logs are separate. Follow-up attempts first timed out on a separate host; one overlapping fetch encountered a lock conflict in audit-owned scratch. A separate fresh shallow HTTP/1.1 fetch succeeded. All nine pinned dependency repositories were freshly fetched, detached at their exact revisions, archived and transferred to the build node with SHA-256 verification. No pre-existing target or tooling checkout was used. Do not read exit 0 of a dispatcher as proof success: actual job status was checked.

## Check implementation and independent checks

`scripts/check.sh` first builds default target, runs lexical scan, redirects `lake env lean audit/PrintAxioms.lean` into **candidate-local `audit/axioms.out`**, then checks footprints. Running it in the pristine candidate would violate the immutable-workspace rule; therefore builds are restricted to disposable copies/snapshots. Advertised `LEXICAL_SCAN=CLEAN`, `AUDITED=774`, `NONSTANDARD=0` require a successful dynamic run; the subsequent run on the compute node reproduced all three advertised outputs.

An independent static scanner scans all 200 tracked Lean files after stripping nested comments and strings. No code occurrence of sorry, admit, native_decide, implemented_by, unsafe, axiom, the listed kernel-bypass options, or custom elab/run_elab/macro/extern was found. Results: (raw audit record, kept privately). This improves on the repository grep patterns but is still a source scanner, not a proof of kernel validity. Dependency source correctness/trust is not certified by this repository-only scan.

`audit/PrintAxioms.lean` contains 774 entries and774 distinct declarations independently enumerated (raw audit record, kept privately). Selected names include the headlines, geometric bridges, HLY/DHZ packages, scalar and round sphere, normal form, attaching, LC and O'Neill interfaces. Successful `#print axioms` traverses declarations' proof dependency cones and exposes axiom dependencies even for unnamed intermediate declarations. It does **not** expose ordinary hypotheses, prove their truth, ensure statement fidelity, or guarantee all standalone library declarations are covered.

The parser accepts only `propext`, `Classical.choice`, `Quot.sound`; rejects `sorryAx` and errors/no declarations. It does not enforce expected count, uniqueness or an independently defined complete list. Independent controlled text probes show allowed single entry/duplicates pass and `sorryAx` fails (raw audit record, kept privately). The successful run was independently parsed with a line-anchored declaration-name parser (including apostrophes in names):774 entries, 774 distinct, no missing/unexpected names, axiom union exactly {propext, Classical.choice, Quot.sound}. Result and original footprints: (raw audit record, kept privately). An initial independent regex mishandled apostrophes; it was corrected before conclusions were recorded. The candidate parser did not have that issue.

Static import cones (raw audit record, kept privately) bound the scope of source inspection. They are module dependency cones, not kernel declaration-level graphs. TheoremsAB cone contains149 repository modules,44 RiemannianGeometry modules. Key interfaces were inspected instead of asserting every file was read in full.

## Trust layers

1. Lean kernel checks terms against types; toolchain/runtime/platform remain the computing trust base.
2. Mathlib provides kernel-checked mathematical infrastructure at the pinned source revision, subject to its ordinary axiom footprint and actual cache/build validation. This run reused matching pre-existing Mathlib cache artifacts rather than rebuilding Mathlib from source.
3. Repository definitions/proofs implement connections, quotient charts, curvature and group calculations; the advertised build and selected recursive axiom checks completed successfully, earning LEAN_VERIFIED for those formal implications, with statement fidelity assessed separately.
4. RW, specific exotic-bundle topology, KM classification/meaning of Rep, Hitchin and orientation reversal are mathematical hypotheses, **not Lean axioms**. An empty nonstandard-axiom census does not remove them. The inappropriate stronger Sp bridge is F01.

Classical choice is used for existence witnesses and frames, with corresponding existence proofs; `frameAt_spec` proves the chosen frame exists under genuine positive smooth metric assumptions. Local positive metrics/typeclass bridges and quotients were inspected for assumptions hidden as fields; no extra published theorem was established as an unproved structure field apart from the explicit input interfaces discussed in the synthesis.

## Limits

A clean candidate-source build and separate root build completed in a disposable build snapshot. The node cache was warm; no fully cold Mathlib download/bootstrap or full Mathlib source rebuild was attempted. Selected axiom footprints and a constant-clutching Lean probe were independently checked. No claim that arbitrary Rep is inconsistent is made. GitHub identity, candidate-source checks and the actual cached build are independently established; F01 remains a statement-fidelity blocker. Audit reports are uncommitted because the task expressly prohibited commits. Candidate remains unchanged; final byte comparison and Git verification are recorded separately.

## Successful retry

Retry job: exit 0; started 2026-10-04T21:55:45+01:00, finished 22:08:41. Exact command, stdout, stderr and telemetry are in the raw audit record (kept privately). The local polling wrapper ended with 143 before collection; the remote job continued and its final result was collected manually. No remote job was cancelled.

| Command | Exit | Wall time | /usr/bin/time maximum RSS (KiB) | Result |
|---|---:|---:|---:|---|
| `lake exe cache get` | 0 | 24.94s | 969996 | Mathlib revision verified;8689 already-cached files decompressed, no files downloaded |
| `sh scripts/check.sh` | 0 | 12m27.23s | 6883172 | Build8904 jobs; LEXICAL_SCAN=CLEAN; AUDITED=774 NONSTANDARD=0 |
| `lake build RiemannianGeometry` | 0 | 2.73s | 2949736 | Build2579 jobs; reuses modules already compiled in default build |
| scratch `lake env lean audit-probes/ConstantClutchingProbe.lean` | 0 | 5.02s | 6632168 | Fixed representation and identity attaching, three allowed axioms only |

Routine deprecation/unused-tactic/simp warnings are retained; no lexical placeholder or nonstandard axiom was found. The snapshot was cold with respect to candidate build outputs, warm with respect to dependency cache. Therefore this establishes GitHub-source verification with an available matching Mathlib cache; it does not establish successful internet bootstrap on the build node. All build computation ran on the expressly authorized compute node. Package source archiveSHA and transfer verification are in the raw audit record (kept privately).

Build host: Linux x86_64. Full environment output is in the raw audit record (kept privately). The build telemetry's summed process-RSS peak exceeds physical memory because it counts shared mappings; it is not physical memory consumed. The `/usr/bin/time` and node-available-memory values should be used alongside it, not substituted by the summed number.

## Final frozen-source verification

Final candidate `git status --porcelain`: empty; HEAD `ad7a77f4b6619cd160090095211fbc001939a540`; tree `7424f98ad372e2b6f12dd345d86c92975ebc3ffc`; `git diff --check`: exit 0. Independent comparison of all 217 tracked files to initial SHA-256 fingerprints:0 byte mismatches. The built snapshot on the compute node separately matched all 217 original file hashes and all 9 frozen dependency revisions, exit 0. Evidence: (raw audit record, kept privately). Candidate remained frozen; reports and scratch evidence are outside it. No commits or pushes.
