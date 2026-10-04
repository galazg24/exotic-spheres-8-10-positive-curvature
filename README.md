# Positive sectional curvature on exotic spheres in dimensions 8 and 10: a Lean formalisation

This repository contains a formalisation, in [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4), of the new arguments in

> **[GG]** F. Galaz-García, *Positive sectional curvature on the exotic 8-sphere and order-three
> homotopy 10-spheres*, arXiv:2609.38126 [math.DG] (2026).

[GG] proves that the exotic smooth 8-sphere, and both oriented homotopy 10-spheres representing
elements of order three in `Θ₁₀ ≅ ℤ/6`, admit Riemannian metrics of strictly positive
sectional curvature. Every argument specific to [GG] is formalised and checked by Lean's kernel.
Five previously published results used by [GG] are not formalised; instead they enter the
relevant Lean theorems as explicit, named hypotheses (see [What is assumed](#what-is-assumed)).

- Library: `ExoticSpheres8And10` (about 37,000 lines, 2,800 declarations), together with
  `RiemannianGeometry` (about 15,000 lines: Levi-Civita connection, curvature, Riemannian
  submersions, O'Neill's formula).
- Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`. Both are pinned in `lean-toolchain` and
  `lake-manifest.json`.
- Licence: Apache 2.0. Citation: see `CITATION.cff` and the Zenodo DOI (to be added at release).

## Main results

| [GG] | Lean declaration | Module |
|---|---|---|
| Theorem A (exotic 8-sphere) | `ExoticSpheres8And10.theoremA` | `Main.TheoremsAB` |
| Theorem B (order-three homotopy 10-spheres) | `ExoticSpheres8And10.theoremB` | `Main.TheoremsAB` |
| Corollary C | `corollaryC_dim8_geom`, `corollaryC_dim10_geom` | `Main.CorollaryC` |
| `thm:HLYgeneral` | `hly_general` | `Curvature.HLYGeneral` |
| `prop:polar` | `StarBundle.prop_polar` | `StarBundles.Equivariant` |
| `lem:attaching` | `lem_attaching_1`, `lem_attaching_3` | `PolarBundles.AttachingDiffeo` |
| `lem:K` | `lem_K` | `Main.Representations` (with `ActionField`) |
| `fact:prop31` ([HLY] Prop. 3.1) | `hly_prop31_global_intrinsic` | `Curvature.Prop31.Bundle.Intrinsic` |
| `rem:general_bound` | `remark_general_bound_RW` | `Curvature.DHZ` |

`docs/correspondence.md` lists every numbered item of [GG], the declarations that prove it, and
every place where the Lean statement differs from the wording of [GG], with the reason each
difference is harmless.

For example, Theorem A reads:

```lean
theorem theoremA
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (7 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 7) ∞ E] [T2Space E] (B : StarBundle (m := 7) rep8 E)
    {Q : Type} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin (7 + 1))) Q]
    [IsManifold (𝓡 (7 + 1)) ∞ Q] (p : E → Q) (hp : B.IsSmoothStarQuotient (m := 7) p) :
    letI := rep8.factVs 7
    (∀ D : PolarData (m := 7) e8, D.ρ = rep8.ρ → RWGluing (𝓡 (7 + 1)) (QuotSpace D)) →
      HasPosCurvMetric (𝓡 (7 + 1)) Q
```

In words: let `E` be a special `S³`-`S³` bundle of Sperança's type for the representation `ρ₈`,
and let `p : E → Q` be the smooth manifold `E/S³_⋆`. Precisely, `p` is a smooth quotient of `E`
by the star action (`IsSmoothStarQuotient`): a smooth surjection whose fibres are the star orbits
and along which smoothness descends. Any two such quotients are diffeomorphic
(`IsSmoothStarQuotient.diffeomorph`). If the Reiser–Wraith gluing theorem holds for the polar
models (the hypothesis `RWGluing`), then `Q` carries a smooth metric of positive sectional
curvature, in the sense of `sectionalCurvatureAt` from `RiemannianGeometry`.

The proof builds the metric on the polar model `QuotSpace D` of `prop:polar`, which is itself a
smooth quotient of `E` (`polarModelA`). It then pulls the metric back along the diffeomorphism
`Q ≅ QuotSpace D` (`HasPosCurvMetric.of_diffeomorph`). Sperança's Theorem 1, that `E¹¹/S³_⋆` is
diffeomorphic to the exotic 8-sphere, is the second imported input.

## What is assumed

Lean's kernel checks every proof. The only axioms used are Lean's three standard ones,
`propext`, `Classical.choice` and `Quot.sound`. `audit/PrintAxioms.lean` audits Theorems A and
B, both geometric statements comprising Corollary C, and the principal results of every
formalisation target (`docs/targets.md`) and every section of [GG], for 785 declarations in
all. `#print axioms` reports every axiom in a declaration's full dependency closure, Mathlib
included, so the audit covers everything on which these results depend. The library contains no
`sorry`, `admit` or `native_decide`.

The following published results are **not** formalised. Each enters as an explicit hypothesis
of the theorems that use it, never as an axiom:

| Input | Reference | Lean form |
|---|---|---|
| The gluing theorem for positive curvature | [RW] Theorem A(i) | hypothesis `RWGluing` |
| `E¹¹`, `E¹³` are special `S³`-`S³` bundles whose quotient manifolds `E/S³_⋆` are diffeomorphic to the exotic 8-sphere, resp. a generator of the order-three subgroup of `Θ₁₀` | [Sp] Theorem 1 | hypothesis `B : StarBundle rep8 E` (resp. `rep10`); in `SECc_of_theoremA`/`B`, the hypothesis that some smooth star quotient `p : E → Q` (`IsSmoothStarQuotient`) has `Rep Q g` |
| `Θ₈ ≅ ℤ/2`, `Θ₁₀ ≅ ℤ/6`; the standard sphere represents `0` | [KM] | interface `RepRel`, hypothesis `hround` |
| `α : Θ₁₀ → ℤ/2` is nonzero and vanishes on manifolds of positive scalar curvature | [Hi] | hypotheses `hα`, `hHitchin` |
| Reversing orientation negates the class in `Θ₁₀` | standard | hypothesis `hneg` |

Stating [Sp] for a smooth star quotient uses only standard facts about quotient manifolds. The
projection of the free smooth action of `S³_⋆` is a surjective submersion, and smoothness
descends along surjective submersions [Lee, Thms 21.10 and 4.29]. So Sperança's quotient
manifold is a smooth star quotient. All smooth star quotients of `E` are diffeomorphic to one
another, and this is proved here (`IsSmoothStarQuotient.diffeomorph`).

The rest of [GG] is proved here. That includes the smooth identification of the polar model with
`E/S³_⋆` and the transport of the metric along diffeomorphisms, and [HLY] Proposition 3.1 in the
generality [GG] states it. That covers principal `S³`-bundles with connection over compact bases with boundary, with
frame-independent curvature norms; non-vacuity is shown on two explicit models. It also
includes [DHZ] Proposition 5.1, the positive scalar curvature of positively curved metrics,
and the positive curvature of the round sphere.

## Building and checking

You need [elan](https://github.com/leanprover/elan) (the Lean toolchain manager) and git.

```sh
git clone https://github.com/galazg24/exotic-spheres-8-10-positive-curvature.git
cd exotic-spheres-8-10-positive-curvature
lake exe cache get        # download the compiled Mathlib (a few minutes)
lake build                # build the library
sh scripts/check.sh       # build, lexical scan, and axiom audit
```

On the development workstation, `lake build` takes about 12 minutes once Mathlib is cached;
it needs about 8 GB of memory.
`scripts/check.sh` exits with status 0 only if:
- the build succeeds;
- the lexical scan finds no `sorry`, `admit`, `native_decide`, `implemented_by` or new axiom;
- every audited declaration depends only on the three standard axioms.

Continuous integration runs the same check on every push
(`.github/workflows/ci.yml`).

## Layout

```
ExoticSpheres8And10/
  Main/            Theorems A and B, Corollary C, group theory, scalar curvature, round sphere
  ActionField/     lem:K: the bound on the infinitesimal action fields
  PolarBundles/    §2: polar data, polar bundles, star quotients, lem:attaching
  StarBundles/     §3: special S³-S³ bundles and prop:polar (equivariant polar normal forms)
  Curvature/       §4: the northern and southern fillings, boundary compatibility,
                   thm:HLYgeneral, [HLY] Prop. 3.1 (Prop31/), [DHZ] Prop. 5.1
  Geometry/        Riemannian geometry in coordinates, pullbacks, second fundamental forms,
                   manifolds with boundary (Boundary/)
  Analysis/        parametric integrals, ODEs with parameters, Haar measure on S³
RiemannianGeometry/  Levi-Civita connection, curvature, sectional curvature, O'Neill's formula
audit/               axiom audit
scripts/             check scripts
docs/                correspondence with [GG], formalisation targets, project dashboard
```

## Documentation

- `docs/correspondence.md`: every numbered item of [GG], the Lean declarations, its status, and
  the statement-fidelity notes.
- `docs/targets.md`: the formalisation targets A1–A9, B1–B3, D1–D2, referred to by these
  labels in docstrings.
- `docs/dashboard.html`: an interactive dashboard. It shows the 3D dependency graph of modules
  and declarations, the dependency cones of the main theorems, module statistics, and the
  compute history of the development. Download it and open it in a browser.

## How this formalisation was produced

The formalisation was developed by Fernando Galaz-García (Durham University) with extensive
assistance from Claude (Anthropic), used through Claude Code. Galaz-García determined the
mathematical architecture and formalisation targets, made the mathematical and scope decisions,
adjudicated proof routes and failures, and reviewed the correspondence between the Lean
statements and [GG]. Claude was used extensively to draft, revise and check Lean code under this
direction.

Every accepted proof is checked by Lean's kernel. The trusted computing base is Lean's kernel.
Mathlib supplies definitions and previously formalised results, all checked by the kernel. The
only mathematical inputs not formalised in this repository are the explicit published
hypotheses listed above. An independent cross-vendor audit of the statements will precede the
v1.0.0 release.

Development and large-scale checking ran on Tláloc, a private research cluster of desktop
workstations, allowing multiple builds and audits to run in parallel; the dashboard's Compute
tab records this history. Reproducing the formalisation requires none of this infrastructure:
`scripts/check.sh` runs on a single ordinary machine, and the CI workflow runs it on a standard
GitHub runner.

## References

- **[GG]** F. Galaz-García, *Positive sectional curvature on the exotic 8-sphere and
  order-three homotopy 10-spheres*, arXiv:2609.38126 [math.DG], 2026.
- **[DHZ]** S. Deng, Z. Hu and H. Zhang, *Positive sectional curvature and non-isometric circle
  actions on a family of eleven-spheres*, arXiv:2609.32680, 2026.
- **[HLY]** Y.-H. He, Z. Liu and S.-T. Yau, *Positive sectional curvature on all smooth
  7-spheres*, arXiv:2609.29426, 2026.
- **[Hi]** N. Hitchin, *Harmonic spinors*, Adv. Math. 14 (1974), 1–55.
- **[KM]** M. A. Kervaire and J. W. Milnor, *Groups of homotopy spheres: I*, Ann. of Math. (2)
  77 (1963), 504–537.
- **[Lee]** J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in
  Mathematics 218, Springer, 2013.
- **[O'N]** B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469.
- **[RW]** P. Reiser and D. J. Wraith, *A generalization of the Perelman gluing theorem and
  applications*, arXiv:2308.06996, 2024.
- **[Sp]** L. D. Sperança, *Pulling back the Gromoll–Meyer construction and models of exotic
  spheres*, Proc. Amer. Math. Soc. 144 (2016), 3181–3196.

## Licence and citation

Apache License 2.0; see `LICENSE` and `NOTICE`. If you use this formalisation, please cite [GG]
and the Zenodo record of this repository (`CITATION.cff`).
