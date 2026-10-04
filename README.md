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
    [IsManifold (IP 7) ∞ E] [T2Space E] (B : StarBundle (m := 7) rep8 E) :
    letI := rep8.factVs 7
    ∃ D : PolarData (m := 7) e8, D.ρ = rep8.ρ ∧
      Nonempty (Quotient (EquivSections.starSetoid B) ≃ₜ QuotSpace D) ∧
      (RWGluing (𝓡 (7 + 1)) (QuotSpace D) → HasPosCurvMetric (𝓡 (7 + 1)) (QuotSpace D))
```

In words: for every special `S³`-`S³` bundle `E` of Sperança's type for the representation `ρ₈`,
the star quotient `E/S³_⋆` is homeomorphic to the smooth manifold `QuotSpace D` of a polar
datum `D`. If the Reiser–Wraith gluing theorem holds for `QuotSpace D` (the hypothesis
`RWGluing`), then `QuotSpace D` carries a smooth metric of positive sectional curvature, in the
sense of `sectionalCurvatureAt` from `RiemannianGeometry`. Sperança's theorem, that the exotic
8-sphere is such a quotient, is the second imported input.

## What is assumed

Lean's kernel checks every proof. The only axioms used are Lean's three standard ones,
`propext`, `Classical.choice` and `Quot.sound`. `audit/PrintAxioms.lean` audits Theorems A and
B, both geometric statements comprising Corollary C, and the principal results of every
formalisation target (`docs/targets.md`) and every section of [GG], for 774 declarations in
all. `#print axioms` reports every axiom in a declaration's full dependency closure, Mathlib
included, so the audit covers everything on which these results depend. The library contains no
`sorry`, `admit` or `native_decide`.

The following published results are **not** formalised. Each enters as an explicit hypothesis
of the theorems that use it, never as an axiom:

| Input | Reference | Lean form |
|---|---|---|
| The gluing theorem for positive curvature | [RW] Theorem A(i) | hypothesis `RWGluing` |
| `E¹¹`, `E¹³` are special `S³`-`S³` bundles whose star quotients are the exotic spheres | [Sp] | hypothesis `B : StarBundle rep8 E` (resp. `rep10`) |
| `Θ₈ ≅ ℤ/2`, `Θ₁₀ ≅ ℤ/6`; the standard sphere represents `0` | [KM] | interface `RepRel`, hypothesis `hround` |
| `α : Θ₁₀ → ℤ/2` is nonzero and vanishes on manifolds of positive scalar curvature | [Hi] | hypotheses `hα`, `hHitchin` |
| Reversing orientation negates the class in `Θ₁₀` | standard | hypothesis `hneg` |

The rest of [GG] is proved here, including [HLY] Proposition 3.1 in the generality [GG] states
it. That covers principal `S³`-bundles with connection over compact bases with boundary, with
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
- **[O'N]** B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469.
- **[RW]** P. Reiser and D. J. Wraith, *A generalization of the Perelman gluing theorem and
  applications*, arXiv:2308.06996, 2024.
- **[Sp]** L. D. Sperança, *Pulling back the Gromoll–Meyer construction and models of exotic
  spheres*, Proc. Amer. Math. Soc. 144 (2016), 3181–3196.

## Licence and citation

Apache License 2.0; see `LICENSE` and `NOTICE`. If you use this formalisation, please cite [GG]
and the Zenodo record of this repository (`CITATION.cff`).
