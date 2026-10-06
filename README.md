# Positive sectional curvature on exotic spheres in dimensions 8 and 10: a Lean formalisation

This repository contains a Lean 4 formalisation of the arguments in

> **[GG]** F. Galaz-García, *Positive sectional curvature on the exotic 8-sphere
> and order-three homotopy 10-spheres*, [arXiv:2609.38126](https://arxiv.org/abs/2609.38126) [math.DG] (2026).

The paper proves that the exotic 8-sphere and the two oriented homotopy
10-spheres of order three admit Riemannian metrics of positive sectional
curvature.

The repository contains two libraries:

- `ExoticSpheres8And10`, the formalisation of [GG] (about 37,000 lines and
  2,800 declarations);
- `RiemannianGeometry`, a reusable library of about 15,000 lines covering
  the Levi-Civita connection, curvature, sectional curvature, Riemannian
  submersions and O'Neill's formula.

The project uses Lean `v4.33.1` and Mathlib `v4.33.1`, both pinned by
`lean-toolchain` and `lake-manifest.json`.

## Main results

| [GG] | Lean declaration | Module |
|---|---|---|
| Theorem A (exotic 8-sphere) | `ExoticSpheres8And10.theoremA` | `Main.TheoremsAB` |
| Theorem B (order-three homotopy 10-spheres) | `ExoticSpheres8And10.theoremB` | `Main.TheoremsAB` |
| Corollary C | `corollaryC_dim8_geom`, `corollaryC_dim10_geom` | `Main.CorollaryC` |
| `thm:HLYgeneral` | `hly_general` | `Curvature.HLYGeneral` |
| `prop:polar` | `StarBundle.prop_polar` | `StarBundles.Equivariant` |
| `lem:attaching` | `lem_attaching_1`, `lem_attaching_3` | `PolarBundles.AttachingDiffeo` |
| `lem:K` | `lem_K` | `Main.Representations` |
| `fact:prop31` ([HLY], Prop. 3.1) | `hly_prop31_global_intrinsic` | `Curvature.Prop31.Bundle.Intrinsic` |
| `rem:general_bound` | `remark_general_bound_RW` | `Curvature.DHZ` |

A complete paper-to-Lean correspondence is given in
[`docs/correspondence.md`](docs/correspondence.md). It records every numbered
item of [GG], the declarations which prove it, and the places where the Lean
statement differs from the wording in the paper.

## What is assumed

The only axioms appearing in the audited dependency closures are Lean's three
standard axioms

- `propext`,
- `Classical.choice`,
- `Quot.sound`.

`audit/PrintAxioms.lean` audits 785 declarations, including Theorems A and B,
the geometric statements comprising Corollary C, and the principal results of
every formalisation target. The repository contains no `sorry`, `admit` or
`native_decide`.

The following external results are used as explicit hypotheses where needed:

| Input | Reference | Lean form |
|---|---|---|
| Positive-curvature gluing theorem | [RW], Theorem A(i) | `RWGluing` |
| Identification of the relevant star quotients with the exotic spheres | [Sp], Theorem 1 | `StarBundle` / `IsSmoothStarQuotient` hypotheses |
| `Θ₈ ≅ ℤ/2`, `Θ₁₀ ≅ ℤ/6`, and the standard sphere represents `0` | [KM] | `RepRel`, `hround` |
| Hitchin's `α`-invariant obstruction in dimension 10 | [Hi] | `hα`, `hHitchin` |
| Reversal of orientation acts by negation in `Θ₁₀` | standard | `hneg` |

To interpret Sperança's quotient manifolds in the form used in Lean, we also
use the standard facts that compact Lie group actions are proper and that a
free proper smooth action has a smooth quotient for which the projection is a
surjective smooth submersion; see [Lee, Cor. 21.6, Thms 21.10 and 4.29].
These facts are not assumptions of any Lean theorem. The corresponding
uniqueness statement for smooth star quotients is proved in the repository as
`IsSmoothStarQuotient.diffeomorph`.

Everything else needed for the main results is proved here. This includes the
polar normal form, the smooth identification of the polar model with the star
quotient, transport of positive sectional curvature along diffeomorphisms,
[HLY, Prop. 3.1] in the generality used in [GG], [DHZ, Prop. 5.1], the
positive scalar curvature of positively curved metrics, and the positive
curvature of the round sphere.

## Building and checking

You need [elan](https://github.com/leanprover/elan), the Lean toolchain
manager, and git.

```sh
git clone https://github.com/galazg24/exotic-spheres-8-10-positive-curvature.git
cd exotic-spheres-8-10-positive-curvature

lake exe cache get
lake build
sh scripts/check.sh
```

`scripts/check.sh` succeeds only if

- the project builds;
- the lexical scan finds no `sorry`, `admit`, `native_decide`,
  `implemented_by`, or new axiom;
- every audited declaration depends only on Lean's three standard axioms.

The same check is run by continuous integration.

## Repository structure

```text
ExoticSpheres8And10/
  Main/            Theorems A and B, Corollary C, group theory
  ActionField/     the infinitesimal-action estimate lem:K
  PolarBundles/    polar data, polar bundles and attaching maps
  StarBundles/     special S³-S³ bundles and polar normal forms
  Curvature/       the curvature construction, HLY and DHZ results
  Geometry/        pullbacks, second fundamental forms, manifolds with boundary
  Analysis/        parametric integrals, ODEs with parameters, Haar measure

RiemannianGeometry/
                   Levi-Civita connection, curvature, sectional curvature,
                   Riemannian submersions and O'Neill's formula

audit/             axiom audit and sanitised audit reports
docs/              paper correspondence, targets and project dashboard
scripts/           build and checking scripts
```

## Documentation

The main documentation files are:

- [`docs/correspondence.md`](docs/correspondence.md), giving the detailed
  correspondence between [GG] and the Lean declarations;
- [`docs/targets.md`](docs/targets.md), listing the formalisation targets;
- [`docs/dashboard.html`](docs/dashboard.html), an interactive view of the
  module and declaration dependencies, theorem dependency cones, and basic
  project statistics.

## Independent audit

The formalisation was independently audited using OpenAI Codex after the
Claude-assisted candidate had been frozen. The first audit led to revisions of
the formalisation, after which a second independent audit of the revised
candidate reported no remaining findings. The audit covered 785 declarations and found no nonstandard axioms.

The sanitised audit reports and reproducibility summaries are preserved under
`audit/cross-vendor-v1.0.0-rc2/` and
`audit/cross-vendor-v1.0.0-rc3/`.

## Development and provenance

The formalisation was developed by Fernando Galaz-García (Durham University)
with assistance from Claude (Anthropic), used through Claude Code.

## References

- **[GG]** F. Galaz-García, *Positive sectional curvature on the exotic
  8-sphere and order-three homotopy 10-spheres*, arXiv:2609.38126 [math.DG],
  2026.
- **[DHZ]** S. Deng, Z. Hu and H. Zhang, *Positive sectional curvature and
  non-isometric circle actions on a family of eleven-spheres*,
  arXiv:2609.32680, 2026.
- **[HLY]** Y.-H. He, Z. Liu and S.-T. Yau, *Positive sectional curvature on
  all smooth 7-spheres*, arXiv:2609.29426, 2026.
- **[Hi]** N. Hitchin, *Harmonic spinors*, Adv. Math. 14 (1974), 1–55.
- **[KM]** M. A. Kervaire and J. W. Milnor, *Groups of homotopy spheres: I*,
  Ann. of Math. (2) 77 (1963), 504–537.
- **[Lee]** J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed.,
  Graduate Texts in Mathematics 218, Springer, 2013.
- **[O'N]** B. O'Neill, *The fundamental equations of a submersion*,
  Michigan Math. J. 13 (1966), 459–469.
- **[RW]** P. Reiser and D. J. Wraith, *A generalization of the Perelman
  gluing theorem and applications*, arXiv:2308.06996, 2024.
- **[Sp]** L. D. Sperança, *Pulling back the Gromoll–Meyer construction and
  models of exotic spheres*, Proc. Amer. Math. Soc. 144 (2016), no. 7,
  3181–3196, doi:10.1090/proc/12945.

## Licence and citation

Released under the Apache License 2.0; see `LICENSE` and `NOTICE`.

If you use this formalisation, please cite [GG] and this repository. Citation
metadata are provided in `CITATION.cff`.
