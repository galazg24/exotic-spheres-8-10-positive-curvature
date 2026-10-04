/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Differentiability of an applied covariant derivative

A covariant derivative sends a section `σ` of `V` to a section `∇σ` of `Hom(TM, V)`. Applying it to
a vector field `X` reassembles a section `fun y ↦ cov σ y (X y)` of `V` — the object usually written
`∇_X σ`. Iterated covariant derivatives are built from exactly this reassembly, so any result about
curvature needs to know it is differentiable.

This file supplies that, in three steps of increasing convenience.

## Main results

* `MDiffAtCovSection` — the hypothesis "`∇σ` is differentiable at `x` as a section of `Hom(TM, V)`",
  named so that downstream statements can carry it legibly.
* `mdiffAt_cov_apply` — the reusable bridge: `MDiffAtCovSection` plus differentiability of `X` gives
  differentiability of `∇_X σ`.
* `mdiffAt_covSection_of_contMDiff` — `MDiffAtCovSection` itself, obtained from
  `ContMDiffCovariantDerivativeOn`, which is precisely the class asserting that `∇` preserves
  regularity.
* `mdiffAt_cov_apply_of_contMDiff` — the composite: from regularity of the connection and of `σ`,
  plus differentiability of `X`, conclude differentiability of `∇_X σ`.

## Which hypothesis downstream results should carry

`MDiffAtCovSection F cov σ x`, not the `ContMDiff` package. It is weaker — pointwise, and asking
only differentiability rather than a global `C^k` bound — and `mdiffAt_covSection_of_contMDiff`
supplies it for any caller who has the class. The decisive property either way is that it does not
mention `X`: a single hypothesis on `σ` serves every differentiable vector field, so it can be
hoisted outside a `TensorialAt` structure, whose fields quantify over `X`.

## Why this exists

  `hσX : MDiffAt (T% (fun y ↦ cov σ y (X y))) x`

asserting exactly this differentiability. That was honest but wrong as a destination. It is not part
of the mathematical content of a tensoriality statement, it is contagious to everything downstream,
and — decisively — it **blocks the bundled tensor**: `TensorialAt`'s `smul` and `add` fields admit
only `MDiffAt f x` and `MDiffAt (T% σ) x`, so there is nowhere to pass `hσX` and
`TensorialAt.mkHom₂` cannot be reached. Discharging it is therefore a prerequisite for bundling,
independently of tensoriality in the section slot.

## Note on how this was found

-/

noncomputable section

open Bundle NormedSpace Set
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [IsManifold I 1 M]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}

/-- `∇σ` is differentiable at `x` as a section of the bundle `Hom(TM, V)`.

Spelled out rather than written with the `T%` elaborator, which cannot infer the model fibre
`E →L[𝕜] F` for the `Hom` bundle; this is the same spelling Mathlib's
`ContMDiffCovariantDerivativeOn` uses. The model fibre `F` is an **explicit** argument because
nothing in `cov`, `σ` or `x` determines it — `V`'s fibres are types of their own — so leaving it
implicit stalls instance search for `VectorBundle 𝕜 ?F V` at every use site. -/
abbrev MDiffAtCovSection (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (σ : Π x : M, V x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] F))
    (fun y ↦ (⟨y, cov σ y⟩ :
      TotalSpace (E →L[𝕜] F) fun z : M ↦ TangentSpace I z →L[𝕜] V z)) x

/-- **The bridge.** If `∇σ` is differentiable at `x` as a section of `Hom(TM, V)`, and the vector
field `X` is differentiable at `x`, then the reassembled section `∇_X σ` is differentiable at `x`.

This is `MDifferentiableAt.clm_bundle_apply` with the bundles instantiated: the `Hom` bundle's
section is `cov σ`, the source bundle's section is `X`, and the base map is the identity. -/
theorem mdiffAt_cov_apply (hcovσ : MDiffAtCovSection F cov σ x) (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (fun y ↦ cov σ y (X y))) x :=
  hcovσ.clm_bundle_apply hX

/-- Differentiability of `∇σ` from the regularity of the connection.

`ContMDiffCovariantDerivativeOn F k cov univ` says exactly that `∇` sends `C^(k+1)` sections to
`C^k` sections, so this is that class specialised to a point. The hypothesis `hk : k ≠ 0` is what
makes `C^k` imply differentiable. -/
theorem mdiffAt_covSection_of_contMDiff {k : ℕ∞ω}
    [ContMDiffCovariantDerivativeOn F k cov univ] (hk : k ≠ 0)
    (hσ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) (k + 1) (T% σ) univ) :
    MDiffAtCovSection F cov σ x :=
  ((ContMDiffCovariantDerivativeOn.contMDiff (F := F) (cov := cov) hσ).contMDiffAt
    Filter.univ_mem).mdifferentiableAt hk

/-- **The composite.** From regularity of the connection and of `σ`, plus differentiability of `X`,
the reassembled section `∇_X σ` is differentiable at `x`.

This is what replaces the old `hσX` hypothesis outright, for a caller who happens to have the
`ContMDiff` package rather than the pointwise hypothesis. -/
theorem mdiffAt_cov_apply_of_contMDiff {k : ℕ∞ω}
    [ContMDiffCovariantDerivativeOn F k cov univ] (hk : k ≠ 0)
    (hσ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) (k + 1) (T% σ) univ) (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (fun y ↦ cov σ y (X y))) x :=
  mdiffAt_cov_apply (mdiffAt_covSection_of_contMDiff hk hσ) hX

end RiemannianGeometry
