/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smoothness of the fibrewise inverse of a family of continuous linear maps between fibers

Let `E₁` and `E₂` be two vector bundles, with model fibers `F₁` and `F₂`, and let
`ϕ m : E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)` be a family of continuous linear maps between their fibers,
along base maps `b₁` and `b₂`. We show that if `ϕ` is `C^n` (resp. differentiable) at a point `x`
and if `ϕ x` is invertible, then the fibrewise inverses `fun m ↦ (ϕ m).inverse` are again `C^n`
(resp. differentiable) at `x`.

As `ContinuousLinearMap.inverse` is defined everywhere, with junk value `0` at a non-invertible
map, no bundling into continuous linear equivalences is needed in the statements.

As in the normed space case (see `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`), the
model fiber `F₁` is assumed to be complete: otherwise the set of invertible maps need not be open,
and inversion can behave wildly even at an invertible map.

## Main results

* `ContinuousLinearMap.inCoordinates_inverse`: reading the inverse of `ϕ` in coordinates is the
  same as inverting `ϕ` read in coordinates.
* `ContMDiffWithinAt.clm_inverse_of_inCoordinates` and `ContMDiffAt.clm_inverse_of_inCoordinates`:
  the smoothness of the fibrewise inverse, for two possibly different base maps, with the
  smoothness of `ϕ` expressed in coordinates.
* `ContMDiffWithinAt.clm_bundle_inverse`, `ContMDiffAt.clm_bundle_inverse`,
  `ContMDiffOn.clm_bundle_inverse` and `ContMDiff.clm_bundle_inverse`: over a single base map,
  the fibrewise inverse of a `C^n` section of the hom-bundle is `C^n` at the points where it is
  invertible.
* `MDifferentiableWithinAt.clm_inverse_of_inCoordinates`,
  `MDifferentiableWithinAt.clm_bundle_inverse` and their variants: the same statements for
  differentiability.

## Implementation notes

The argument is the one used inline in `ContMDiffWithinAt.mpullbackWithin_vectorField_inter` for
the specific family `fun x ↦ (mfderivWithin I I' f s x).inverse`: `ϕ` read in coordinates is
invertible at `x` since `ϕ x` is, so composing with the normed space result
`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse` shows that the inverse of `ϕ` read in
coordinates is `C^n` at `x`, and `ContinuousLinearMap.inCoordinates_inverse` identifies it with
the inverse of `ϕ`, read in coordinates, near `x`.

The statements mention no trivialization: independence of the choice of trivialization is
contained in the `ContinuousLinearMap.inCoordinates` transfer. As in
`ContMDiffWithinAt.clm_apply_of_inCoordinates`, the version for two different base maps has to be
stated in coordinates, since the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds
only when `b₁` and `b₂` are globally smooth, while only local information is available here.

## Evidence that this is an extraction and not a restatement

The 25 lines of inline argument at `Mathlib/Geometry/Manifold/VectorBundle/Pullback.lean:429-453`
collapse to one term application of `ContMDiffWithinAt.clm_inverse_of_inCoordinates`:

    (hf.mfderivWithin_const hmn hx₀ hs).clm_inverse_of_inCoordinates
      continuousWithinAt_id hf.continuousWithinAt hf'

That use case is also why the two-base-map version exists: there `b₁ = f : M → M'` and
`b₂ = id : M → M`, so the single-base hom-bundle form cannot express it. Checked by compilation.

Intended upstream destinations: `ContinuousLinearMap.inCoordinates_inverse` and its `IsInvertible`
companion in `Mathlib/Topology/VectorBundle/Hom.lean`; everything else in
`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` beside the `clm_apply_of_inCoordinates` and
`clm_bundle_apply` families, whose statement shapes and docstring conventions these follow.

`[CompleteSpace F₁]` is the only analytic hypothesis, inherited from the normed engine; in
particular no finite-dimensionality, no `ContMDiffVectorBundle` and no `IsManifold` instance is
needed.
-/

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology

namespace ContinuousLinearMap

section InCoordinates

variable {𝕜 B₁ B₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B₁] [TopologicalSpace B₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {x₀ x : B₁} {y₀ y : B₂} {ϕ : E₁ x →L[𝕜] E₂ y}

/-- A continuous linear map between fibers of two vector bundles is invertible if and only if it is
invertible when read in coordinates, provided the coordinates are given by trivializations whose
base sets contain the relevant points. -/
theorem isInvertible_inCoordinates_iff
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) :
    (inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y ϕ).IsInvertible ↔ ϕ.IsInvertible := by
  rw [inCoordinates_eq hx hy]
  simp

/-- Reading the inverse of a continuous linear map between fibers of two vector bundles in
coordinates is the same as inverting the map read in coordinates, provided the coordinates are
given by trivializations whose base sets contain the relevant points. -/
theorem inCoordinates_inverse
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) :
    inCoordinates F₂ E₂ F₁ E₁ y₀ y x₀ x ϕ.inverse =
      (inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y ϕ).inverse := by
  rw [inCoordinates_eq hy hx, inCoordinates_eq hx hy]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm]
  rfl

end InCoordinates

end ContinuousLinearMap

section TwoBases

open ContinuousLinearMap

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`), and
two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers `F₁` and `F₂`).
Also a third manifold `M`, which will be the source of all our maps. -/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*}
  [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*}
  [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : WithTop ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] [CompleteSpace F₁]
  {b₁ : M → B₁} {b₂ : M → B₂} {x : M} {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {s : Set M}

/-- Consider continuous linear maps `ϕ m : E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)` between the fibers of two
vector bundles, over two base maps `b₁ : M → B₁` and `b₂ : M → B₂`, depending in a `C^n` way on
`m` when read in coordinates. If `ϕ x` is invertible, then the fibrewise inverses
`(ϕ m).inverse`, read in coordinates, also depend in a `C^n` way on `m` at `x`.

Version for `ContMDiffWithinAt`. See `ContMDiffWithinAt.clm_bundle_inverse` for a version with
`B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without `inCoordinates`. -/
theorem ContMDiffWithinAt.clm_inverse_of_inCoordinates
    (hϕ : CMDiffAt[s] n
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ m) (b₂ x) (b₂ m) (ϕ m)) x)
    (hb₁ : ContinuousWithinAt b₁ s x) (hb₂ : ContinuousWithinAt b₂ s x)
    (h : (ϕ x).IsInvertible) :
    CMDiffAt[s] n
      (fun m ↦ inCoordinates F₂ E₂ F₁ E₁ (b₂ x) (b₂ m) (b₁ x) (b₁ m) (ϕ m).inverse) x := by
  rw [← contMDiffWithinAt_insert_self] at hϕ ⊢
  rw [← continuousWithinAt_insert_self] at hb₁ hb₂
  -- inversion is `C^n` at the value at `x` of `ϕ` read in coordinates, as the latter is invertible
  have H : ContMDiffAt 𝓘(𝕜, F₁ →L[𝕜] F₂) 𝓘(𝕜, F₂ →L[𝕜] F₁) n ContinuousLinearMap.inverse
      (inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ x) (b₂ x) (b₂ x) (ϕ x)) :=
    ContDiffAt.contMDiffAt (IsInvertible.contDiffAt_map_inverse
      ((isInvertible_inCoordinates_iff (FiberBundle.mem_baseSet_trivializationAt' (b₁ x))
        (FiberBundle.mem_baseSet_trivializationAt' (b₂ x))).2 h))
  -- hence the inverse of `ϕ` read in coordinates depends in a `C^n` way on the point, and it
  -- coincides with the inverse of `ϕ`, read in coordinates, near `x`
  apply (H.comp_contMDiffWithinAt x hϕ).congr_of_eventuallyEq_of_mem ?_ (mem_insert x s)
  filter_upwards [hb₁ ((trivializationAt F₁ E₁ (b₁ x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b₁ x))),
    hb₂ ((trivializationAt F₂ E₂ (b₂ x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b₂ x)))] with m hm h'm
  simp only [Function.comp_apply]
  exact inCoordinates_inverse hm h'm

/-- Consider continuous linear maps `ϕ m : E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)` between the fibers of two
vector bundles, over two base maps `b₁ : M → B₁` and `b₂ : M → B₂`, depending in a `C^n` way on
`m` when read in coordinates. If `ϕ x` is invertible, then the fibrewise inverses
`(ϕ m).inverse`, read in coordinates, also depend in a `C^n` way on `m` at `x`.

Version for `ContMDiffAt`. See `ContMDiffAt.clm_bundle_inverse` for a version with `B₁ = B₂` and
`b₁ = b₂`, in which smoothness can be expressed without `inCoordinates`. -/
theorem ContMDiffAt.clm_inverse_of_inCoordinates
    (hϕ : CMDiffAt n (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ m) (b₂ x) (b₂ m) (ϕ m)) x)
    (hb₁ : ContinuousAt b₁ x) (hb₂ : ContinuousAt b₂ x) (h : (ϕ x).IsInvertible) :
    CMDiffAt n (fun m ↦ inCoordinates F₂ E₂ F₁ E₁ (b₂ x) (b₂ m) (b₁ x) (b₁ m) (ϕ m).inverse) x := by
  rw [← contMDiffWithinAt_univ] at hϕ ⊢
  rw [← continuousWithinAt_univ] at hb₁ hb₂
  exact hϕ.clm_inverse_of_inCoordinates hb₁ hb₂ h

/-- Consider continuous linear maps `ϕ m : E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)` between the fibers of two
vector bundles, over two base maps `b₁ : M → B₁` and `b₂ : M → B₂`, depending differentiably on
`m` when read in coordinates. If `ϕ x` is invertible, then the fibrewise inverses
`(ϕ m).inverse`, read in coordinates, also depend differentiably on `m` at `x`.

Version for `MDifferentiableWithinAt`. See `MDifferentiableWithinAt.clm_bundle_inverse` for a
version with `B₁ = B₂` and `b₁ = b₂`, in which differentiability can be expressed without
`inCoordinates`. -/
theorem MDifferentiableWithinAt.clm_inverse_of_inCoordinates
    (hϕ : MDiffAt[s] (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ m) (b₂ x) (b₂ m) (ϕ m)) x)
    (hb₁ : ContinuousWithinAt b₁ s x) (hb₂ : ContinuousWithinAt b₂ s x)
    (h : (ϕ x).IsInvertible) :
    MDiffAt[s]
      (fun m ↦ inCoordinates F₂ E₂ F₁ E₁ (b₂ x) (b₂ m) (b₁ x) (b₁ m) (ϕ m).inverse) x := by
  rw [← mdifferentiableWithinAt_insert_self] at hϕ ⊢
  rw [← continuousWithinAt_insert_self] at hb₁ hb₂
  -- inversion is differentiable at the value at `x` of `ϕ` read in coordinates, as the latter is
  -- invertible
  have H : MDifferentiableAt 𝓘(𝕜, F₁ →L[𝕜] F₂) 𝓘(𝕜, F₂ →L[𝕜] F₁) ContinuousLinearMap.inverse
      (inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ x) (b₂ x) (b₂ x) (ϕ x)) :=
    ContMDiffAt.mdifferentiableAt (ContDiffAt.contMDiffAt (n := 1)
      (IsInvertible.contDiffAt_map_inverse
        ((isInvertible_inCoordinates_iff (FiberBundle.mem_baseSet_trivializationAt' (b₁ x))
          (FiberBundle.mem_baseSet_trivializationAt' (b₂ x))).2 h))) one_ne_zero
  -- hence the inverse of `ϕ` read in coordinates depends differentiably on the point, and it
  -- coincides with the inverse of `ϕ`, read in coordinates, near `x`
  have H' : MDiffAt[insert x s] (ContinuousLinearMap.inverse ∘
      fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ m) (b₂ x) (b₂ m) (ϕ m)) x :=
    H.comp_mdifferentiableWithinAt x hϕ
  apply H'.congr_of_eventuallyEq_of_mem ?_ (mem_insert x s)
  filter_upwards [hb₁ ((trivializationAt F₁ E₁ (b₁ x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b₁ x))),
    hb₂ ((trivializationAt F₂ E₂ (b₂ x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b₂ x)))] with m hm h'm
  simp only [Function.comp_apply]
  exact inCoordinates_inverse hm h'm

/-- Consider continuous linear maps `ϕ m : E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)` between the fibers of two
vector bundles, over two base maps `b₁ : M → B₁` and `b₂ : M → B₂`, depending differentiably on
`m` when read in coordinates. If `ϕ x` is invertible, then the fibrewise inverses
`(ϕ m).inverse`, read in coordinates, also depend differentiably on `m` at `x`.

Version for `MDifferentiableAt`. See `MDifferentiableAt.clm_bundle_inverse` for a version with
`B₁ = B₂` and `b₁ = b₂`, in which differentiability can be expressed without `inCoordinates`. -/
theorem MDifferentiableAt.clm_inverse_of_inCoordinates
    (hϕ : MDiffAt (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ m) (b₂ x) (b₂ m) (ϕ m)) x)
    (hb₁ : ContinuousAt b₁ x) (hb₂ : ContinuousAt b₂ x) (h : (ϕ x).IsInvertible) :
    MDiffAt (fun m ↦ inCoordinates F₂ E₂ F₁ E₁ (b₂ x) (b₂ m) (b₁ x) (b₁ m) (ϕ m).inverse) x := by
  rw [← mdifferentiableWithinAt_univ] at hϕ ⊢
  rw [← continuousWithinAt_univ] at hb₁ hb₂
  exact hϕ.clm_inverse_of_inCoordinates hb₁ hb₂ h

end TwoBases

section OneBase

open ContinuousLinearMap

/- Declare a manifold `B` (with model `IB : HB → EB`) and two vector bundles `E₁` and `E₂` over
`B` (with model fibers `F₁` and `F₂`), together with a second manifold `M`, which will be the
source of all our maps. -/
variable {𝕜 B F₁ F₂ M : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [CompleteSpace F₁]
  {b : M → B} {ϕ : Π (m : M), E₁ (b m) →L[𝕜] E₂ (b m)} {s : Set M} {x : M}

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending in a `C^n` way on `m`. If `ϕ x` is
invertible, then the fibrewise inverses `(ϕ m).inverse` also depend in a `C^n` way on `m` at `x`.

We give here a version of this statement within a set at a point. -/
theorem ContMDiffWithinAt.clm_bundle_inverse
    (hϕ : CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (h : (ϕ x).IsInvertible) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) x := by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ ⊢
  exact ⟨hϕ.1, hϕ.2.clm_inverse_of_inCoordinates hϕ.1.continuousWithinAt
    hϕ.1.continuousWithinAt h⟩

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending in a `C^n` way on `m`. If `ϕ x` is
invertible, then the fibrewise inverses `(ϕ m).inverse` also depend in a `C^n` way on `m` at `x`.

We give here a version of this statement at a point. -/
theorem ContMDiffAt.clm_bundle_inverse
    (hϕ : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (h : (ϕ x).IsInvertible) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) x :=
  ContMDiffWithinAt.clm_bundle_inverse hϕ h

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending in a `C^n` way on `m` and invertible
at every point of a set `s`. Then the fibrewise inverses `(ϕ m).inverse` depend in a `C^n` way on
`m` on `s`. -/
theorem ContMDiffOn.clm_bundle_inverse
    (hϕ : CMDiff[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (h : ∀ m ∈ s, (ϕ m).IsInvertible) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) :=
  fun m hm ↦ (hϕ m hm).clm_bundle_inverse (h m hm)

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending in a `C^n` way on `m` and everywhere
invertible. Then the fibrewise inverses `(ϕ m).inverse` depend in a `C^n` way on `m`. -/
theorem ContMDiff.clm_bundle_inverse
    (hϕ : CMDiff n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (h : ∀ m, (ϕ m).IsInvertible) :
    CMDiff n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) :=
  fun m ↦ (hϕ m).clm_bundle_inverse (h m)

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending differentiably on `m`. If `ϕ x` is
invertible, then the fibrewise inverses `(ϕ m).inverse` also depend differentiably on `m` at `x`.

We give here a version of this statement within a set at a point. -/
theorem MDifferentiableWithinAt.clm_bundle_inverse
    (hϕ : MDiffAt[s]
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (h : (ϕ x).IsInvertible) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) x := by
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ ⊢
  exact ⟨hϕ.1, hϕ.2.clm_inverse_of_inCoordinates hϕ.1.continuousWithinAt
    hϕ.1.continuousWithinAt h⟩

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending differentiably on `m`. If `ϕ x` is
invertible, then the fibrewise inverses `(ϕ m).inverse` also depend differentiably on `m` at `x`.

We give here a version of this statement at a point. -/
theorem MDifferentiableAt.clm_bundle_inverse
    (hϕ : MDiffAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (h : (ϕ x).IsInvertible) :
    MDiffAt (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) x :=
  MDifferentiableWithinAt.clm_bundle_inverse hϕ h

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending differentiably on `m` and invertible
at every point of a set `s`. Then the fibrewise inverses `(ϕ m).inverse` depend differentiably on
`m` on `s`. -/
theorem MDifferentiableOn.clm_bundle_inverse
    (hϕ : MDiff[s]
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (h : ∀ m ∈ s, (ϕ m).IsInvertible) :
    MDiff[s] (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) :=
  fun m hm ↦ (hϕ m hm).clm_bundle_inverse (h m hm)

/-- Consider continuous linear maps `ϕ m : E₁ (b m) →L[𝕜] E₂ (b m)` between the fibers of two
vector bundles over a common base map `b : M → B`, depending differentiably on `m` and everywhere
invertible. Then the fibrewise inverses `(ϕ m).inverse` depend differentiably on `m`. -/
theorem MDifferentiable.clm_bundle_inverse
    (hϕ : MDiff
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (h : ∀ m, (ϕ m).IsInvertible) :
    MDiff (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m) (ϕ m).inverse) :=
  fun m ↦ (hϕ m).clm_bundle_inverse (h m)

end OneBase
