/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Fibrewise composition of sections of hom-bundles

Let `E₁`, `E₂` and `E₃` be `C^n` vector bundles over a manifold `B`, and let `b : M → B` be a map
from a manifold `M`. Given continuous linear maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and
`ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` depending smoothly on `m`, we show that their fibrewise
composition `ϕ m ∘L ψ m : E₁ (b m) →L[𝕜] E₃ (b m)` also depends smoothly on `m`.

This is the bundle analogue of `ContMDiffWithinAt.clm_comp`, which is the corresponding statement
for maps into the model fibres `F₁ →L[𝕜] F₂` rather than for sections of hom-bundles.

Taking `M := B` and `b := id` gives the statement that the composition of two `C^n` sections of
hom-bundles is a `C^n` section of the composite hom-bundle.

## Main results

* `ContinuousLinearMap.inCoordinates_comp` — reading a fibrewise composition in coordinates
* `ContMDiffWithinAt.clm_bundle_comp` and its `ContMDiffAt`, `ContMDiffOn`, `ContMDiff` variants
* `MDifferentiableWithinAt.clm_bundle_comp` and its `MDifferentiableAt`, `MDifferentiableOn`,
  `MDifferentiable` variants

## Why this is here rather than in Mathlib

Mathlib has the `ContMDiff*.clm_bundle_apply` family — *applying* a smooth hom-section to a smooth
section — but nothing that composes two hom-sections. The route through the fixed bilinear map
`ContinuousLinearMap.compL` is not available: `clm_bundle_apply₂` does not take a fixed bilinear map
on the model fibres, it takes a smooth section of a bilinear hom-bundle, so using it would first
require proving that `x ↦ compL 𝕜 (E₁ x) (E₂ x) (E₃ x)` is a smooth section of a triple hom-bundle —
strictly more work, and by the same coordinate argument. Hence the direct proof below.

The three-line content is `inCoordinates_comp`: in coordinates the middle bundle's trivialization
cancels (`Trivialization.symmL_continuousLinearMapAt`), so the coordinate representative of a
composition is the composition of the coordinate representatives, and
`ContMDiffWithinAt.clm_comp` — the *flat* model-fibre statement — finishes it.

Intended upstream destinations: `ContinuousLinearMap.inCoordinates_comp` is purely topological and
belongs in `Mathlib/Topology/VectorBundle/Hom.lean` beside `inCoordinates_eq`; the eight smoothness
lemmas belong in `Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` beside the `clm_bundle_apply`
family, whose variable block and naming they follow.

No `ContMDiffVectorBundle`, `FiniteDimensional` or completeness hypothesis is needed anywhere.
-/

noncomputable section

open Bundle Set ContinuousLinearMap

open scoped Manifold Bundle Topology

section

/- Declare a manifold `B` (with model `IB : HB → EB`), and three vector bundles `E₁`, `E₂` and
`E₃` over `B` (with model fibers `F₁`, `F₂` and `F₃`).

Also a second manifold `M`, which will be the source of all our maps. -/
variable {𝕜 B F₁ F₂ F₃ M : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)]
  [∀ x, Module 𝕜 (E₃ x)] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- Reading a fibrewise composition of continuous linear maps between fibres of vector bundles in
coordinates gives the composition of the coordinate representations, provided the base point lies
in the base set of the trivialization of the middle bundle. -/
lemma ContinuousLinearMap.inCoordinates_comp {x₀ x : B}
    (hx : x ∈ (trivializationAt F₂ E₂ x₀).baseSet)
    (f : E₂ x →L[𝕜] E₃ x) (g : E₁ x →L[𝕜] E₂ x) :
    inCoordinates F₁ E₁ F₃ E₃ x₀ x x₀ x (f ∘L g) =
      (inCoordinates F₂ E₂ F₃ E₃ x₀ x x₀ x f) ∘L (inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x g) := by
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_continuousLinearMapAt _ hx]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {b : M → B} {ϕ : ∀ m, E₂ (b m) →L[𝕜] E₃ (b m)} {ψ : ∀ m, E₁ (b m) →L[𝕜] E₂ (b m)}
  {s : Set M} {x : M}

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending in a `C^n` way on `m`. Then their
fibrewise composition depends in a `C^n` way on `m`.

We give here a version of this statement within a set at a point. -/
lemma ContMDiffWithinAt.clm_bundle_comp
    (hϕ : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)) x)
    (hψ : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m)) x) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) x := by
  rw [← contMDiffWithinAt_insert_self] at hϕ hψ ⊢
  simp only [contMDiffWithinAt_hom_bundle] at hϕ hψ ⊢
  refine ⟨hψ.1, ?_⟩
  apply (hϕ.2.clm_comp hψ.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert x _)
  have H : ∀ᶠ m in 𝓝[insert x s] x, b m ∈ (trivializationAt F₂ E₂ (b x)).baseSet :=
    hψ.1.continuousWithinAt <| (trivializationAt F₂ E₂ (b x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b x))
  filter_upwards [H] with m hm using inCoordinates_comp hm (ϕ m) (ψ m)

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending in a `C^n` way on `m`. Then their
fibrewise composition depends in a `C^n` way on `m`.

We give here a version of this statement at a point. -/
lemma ContMDiffAt.clm_bundle_comp
    (hϕ : CMDiffAt n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)) x)
    (hψ : CMDiffAt n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m)) x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) x :=
  ContMDiffWithinAt.clm_bundle_comp hϕ hψ

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending in a `C^n` way on `m`. Then their
fibrewise composition depends in a `C^n` way on `m`.

We give here a version of this statement on a set. -/
lemma ContMDiffOn.clm_bundle_comp
    (hϕ : CMDiff[s] n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)))
    (hψ : CMDiff[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m))) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) :=
  fun x hx ↦ (hϕ x hx).clm_bundle_comp (hψ x hx)

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending in a `C^n` way on `m`. Then their
fibrewise composition depends in a `C^n` way on `m`. -/
lemma ContMDiff.clm_bundle_comp
    (hϕ : CMDiff n (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)))
    (hψ : CMDiff n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m))) :
    CMDiff n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) :=
  fun x ↦ (hϕ x).clm_bundle_comp (hψ x)

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending differentiably on `m`. Then their
fibrewise composition depends differentiably on `m`.

We give here a version of this statement within a set at a point. -/
lemma MDifferentiableWithinAt.clm_bundle_comp
    (hϕ : MDiffAt[s] (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)) x)
    (hψ : MDiffAt[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m)) x) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) x := by
  rw [← mdifferentiableWithinAt_insert_self] at hϕ hψ ⊢
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ hψ ⊢
  refine ⟨hψ.1, ?_⟩
  apply (hϕ.2.clm_comp hψ.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert x _)
  have H : ∀ᶠ m in 𝓝[insert x s] x, b m ∈ (trivializationAt F₂ E₂ (b x)).baseSet :=
    hψ.1.continuousWithinAt <| (trivializationAt F₂ E₂ (b x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b x))
  filter_upwards [H] with m hm using inCoordinates_comp hm (ϕ m) (ψ m)

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending differentiably on `m`. Then their
fibrewise composition depends differentiably on `m`.

We give here a version of this statement at a point. -/
lemma MDifferentiableAt.clm_bundle_comp
    (hϕ : MDiffAt (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)) x)
    (hψ : MDiffAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) x :=
  MDifferentiableWithinAt.clm_bundle_comp hϕ hψ

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending differentiably on `m`. Then their
fibrewise composition depends differentiably on `m`.

We give here a version of this statement on a set. -/
lemma MDifferentiableOn.clm_bundle_comp
    (hϕ : MDiff[s] (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)))
    (hψ : MDiff[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) :=
  fun x hx ↦ (hϕ x hx).clm_bundle_comp (hψ x hx)

/-- Consider maps `ϕ m : E₂ (b m) →L[𝕜] E₃ (b m)` and `ψ m : E₁ (b m) →L[𝕜] E₂ (b m)` between
fibres of vector bundles over a base map `b : M → B`, depending differentiably on `m`. Then their
fibrewise composition depends differentiably on `m`. -/
lemma MDifferentiable.clm_bundle_comp
    (hϕ : MDiff (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₂ x →L[𝕜] E₃ x)) (b m) (ϕ m)))
    (hψ : MDiff (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ψ m))) :
    MDiff (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
      (E := fun x : B ↦ (E₁ x →L[𝕜] E₃ x)) (b m) (ϕ m ∘L ψ m)) :=
  fun x ↦ (hϕ x).clm_bundle_comp (hψ x)

end
