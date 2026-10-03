/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Frame test for hom-sections

A converse to the `ContMDiff*.clm_bundle_apply` family of
`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean`: a section of the hom-bundle
`x ↦ Φ x : E₁ x →L[𝕜] E₂ x` is `C^n` at `x₀` as soon as its values on the local frame of `E₁`
induced by a trivialisation `e` (with `x₀ ∈ e.baseSet`) and a basis `b` of the model fibre `F₁`
are `C^n` sections of `E₂`.

## Main results

* `contMDiffAt_hom_bundle_of_contMDiffAt_localFrame`, and the `iff` form
  `contMDiffAt_hom_bundle_iff_contMDiffAt_localFrame`;
* `mdifferentiableAt_hom_bundle_of_mdifferentiableAt_localFrame` and its `iff` form;
* `ContinuousLinearMap.eq_sum_smulRightL_basis` — a continuous linear map out of a
  finite-dimensional space is the sum of the rank-one operators given by its values on a basis;
* `mdifferentiableAt_sum_univ` — `MDifferentiableAt.sum` for an index type in an arbitrary
  universe.

## Why this is needed

## Implementation notes

The reduction is **not** through `ContinuousLinearMap.inCoordinates`. That representative
hard-wires `trivializationAt F₁ E₁ x₀` on the source side, which would force either a
change-of-trivialisation argument or a weakening of the statement to that particular `e`. Instead,
`Bundle.Trivialization.continuousLinearMap` (`Topology/VectorBundle/Hom.lean`) builds a
trivialisation of the hom-bundle from *arbitrary* atlas trivialisations `e₁`, `e₂` with
`baseSet = e₁.baseSet ∩ e₂.baseSet`, and `Trivialization.contMDiffAt_section_iff` accepts any atlas
trivialisation whose base set contains `x₀`. Feeding the first to the second turns the goal directly
into smoothness of `fun x ↦ e₂.continuousLinearMapAt 𝕜 x ∘L Φ x ∘L e.symmL 𝕜 x` with the caller's
own `e`, so the general statement costs nothing over the specialised one.

Reassembling a map into the fixed space `F₁ →L[𝕜] F₂` from its values on a basis has no
off-the-shelf solution: `Basis.constrL` is a function of the values rather than a bundled map in
them, so it supplies no continuity in `v`, and `ContinuousLinearEquiv.piRing` has the wrong source
space. `ContinuousLinearMap.smulRightL` is the cleanest route, and the `MDifferentiable` twin cannot
reuse even that, since there is no `mdifferentiableAt_pi_space`; it goes through the explicit
rank-one decomposition and a finite sum.

`[CompleteSpace 𝕜]` is needed — not for the bundles, but because the coordinate functionals
`b.coord i` must be continuous, and `LinearMap.toContinuousLinearMap` carries that hypothesis. It is
not an artefact: over `𝕜 = ℚ`, the two-dimensional `ℚ + ℚ√2 ⊂ ℝ` has unbounded coordinate
functionals. Mathlib's `LocalFrame.lean` assumes a complete field for the same reason. Nothing else
is needed: no completeness or finiteness of `F₂`, no Riemannian structure.

-/

noncomputable section

open Bundle Set Module Filter ContinuousLinearMap
open scoped Manifold Bundle Topology

variable {𝕜 B F₁ F₂ : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

/-! ### Auxiliary algebraic and analytic lemmas -/

/-- A continuous linear map out of a finite-dimensional space is the sum of the rank-one
operators determined by its values on a basis. -/
lemma ContinuousLinearMap.eq_sum_smulRightL_basis {ι : Type*} [Fintype ι] [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 F₁] (b : Basis ι 𝕜 F₁) (L : F₁ →L[𝕜] F₂) :
    L = ∑ i, ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
      (LinearMap.toContinuousLinearMap (b.coord i)) (L (b i)) := by
  ext w
  have h : (∑ i, ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
      (LinearMap.toContinuousLinearMap (b.coord i)) (L (b i))) w
      = ∑ i, b.repr w i • L (b i) := by
    simp [Basis.coord_apply]
  rw [h]
  conv_lhs => rw [show w = ∑ i, b.repr w i • b i from (b.sum_repr w).symm]
  simp only [map_sum, map_smul]

/-- A finite sum of maps into a normed space which are `MDifferentiableAt` is
`MDifferentiableAt`.  This is `MDifferentiableAt.sum` for an index type in an arbitrary
universe: the Mathlib version is stated only for `ι : Type`. -/
lemma mdifferentiableAt_sum_univ {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {κ : Type*} [Fintype κ] {x₀ : B} (u : κ → B → G)
    (hu : ∀ i, MDifferentiableAt IB 𝓘(𝕜, G) (u i) x₀) :
    MDifferentiableAt IB 𝓘(𝕜, G) (fun x ↦ ∑ i, u i x) x₀ := by
  have h : MDifferentiableAt IB 𝓘(𝕜, G)
      (fun x ↦ ∑ k : Fin (Fintype.card κ), u ((Fintype.equivFin κ).symm k) x) x₀ :=
    (MDifferentiableAt.sum (t := Finset.univ) (z := x₀)
        (f := fun k ↦ u ((Fintype.equivFin κ).symm k))
        (fun k _ ↦ hu _)).congr_of_eventuallyEq
      (Eventually.of_forall fun x ↦ (Finset.sum_apply x Finset.univ _).symm)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun x ↦
    (Equiv.sum_comp (Fintype.equivFin κ).symm fun i ↦ u i x).symm)

/-! ### The frame test -/

/-- A hom-section is `C^n` at `x₀` as soon as its values on the local frame induced by a
trivialisation are `C^n` sections. -/
lemma contMDiffAt_hom_bundle_of_contMDiffAt_localFrame
    {ι : Type*} [Finite ι] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] (b : Basis ι 𝕜 F₁)
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [MemTrivializationAtlas e]
    {x₀ : B} (hx₀ : x₀ ∈ e.baseSet)
    (Φ : Π x : B, E₁ x →L[𝕜] E₂ x)
    (hΦ : ∀ i, ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂)) n
      (fun x ↦ TotalSpace.mk' F₂ x (Φ x (e.localFrame b i x))) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) x (Φ x)) x₀ := by
  have : Fintype ι := Fintype.ofFinite ι
  have hx₀₂ : x₀ ∈ (trivializationAt F₂ E₂ x₀).baseSet := mem_baseSet_trivializationAt F₂ E₂ x₀
  have hnhds : e.baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (e.open_baseSet.inter (trivializationAt F₂ E₂ x₀).open_baseSet).mem_nhds ⟨hx₀, hx₀₂⟩
  -- on `e.baseSet`, the local frame is `e.symmL` applied to the basis
  have hframe : ∀ x ∈ e.baseSet, ∀ i, e.localFrame b i x = e.symmL 𝕜 x (b i) := by
    intro x hx i
    rw [e.localFrame_apply_of_mem_baseSet b hx]
    simp [Bundle.Trivialization.basisAt, hx]
  -- Step 2: the trivialisation coordinates of the frame values are `C^n` at `x₀`
  have hg : ∀ i, ContMDiffAt IB 𝓘(𝕜, F₂) n
      (fun x ↦ (trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x
        (Φ x (e.symmL 𝕜 x (b i)))) x₀ := by
    intro i
    have h := ((trivializationAt F₂ E₂ x₀).contMDiffAt_section_iff (n := n) hx₀₂).mp (hΦ i)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with x hx
    rw [(trivializationAt F₂ E₂ x₀).continuousLinearMapAt_apply_of_mem (R := 𝕜) hx.2,
      hframe x hx.1 i]
  -- Step 3: a fixed continuous linear map reassembles a hom from its values on the basis
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (ι → F₂) →L[𝕜] (F₁ →L[𝕜] F₂),
      ∀ (v : ι → F₂) (w : F₁), Ψ v w = ∑ i, b.repr w i • v i := by
    refine ⟨∑ i, (ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
      (LinearMap.toContinuousLinearMap (b.coord i))).comp (ContinuousLinearMap.proj i),
      fun v w ↦ ?_⟩
    simp [Basis.coord_apply]
  have main : ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n
      (fun x ↦ Ψ (fun i ↦ (trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x
        (Φ x (e.symmL 𝕜 x (b i))))) x₀ :=
    Ψ.contMDiffAt.comp x₀ (contMDiffAt_pi_space.mpr hg)
  -- Step 1: reduce to the trivialisation `e.continuousLinearMap (RingHom.id 𝕜) _` of the hom bundle
  rw [Bundle.Trivialization.contMDiffAt_section_iff
    (e.continuousLinearMap (RingHom.id 𝕜) (trivializationAt F₂ E₂ x₀)) ⟨hx₀, hx₀₂⟩]
  refine main.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)
  have hexp : ∀ w : F₁,
      (trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x ((Φ x) (e.symmL 𝕜 x w))
        = ∑ i, b.repr w i •
            (trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x ((Φ x) (e.symmL 𝕜 x (b i))) := by
    intro w
    conv_lhs => rw [show w = ∑ i, b.repr w i • b i from (b.sum_repr w).symm]
    simp only [map_sum, map_smul]
  simp only [Bundle.Trivialization.continuousLinearMap_apply]
  ext w
  rw [hΨ]
  simp only [ContinuousLinearMap.comp_apply]
  exact hexp w

/-- Frame test for hom-sections, `iff` form: the converse direction is
`ContMDiffAt.clm_bundle_apply` applied to the (smooth) local frame. -/
lemma contMDiffAt_hom_bundle_iff_contMDiffAt_localFrame
    {ι : Type*} [Finite ι] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] (b : Basis ι 𝕜 F₁)
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [MemTrivializationAtlas e]
    {x₀ : B} (hx₀ : x₀ ∈ e.baseSet)
    (Φ : Π x : B, E₁ x →L[𝕜] E₂ x) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) x (Φ x)) x₀ ↔
    ∀ i, ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂)) n
      (fun x ↦ TotalSpace.mk' F₂ x (Φ x (e.localFrame b i x))) x₀ :=
  ⟨fun h i ↦ h.clm_bundle_apply
      (contMDiffAt_localFrame_of_mem (I := IB) (n := n) (e := e) (b := b) i hx₀),
    contMDiffAt_hom_bundle_of_contMDiffAt_localFrame b e hx₀ Φ⟩

/-- `MDifferentiableAt` twin of `contMDiffAt_hom_bundle_of_contMDiffAt_localFrame`. -/
lemma mdifferentiableAt_hom_bundle_of_mdifferentiableAt_localFrame
    {ι : Type*} [Finite ι] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] (b : Basis ι 𝕜 F₁)
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [MemTrivializationAtlas e]
    {x₀ : B} (hx₀ : x₀ ∈ e.baseSet)
    (Φ : Π x : B, E₁ x →L[𝕜] E₂ x)
    (hΦ : ∀ i, MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₂))
      (fun x ↦ TotalSpace.mk' F₂ x (Φ x (e.localFrame b i x))) x₀) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) x (Φ x)) x₀ := by
  have : Fintype ι := Fintype.ofFinite ι
  have hx₀₂ : x₀ ∈ (trivializationAt F₂ E₂ x₀).baseSet := mem_baseSet_trivializationAt F₂ E₂ x₀
  have hnhds : e.baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (e.open_baseSet.inter (trivializationAt F₂ E₂ x₀).open_baseSet).mem_nhds ⟨hx₀, hx₀₂⟩
  have hframe : ∀ x ∈ e.baseSet, ∀ i, e.localFrame b i x = e.symmL 𝕜 x (b i) := by
    intro x hx i
    rw [e.localFrame_apply_of_mem_baseSet b hx]
    simp [Bundle.Trivialization.basisAt, hx]
  have hg : ∀ i, MDifferentiableAt IB 𝓘(𝕜, F₂)
      (fun x ↦ (trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x
        (Φ x (e.symmL 𝕜 x (b i)))) x₀ := by
    intro i
    have h := ((trivializationAt F₂ E₂ x₀).mdifferentiableAt_section_iff IB _ hx₀₂).mp (hΦ i)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with x hx
    rw [(trivializationAt F₂ E₂ x₀).continuousLinearMapAt_apply_of_mem (R := 𝕜) hx.2,
      hframe x hx.1 i]
  have hL : ∀ i, MDifferentiableAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂)
      (fun x ↦ ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
        (LinearMap.toContinuousLinearMap (b.coord i))
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x
          (Φ x (e.symmL 𝕜 x (b i))))) x₀ := fun i ↦
    (((ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
      (LinearMap.toContinuousLinearMap (b.coord i))).contMDiffAt
        (n := 1)).mdifferentiableAt one_ne_zero).comp x₀ (hg i)
  have main : MDifferentiableAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂)
      (fun x ↦ ∑ i, ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
        (LinearMap.toContinuousLinearMap (b.coord i))
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x
          (Φ x (e.symmL 𝕜 x (b i))))) x₀ :=
    mdifferentiableAt_sum_univ
      (u := fun i x ↦ ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
        (LinearMap.toContinuousLinearMap (b.coord i))
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x
          (Φ x (e.symmL 𝕜 x (b i))))) hL
  rw [(e.continuousLinearMap (RingHom.id 𝕜)
    (trivializationAt F₂ E₂ x₀)).mdifferentiableAt_section_iff IB Φ ⟨hx₀, hx₀₂⟩]
  refine main.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)
  simp only [Bundle.Trivialization.continuousLinearMap_apply]
  exact ContinuousLinearMap.eq_sum_smulRightL_basis b
    (((trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 x).comp
      ((Φ x).comp (e.symmL 𝕜 x)))

/-- `MDifferentiableAt` frame test for hom-sections, `iff` form. -/
lemma mdifferentiableAt_hom_bundle_iff_mdifferentiableAt_localFrame
    {ι : Type*} [Finite ι] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] (b : Basis ι 𝕜 F₁)
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [MemTrivializationAtlas e]
    {x₀ : B} (hx₀ : x₀ ∈ e.baseSet)
    (Φ : Π x : B, E₁ x →L[𝕜] E₂ x) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x : B ↦ (E₁ x →L[𝕜] E₂ x)) x (Φ x)) x₀ ↔
    ∀ i, MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₂))
      (fun x ↦ TotalSpace.mk' F₂ x (Φ x (e.localFrame b i x))) x₀ :=
  ⟨fun h i ↦ h.clm_bundle_apply
      ((contMDiffAt_localFrame_of_mem (I := IB) (n := 1) (e := e) (b := b)
        i hx₀).mdifferentiableAt one_ne_zero),
    mdifferentiableAt_hom_bundle_of_mdifferentiableAt_localFrame b e hx₀ Φ⟩
