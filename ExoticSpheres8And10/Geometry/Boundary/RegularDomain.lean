/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # Infrastructure: sublevel sets in `ℝⁿ` as smooth manifolds with boundary

Mathlib models manifolds with boundary on `EuclideanHalfSpace n = {x | 0 ≤ x 0}` (`𝓡∂ n`). It
has no smooth closed balls. This file gives any sublevel set `S = {g ≤ c} ⊆ ℝⁿ` a charted space
structure on `EuclideanHalfSpace n`. The charts are restrictions of **admissible ambient
charts**: open partial homeomorphisms `A` of `ℝⁿ` that are smooth with smooth inverse, and whose
first coordinate is `≥ 0` exactly on `S`.
* `AdmChart g c`, `AdmChart.toChart`;
* `regDomChartedSpace`, `regDom_isManifold`: if every point of `S` lies in an admissible chart,
  `S` is a `C^∞` manifold with boundary;
* `contMDiff_val_regDom`: the inclusion `S → ℝⁿ` is smooth;
* `isInvertible_mfderiv_val_regDom`: it is an immersion at every point, boundary points included.
-/

open Set Function Filter Topology

open scoped Manifold ContDiff

namespace ExoticSpheres8And10

noncomputable section

section RegDom

variable {n : ℕ} [NeZero n]

variable (g : (EuclideanSpace ℝ (Fin n)) → ℝ) (c : ℝ)

/-- The sublevel set `{g ≤ c}`. -/
abbrev RegDom : Type := {y : EuclideanSpace ℝ (Fin n) // g y ≤ c}

/-- An **admissible ambient chart** for `{g ≤ c}`. -/
structure AdmChart where
  A : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
  smooth : ContDiffOn ℝ ∞ A A.source
  smooth_symm : ContDiffOn ℝ ∞ A.symm A.target
  compat : ∀ y ∈ A.source, (0 ≤ (A y) 0 ↔ g y ≤ c)
  compat_lt : ∀ y ∈ A.source, (0 < (A y) 0 ↔ g y < c)

variable {g c}

theorem AdmChart.mem_halfSpace (C : AdmChart g c) {y : RegDom g c} (hy : y.1 ∈ C.A.source) :
    0 ≤ (C.A y.1) 0 :=
  (C.compat _ hy).2 y.2

theorem AdmChart.le_of_target (C : AdmChart g c) {z : (EuclideanSpace ℝ (Fin n))} (hz : z ∈ C.A.target) (hz0 : 0 ≤ z 0) :
    g (C.A.symm z) ≤ c := by
  have := (C.compat _ (C.A.map_target hz)).1
  rw [C.A.right_inv hz] at this
  exact this hz0

theorem halfSpace_symm_val {z : (EuclideanSpace ℝ (Fin n))} (hz : 0 ≤ z 0) : ((𝓡∂ n).symm z).val = z := by
  have : z ∈ range (𝓡∂ n) := by
    rw [range_modelWithCornersEuclideanHalfSpace]; exact hz
  exact (𝓡∂ n).right_inv this

open Classical in
/-- The chart of `S` induced by an admissible chart; `s₀` is a junk value. -/
def AdmChart.toChart (C : AdmChart g c) (s₀ : RegDom g c) :
    OpenPartialHomeomorph (RegDom g c) (EuclideanHalfSpace n) where
  toFun y := (𝓡∂ n).symm (C.A y.1)
  invFun z := if h : z.1 ∈ C.A.target then ⟨C.A.symm z.1, C.le_of_target h z.2⟩ else s₀
  source := {y | y.1 ∈ C.A.source}
  target := {z | z.1 ∈ C.A.target}
  map_source' y hy := by
    show ((𝓡∂ n).symm (C.A y.1)).val ∈ C.A.target
    rw [halfSpace_symm_val (C.mem_halfSpace hy)]
    exact C.A.map_source hy
  map_target' z hz := by
    show (if h : z.1 ∈ C.A.target then _ else s₀).1 ∈ C.A.source
    rw [dif_pos (show z.1 ∈ C.A.target from hz)]
    exact C.A.map_target hz
  left_inv' y hy := by
    show (if h : ((𝓡∂ n).symm (C.A y.1)).1 ∈ C.A.target then _ else s₀) = y
    have e1 := halfSpace_symm_val (C.mem_halfSpace hy)
    have ht : ((𝓡∂ n).symm (C.A y.1)).1 ∈ C.A.target := by rw [e1]; exact C.A.map_source hy
    rw [dif_pos ht]
    apply Subtype.ext
    show C.A.symm ((𝓡∂ n).symm (C.A y.1)).1 = y.1
    rw [e1, C.A.left_inv hy]
  right_inv' z hz := by
    show (𝓡∂ n).symm (C.A (if h : z.1 ∈ C.A.target then _ else s₀).1) = z
    rw [dif_pos (show z.1 ∈ C.A.target from hz)]
    apply Subtype.ext
    show ((𝓡∂ n).symm (C.A (C.A.symm z.1))).1 = z.1
    rw [C.A.right_inv hz, halfSpace_symm_val z.2]
  open_source := C.A.open_source.preimage continuous_subtype_val
  open_target := C.A.open_target.preimage continuous_subtype_val
  continuousOn_toFun := (𝓡∂ n).continuous_symm.comp_continuousOn
    (C.A.continuousOn.comp continuous_subtype_val.continuousOn fun _ h => h)
  continuousOn_invFun := by
    rw [(Topology.IsEmbedding.subtypeVal (p := fun y : EuclideanSpace ℝ (Fin n) => g y ≤ c)).isInducing.continuousOn_iff]
    refine (C.A.continuousOn_symm.comp continuous_subtype_val.continuousOn fun _ h => h).congr ?_
    intro z hz
    show (if h : z.1 ∈ C.A.target then _ else s₀).1 = C.A.symm z.1
    rw [dif_pos (show z.1 ∈ C.A.target from hz)]

theorem AdmChart.toChart_apply_val (C : AdmChart g c) (s₀ : RegDom g c) {y : RegDom g c}
    (hy : y.1 ∈ C.A.source) : (C.toChart s₀ y).val = C.A y.1 :=
  halfSpace_symm_val (C.mem_halfSpace hy)

open Classical in
theorem AdmChart.toChart_symm_val (C : AdmChart g c) (s₀ : RegDom g c)
    {z : EuclideanHalfSpace n} (hz : z.1 ∈ C.A.target) :
    ((C.toChart s₀).symm z).val = C.A.symm z.1 := by
  show (if h : z.1 ∈ C.A.target then _ else s₀).1 = _
  rw [dif_pos hz]

variable (g c) in
/-- **The charted space structure** on `{g ≤ c}`, given admissible charts covering it. -/
def regDomChartedSpace (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source) :
    ChartedSpace (EuclideanHalfSpace n) (RegDom g c) where
  atlas := {e | ∃ (C : AdmChart g c) (s : RegDom g c), e = C.toChart s}
  chartAt y := (Classical.choose (hcov y)).toChart y
  mem_chart_source y := Classical.choose_spec (hcov y)
  chart_mem_atlas y := ⟨_, y, rfl⟩

theorem range_halfSpace_mem {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ range (𝓡∂ n)) : 0 ≤ w 0 := by
  rw [range_modelWithCornersEuclideanHalfSpace] at hw; exact hw

theorem halfSpace_symm_val' {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ range (𝓡∂ n)) :
    ((𝓡∂ n).symm w).val = w :=
  halfSpace_symm_val (range_halfSpace_mem hw)

/-- **`{g ≤ c}` is a `C^∞` manifold with boundary.** -/
theorem regDom_isManifold (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source) :
    @IsManifold ℝ _ _ _ _ _ _ (𝓡∂ n) ∞ (RegDom g c) _ (regDomChartedSpace g c hcov) := by
  letI := regDomChartedSpace g c hcov
  apply isManifold_of_contDiffOn
  rintro e e' ⟨C, s, rfl⟩ ⟨C', s', rfl⟩
  have hdom : (𝓡∂ n).symm ⁻¹' ((C.toChart s).symm ≫ₕ C'.toChart s').source ∩ range (𝓡∂ n) ⊆
      C.A.target ∩ C.A.symm ⁻¹' C'.A.source := by
    rintro w ⟨hw1, hw2⟩
    rw [OpenPartialHomeomorph.trans_source] at hw1
    obtain ⟨hw1a, hw1b⟩ := hw1
    have hv := halfSpace_symm_val' hw2
    have ht : ((𝓡∂ n).symm w).1 ∈ C.A.target := hw1a
    rw [hv] at ht
    refine ⟨ht, ?_⟩
    have hb : ((C.toChart s).symm ((𝓡∂ n).symm w)).1 ∈ C'.A.source := hw1b
    rw [C.toChart_symm_val s (by rw [hv]; exact ht), hv] at hb
    exact hb
  refine ((C'.smooth.comp (C.smooth_symm.mono inter_subset_left) fun w hw => hw.2).mono hdom).congr ?_
  intro w hw
  obtain ⟨ht, hs'⟩ := hdom hw
  have hv := halfSpace_symm_val' hw.2
  show ((C'.toChart s') ((C.toChart s).symm ((𝓡∂ n).symm w))).val = C'.A (C.A.symm w)
  have e1 : ((C.toChart s).symm ((𝓡∂ n).symm w)).val = C.A.symm w := by
    rw [C.toChart_symm_val s (by rw [hv]; exact ht), hv]
  rw [C'.toChart_apply_val s' (by rw [e1]; exact hs'), e1]

/-- In the chart at `y`, the inclusion is `A.symm`, near the base point within the half space. -/
theorem val_extChart_symm_eventually (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source)
    (y : RegDom g c) :
    letI := regDomChartedSpace g c hcov
    (Subtype.val ∘ (extChartAt (𝓡∂ n) y).symm) =ᶠ[𝓝[range (𝓡∂ n)] (extChartAt (𝓡∂ n) y y)]
      (Classical.choose (hcov y)).A.symm := by
  letI := regDomChartedSpace g c hcov
  set C := Classical.choose (hcov y)
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡∂ n) y] with w hw
  rw [extChartAt_target] at hw
  obtain ⟨hw1, hw2⟩ := hw
  have hv := halfSpace_symm_val' hw2
  rw [extChartAt_coe_symm]
  show ((C.toChart y).symm ((𝓡∂ n).symm w)).val = C.A.symm w
  have ht : ((𝓡∂ n).symm w).1 ∈ C.A.target := hw1
  rw [C.toChart_symm_val y ht, hv]

theorem extChartAt_regDom_self (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source)
    (y : RegDom g c) :
    letI := regDomChartedSpace g c hcov
    extChartAt (𝓡∂ n) y y = (Classical.choose (hcov y)).A y.1 := by
  letI := regDomChartedSpace g c hcov
  rw [extChartAt_coe]
  exact (Classical.choose (hcov y)).toChart_apply_val y (Classical.choose_spec (hcov y))

/-- **The inclusion `{g ≤ c} → ℝⁿ` is smooth.** -/
theorem contMDiff_val_regDom (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source) :
    letI := regDomChartedSpace g c hcov
    ContMDiff (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Subtype.val : RegDom g c → _) := by
  letI := regDomChartedSpace g c hcov
  intro y
  set C := Classical.choose (hcov y)
  have hy : y.1 ∈ C.A.source := Classical.choose_spec (hcov y)
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
  have hpt : extChartAt (𝓡∂ n) y y ∈ C.A.target := by
    rw [extChartAt_regDom_self hcov y]; exact C.A.map_source hy
  have h1 : ContDiffAt ℝ ∞ C.A.symm (extChartAt (𝓡∂ n) y y) :=
    C.smooth_symm.contDiffAt (C.A.open_target.mem_nhds hpt)
  exact h1.contDiffWithinAt.congr_of_eventuallyEq (val_extChart_symm_eventually hcov y)
    (by
      show ((extChartAt (𝓡∂ n) y).symm (extChartAt (𝓡∂ n) y y)).val = C.A.symm _
      rw [extChartAt_to_inv, extChartAt_regDom_self hcov y, C.A.left_inv hy])

/-- The differential of the inclusion, in the chart at `y`. -/
theorem hasMFDerivAt_val_regDom (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source)
    (y : RegDom g c) :
    letI := regDomChartedSpace g c hcov
    HasMFDerivAt (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Subtype.val : RegDom g c → _) y
      (fderiv ℝ (Classical.choose (hcov y)).A.symm ((Classical.choose (hcov y)).A y.1)) := by
  letI := regDomChartedSpace g c hcov
  set C := Classical.choose (hcov y)
  have hy : y.1 ∈ C.A.source := Classical.choose_spec (hcov y)
  have hpt : C.A y.1 ∈ C.A.target := C.A.map_source hy
  have h1 : ContDiffAt ℝ ∞ C.A.symm (C.A y.1) :=
    C.smooth_symm.contDiffAt (C.A.open_target.mem_nhds hpt)
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hd := (h1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt (s := range (𝓡∂ n))
  rw [← extChartAt_regDom_self hcov y] at hd ⊢
  refine hd.congr_of_eventuallyEq ?_ ?_
  · have := val_extChart_symm_eventually hcov y
    filter_upwards [this] with w hw
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]
    exact hw
  · simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp, Function.comp_apply]
    rw [extChartAt_to_inv, extChartAt_regDom_self hcov y, C.A.left_inv hy]
    rfl

theorem isInvertible_fderiv_symm (C : AdmChart g c) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ C.A.source) : (fderiv ℝ C.A.symm (C.A y)).IsInvertible := by
  have hpt : C.A y ∈ C.A.target := C.A.map_source hy
  have hA : DifferentiableAt ℝ C.A y :=
    (C.smooth.contDiffAt (C.A.open_source.mem_nhds hy)).differentiableAt (by simp)
  have hS : DifferentiableAt ℝ C.A.symm (C.A y) :=
    (C.smooth_symm.contDiffAt (C.A.open_target.mem_nhds hpt)).differentiableAt (by simp)
  have e1 : C.A.symm ∘ C.A =ᶠ[𝓝 y] id := by
    filter_upwards [C.A.open_source.mem_nhds hy] with z hz; exact C.A.left_inv hz
  have e2 : C.A ∘ C.A.symm =ᶠ[𝓝 (C.A y)] id := by
    filter_upwards [C.A.open_target.mem_nhds hpt] with z hz; exact C.A.right_inv hz
  have h1 : (fderiv ℝ C.A.symm (C.A y)).comp (fderiv ℝ C.A y) = ContinuousLinearMap.id ℝ _ := by
    rw [← fderiv_comp y hS hA, e1.fderiv_eq, fderiv_id]
  have h2 : (fderiv ℝ C.A y).comp (fderiv ℝ C.A.symm (C.A y)) = ContinuousLinearMap.id ℝ _ := by
    have hA' : DifferentiableAt ℝ C.A (C.A.symm (C.A y)) := by rw [C.A.left_inv hy]; exact hA
    have := fderiv_comp (C.A y) hA' hS
    rw [C.A.left_inv hy] at this
    rw [← this, e2.fderiv_eq, fderiv_id]
  exact ⟨ContinuousLinearEquiv.equivOfInverse _ (fderiv ℝ C.A y)
    (fun v => by simpa using congrArg (fun L => L v) h2)
    (fun v => by simpa using congrArg (fun L => L v) h1), rfl⟩

/-- **The inclusion is an immersion**, boundary points included. -/
theorem isInvertible_mfderiv_val_regDom
    (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source) (y : RegDom g c) :
    letI := regDomChartedSpace g c hcov
    (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Subtype.val : RegDom g c → _) y).IsInvertible := by
  letI := regDomChartedSpace g c hcov
  rw [(hasMFDerivAt_val_regDom hcov y).mfderiv]
  exact isInvertible_fderiv_symm _ (Classical.choose_spec (hcov y))

/-- **The manifold boundary of `{g ≤ c}` is the level set `{g = c}`.** -/
theorem isBoundaryPoint_regDom_iff
    (hcov : ∀ y : RegDom g c, ∃ C : AdmChart g c, y.1 ∈ C.A.source) (y : RegDom g c) :
    letI := regDomChartedSpace g c hcov
    (𝓡∂ n).IsBoundaryPoint y ↔ g y.1 = c := by
  letI := regDomChartedSpace g c hcov
  set C := Classical.choose (hcov y)
  have hy : y.1 ∈ C.A.source := Classical.choose_spec (hcov y)
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace,
    mem_setOf_eq, extChartAt_regDom_self hcov y]
  have h1 := C.compat _ hy
  have h2 := C.compat_lt _ hy
  constructor
  · intro h
    exact le_antisymm (h1.1 h.symm.ge) (not_lt.1 fun h' => (h2.2 h').ne h)
  · intro h
    exact le_antisymm (not_lt.1 fun h' => (h2.1 h').ne h) (h1.2 h.le) |>.symm

/-- **Admissible charts from the inverse function theorem.** A smooth `Θ` whose first coordinate
is `≥ 0` exactly on `{g ≤ c}` and whose derivative at `p` is invertible gives an admissible chart
around `p`. -/
theorem exists_admChart_of_ift {Θ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hΘ : ContDiff ℝ ∞ Θ) (hcompat : ∀ y, (0 ≤ (Θ y) 0 ↔ g y ≤ c))
    (hcompat' : ∀ y, (0 < (Θ y) 0 ↔ g y < c)) {p : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hf' : HasFDerivAt Θ (f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) p) :
    ∃ C : AdmChart g c, p ∈ C.A.source := by
  set B := (hΘ.contDiffAt (x := p)).toOpenPartialHomeomorph Θ hf' (by simp)
  set U := {y | fderiv ℝ Θ y ∈ range ((↑) : (EuclideanSpace ℝ (Fin n) ≃L[ℝ]
    EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))}
  have hU : IsOpen U :=
    ContinuousLinearEquiv.isOpen.preimage (hΘ.continuous_fderiv (by simp))
  have hpU : p ∈ U := ⟨f', hf'.fderiv.symm⟩
  set A := B.restrOpen U hU
  have hBc : (B : _ → _) = Θ := rfl
  refine ⟨⟨A, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hΘ.contDiffOn
  · intro a ha
    have hsa : A.symm a ∈ A.source := A.map_target ha
    rw [OpenPartialHomeomorph.restrOpen_source] at hsa
    obtain ⟨φ, hφ⟩ := hsa.2
    have hd : HasFDerivAt A (φ : EuclideanSpace ℝ (Fin n) →L[ℝ] _) (A.symm a) := by
      rw [hφ]
      exact ((hΘ.differentiable (by simp)) _).hasFDerivAt
    exact (A.contDiffAt_symm ha hd (hΘ.contDiffAt)).contDiffWithinAt
  · intro y _; exact hcompat y
  · intro y _; exact hcompat' y
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hpU⟩

/-- **Admissible charts at interior points**: translations on a ball inside `{g ≤ c}`. -/
theorem exists_admChart_of_ball {q : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y ∈ Metric.ball q r, g y < c) : ∃ C : AdmChart g c, q ∈ C.A.source := by
  set v : EuclideanSpace ℝ (Fin n) := -q + (r + 1) • EuclideanSpace.single 0 1
  set A := (Homeomorph.addRight v).toOpenPartialHomeomorph.restrOpen (Metric.ball q r)
    Metric.isOpen_ball
  have hsrc : A.source = univ ∩ Metric.ball q r := by
    rw [OpenPartialHomeomorph.restrOpen_source]; rfl
  have hpos : ∀ y ∈ A.source, 0 < (A y) 0 := by
    intro y hy
    rw [hsrc] at hy
    have hy' : y ∈ Metric.ball q r := hy.2
    show 0 < (y + v) 0
    have h1 : |(y - q) 0| ≤ ‖y - q‖ := by
      have := PiLp.norm_apply_le (y - q) 0; rwa [Real.norm_eq_abs] at this
    have h2 : ‖y - q‖ < r := by rw [← dist_eq_norm]; exact hy'
    have e : (y + v) 0 = (y - q) 0 + (r + 1) := by
      simp [v, sub_eq_add_neg, add_assoc]
    rw [e]
    linarith [neg_abs_le ((y - q) 0)]
  have hlt : ∀ y ∈ A.source, g y < c := fun y hy => by
    rw [hsrc] at hy; exact hball y hy.2
  refine ⟨⟨A, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (contDiff_id.add contDiff_const).contDiffOn
  · exact (contDiff_id.add contDiff_const).contDiffOn
  · intro y hy
    exact ⟨fun _ => (hlt y hy).le, fun _ => (hpos y hy).le⟩
  · intro y hy
    exact ⟨fun _ => hlt y hy, fun _ => hpos y hy⟩
  · rw [hsrc]; exact ⟨mem_univ _, Metric.mem_ball_self hr⟩

end RegDom

end

end ExoticSpheres8And10
