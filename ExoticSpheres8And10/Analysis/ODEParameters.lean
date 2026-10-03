/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.StarBundles.Transport
import ExoticSpheres8And10.Analysis.ParametricIntegral

/-! # Infrastructure: smooth dependence of the transport equation on parameters

Mathlib has no smooth dependence of ODE solutions on parameters. For the quaternionic transport
equation `u' = M(s, λ) u`, `u(0) = 1`, with `M` smooth and `Im ℍ`-valued (so `‖u‖ ≡ 1`), we prove
that the time-one map `λ ↦ u_λ(1)` is `C^∞` (`contDiff_T`), and that `(s, λ) ↦ u_λ(s)` is `C^∞`
on `[0,1] × Λ` (`sol_eq_T_reparam`, `contDiff_T`).

Method: the Duhamel identity
`u_λ(s) = u_{λ₀}(s) (1 + ∫₀^s u_{λ₀}(r)* (M(r,λ) − M(r,λ₀)) u_λ(r) dr)` (`duhamel`) gives
Lipschitz dependence and the derivative
`D_λ u_λ(1) h = u_λ(1) ∫₀¹ u_λ(r)* ∂_λM(r,λ)h u_λ(r) dr`; induction on the order uses
the reparametrisation `u_λ(s) = ũ_{(s,λ)}(1)` with `M̃(σ,(s,λ)) = s M(sσ, λ)`.
-/

namespace ExoticSpheres8And10

open Set Filter Topology MeasureTheory intervalIntegral

open scoped ContDiff Interval

open Quaternion

noncomputable section

/-- Smooth imaginary coefficients `M : ℝ × Λ → Im ℍ`. -/
structure LinCoeff (Λ : Type) [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] where
  M : ℝ × Λ → ℍ[ℝ]
  smooth : ContDiff ℝ ∞ M
  pure : ∀ p, (M p).re = 0

namespace LinCoeff

variable {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] (C : LinCoeff Λ)

theorem continuous_M_slice (x : Λ) : Continuous fun s : ℝ => C.M (s, x) :=
  C.smooth.continuous.comp (continuous_id.prodMk continuous_const)

theorem exists_sol (x : Λ) : ∃ u : ℝ → ℍ[ℝ], u 0 = 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ = 1) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (C.M (t, x) * u t) (Icc 0 1) t :=
  exists_transport (fun s => C.M (s, x))
  (C.continuous_M_slice x).continuousOn (fun s => C.pure _) 0 ⟨le_rfl, zero_le_one⟩

/-- The solution `u_λ` of `u' = M(·, λ) u`, `u(0) = 1`, on `[0,1]`. -/
def sol (x : Λ) : ℝ → ℍ[ℝ] := Classical.choose (C.exists_sol x)

theorem sol_zero (x : Λ) : C.sol x 0 = 1 := (Classical.choose_spec (C.exists_sol x)).1

theorem norm_sol (x : Λ) : ∀ s ∈ Icc (0 : ℝ) 1, ‖C.sol x s‖ = 1 :=
  (Classical.choose_spec (C.exists_sol x)).2.1

theorem hasDeriv_sol (x : Λ) :
    ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (C.sol x) (C.M (s, x) * C.sol x s) (Icc 0 1) s :=
  (Classical.choose_spec (C.exists_sol x)).2.2

theorem continuousOn_sol (x : Λ) : ContinuousOn (C.sol x) (Icc 0 1) :=
  fun s hs => (C.hasDeriv_sol x s hs).continuousWithinAt

/-- **The time-one map.** -/
def T (x : Λ) : ℍ[ℝ] := C.sol x 1

/-- Uniqueness: any solution on `[0,1]` with value `1` at `0` is `sol`. -/
theorem sol_unique (x : Λ) (u : ℝ → ℍ[ℝ]) (hu0 : u 0 = 1)
    (hu : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (C.M (s, x) * u s) (Icc 0 1) s) :
    ∀ s ∈ Icc (0 : ℝ) 1, u s = C.sol x s := by
  obtain ⟨b, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (C.continuous_M_slice x).continuousOn (s := Icc (0 : ℝ) 1)
  exact transport_unique (fun s => C.M (s, x)) ⟨max b 0, le_max_right _ _⟩
    (fun t ht => (hb t ht).trans (le_max_left _ _)) u (C.sol x) hu (C.hasDeriv_sol x) 0
    ⟨le_rfl, zero_le_one⟩ (by rw [hu0, C.sol_zero])

theorem star_of_pure {q : ℍ[ℝ]} (h : q.re = 0) : star q = -q := by
  ext <;> simp [h]

/-- The derivative of `D(r) = u_{λ₀}(r)* u_λ(r)`. -/
theorem hasDeriv_D (x x₀ : Λ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun r => star (C.sol x₀ r) * C.sol x r)
      (star (C.sol x₀ r) * (C.M (r, x) - C.M (r, x₀)) * C.sol x r) (Icc 0 1) r := by
  have h := ((C.hasDeriv_sol x₀ r hr).star).mul (C.hasDeriv_sol x r hr)
  refine h.congr_deriv ?_
  rw [star_mul, star_of_pure (C.pure _)]
  noncomm_ring

theorem continuousOn_D' (x x₀ : Λ) : ContinuousOn
    (fun r => star (C.sol x₀ r) * (C.M (r, x) - C.M (r, x₀)) * C.sol x r) (Icc 0 1) :=
  ((((C.continuousOn_sol x₀).star).mul (((C.continuous_M_slice x).sub
    (C.continuous_M_slice x₀)).continuousOn)).mul (C.continuousOn_sol x))

/-- **The Duhamel identity.** -/
theorem duhamel (x x₀ : Λ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    C.sol x s = C.sol x₀ s * (1 + ∫ r in (0 : ℝ)..s,
      star (C.sol x₀ r) * (C.M (r, x) - C.M (r, x₀)) * C.sol x r) := by
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hs.2
  have hFTC := integral_eq_sub_of_hasDeriv_right_of_le hs.1
    (f := fun r => star (C.sol x₀ r) * C.sol x r)
    ((((C.continuousOn_sol x₀).star).mul (C.continuousOn_sol x)).mono hsub)
    (fun r hr => by
      have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, lt_of_lt_of_le hr.2 hs.2⟩
      exact ((C.hasDeriv_D x x₀ r (Ioo_subset_Icc_self hr1)).hasDerivAt
        (Icc_mem_nhds hr1.1 hr1.2)).hasDerivWithinAt)
    (((C.continuousOn_D' x x₀).mono hsub).intervalIntegrable_of_Icc hs.1)
  rw [hFTC, C.sol_zero, C.sol_zero, star_one, one_mul, add_sub_cancel, ← mul_assoc,
    mul_star_of_norm_one (C.norm_sol x₀ s hs), one_mul]

/-- **Lipschitz-type estimate**: `‖u_λ(s) − u_{λ₀}(s)‖ ≤ sup_r ‖M(r,λ) − M(r,λ₀)‖`. -/
theorem norm_sol_sub_le (x x₀ : Λ) (ε : ℝ)
    (hε : ∀ r ∈ Icc (0 : ℝ) 1, ‖C.M (r, x) - C.M (r, x₀)‖ ≤ ε) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖C.sol x s - C.sol x₀ s‖ ≤ ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0 ⟨le_rfl, zero_le_one⟩)
  rw [C.duhamel x x₀ s hs, mul_add, mul_one, add_sub_cancel_left, norm_mul,
    C.norm_sol x₀ s hs, one_mul]
  have hb : ∀ r ∈ Ι (0 : ℝ) s,
      ‖star (C.sol x₀ r) * (C.M (r, x) - C.M (r, x₀)) * C.sol x r‖ ≤ ε := by
    intro r hr
    rw [uIoc_of_le hs.1] at hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.trans hs.2⟩
    rw [norm_mul, norm_mul, norm_star, C.norm_sol x₀ r hr', C.norm_sol x r hr', one_mul,
      mul_one]
    exact hε r hr'
  calc _ ≤ ε * |s - 0| := norm_integral_le_of_norm_le_const hb
    _ ≤ ε * 1 := by
        gcongr; rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2
    _ = ε := mul_one ε

end LinCoeff

/-! ### Bounds from smoothness on compact sets -/

section Bounds

variable {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]

/-- A `C¹` function of `(r, x)` is Lipschitz in `x`, uniformly for `r ∈ [0,1]`, near `x₀`. -/
theorem exists_lip {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : ℝ × Λ → X}
    (hF : ContDiff ℝ 1 F) (x₀ : Λ) : ∃ K ≥ 0, ∀ r ∈ Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall x₀ 1,
      ∀ y ∈ Metric.closedBall x₀ 1, ‖F (r, y) - F (r, x)‖ ≤ K * ‖y - x‖ := by
  have hc : Continuous (pderivΛ F) := by
    have := contDiff_pderivΛ (n := 0) (by simpa using hF)
    exact this.continuous
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
    hc.continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x₀ 1)
  refine ⟨max K 0, le_max_right _ _, fun r hr x hx y hy => ?_⟩
  refine (convex_closedBall x₀ 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => F (r, z)) (f' := fun z => pderivΛ F (r, z)) (fun z _ =>
      (hasFDerivAt_param (hF.differentiable (by norm_num)) r z).hasFDerivWithinAt)
    (fun z hz => (hK (r, z) ⟨hr, hz⟩).trans (le_max_left _ _)) hx hy

/-- Second-order Taylor bound in the parameter, uniformly for `r ∈ [0,1]`. -/
theorem exists_taylor2 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : ℝ × Λ → X}
    (hF : ContDiff ℝ 2 F) (x₀ : Λ) : ∃ K ≥ 0, ∀ r ∈ Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall x₀ 1,
      ‖F (r, x) - F (r, x₀) - pderivΛ F (r, x₀) (x - x₀)‖ ≤ K * ‖x - x₀‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_lip (F := pderivΛ F) (contDiff_pderivΛ (n := 1) hF) x₀
  refine ⟨K, hK0, fun r hr x hx => ?_⟩
  have hseg : segment ℝ x₀ x ⊆ Metric.closedBall x₀ 1 :=
    (convex_closedBall x₀ 1).segment_subset (Metric.mem_closedBall_self zero_le_one) hx
  have hmv := (convex_segment x₀ x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => F (r, z) - pderivΛ F (r, x₀) z)
    (f' := fun z => pderivΛ F (r, z) - pderivΛ F (r, x₀)) (C := K * ‖x - x₀‖)
    (fun z _ => ((hasFDerivAt_param (hF.differentiable (by norm_num)) r z).sub
      (pderivΛ F (r, x₀)).hasFDerivAt).hasFDerivWithinAt)
    (fun z hz => by
      refine (hK r hr x₀ (Metric.mem_closedBall_self zero_le_one) z (hseg hz)).trans ?_
      gcongr
      have h1 := segment_subset_closedBall_left x₀ x hz
      rw [Metric.mem_closedBall, dist_eq_norm, dist_comm, dist_eq_norm] at h1
      exact h1)
    (left_mem_segment ℝ x₀ x) (right_mem_segment ℝ x₀ x)
  calc _ = ‖(F (r, x) - pderivΛ F (r, x₀) x) - (F (r, x₀) - pderivΛ F (r, x₀) x₀)‖ := by
        congr 1; rw [map_sub]; abel
    _ ≤ K * ‖x - x₀‖ * ‖x - x₀‖ := hmv
    _ = K * ‖x - x₀‖ ^ 2 := by ring

end Bounds


/-! ### Continuity, derivative, and smoothness of the time-one map -/

namespace LinCoeff

variable {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  (C : LinCoeff Λ)

theorem smooth_n (n : ℕ) : ContDiff ℝ n C.M := C.smooth.of_le (by exact_mod_cast le_top)

theorem exists_lip_sol (x₀ : Λ) : ∃ K ≥ 0, ∀ x ∈ Metric.closedBall x₀ 1, ∀ s ∈ Icc (0 : ℝ) 1,
    ‖C.sol x s - C.sol x₀ s‖ ≤ K * ‖x - x₀‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_lip (C.smooth_n 1) x₀
  exact ⟨K, hK0, fun x hx s hs => C.norm_sol_sub_le x x₀ _
    (fun r hr => hK r hr x₀ (Metric.mem_closedBall_self zero_le_one) x hx) s hs⟩

theorem continuous_T : Continuous C.T := by
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.continuousAt_iff.2 fun ε hε => ?_
  obtain ⟨K, hK0, hK⟩ := C.exists_lip_sol x₀
  refine ⟨min 1 (ε / (K + 1)), by positivity, fun x hx => ?_⟩
  have hx1 : x ∈ Metric.closedBall x₀ 1 := le_of_lt (lt_of_lt_of_le hx (min_le_left _ _))
  have hx2 : ‖x - x₀‖ < ε / (K + 1) := by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_right _ _)
  rw [dist_eq_norm]
  calc ‖C.T x - C.T x₀‖ ≤ K * ‖x - x₀‖ := hK x hx1 1 ⟨zero_le_one, le_rfl⟩
    _ ≤ (K + 1) * ‖x - x₀‖ := by nlinarith [norm_nonneg (x - x₀)]
    _ < (K + 1) * (ε / (K + 1)) := by gcongr
    _ = ε := by field_simp

/-- Conjugation `v ↦ u* v u`. -/
def conjL (u : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := ContinuousLinearMap.mulLeftRight ℝ ℍ[ℝ] (star u) u

theorem conjL_apply (u v : ℍ[ℝ]) : conjL u v = star u * v * u := by
  simp [conjL, ContinuousLinearMap.mulLeftRight_apply]

theorem contDiff_conjL : ContDiff ℝ ∞ conjL :=
  ((ContinuousLinearMap.mulLeftRight ℝ ℍ[ℝ]).contDiff.comp
    (starL' ℝ : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]).contDiff).clm_apply contDiff_id

/-- The reparametrised coefficients `M̃(σ, (s, x)) = s M(sσ, x)`. -/
def rep : LinCoeff (ℝ × Λ) where
  M p := p.2.1 • C.M (p.2.1 * p.1, p.2.2)
  smooth := (contDiff_snd.fst).smul (C.smooth.comp
    ((contDiff_snd.fst.mul contDiff_fst).prodMk contDiff_snd.snd))
  pure p := by simp [C.pure]

/-- **Reparametrisation**: `u_x(s) = ũ_{(s,x)}(1)` for `s ∈ [0,1]`. -/
theorem rep_T (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : Λ) : C.rep.T (s, x) = C.sol x s := by
  have hmaps : MapsTo (fun σ : ℝ => s * σ) (Icc 0 1) (Icc 0 1) := fun σ hσ =>
    ⟨mul_nonneg hs.1 hσ.1, mul_le_one₀ hs.2 hσ.1 hσ.2⟩
  have hu : ∀ σ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun σ => C.sol x (s * σ))
      (C.rep.M (σ, (s, x)) * C.sol x (s * σ)) (Icc 0 1) σ := by
    intro σ hσ
    have h1 := (C.hasDeriv_sol x (s * σ) (hmaps hσ)).scomp σ
      ((hasDerivWithinAt_id σ (Icc 0 1)).const_mul s) hmaps
    refine h1.congr_deriv ?_
    show (s * 1) • (C.M (s * σ, x) * C.sol x (s * σ)) = (s • C.M (s * σ, x)) * C.sol x (s * σ)
    rw [mul_one, smul_mul_assoc]
  have := C.rep.sol_unique (s, x) (fun σ => C.sol x (s * σ)) (by simp [C.sol_zero]) hu 1
    ⟨zero_le_one, le_rfl⟩
  rw [T, ← this, mul_one]

/-- The derivative of the time-one map. -/
def L (x : Λ) : Λ →L[ℝ] ℍ[ℝ] :=
  (ContinuousLinearMap.mul ℝ ℍ[ℝ] (C.T x)).comp
    (∫ r in (0 : ℝ)..1, (conjL (C.rep.T (r, x))).comp (pderivΛ C.M (r, x)))

theorem continuous_G (x : Λ) :
    Continuous fun r : ℝ => (conjL (C.rep.T (r, x))).comp (pderivΛ C.M (r, x)) :=
  ((contDiff_conjL.continuous.comp (C.rep.continuous_T.comp (continuous_id.prodMk
    continuous_const))).clm_comp ((contDiff_pderivΛ (n := 0) (by simpa using C.smooth_n 1)
    ).continuous.comp (continuous_id.prodMk continuous_const)))

theorem L_apply (x h : Λ) : C.L x h = C.T x * ∫ r in (0 : ℝ)..1,
    star (C.sol x r) * pderivΛ C.M (r, x) h * C.sol x r := by
  rw [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.intervalIntegral_apply ((C.continuous_G x).intervalIntegrable 0 1)]
  congr 1
  refine integral_congr fun r hr => ?_
  rw [uIcc_of_le zero_le_one] at hr
  simp only [ContinuousLinearMap.comp_apply, conjL_apply, C.rep_T r hr]

/-- **The time-one map is differentiable**, with derivative `L`. -/
theorem hasFDerivAt_T (x₀ : Λ) : HasFDerivAt C.T (C.L x₀) x₀ := by
  obtain ⟨Kl, hKl0, hKl⟩ := C.exists_lip_sol x₀
  obtain ⟨K2, hK20, hK2⟩ := exists_taylor2 (C.smooth_n 2) x₀
  obtain ⟨Kd, hKd⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((contDiff_pderivΛ (n := 0) (by simpa using C.smooth_n 1)).continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn (s := Icc (0 : ℝ) 1)
    (f := fun r => pderivΛ C.M (r, x₀))
  have hKd0 : 0 ≤ Kd := (norm_nonneg _).trans (hKd 0 ⟨le_rfl, zero_le_one⟩)
  -- the quadratic remainder bound
  have hbound : ∀ h ∈ Metric.closedBall (0 : Λ) 1,
      ‖C.T (x₀ + h) - C.T x₀ - C.L x₀ h‖ ≤ (K2 + Kd * Kl) * ‖h‖ ^ 2 := by
    intro h hh
    have hx : x₀ + h ∈ Metric.closedBall x₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      simpa using hh
    have hD := C.duhamel (x₀ + h) x₀ 1 ⟨zero_le_one, le_rfl⟩
    have hint1 := (C.continuousOn_D' (x₀ + h) x₀).intervalIntegrable_of_Icc (μ := volume)
      zero_le_one
    have hcont2 : ContinuousOn (fun r => star (C.sol x₀ r) * pderivΛ C.M (r, x₀) h * C.sol x₀ r)
        (Icc 0 1) :=
      (((C.continuousOn_sol x₀).star).mul (((contDiff_pderivΛ (n := 0)
        (by simpa using C.smooth_n 1)).continuous.comp (continuous_id.prodMk continuous_const)
        ).clm_apply continuous_const).continuousOn).mul (C.continuousOn_sol x₀)
    have hint2 := hcont2.intervalIntegrable_of_Icc (μ := volume) zero_le_one
    have heq : C.T (x₀ + h) - C.T x₀ - C.L x₀ h = C.T x₀ * ∫ r in (0 : ℝ)..1,
        (star (C.sol x₀ r) * (C.M (r, x₀ + h) - C.M (r, x₀)) * C.sol (x₀ + h) r -
          star (C.sol x₀ r) * pderivΛ C.M (r, x₀) h * C.sol x₀ r) := by
      rw [intervalIntegral.integral_sub hint1 hint2, mul_sub, C.L_apply, ← sub_add_eq_sub_sub_swap]
      simp only [T] at hD ⊢
      rw [hD]; noncomm_ring
    rw [heq, norm_mul, show C.T x₀ = C.sol x₀ 1 from rfl, C.norm_sol x₀ 1 ⟨zero_le_one, le_rfl⟩,
      one_mul]
    have hpt : ∀ r ∈ Ι (0 : ℝ) 1,
        ‖star (C.sol x₀ r) * (C.M (r, x₀ + h) - C.M (r, x₀)) * C.sol (x₀ + h) r -
          star (C.sol x₀ r) * pderivΛ C.M (r, x₀) h * C.sol x₀ r‖ ≤ (K2 + Kd * Kl) * ‖h‖ ^ 2 := by
      intro r hr
      rw [uIoc_of_le zero_le_one] at hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2⟩
      have hsplit : star (C.sol x₀ r) * (C.M (r, x₀ + h) - C.M (r, x₀)) * C.sol (x₀ + h) r -
          star (C.sol x₀ r) * pderivΛ C.M (r, x₀) h * C.sol x₀ r =
          star (C.sol x₀ r) * ((C.M (r, x₀ + h) - C.M (r, x₀) - pderivΛ C.M (r, x₀) h) *
            C.sol (x₀ + h) r + pderivΛ C.M (r, x₀) h * (C.sol (x₀ + h) r - C.sol x₀ r)) := by
        noncomm_ring
      rw [hsplit, norm_mul, norm_star, C.norm_sol x₀ r hr', one_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, C.norm_sol (x₀ + h) r hr', mul_one]
      have h1 := hK2 r hr' (x₀ + h) hx
      rw [add_sub_cancel_left] at h1
      have h2 := hKl (x₀ + h) hx r hr'
      rw [add_sub_cancel_left] at h2
      have h3 : ‖pderivΛ C.M (r, x₀) h‖ ≤ Kd * ‖h‖ :=
        ((pderivΛ C.M (r, x₀)).le_opNorm h).trans (by gcongr; exact hKd r hr')
      calc _ ≤ K2 * ‖h‖ ^ 2 + Kd * ‖h‖ * (Kl * ‖h‖) := by gcongr
        _ = (K2 + Kd * Kl) * ‖h‖ ^ 2 := by ring
    calc _ ≤ (K2 + Kd * Kl) * ‖h‖ ^ 2 * |1 - 0| := norm_integral_le_of_norm_le_const hpt
      _ = (K2 + Kd * Kl) * ‖h‖ ^ 2 := by norm_num
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound (K2 + Kd * Kl) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  filter_upwards [Metric.closedBall_mem_nhds (0 : Λ) one_pos] with h hh
  rw [Real.norm_of_nonneg (by positivity)]
  exact hbound h hh

/-- **Smooth dependence on parameters**: the time-one map is `C^k` for every `k`. -/
theorem contDiff_T_nat (k : ℕ) : ∀ {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    [FiniteDimensional ℝ Λ] (C : LinCoeff Λ), ContDiff ℝ k C.T := by
  induction k with
  | zero => intro Λ _ _ _ C; rw [Nat.cast_zero, contDiff_zero]; exact C.continuous_T
  | succ k ih =>
    intro Λ _ _ _ C
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨C.L, ?_, C.hasFDerivAt_T⟩
    have hG : ContDiff ℝ k (fun p : ℝ × Λ => (conjL (C.rep.T p)).comp (pderivΛ C.M p)) :=
      ((contDiff_conjL.of_le (by exact_mod_cast le_top)).comp (ih C.rep)).clm_comp
        (contDiff_pderivΛ (n := k) (by exact_mod_cast C.smooth_n (k + 1)))
    exact ((ContinuousLinearMap.mul ℝ ℍ[ℝ]).contDiff.comp (ih C)).clm_comp
      (contDiff_intervalIntegral_param k hG 0 1)

/-- **The time-one map is `C^∞`.** -/
theorem contDiff_T : ContDiff ℝ ∞ C.T := contDiff_infty.2 fun k => contDiff_T_nat k C

/-- **Joint smoothness**: `(s, x) ↦ u_x(s)` agrees on `[0,1] × Λ` with the `C^∞` map
`(s, x) ↦ ũ_{(s,x)}(1)`. -/
theorem contDiff_sol_joint : ContDiff ℝ ∞ C.rep.T ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, C.rep.T (s, x) = C.sol x s :=
  ⟨C.rep.contDiff_T, fun s hs x => C.rep_T s hs x⟩

end LinCoeff

end

end ExoticSpheres8And10
