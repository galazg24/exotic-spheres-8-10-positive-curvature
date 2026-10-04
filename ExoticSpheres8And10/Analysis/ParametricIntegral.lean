/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # Infrastructure: smoothness of parametric interval integrals

Mathlib has the first derivative of a parametric integral
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`) but no `C^n` statement.

* `contDiff_intervalIntegral_param`: if `F : ℝ × Λ → X` is `C^n` (`Λ` finite-dimensional), then
  `λ ↦ ∫_a^b F(s, λ) ds` is `C^n`.
-/

namespace ExoticSpheres8And10

open Set Filter Topology MeasureTheory intervalIntegral

open scoped ContDiff

variable {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]

/-- The partial derivative in the parameter. -/
noncomputable def pderivΛ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : ℝ × Λ → X) (p : ℝ × Λ) : Λ →L[ℝ] X :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ Λ)

theorem hasFDerivAt_param {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : ℝ × Λ → X} (hF : Differentiable ℝ F) (t : ℝ) (x : Λ) :
    HasFDerivAt (fun x => F (t, x)) (pderivΛ F (t, x)) x :=
  (hF (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)

theorem contDiff_pderivΛ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : ℝ × Λ → X} {n : ℕ} (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (pderivΛ F) :=
  (hF.fderiv_right (by exact_mod_cast le_rfl)).clm_comp contDiff_const

/-- The partial derivative in the second factor of `Z × Λ`. -/
noncomputable def pderivΛ' {Z X : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (F : Z × Λ → X) (p : Z × Λ) : Λ →L[ℝ] X :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ Z Λ)

theorem hasFDerivAt_param' {Z X : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Z × Λ → X} (hF : Differentiable ℝ F) (t : Z) (x : Λ) :
    HasFDerivAt (fun x => F (t, x)) (pderivΛ' F (t, x)) x :=
  (hF (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)

theorem contDiff_pderivΛ' {Z X : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Z × Λ → X} {n : ℕ} (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (pderivΛ' F) :=
  (hF.fderiv_right (by exact_mod_cast le_rfl)).clm_comp contDiff_const

/-- **Parametric interval integrals of `C^n` functions are `C^n`.** -/
theorem contDiff_intervalIntegral_param (n : ℕ) :
    ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      {F : ℝ × Λ → X}, ContDiff ℝ n F → ∀ a b : ℝ,
      ContDiff ℝ n (fun x : Λ => ∫ s in a..b, F (s, x)) := by
  induction n with
  | zero =>
    intro X _ _ _ F hF a b
    rw [Nat.cast_zero, contDiff_zero] at hF ⊢
    exact continuous_parametric_intervalIntegral_of_continuous' (f := fun x s => F (s, x))
      (hF.comp continuous_swap) a b
  | succ n ih =>
    intro X _ _ _ F hF a b
    have hdiff : Differentiable ℝ F := hF.differentiable (by exact_mod_cast Nat.succ_ne_zero n)
    have hF'c : ContDiff ℝ n (pderivΛ F) := contDiff_pderivΛ (by exact_mod_cast hF)
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun x => ∫ s in a..b, pderivΛ F (s, x), ih hF'c a b,
      fun x₀ => ?_⟩
    -- a bound on the parameter derivative near `x₀`
    have hcpt : IsCompact (uIcc a b ×ˢ Metric.closedBall x₀ 1) :=
      isCompact_uIcc.prod (isCompact_closedBall x₀ 1)
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hF'c.continuous.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (F := fun x t => F (t, x)) (F' := fun x t => pderivΛ F (t, x)) (μ := volume) (a := a) (b := b)
      (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun x =>
        (hF.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hF.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact (hF'c.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht x hx => hC (t, x) ⟨?_, ?_⟩
      · exact uIoc_subset_uIcc ht
      · exact Metric.ball_subset_closedBall hx
    · exact Eventually.of_forall fun t _ x _ => hasFDerivAt_param hdiff t x

theorem contDiff_intervalIntegral_param_infty {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {F : ℝ × Λ → X} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : Λ => ∫ s in a..b, F (s, x)) :=
  contDiff_infty.2 fun n => contDiff_intervalIntegral_param n (hF.of_le (by exact_mod_cast le_top)) a b

end ExoticSpheres8And10
