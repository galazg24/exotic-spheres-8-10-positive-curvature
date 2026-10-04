/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Analysis.ParametricIntegral

/-! # Infrastructure: normalised Haar measure on `S³` and smooth parametric integrals

[GG] §3 Step 1 averages a connection over `S³` with "normalised Haar measure `dq`". Mathlib has
Haar measures on compact groups but no measurable structure on `ℍ` or `S³`, and no smoothness
statement for parametric integrals over a compact measure space.

* `haarS3`: the Borel structure on `S³` and its normalised Haar measure (a left-invariant
  probability measure);
* `contDiff_integral_param`: if `F : Z × Λ → X` is `C^n` and `ι : Y → Z` is continuous on a
  compact `Y` carrying a finite measure, then `λ ↦ ∫ F(ι y, λ) dμ(y)` is `C^n`.
-/

namespace ExoticSpheres8And10

open Set Filter Topology MeasureTheory Metric

open scoped ContDiff

noncomputable section

section Param

variable {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ] {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {ι : Y → Z} (hι : Continuous ι)

include hι in
theorem integrable_param {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Z × Λ → X} (hF : Continuous F) (x : Λ) : Integrable (fun y => F (ι y, x)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_range (hF.comp (hι.prodMk continuous_const))).isBounded.exists_norm_le
  refine Integrable.of_bound (C := C)
    (hF.comp (hι.prodMk continuous_const)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  exact hC _ ⟨y, rfl⟩

include hι in
/-- **Parametric integrals over a compact finite measure space of `C^n` integrands are `C^n`.** -/
theorem contDiff_integral_param (n : ℕ) :
    ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      {F : Z × Λ → X}, ContDiff ℝ n F →
      ContDiff ℝ n (fun x : Λ => ∫ y, F (ι y, x) ∂μ) := by
  induction n with
  | zero =>
    intro X _ _ _ F hF
    rw [Nat.cast_zero, contDiff_zero] at hF ⊢
    have h := continuous_parametric_integral_of_continuous (μ := μ) (f := fun x y => F (ι y, x))
      (hF.comp ((hι.comp continuous_snd).prodMk continuous_fst)) isCompact_univ
    simpa only [Measure.restrict_univ] using h
  | succ n ih =>
    intro X _ _ _ F hF
    have hdiff : Differentiable ℝ F := hF.differentiable (by exact_mod_cast Nat.succ_ne_zero n)
    have hF'c : ContDiff ℝ n (pderivΛ' F) := contDiff_pderivΛ' (by exact_mod_cast hF)
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun x => ∫ y, pderivΛ' F (ι y, x) ∂μ, ih hF'c,
      fun x₀ => ?_⟩
    have hcpt : IsCompact (range ι ×ˢ closedBall x₀ 1) :=
      (isCompact_range hι).prod (isCompact_closedBall x₀ 1)
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hF'c.continuous.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (F := fun x y => F (ι y, x)) (F' := fun x y => pderivΛ' F (ι y, x)) (μ := μ)
      (ball_mem_nhds x₀ one_pos) ?_ (integrable_param μ hι hF.continuous x₀) ?_ ?_
      (integrable_const C) ?_
    · exact Eventually.of_forall fun x =>
        (hF.continuous.comp (hι.prodMk continuous_const)).aestronglyMeasurable
    · exact (hF'c.continuous.comp (hι.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun y x hx => hC _ ⟨⟨y, rfl⟩, ball_subset_closedBall hx⟩
    · exact Eventually.of_forall fun y x _ => hasFDerivAt_param' hdiff (ι y) x

include hι in
theorem contDiff_integral_param_infty {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {F : Z × Λ → X} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x : Λ => ∫ y, F (ι y, x) ∂μ) :=
  contDiff_infty.2 fun n => contDiff_integral_param μ hι n (hF.of_le (by exact_mod_cast le_top))

end Param

section Haar

local notation "S3" => sphere (0 : Quaternion ℝ) 1

/-- The Borel structure on `S³`. -/
instance measurableSpaceS3 : MeasurableSpace S3 := borel S3

instance borelSpaceS3 : BorelSpace S3 := ⟨rfl⟩

/-- **Normalised Haar measure on `S³`.** -/
def haarS3 : Measure S3 := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts S3)

instance : IsProbabilityMeasure haarS3 :=
  ⟨by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts S3))
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at this⟩

instance : haarS3.IsMulLeftInvariant := by unfold haarS3; infer_instance

theorem integral_haarS3_mul_left {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : S3 → X) (a : S3) : ∫ q, f (a * q) ∂haarS3 = ∫ q, f q ∂haarS3 :=
  integral_mul_left_eq_self f a

theorem integral_haarS3_const {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (c : X) :
    ∫ _q, c ∂haarS3 = c := by rw [integral_const, probReal_univ, one_smul]

end Haar

end

end ExoticSpheres8And10
