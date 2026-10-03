/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.ProfilesExistence

/-! # A7 at the centre: polar smoothness conditions and the curvature `δ⁻²`

[D] §5 (northern filling): "The inverse of the odd function `F ↦ ∫₀^F e^{z²/(2δ²)}dz` is smooth
and odd, with `F(s) = s − s³/(6δ²) + O(s⁵)`. As `r` is constant near zero, these are the polar
smoothness conditions for `eq:north`. [...] The latter has sectional curvature `δ⁻²`, proving
positivity there directly."

* `G_neg`, `Fprof_neg`: `G` and `F = G⁻¹` are odd;
* `Fprof_contDiff`: `F` is `C^∞` (bootstrap from `F' = e^{−F²/2δ²}`);
* `Fprof_deriv_zero`, `Fprof_second_zero`, `Fprof_third_zero`: `F'(0) = 1`, `F''(0) = 0`,
  `F'''(0) = −1/δ²`, i.e. the Taylor coefficients of `s − s³/(6δ²)`;
* `rprof_const_near_zero`: `r` is constant on `(−∞, δ/4]`;
* `radial_curv_tendsto`, `tangential_curv_tendsto`: the radial curvature `−F''/F` and the
  tangential curvature `(1 − F'²)/F²` of `ds² + F(s)² g_{S^{n−1}}` both tend to `δ⁻²` at the
  centre.

Imported, not formalised: the standard lemma that these conditions make the polar metric smooth
at the centre, and the warped-product curvature formulas themselves.
-/

namespace ExoticSpheres8And10

open Real intervalIntegral MeasureTheory Filter Topology Set

open scoped ContDiff

/-- `F' = e^{−F²/(2δ²)}`. -/
noncomputable def Fder (δ s : ℝ) : ℝ := Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2))

theorem G_neg (δ z : ℝ) : Gδ δ (-z) = -Gδ δ z := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := z)
    (fun t : ℝ => Real.exp (t ^ 2 / (2 * δ ^ 2)))
  simp only [neg_sq, neg_zero] at h
  rw [Gδ, Gδ, h, intervalIntegral.integral_symm 0 (-z), neg_neg]

/-- **`F` is odd.** -/
theorem Fprof_neg (δ s : ℝ) : Fprof δ (-s) = -Fprof δ s := by
  apply (G_strictMono δ).injective
  rw [G_Fprof, G_neg, G_Fprof]

theorem Fprof_ne_zero {δ s : ℝ} (hs : s ≠ 0) : Fprof δ s ≠ 0 := by
  intro h
  apply hs
  have := G_Fprof δ s
  rw [h, G_zero] at this
  exact this.symm

theorem deriv_Fprof (δ : ℝ) : deriv (Fprof δ) = Fder δ :=
  funext fun s => (hasDerivAt_Fprof δ s).deriv

/-- **`F` is `C^∞`.** -/
theorem Fprof_contDiff (δ : ℝ) : ContDiff ℝ ∞ (Fprof δ) := by
  have hdiff : Differentiable ℝ (Fprof δ) := fun s => (hasDerivAt_Fprof δ s).differentiableAt
  have key : ∀ k : ℕ, ContDiff ℝ k (Fprof δ) := by
    intro k
    induction k with
    | zero => exact contDiff_zero.2 (Fprof_continuous δ)
    | succ k ih =>
      have : ContDiff ℝ ((k : WithTop ℕ∞) + 1) (Fprof δ) := by
        rw [contDiff_succ_iff_deriv]
        refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
        rw [deriv_Fprof]
        exact Real.contDiff_exp.comp ((ih.pow 2).neg.div_const _)
      exact_mod_cast this
  exact contDiff_infty.2 key

theorem Fprof_deriv_zero (δ : ℝ) : HasDerivAt (Fprof δ) 1 0 := by
  have h := hasDerivAt_Fprof δ 0
  rwa [Fprof_zero, show (-(0 : ℝ) ^ 2 / (2 * δ ^ 2)) = 0 by ring, Real.exp_zero] at h

theorem Fprof_second_zero (δ : ℝ) (hδ : δ ≠ 0) : HasDerivAt (Fder δ) 0 0 := by
  have h := hasDerivAt_Fprof' δ 0 hδ
  rw [Fprof_zero, zero_div, neg_zero, zero_mul] at h
  exact h

/-- **`F'''(0) = −1/δ²`**: `F''` is `−(F/δ²)F'²`, whose derivative at `0` is `−1/δ²`. -/
theorem Fprof_third_zero (δ : ℝ) (hδ : δ ≠ 0) :
    HasDerivAt (fun s => -(Fprof δ s / δ ^ 2) * Fder δ s ^ 2) (-(1 / δ ^ 2)) 0 := by
  have h := ((Fprof_deriv_zero δ).div_const (δ ^ 2)).neg.mul ((hasDerivAt_Fprof' δ 0 hδ).pow 2)
  refine h.congr_deriv ?_
  simp [Fprof_zero]

/-- **`r` is constant near the centre.** -/
theorem rprof_const_near_zero {ra d δ ℓ s : ℝ} (hδ : 0 < δ) (hs : s ≤ δ / 4) :
    rprof ra d δ ℓ s = rprof ra d δ ℓ (δ / 4) := by
  have hi := fun a b => (continuous_eta_div δ).intervalIntegrable (μ := volume) a b
  have h0 : ∫ v in s..δ / 4, etaCut (v / δ) = 0 := by
    have heq : EqOn (fun v => etaCut (v / δ)) (fun _ => (0 : ℝ)) (uIcc s (δ / 4)) := by
      intro v hv
      rw [uIcc_of_le hs] at hv
      exact etaCut_zero (by rw [div_le_iff₀ hδ]; linarith [hv.2])
    rw [intervalIntegral.integral_congr heq]; simp
  simp only [rprof]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi s (δ / 4)) (hi (δ / 4) ℓ), h0,
    zero_add]

theorem continuous_Fder (δ : ℝ) : Continuous (Fder δ) :=
  Real.continuous_exp.comp (((Fprof_continuous δ).pow 2).neg.div_const _)

theorem Fder_zero (δ : ℝ) : Fder δ 0 = 1 := by
  simp [Fder, Fprof_zero]

/-- **Radial curvature at the centre:** `−F''/F = (F/δ²)F'²/F → δ⁻²`. -/
theorem radial_curv_tendsto (δ : ℝ) :
    Tendsto (fun s => (Fprof δ s / δ ^ 2) * Fder δ s ^ 2 / Fprof δ s) (𝓝[≠] 0)
      (𝓝 (1 / δ ^ 2)) := by
  have hc : Tendsto (fun s => Fder δ s ^ 2 / δ ^ 2) (𝓝[≠] 0) (𝓝 (1 / δ ^ 2)) := by
    have := (((continuous_Fder δ).pow 2).div_const (δ ^ 2)).tendsto 0
    simp only [Pi.pow_apply, Fder_zero, one_pow] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine hc.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
  have hF := Fprof_ne_zero (δ := δ) hs
  field_simp

/-- **Tangential curvature at the centre:** `(1 − F'²)/F² → δ⁻²`. -/
theorem tangential_curv_tendsto (δ : ℝ) :
    Tendsto (fun s => (1 - Fder δ s ^ 2) / Fprof δ s ^ 2) (𝓝[≠] 0) (𝓝 (1 / δ ^ 2)) := by
  -- `h(u) = 1 − e^{−u/δ²}` has `h(0) = 0`, `h'(0) = 1/δ²`
  have hh : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u / δ ^ 2)) (1 / δ ^ 2) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).neg.div_const (δ ^ 2)).exp).const_sub 1
    refine this.congr_deriv ?_
    simp [neg_div]
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hh)
  -- `u(s) = F(s)²` tends to `0` through nonzero values
  have hu : Tendsto (fun s => Fprof δ s ^ 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs =>
      pow_ne_zero 2 (Fprof_ne_zero hs)⟩
    have := ((Fprof_continuous δ).pow 2).tendsto 0
    simp only [Pi.pow_apply, Fprof_zero] at this
    rw [zero_pow two_ne_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (hslope.comp hu).congr' (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, zero_add, neg_zero, zero_div, Real.exp_zero, sub_self,
    sub_zero, smul_eq_mul, Fder]
  rw [← Real.exp_nat_mul]
  field_simp
  ring_nf

/-- Positivity at the centre: the limiting curvature `δ⁻²` is positive. -/
theorem centre_curv_pos {δ : ℝ} (hδ : δ ≠ 0) : 0 < 1 / δ ^ 2 := by positivity

end ExoticSpheres8And10
