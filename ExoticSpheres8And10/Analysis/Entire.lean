/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # Infrastructure: `cos √v` and `sin √v / √v` are smooth

The even functions `cos τ` and `sin τ / τ` are smooth functions of `v = τ²`. They are the entire
functions `Σ (−1)ⁿ vⁿ/(2n)!` and `Σ (−1)ⁿ vⁿ/(2n+1)!`. Smoothness at `v = 0` is what makes polar
coordinates smooth at the centre of a disk without Whitney's theorem on even functions.

* `cosSq`, `sincSq`: the two power series, `C^∞` on `ℝ` (`contDiff_cosSq`, `contDiff_sincSq`);
* `cosSq_sq : cosSq (τ²) = cos τ`, `sincSq_sq : τ · sincSq (τ²) = sin τ`, `sincSq_zero`.
-/

namespace ExoticSpheres8And10

open Filter Topology Real

open scoped ContDiff

noncomputable section

/-- The coefficients `(−1)ⁿ/(2n)!`. -/
def cCos (n : ℕ) : ℝ := (-1) ^ n / ((2 * n).factorial : ℝ)

/-- The coefficients `(−1)ⁿ/(2n+1)!`. -/
def cSinc (n : ℕ) : ℝ := (-1) ^ n / ((2 * n + 1).factorial : ℝ)

theorem ratio_tendsto_zero {c : ℕ → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hc : ∀ n : ℕ, ‖c (n + 1)‖ / ‖c n‖ = 1 / ((2 * (n : ℝ) + k + 1) * (2 * n + k + 2))) :
    Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0) := by
  simp only [Nat.succ_eq_add_one, hc]
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem cCos_ratio (n : ℕ) :
    ‖cCos (n + 1)‖ / ‖cCos n‖ = 1 / ((2 * (n : ℝ) + 0 + 1) * (2 * n + 0 + 2)) := by
  simp only [cCos, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
  field_simp
  ring

theorem cSinc_ratio (n : ℕ) :
    ‖cSinc (n + 1)‖ / ‖cSinc n‖ = 1 / ((2 * (n : ℝ) + 1 + 1) * (2 * n + 1 + 2)) := by
  simp only [cSinc, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]
  rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have : (0 : ℝ) < (2 * n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  field_simp
  ring

theorem radius_cCos : (FormalMultilinearSeries.ofScalars ℝ cCos).radius = ⊤ :=
  FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℝ _
    (Eventually.of_forall fun n => by simp [cCos, Nat.factorial_ne_zero])
    (ratio_tendsto_zero le_rfl cCos_ratio)

theorem radius_cSinc : (FormalMultilinearSeries.ofScalars ℝ cSinc).radius = ⊤ :=
  FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℝ _
    (Eventually.of_forall fun n => by simp [cSinc, Nat.factorial_ne_zero])
    (ratio_tendsto_zero zero_le_one cSinc_ratio)

/-- An entire power series is `C^∞`. -/
theorem contDiff_sum_of_radius_top {p : FormalMultilinearSeries ℝ ℝ ℝ} (hp : p.radius = ⊤) :
    ContDiff ℝ ∞ p.sum := by
  have h := p.hasFPowerSeriesOnBall (by rw [hp]; exact ENNReal.zero_lt_top)
  refine AnalyticOnNhd.contDiff fun x _ => ?_
  have hx : x ∈ EMetric.ball (0 : ℝ) p.radius := by rw [hp]; exact EMetric.mem_ball.2 (by simp)
  exact h.analyticAt_of_mem hx

/-- `cos √v`, as an entire function of `v`. -/
def cosSq (v : ℝ) : ℝ := (FormalMultilinearSeries.ofScalars ℝ cCos).sum v

/-- `sin √v / √v`, as an entire function of `v`. -/
def sincSq (v : ℝ) : ℝ := (FormalMultilinearSeries.ofScalars ℝ cSinc).sum v

theorem contDiff_cosSq : ContDiff ℝ ∞ cosSq := contDiff_sum_of_radius_top radius_cCos

theorem contDiff_sincSq : ContDiff ℝ ∞ sincSq := contDiff_sum_of_radius_top radius_cSinc

theorem cosSq_eq_tsum (v : ℝ) : cosSq v = ∑' n, cCos n * v ^ n := by
  simp only [cosSq, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul]

theorem sincSq_eq_tsum (v : ℝ) : sincSq v = ∑' n, cSinc n * v ^ n := by
  simp only [sincSq, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul]

theorem cosSq_sq (τ : ℝ) : cosSq (τ ^ 2) = Real.cos τ := by
  rw [cosSq_eq_tsum, ← (Real.hasSum_cos τ).tsum_eq]
  congr 1; funext n
  simp only [cCos, ← pow_mul]
  ring

theorem sincSq_sq (τ : ℝ) : τ * sincSq (τ ^ 2) = Real.sin τ := by
  rw [sincSq_eq_tsum, ← (Real.hasSum_sin τ).tsum_eq, ← tsum_mul_left]
  congr 1; funext n
  simp only [cSinc, ← pow_mul, pow_succ]
  ring

theorem sincSq_zero : sincSq 0 = 1 := by
  rw [sincSq_eq_tsum, tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
  simp [cSinc]

theorem cosSq_zero : cosSq 0 = 1 := by
  rw [cosSq_eq_tsum, tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
  simp [cCos]

end

end ExoticSpheres8And10
