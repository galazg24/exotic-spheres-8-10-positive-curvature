/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.ProfilesExistence

/-! # Infrastructure: a reparametrisation of `ℝ` onto `(0, ∞)` that is the identity near `s₀`

For `s₀ > 0`, `reparam s₀ : ℝ → ℝ` is smooth, positive, has positive derivative everywhere, and
is the identity on `[s₀/2, ∞)`. Composing [D]'s northern profiles with it gives a polar chart
that is a local diffeomorphism **everywhere** (its radius never vanishes) and agrees with the
true polar chart near `s₀`.

`reparam s₀ t = η(t) t + (1 − η(t)) ℓ(t)`, with `η = etaCut(t/s₀)` switching from `0`
(`t ≤ s₀/4`) to `1` (`t ≥ s₀/2`), and `ℓ(t) = (s₀/4) eᵗ/(1 + eᵗ) ∈ (0, s₀/4)`.
-/

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped ContDiff

noncomputable section

/-- The switch `η(t) = etaCut(t/s₀)`. -/
def ηs (s₀ t : ℝ) : ℝ := etaCut (t / s₀)

/-- The logistic lower branch `ℓ(t) = (s₀/4) eᵗ/(1 + eᵗ)`. -/
def lgs (s₀ t : ℝ) : ℝ := s₀ / 4 * (Real.exp t / (1 + Real.exp t))

/-- **The reparametrisation.** -/
def reparam (s₀ t : ℝ) : ℝ := ηs s₀ t * t + (1 - ηs s₀ t) * lgs s₀ t

variable {s₀ : ℝ}

theorem contDiff_ηs : ContDiff ℝ ∞ (ηs s₀) :=
  etaCut_contDiff.comp (contDiff_id.div_const s₀)

theorem contDiff_lgs : ContDiff ℝ ∞ (lgs s₀) := by
  unfold lgs
  refine contDiff_const.mul (Real.contDiff_exp.div (contDiff_const.add Real.contDiff_exp)
    fun t => by positivity)

theorem contDiff_reparam : ContDiff ℝ ∞ (reparam s₀) := by
  unfold reparam
  exact (contDiff_ηs.mul contDiff_id).add ((contDiff_const.sub contDiff_ηs).mul contDiff_lgs)

theorem ηs_nonneg (t : ℝ) : 0 ≤ ηs s₀ t := Real.smoothTransition.nonneg _

theorem ηs_le_one (t : ℝ) : ηs s₀ t ≤ 1 := Real.smoothTransition.le_one _

theorem ηs_zero (hs : 0 < s₀) {t : ℝ} (ht : t ≤ s₀ / 4) : ηs s₀ t = 0 :=
  etaCut_zero (by rw [div_le_iff₀ hs]; linarith)

theorem ηs_one (hs : 0 < s₀) {t : ℝ} (ht : s₀ / 2 ≤ t) : ηs s₀ t = 1 :=
  etaCut_one (by rw [le_div_iff₀ hs]; linarith)

theorem ηs_monotone (hs : 0 < s₀) : Monotone (ηs s₀) := fun a b hab =>
  Real.smoothTransition.monotone (by
    have : a / s₀ ≤ b / s₀ := div_le_div_of_nonneg_right hab hs.le
    linarith)

theorem lgs_pos (hs : 0 < s₀) (t : ℝ) : 0 < lgs s₀ t := by unfold lgs; positivity

theorem lgs_lt (hs : 0 < s₀) (t : ℝ) : lgs s₀ t < s₀ / 4 := by
  unfold lgs
  have h : Real.exp t / (1 + Real.exp t) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have : 0 < s₀ / 4 := by positivity
  calc s₀ / 4 * (Real.exp t / (1 + Real.exp t)) < s₀ / 4 * 1 := by gcongr
    _ = s₀ / 4 := mul_one _

theorem hasDerivAt_lgs (t : ℝ) :
    HasDerivAt (lgs s₀) (s₀ / 4 * (Real.exp t / (1 + Real.exp t) ^ 2)) t := by
  have h1 := Real.hasDerivAt_exp t
  have h2 := (h1.const_add 1)
  have h := (h1.div h2 (by positivity)).const_mul (s₀ / 4)
  refine h.congr_deriv ?_
  field_simp
  ring

theorem deriv_ηs_eq_zero (hs : 0 < s₀) {t : ℝ} (ht : t < s₀ / 4 ∨ s₀ / 2 < t) :
    deriv (ηs s₀) t = 0 := by
  rcases ht with ht | ht
  · have e : ηs s₀ =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with u hu
      exact ηs_zero hs (le_of_lt hu)
    rw [e.deriv_eq, deriv_const]
  · have e : ηs s₀ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ηs_one hs (le_of_lt hu)
    rw [e.deriv_eq, deriv_const]

/-- The derivative of the reparametrisation. -/
def reparamDeriv (s₀ t : ℝ) : ℝ :=
  deriv (ηs s₀) t * (t - lgs s₀ t) + ηs s₀ t +
    (1 - ηs s₀ t) * (s₀ / 4 * (Real.exp t / (1 + Real.exp t) ^ 2))

theorem hasDerivAt_reparam (t : ℝ) : HasDerivAt (reparam s₀) (reparamDeriv s₀ t) t := by
  have hη : HasDerivAt (ηs s₀) (deriv (ηs s₀) t) t :=
    ((contDiff_ηs (s₀ := s₀)).differentiable (by simp) t).hasDerivAt
  have h := (hη.mul (hasDerivAt_id t)).add ((hη.const_sub 1).mul (hasDerivAt_lgs (s₀ := s₀) t))
  refine h.congr_deriv ?_
  simp only [reparamDeriv, id]
  ring

theorem reparamDeriv_pos (hs : 0 < s₀) (t : ℝ) : 0 < reparamDeriv s₀ t := by
  have hl' : 0 < s₀ / 4 * (Real.exp t / (1 + Real.exp t) ^ 2) := by positivity
  have h0 := ηs_nonneg (s₀ := s₀) t
  have h1 := ηs_le_one (s₀ := s₀) t
  -- the transition term is nonnegative
  have htr : 0 ≤ deriv (ηs s₀) t * (t - lgs s₀ t) := by
    by_cases hin : s₀ / 4 ≤ t ∧ t ≤ s₀ / 2
    · have hd := (ηs_monotone hs).deriv_nonneg (x := t)
      have hlt := lgs_lt hs t
      exact mul_nonneg hd (by linarith [hin.1])
    · have : t < s₀ / 4 ∨ s₀ / 2 < t := by
        by_contra hc; push_neg at hc; exact hin ⟨hc.1, hc.2⟩
      rw [deriv_ηs_eq_zero hs this, zero_mul]
  have hrest : 0 < ηs s₀ t + (1 - ηs s₀ t) * (s₀ / 4 * (Real.exp t / (1 + Real.exp t) ^ 2)) := by
    rcases eq_or_lt_of_le h1 with h | h
    · rw [h]; norm_num
    · have : 0 < (1 - ηs s₀ t) * (s₀ / 4 * (Real.exp t / (1 + Real.exp t) ^ 2)) :=
        mul_pos (by linarith) hl'
      linarith
  unfold reparamDeriv
  linarith

theorem reparam_pos (hs : 0 < s₀) (t : ℝ) : 0 < reparam s₀ t := by
  have hg := lgs_pos hs t
  unfold reparam
  by_cases ht : t ≤ s₀ / 4
  · rw [ηs_zero hs ht]; simpa using hg
  · rw [not_le] at ht
    have htp : 0 < t := by linarith [show 0 < s₀ / 4 by positivity]
    have h0 := ηs_nonneg (s₀ := s₀) t
    have h1 := ηs_le_one (s₀ := s₀) t
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]; simpa using hg
    · have : 0 < ηs s₀ t * t := mul_pos h htp
      have : 0 ≤ (1 - ηs s₀ t) * lgs s₀ t := mul_nonneg (by linarith) hg.le
      linarith

theorem reparam_eq (hs : 0 < s₀) {t : ℝ} (ht : s₀ / 2 ≤ t) : reparam s₀ t = t := by
  simp [reparam, ηs_one hs ht]

theorem reparam_eventuallyEq (hs : 0 < s₀) : ∀ᶠ t in 𝓝 s₀, reparam s₀ t = t := by
  filter_upwards [Ioi_mem_nhds (show s₀ / 2 < s₀ by linarith)] with t ht
  exact reparam_eq hs ht.le

end

end ExoticSpheres8And10
