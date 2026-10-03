/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.ActionField.Bound
import ExoticSpheres8And10.PolarBundles.OrientationDerivative

/-! # A1: the maximum `‖K_y‖ = 2` is attained only at non-free points

[D] `lem:K`: "The value 4 is attained, and the maximum is not attained on the free stratum
alone." The proof gives the equality cases: in dimension 8 equality requires `x = 0`,
`Re w = 0`; in dimension 10, `|x| = 1`. Here the converse direction is proved: **every** point
`y ∈ S^{n−1}` at which `‖K_y ξ‖² = 4‖ξ‖²` for some `ξ ≠ 0` has non-trivial isotropy (it is fixed
by the unit quaternion `q = w`, resp. `q = x`, which is `≠ 1`). With the attainment theorems
`actionField_eq_dim8`, `actionField_eq_dim10`, this gives: the maximum `4` is attained, and
only off the free stratum.
-/

namespace ExoticSpheres8And10

open Quaternion

theorem norm_sq_eq_re_im (v : ℍ[ℝ]) : ‖v‖ ^ 2 = v.re ^ 2 + ‖v.im‖ ^ 2 := by
  simp only [norm_sq_eq, Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im,
    Quaternion.imK_im]
  ring

/-- **Dimension 8, equality case.** -/
theorem eq_case_dim8 (ξ x w : ℍ[ℝ]) (hξ0 : ξ ≠ 0) (h : ‖x‖ ^ 2 + ‖w‖ ^ 2 = 1)
    (heq : ‖ξ * x‖ ^ 2 + ‖ξ * w - w * ξ‖ ^ 2 = 4 * ‖ξ‖ ^ 2) :
    x = 0 ∧ w.re = 0 ∧ ‖w‖ = 1 := by
  have h1 := norm_commutator_sq_le ξ w
  have hIm : ‖w.im‖ ^ 2 = 1 - ‖x‖ ^ 2 - w.re ^ 2 := by linarith [norm_sq_eq_re_im w]
  rw [hIm] at h1
  rw [norm_mul_sq] at heq
  have hξ : 0 < ‖ξ‖ ^ 2 := by have := norm_pos_iff.2 hξ0; positivity
  have key : ‖ξ‖ ^ 2 * (3 * ‖x‖ ^ 2 + 4 * w.re ^ 2) ≤ ‖ξ‖ ^ 2 * 0 := by nlinarith
  have hS := le_of_mul_le_mul_left key hξ
  have hx : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg w.re]
  have hr : w.re ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg w.re]
  refine ⟨norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hx), pow_eq_zero_iff two_ne_zero |>.1 hr,
    ?_⟩
  have hw : ‖w‖ ^ 2 = 1 ^ 2 := by rw [one_pow]; linarith
  exact (pow_left_inj₀ (norm_nonneg w) zero_le_one two_ne_zero).1 hw

/-- **Dimension 8: maximising points are not free.** -/
theorem maximizer_not_free_dim8 (ξ x w : ℍ[ℝ]) (hξ0 : ξ ≠ 0) (h : ‖x‖ ^ 2 + ‖w‖ ^ 2 = 1)
    (heq : ‖ξ * x‖ ^ 2 + ‖ξ * w - w * ξ‖ ^ 2 = 4 * ‖ξ‖ ^ 2) :
    ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ q ≠ 1 ∧ rho8 q (x, w) = (x, w) := by
  obtain ⟨hx, hre, hw1⟩ := eq_case_dim8 ξ x w hξ0 h heq
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  refine ⟨w, hw1, fun h1 => by simp [h1] at hre, ?_⟩
  simp only [rho8, hx, mul_zero, mul_inv_cancel_right₀ hw0]

/-- **Dimension 10, equality case.** -/
theorem eq_case_dim10 (ξ p w x : ℍ[ℝ]) (hξ0 : ξ ≠ 0) (h : ‖p‖ ^ 2 + ‖w‖ ^ 2 + ‖x‖ ^ 2 = 1)
    (heq : ‖ξ * w‖ ^ 2 + ‖ξ * x - x * ξ‖ ^ 2 = 4 * ‖ξ‖ ^ 2) :
    p = 0 ∧ w = 0 ∧ x.re = 0 ∧ ‖x‖ = 1 := by
  have h1 := norm_commutator_sq_le ξ x
  have hIm : ‖x.im‖ ^ 2 = 1 - ‖p‖ ^ 2 - ‖w‖ ^ 2 - x.re ^ 2 := by
    linarith [norm_sq_eq_re_im x]
  rw [hIm] at h1
  rw [norm_mul_sq] at heq
  have hξ : 0 < ‖ξ‖ ^ 2 := by have := norm_pos_iff.2 hξ0; positivity
  have key : ‖ξ‖ ^ 2 * (4 * ‖p‖ ^ 2 + 3 * ‖w‖ ^ 2 + 4 * x.re ^ 2) ≤ ‖ξ‖ ^ 2 * 0 := by nlinarith
  have hS := le_of_mul_le_mul_left key hξ
  have hp : ‖p‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p‖, sq_nonneg ‖w‖, sq_nonneg x.re]
  have hw : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p‖, sq_nonneg ‖w‖, sq_nonneg x.re]
  have hr : x.re ^ 2 = 0 := by nlinarith [sq_nonneg ‖p‖, sq_nonneg ‖w‖, sq_nonneg x.re]
  refine ⟨norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hp),
    norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hw), pow_eq_zero_iff two_ne_zero |>.1 hr, ?_⟩
  have hx : ‖x‖ ^ 2 = 1 ^ 2 := by rw [one_pow]; linarith
  exact (pow_left_inj₀ (norm_nonneg x) zero_le_one two_ne_zero).1 hx

/-- **Dimension 10: maximising points are not free.** -/
theorem maximizer_not_free_dim10 (ξ p w x : ℍ[ℝ]) (hξ0 : ξ ≠ 0)
    (h : ‖p‖ ^ 2 + ‖w‖ ^ 2 + ‖x‖ ^ 2 = 1)
    (heq : ‖ξ * w‖ ^ 2 + ‖ξ * x - x * ξ‖ ^ 2 = 4 * ‖ξ‖ ^ 2) :
    ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ q ≠ 1 ∧ rho10 q (p, w, x) = (p, w, x) := by
  obtain ⟨-, hw, hre, hx1⟩ := eq_case_dim10 ξ p w x hξ0 h heq
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx1
  refine ⟨x, hx1, fun h1 => by simp [h1] at hre, ?_⟩
  simp only [rho10, hw, mul_zero, mul_inv_cancel_right₀ hx0]

/-- Non-vacuity: the maximiser `y = (0, i)`, `ξ = j` of [D] satisfies the hypotheses. -/
example : ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ q ≠ 1 ∧ rho8 q (0, qmk 0 1 0 0) = (0, qmk 0 1 0 0) :=
  maximizer_not_free_dim8 (qmk 0 0 1 0) 0 (qmk 0 1 0 0)
    (fun h => by simpa using congrArg (fun q : ℍ[ℝ] => q.imJ) h)
    (by rw [norm_zero, norm_eq_one_of_components (by norm_num)]; norm_num)
    (actionField_eq_dim8 _ _ rfl rfl (norm_eq_one_of_components (by norm_num)) (by simp [qdot]))

end ExoticSpheres8And10
