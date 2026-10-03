/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib

/-! # A8. Boundary eigenvalue bound ([D] §4.4 "Boundary compatibility")

[D]: "If `b_j ∈ [0,4]` are the eigenvalues of `K_y K_y^*`, the eigenvalues of the shape sum
relative to `h` are `r_a²/(r_a²+F_a² b_j) (μ_N − μ_S) ≥ c_B := r_a²/(r_a²+4F_a²) (μ_N − μ_S) > 0`"
and "`|Y|_h² = |X|² + |U|² ≤ (1 + 4F_a²/r_a²)|X|²`".

We formalise the scalar inequality and the norm estimate. The identification of the
eigenvalues of the shape sum with `r_a²/(r_a²+F_a² b_j)(μ_N−μ_S)` is **not** formalised.
-/

namespace ExoticSpheres8And10

/-- The scalar eigenvalue bound: for `0 ≤ b ≤ 4`, `r_a, F_a > 0` and `μ_N > 0 > μ_S`,
`r_a²/(r_a²+F_a² b)(μ_N−μ_S) ≥ c_B` where `c_B = r_a²/(r_a²+4F_a²)(μ_N−μ_S) > 0`. -/
theorem boundary_eigenvalue_bound (b ra Fa μN μS : ℝ) (hb0 : 0 ≤ b) (hb4 : b ≤ 4)
    (hra : 0 < ra) (hFa : 0 < Fa) (hN : 0 < μN) (hS : μS < 0) :
    ra ^ 2 / (ra ^ 2 + 4 * Fa ^ 2) * (μN - μS) ≤ ra ^ 2 / (ra ^ 2 + Fa ^ 2 * b) * (μN - μS) ∧
      0 < ra ^ 2 / (ra ^ 2 + 4 * Fa ^ 2) * (μN - μS) := by
  have hμ : 0 < μN - μS := by linarith
  have hd1 : 0 < ra ^ 2 + Fa ^ 2 * b := by positivity
  refine ⟨?_, by positivity⟩
  apply mul_le_mul_of_nonneg_right ?_ hμ.le
  apply div_le_div_of_nonneg_left (by positivity) hd1
  nlinarith [sq_nonneg Fa]

/-- The norm estimate: if `‖T‖ ≤ 2F_a/r_a` then `‖X‖² + ‖TX‖² ≤ (1 + 4F_a²/r_a²)‖X‖²`. -/
theorem boundary_norm_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ra Fa : ℝ) (hra : 0 < ra) (hFa : 0 < Fa)
    (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 2 * Fa / ra) (X : E) :
    ‖X‖ ^ 2 + ‖T X‖ ^ 2 ≤ (1 + 4 * Fa ^ 2 / ra ^ 2) * ‖X‖ ^ 2 := by
  have h1 : ‖T X‖ ≤ 2 * Fa / ra * ‖X‖ :=
    (T.le_opNorm X).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have h2 : ‖T X‖ ^ 2 ≤ (2 * Fa / ra * ‖X‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (2 * Fa / ra * ‖X‖) ^ 2 = 4 * Fa ^ 2 / ra ^ 2 * ‖X‖ ^ 2 := by
    field_simp
    ring
  nlinarith [h2, h3]

/-! ### Non-vacuity: the hypotheses are satisfiable, and the bound is attained at `b = 4`. -/

example : (1:ℝ) ^ 2 / (1 ^ 2 + 4 * 1 ^ 2) * (1 - (-1)) ≤
    1 ^ 2 / (1 ^ 2 + 1 ^ 2 * 4) * (1 - (-1)) ∧ 0 < (1:ℝ) ^ 2 / (1 ^ 2 + 4 * 1 ^ 2) * (1 - (-1)) :=
  boundary_eigenvalue_bound 4 1 1 1 (-1) (by norm_num) le_rfl one_pos one_pos one_pos
    (by norm_num)

/-- The norm estimate fires for `T = 2 • id` on `ℝ`, where `‖T‖ = 2 = 2F_a/r_a` at
`F_a = r_a = 1`, and it is then an equality `1 + 4 = 5`. -/
example : ‖(1:ℝ)‖ ^ 2 + ‖((2:ℝ) • ContinuousLinearMap.id ℝ ℝ) 1‖ ^ 2 ≤
    (1 + 4 * 1 ^ 2 / 1 ^ 2) * ‖(1:ℝ)‖ ^ 2 :=
  boundary_norm_bound 1 1 one_pos one_pos _
    (ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => by
      show ‖(2:ℝ) • x‖ ≤ _
      rw [norm_smul]
      norm_num) 1

end ExoticSpheres8And10
