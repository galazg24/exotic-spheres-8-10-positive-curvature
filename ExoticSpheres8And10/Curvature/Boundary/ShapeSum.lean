/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.Eigenvalues

/-! # A8, completed: the shape sum, its eigenvalues relative to `h`, and `eq:compat`

[GG] §4.4 "Boundary compatibility": "For the common lift `X+U` of `Y`, these forms are
`B_N(Y,Y) = μ_N|X|² + q_s|U|²`, `(σ^*B_S)(Y,Y) = −μ_S|X|² − q_s|U|²`. The fibre contributions
therefore cancel: `(B_N + σ^*B_S)(Y,Y) = (μ_N − μ_S)|X|²`. Here `X ≠ 0` for every nonzero
boundary vector `Y`, by the graph description. Moreover `|Y|_h² = |X|² + |U|² ≤ (1+4F_a²/r_a²)|X|²`.
If `b_j ∈ [0,4]` are the eigenvalues of `K_yK_y^*`, the eigenvalues of the shape sum relative to
`h` are `r_a²/(r_a²+F_a²b_j)(μ_N−μ_S) ≥ c_B`, [...]. So `h_N = σ^*h_S`, `B_N + σ^*B_S ≥ c_B h`
(`eq:compat`)."

Setting (at `u = 1`): `H` the angular tangent space, `Vv = Im ℍ` with `Q`, `K : Vv → H` the action
field, `T = −(F_a/r_a)K^*`; a boundary vector `Y` is represented by its horizontal lift
`X + TX`, so `h(Y,Y) = ‖X‖² + ‖TX‖² = ⟪X, (1 + T^*T)X⟫`.
-/

namespace ExoticSpheres8And10

open scoped RealInnerProductSpace

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [CompleteSpace Vv]

/-- The fibre contributions cancel: `(B_N + σ^*B_S)(Y,Y) = (μ_N − μ_S)|X|²`. -/
theorem shape_sum (μN μS qs x2 u2 : ℝ) :
    (μN * x2 + qs * u2) + (-μS * x2 - qs * u2) = (μN - μS) * x2 := by ring

/-- The lift `X + TX` vanishes only if `X = 0` ("`X ≠ 0` for every nonzero `Y`"). -/
theorem lift_ne_zero {T : H →L[ℝ] Vv} {X : H} (hX : ((X, T X) : H × Vv) ≠ 0) : X ≠ 0 := by
  rintro rfl; simp at hX

/-- `T^*T = (F_a/r_a)² KK^*` for `T = −(F_a/r_a)K^*`. -/
theorem adjoint_graphT_comp (K : Vv →L[ℝ] H) (c : ℝ) :
    ContinuousLinearMap.adjoint (-c • ContinuousLinearMap.adjoint K) ∘L
        (-c • ContinuousLinearMap.adjoint K) = c ^ 2 • (K ∘L ContinuousLinearMap.adjoint K) := by
  ext v
  simp [ContinuousLinearMap.adjoint_adjoint, map_smul, smul_smul, sq]

/-- **The eigenvalues `b_j` of `KK^*` lie in `[0, ‖K‖²]`**, so in `[0, 4]` under `‖K‖ ≤ 2`
([GG] `lem:K`: "Hence the eigenvalues `b_j` of `K_yK_y^*` satisfy `0 ≤ b_j ≤ 4`"). -/
theorem eigen_KKstar_mem (K : Vv →L[ℝ] H) (hK : ‖K‖ ≤ 2) {v : H} (hv : v ≠ 0) {b : ℝ}
    (hb : K (ContinuousLinearMap.adjoint K v) = b • v) : 0 ≤ b ∧ b ≤ 4 := by
  have hvv : 0 < ‖v‖ ^ 2 := by positivity
  have key : b * ‖v‖ ^ 2 = ‖ContinuousLinearMap.adjoint K v‖ ^ 2 := by
    have := ContinuousLinearMap.adjoint_inner_right K (ContinuousLinearMap.adjoint K v) v
    rw [hb, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at this
    linarith
  have hle : ‖ContinuousLinearMap.adjoint K v‖ ≤ 2 * ‖v‖ := by
    calc _ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖K‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ 2 * ‖v‖ := by gcongr
  constructor
  · by_contra h; push Not at h
    nlinarith [sq_nonneg ‖ContinuousLinearMap.adjoint K v‖]
  · have h2 : ‖ContinuousLinearMap.adjoint K v‖ ^ 2 ≤ (2 * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    nlinarith

/-- **The relative eigenvalues.** If `KK^* v = b v`, then `v` is an eigenvector of the shape sum
`(μ_N−μ_S)⟪X,X⟫` relative to `h = ⟪X,(1+T^*T)X⟫`, with eigenvalue
`r_a²/(r_a²+F_a²b)(μ_N−μ_S)`: `(μ_N−μ_S) v = λ (v + T^*T v)`. -/
theorem shape_relative_eigen (K : Vv →L[ℝ] H) (ra Fa μN μS b : ℝ) (hra : 0 < ra)
    (hb0 : 0 ≤ b) {v : H} (hb : K (ContinuousLinearMap.adjoint K v) = b • v) :
    (μN - μS) • v = (ra ^ 2 / (ra ^ 2 + Fa ^ 2 * b) * (μN - μS)) •
      (v + (ContinuousLinearMap.adjoint (-(Fa / ra) • ContinuousLinearMap.adjoint K) ∘L
        (-(Fa / ra) • ContinuousLinearMap.adjoint K)) v) := by
  rw [adjoint_graphT_comp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hb]
  have hden : 0 < ra ^ 2 + Fa ^ 2 * b := by positivity
  match_scalars
  field_simp

omit [CompleteSpace H] [CompleteSpace Vv] in
/-- **`eq:compat`, second half, in lifted form.** For every angular `X`,
`c_B (‖X‖² + ‖TX‖²) ≤ (μ_N − μ_S)‖X‖²`, i.e. `B_N + σ^*B_S ≥ c_B h`, with
`c_B = r_a²/(r_a²+4F_a²)(μ_N − μ_S)`, whenever `‖T‖ ≤ 2F_a/r_a` and `μ_N > 0 > μ_S`. -/
theorem compat_lower_bound (ra Fa μN μS : ℝ) (hra : 0 < ra) (hFa : 0 < Fa) (hN : 0 < μN)
    (hS : μS < 0) (T : H →L[ℝ] Vv) (hT : ‖T‖ ≤ 2 * Fa / ra) (X : H) :
    ra ^ 2 / (ra ^ 2 + 4 * Fa ^ 2) * (μN - μS) * (‖X‖ ^ 2 + ‖T X‖ ^ 2) ≤ (μN - μS) * ‖X‖ ^ 2 := by
  have hn := boundary_norm_bound ra Fa hra hFa T hT X
  have hc : 0 ≤ ra ^ 2 / (ra ^ 2 + 4 * Fa ^ 2) * (μN - μS) := by
    have : 0 < μN - μS := by linarith
    positivity
  have e : ra ^ 2 / (ra ^ 2 + 4 * Fa ^ 2) * (μN - μS) * ((1 + 4 * Fa ^ 2 / ra ^ 2) * ‖X‖ ^ 2)
      = (μN - μS) * ‖X‖ ^ 2 := by
    field_simp
  calc _ ≤ ra ^ 2 / (ra ^ 2 + 4 * Fa ^ 2) * (μN - μS) * ((1 + 4 * Fa ^ 2 / ra ^ 2) * ‖X‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hn hc
    _ = _ := e

/-! ### Non-vacuity: `H = Vv = ℝ`, `K = 2·id` (so `KK^* = 4`, the extreme `b = 4`). -/

example : (0 : ℝ) ≤ 4 ∧ (4 : ℝ) ≤ 4 :=
  eigen_KKstar_mem ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => by
      show ‖(2:ℝ) • x‖ ≤ 2 * ‖x‖; rw [norm_smul, Real.norm_two])
    (one_ne_zero) (by simp [ContinuousLinearMap.adjoint_id]; norm_num)

example (X : ℝ) : 1 ^ 2 / (1 ^ 2 + 4 * 1 ^ 2) * (1 - (-1)) *
    (‖X‖ ^ 2 + ‖((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) X‖ ^ 2) ≤ (1 - (-1)) * ‖X‖ ^ 2 :=
  compat_lower_bound 1 1 1 (-1) one_pos one_pos one_pos (by norm_num) _
    (ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => by
      show ‖(2:ℝ) • x‖ ≤ 2 * 1 / 1 * ‖x‖; rw [norm_smul, Real.norm_two]; norm_num) X

end ExoticSpheres8And10
