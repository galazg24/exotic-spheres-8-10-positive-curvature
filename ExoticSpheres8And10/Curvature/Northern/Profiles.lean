/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # A7. The northern profile inequalities ([GG] §4.3, "Choice of profiles")

(a) [GG]: "For `x > 0` the power series for `sinh` gives
`2 sinh(x²/2)/x³ ≥ 1/x + x³/24 ≥ 4/(3·8^{1/4}) > 1/2`,
the minimum of the middle expression occurring at `x⁴ = 8`."
-/

namespace ExoticSpheres8And10

/-- `y + y³/6 ≤ sinh y` for `y ≥ 0`, from the power series of `sinh`. -/
theorem add_cube_div_six_le_sinh {y : ℝ} (hy : 0 ≤ y) : y + y ^ 3 / 6 ≤ Real.sinh y := by
  have h := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) (Real.hasSum_sinh y)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The constant `8^{1/4}`. -/
noncomputable def c8 : ℝ := (8 : ℝ) ^ ((1 : ℝ) / 4)

theorem c8_pos : 0 < c8 := by unfold c8; positivity

theorem c8_pow_four : c8 ^ 4 = 8 := by
  unfold c8
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **A7(a).** For `x > 0`:
`2 sinh(x²/2)/x³ ≥ 1/x + x³/24 ≥ 4/(3·8^{1/4}) > 1/2`. -/
theorem sinh_profile_bound (x : ℝ) (hx : 0 < x) :
    1 / x + x ^ 3 / 24 ≤ 2 * Real.sinh (x ^ 2 / 2) / x ^ 3 ∧
      4 / (3 * (8 : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 / x + x ^ 3 / 24 ∧
      (1 : ℝ) / 2 < 4 / (3 * (8 : ℝ) ^ ((1 : ℝ) / 4)) := by
  have hc := c8_pos
  have hc4 := c8_pow_four
  change 1 / x + x ^ 3 / 24 ≤ 2 * Real.sinh (x ^ 2 / 2) / x ^ 3 ∧
      4 / (3 * c8) ≤ 1 / x + x ^ 3 / 24 ∧ (1 : ℝ) / 2 < 4 / (3 * c8)
  refine ⟨?_, ?_, ?_⟩
  · have hs := add_cube_div_six_le_sinh (by positivity : (0:ℝ) ≤ x ^ 2 / 2)
    rw [le_div_iff₀ (by positivity)]
    have : (1 / x + x ^ 3 / 24) * x ^ 3 = x ^ 2 + x ^ 6 / 24 := by
      field_simp
    rw [this]
    nlinarith [hs]
  · -- `c x⁴ − 32 x + 24 c = c (x − c)² (x² + 2cx + 3c²)` using `c⁴ = 8`.
    rw [div_le_iff₀ (by positivity)]
    have iden : c8 * (x - c8) ^ 2 * (x ^ 2 + 2 * c8 * x + 3 * c8 ^ 2) =
        c8 * x ^ 4 + 24 * c8 - 32 * x := by
      linear_combination (3 * c8 - 4 * x) * hc4
    have hpoly : 0 ≤ c8 * x ^ 4 + 24 * c8 - 32 * x := by
      rw [← iden]; positivity
    have key : (1 / x + x ^ 3 / 24) * (3 * c8) - 4 = (c8 * x ^ 4 + 24 * c8 - 32 * x) / (8 * x) := by
      field_simp
      ring
    have hnn : 0 ≤ (c8 * x ^ 4 + 24 * c8 - 32 * x) / (8 * x) := by positivity
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    -- `c < 8/3` since `c⁴ = 8 < (8/3)⁴`.
    have hlt : c8 < 8 / 3 := by
      by_contra h
      have := pow_le_pow_left₀ (by norm_num) (not_lt.mp h) 4
      rw [hc4] at this
      norm_num at this
    linarith

/-- The minimum is attained at `x = 8^{1/4}`, i.e. `x⁴ = 8`. -/
theorem sinh_profile_min_attained : 1 / c8 + c8 ^ 3 / 24 = 4 / (3 * c8) := by
  have hc := c8_pos
  have key : 1 / c8 + c8 ^ 3 / 24 - 4 / (3 * c8) = (c8 ^ 4 - 8) / (24 * c8) := by
    field_simp
    ring
  rw [c8_pow_four, sub_self, zero_div] at key
  linarith

/-! ## A7(b) — the angular chain

[GG]: "Substitution `x = F/δ` yields `(1−F'²)/F² > FF'/(2δ³) > 32A₀F_aFF' ≥ 8FF'r'/r³`." -/

/-- Step one of the angular chain: `(1−F'²)/F² > FF'/(2δ³)` for `F' = exp(−F²/(2δ²))`. -/
theorem angular_step (F δ : ℝ) (hF : 0 < F) (hδ : 0 < δ) :
    F * Real.exp (-F ^ 2 / (2 * δ ^ 2)) / (2 * δ ^ 3) <
      (1 - Real.exp (-F ^ 2 / (2 * δ ^ 2)) ^ 2) / F ^ 2 := by
  set x := F / δ with hxdef
  have hx : 0 < x := div_pos hF hδ
  have hFx : F = x * δ := by rw [hxdef]; field_simp
  have harg : -F ^ 2 / (2 * δ ^ 2) = -(x ^ 2 / 2) := by rw [hxdef, div_pow]; ring
  rw [harg]
  set E := Real.exp (-(x ^ 2 / 2)) with hE
  set S := Real.exp (x ^ 2 / 2) with hS
  have hEpos : 0 < E := Real.exp_pos _
  have hES : E * S = 1 := by
    rw [hE, hS, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- from A7(a): `x³/2 < 2 sinh(x²/2) = S − E`
  have hsinh : x ^ 3 / 2 < S - E := by
    obtain ⟨h1, h2, h3⟩ := sinh_profile_bound x hx
    have h4 : (1 : ℝ) / 2 < 2 * Real.sinh (x ^ 2 / 2) / x ^ 3 := by linarith
    rw [lt_div_iff₀ (by positivity), Real.sinh_eq] at h4
    rw [hS, hE]
    linarith
  have hkey : E * x ^ 3 / 2 < 1 - E ^ 2 := by
    have e : 1 - E ^ 2 = E * (S - E) := by linear_combination (-1 : ℝ) * hES
    rw [e]
    have := mul_lt_mul_of_pos_left hsinh hEpos
    linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have e2 : F * E * F ^ 2 = δ ^ 3 * (x ^ 3 * E) := by rw [hFx]; ring
  rw [e2]
  have := mul_lt_mul_of_pos_left hkey (pow_pos hδ 3)
  nlinarith [this]

/-- `32 A₀ F_a ≤ 1/(2δ³)` under `eq:delta`. -/
theorem delta_consequence (δ A0 Fa Ceta : ℝ) (hδ : 0 < δ) (hA0 : 0 < A0) (hFa : 0 < Fa)
    (hC : 0 ≤ Ceta) (hδ3 : δ ^ 3 ≤ 1 / (128 * A0 * Fa * (1 + Ceta))) :
    δ ^ 3 * (128 * A0 * Fa * (1 + Ceta)) ≤ 1 ∧ 32 * A0 * Fa ≤ 1 / (2 * δ ^ 3) := by
  have h1 : δ ^ 3 * (128 * A0 * Fa * (1 + Ceta)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hδ3
  refine ⟨h1, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA0.le hFa.le) (pow_pos hδ 3).le) hC]

/-- **A7(b).** The angular chain: `(1−F'²)/F² > 8FF'r'/r³`. -/
theorem angular_chain (F Fp δ A0 Fa Ceta d r rp : ℝ) (hF : 0 < F) (hδ : 0 < δ)
    (hA0 : 0 < A0) (hFa : 0 < Fa) (hC : 0 ≤ Ceta) (hr : 0 < r)
    (hFp : Fp = Real.exp (-F ^ 2 / (2 * δ ^ 2)))
    (hδ3 : δ ^ 3 ≤ 1 / (128 * A0 * Fa * (1 + Ceta)))
    (hd : d / r ^ 3 ≤ 4 * A0 * Fa) (hrpd : rp ≤ d) :
    8 * F * Fp * rp / r ^ 3 < (1 - Fp ^ 2) / F ^ 2 := by
  have hstep := angular_step F δ hF hδ
  rw [← hFp] at hstep
  have hFp0 : 0 ≤ Fp := by rw [hFp]; exact (Real.exp_pos _).le
  have hc := (delta_consequence δ A0 Fa Ceta hδ hA0 hFa hC hδ3).2
  have h1 : rp / r ^ 3 ≤ d / r ^ 3 := div_le_div_of_nonneg_right hrpd (by positivity)
  have h2 : 8 * (rp / r ^ 3) ≤ 1 / (2 * δ ^ 3) := by linarith
  have h3 : F * Fp * (8 * (rp / r ^ 3)) ≤ F * Fp * (1 / (2 * δ ^ 3)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e1 : 8 * F * Fp * rp / r ^ 3 = F * Fp * (8 * (rp / r ^ 3)) := by ring
  have e2 : F * Fp * (1 / (2 * δ ^ 3)) = F * Fp / (2 * δ ^ 3) := by ring
  rw [e1]
  linarith

/-! ## A7(c) — the radial chain

[GG]: "On the support of `r''` one has `s ≤ δ/2` and `F ≤ s`, hence `−F''/F ≥ e^{−1/4}δ^{−2}`,
`4F²r''/r³ ≤ 4A₀F_aC_ηδ ≤ C_η/(32(1+C_η)) δ^{−2}`. This proves the strict radial inequality." -/

/-- **A7(c).** The radial chain: `−F''/F > 4F²r''/r³` where `F'' = −(F/δ²)F'²`. -/
theorem radial_chain (F Fp Fpp s δ A0 Fa Ceta d r rpp : ℝ) (hF : 0 < F) (hδ : 0 < δ)
    (hA0 : 0 < A0) (hFa : 0 < Fa) (hC : 0 ≤ Ceta) (hr : 0 < r)
    (hFp : Fp = Real.exp (-F ^ 2 / (2 * δ ^ 2)))
    (hδ3 : δ ^ 3 ≤ 1 / (128 * A0 * Fa * (1 + Ceta)))
    (hd : d / r ^ 3 ≤ 4 * A0 * Fa) (hFs : F ≤ s) (hs : s ≤ δ / 2)
    (hrpp : rpp ≤ d / δ * Ceta)
    (hFpp : Fpp = -(F / δ ^ 2) * Fp ^ 2) :
    4 * F ^ 2 * rpp / r ^ 3 < -Fpp / F := by
  have hFδ : F ^ 2 ≤ δ ^ 2 / 4 := by nlinarith
  -- `−F''/F = F'²/δ² ≥ e^{−1/4}/δ² ≥ (3/4)/δ²`
  have hL : -Fpp / F = Fp ^ 2 / δ ^ 2 := by
    rw [hFpp]
    field_simp
  have hFp2 : 3 / 4 ≤ Fp ^ 2 := by
    have hq : F ^ 2 / δ ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have e : Fp ^ 2 = Real.exp (-(F ^ 2 / δ ^ 2)) := by
      rw [sq, hFp, ← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-(F ^ 2 / δ ^ 2)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 := Real.add_one_le_exp (-(1 / 4 : ℝ))
    rw [e]; linarith
  have hδ' := (delta_consequence δ A0 Fa Ceta hδ hA0 hFa hC hδ3).1
  have hCAF : 0 ≤ Ceta * A0 * Fa := by positivity
  have h1 : 4 * F ^ 2 * rpp / r ^ 3 ≤ 4 * F ^ 2 * (d / δ * Ceta) / r ^ 3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrpp (by positivity)) (by positivity)
  have h2 : 4 * F ^ 2 * (d / δ * Ceta) / r ^ 3 = 4 * F ^ 2 * Ceta / δ * (d / r ^ 3) := by ring
  have h3 : 4 * F ^ 2 * Ceta / δ * (d / r ^ 3) ≤ 4 * F ^ 2 * Ceta / δ * (4 * A0 * Fa) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have h4 : 4 * F ^ 2 * Ceta / δ * (4 * A0 * Fa) ≤ 4 * δ * (Ceta * A0 * Fa) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ]
    nlinarith [mul_le_mul_of_nonneg_right hFδ hCAF]
  have h5 : 4 * δ * (Ceta * A0 * Fa) < 3 / 4 / δ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA0.le hFa.le) (pow_pos hδ 3).le) hC,
      mul_nonneg (mul_nonneg hA0.le hFa.le) (pow_pos hδ 3).le]
  have h6 : 3 / 4 / δ ^ 2 ≤ Fp ^ 2 / δ ^ 2 := div_le_div_of_nonneg_right hFp2 (by positivity)
  rw [hL]
  linarith

/-! ## A7(d) — the bound on `d/r³`

[GG]: "`d/r³ ≤ 8q_s/r_a² = 4A₀F_a e^{−εA₀|cos a|} ≤ 4A₀F_a`", with `r_a/2 ≤ r`, `d = r_a q_s`,
`q_s = ½εA₀F_a` and `r_a² = ε e^{εA₀|cos a|}` (`eq:bdata`). -/

/-- **A7(d).** -/
theorem d_over_r_cubed_bound (ε A0 Fa a ra r d qs : ℝ) (hε : 0 < ε) (hA0 : 0 < A0)
    (hFa : 0 < Fa) (hra : 0 < ra) (hr : ra / 2 ≤ r) (hd : d = ra * qs)
    (hqs : qs = ε * A0 * Fa / 2) (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) :
    d / r ^ 3 ≤ 8 * qs / ra ^ 2 ∧
      8 * qs / ra ^ 2 = 4 * A0 * Fa * Real.exp (-(ε * A0 * |Real.cos a|)) ∧
      4 * A0 * Fa * Real.exp (-(ε * A0 * |Real.cos a|)) ≤ 4 * A0 * Fa := by
  have hqs0 : 0 ≤ qs := by rw [hqs]; positivity
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  refine ⟨?_, ?_, ?_⟩
  · calc d / r ^ 3 ≤ d / (ra / 2) ^ 3 :=
          div_le_div_of_nonneg_left hd0 (by positivity) (pow_le_pow_left₀ (by positivity) hr 3)
      _ = 8 * qs / ra ^ 2 := by
          rw [hd]
          field_simp
          ring
  · rw [hqs, hra2, Real.exp_neg]
    field_simp
    ring
  · have : Real.exp (-(ε * A0 * |Real.cos a|)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
    have h4 : 0 ≤ 4 * A0 * Fa := by positivity
    nlinarith

/-! ### Non-vacuity for A7(b)–(d)

All hypotheses of (b) and (c) hold at `δ = 1/8`, `A₀ = F_a = 1`, `C_η = 0`, `r = d = 1`,
`r' = 1/2`, `F = s = 1/16`, `r'' = 0`; those of (d) at `ε = A₀ = F_a = 1`, `a = π/2`
(`cos a = 0`), `r_a = r = 1`, `q_s = 1/2`, `d = 1/2`. -/

example : 8 * (1 / 16) * Real.exp (-(1 / 16) ^ 2 / (2 * (1 / 8) ^ 2)) * (1 / 2) / 1 ^ 3 <
    (1 - Real.exp (-(1 / 16) ^ 2 / (2 * (1 / 8) ^ 2)) ^ 2) / (1 / 16) ^ 2 :=
  angular_chain (1 / 16) _ (1 / 8) 1 1 0 1 1 (1 / 2) (by norm_num) (by norm_num) one_pos
    one_pos le_rfl one_pos rfl (by norm_num) (by norm_num) (by norm_num)

example : 4 * (1 / 16) ^ 2 * 0 / 1 ^ 3 <
    -(-((1 / 16) / (1 / 8) ^ 2) * Real.exp (-(1 / 16) ^ 2 / (2 * (1 / 8) ^ 2)) ^ 2) / (1 / 16) :=
  radial_chain (1 / 16) _ _ (1 / 16) (1 / 8) 1 1 0 1 1 0 (by norm_num) (by norm_num) one_pos
    one_pos le_rfl one_pos rfl (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) rfl

example : (1 / 2 : ℝ) / 1 ^ 3 ≤ 8 * (1 / 2) / 1 ^ 2 :=
  (d_over_r_cubed_bound 1 1 1 (Real.pi / 2) 1 1 (1 / 2) (1 / 2) one_pos one_pos one_pos one_pos
    (by norm_num) (by norm_num) (by norm_num) (by simp)).1

end ExoticSpheres8And10
