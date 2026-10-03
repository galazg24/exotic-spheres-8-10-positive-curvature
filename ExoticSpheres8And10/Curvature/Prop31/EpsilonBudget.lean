/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib

/-! # D2(a). HLY Proposition 3.1: the ε-budget (`prop:concave`, "Choice of the fibre scale")

Source: [HLY] §3 (`sec:cap`).

* `eq:sharp-master` (PDF (3.16)) ⇒ `eq:master` (PDF (3.17)) with `C = 4`: `sharp_to_master`.
* `eq:master` ⇒ `eq:reserve` (PDF (3.21)) under `eq:Lambda` (PDF (3.2)) and `eq:smallA`–`eq:smallC`
  (PDF (3.18)–(3.20)): `master_to_reserve`.
* `eq:reserve` ⇒ `eq:southlowerbound` (PDF (3.22)): `southlowerbound`.
* The fibre-radius identities `ϑ = (ε/2) dφ`, `N = −r⁻¹ Hess r = −(ε/2)Hess φ − (ε²/4) dφ⊗dφ`
  for `r² = ε e^{εφ}`, along a curve: `fibreRadius_derivs`; and the consequences `ε/2 ≤ r² ≤ 2ε`,
  `|ϑ| ≤ εD₀/2`, `λ_min N ≥ εΛ/2 − ε²D₀²/4`.

Throughout, `t` stands for `|ϑ|`, `ν` for `λ_min N`, and `h, m, k` for `|α|, |β|, |γ|`.
-/

namespace ExoticSpheres8And10

/-- The right side of `eq:sharp-master`. -/
noncomputable def sharpRHS (κ r M0 M1 t ν h m k : ℝ) : ℝ :=
  (κ - 3 / 4 * r ^ 2 * M0 ^ 2) * h ^ 2 + (ν - 1 / 2 * r ^ 2 * M0 ^ 2) * m ^ 2
    + (1 / r ^ 2 - t ^ 2) * k ^ 2 - 2 * r * (M1 + 2 * t * M0) * h * m
    - (3 * M0 + r ^ 2 * M0 ^ 2) * h * k - 2 * r * t * M0 * k * m

/-- The right side of `eq:master`, with a general constant `C`. -/
noncomputable def masterRHS (C κ r M0 M1 t ν h m k : ℝ) : ℝ :=
  (κ - C * r ^ 2 * M0 ^ 2) * h ^ 2 + (1 / r ^ 2 - t ^ 2) * k ^ 2
    + (ν - C * r ^ 2 * M0 ^ 2) * m ^ 2 - C * r * (M1 + t * M0) * h * m
    - C * (M0 + r ^ 2 * M0 ^ 2) * h * k - C * r * t * M0 * k * m

/-- **`eq:sharp-master` ⇒ `eq:master`, `C = 4`.** -/
theorem sharp_to_master (κ r M0 M1 t ν h m k : ℝ) (hr : 0 ≤ r) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hm : 0 ≤ m) (hk : 0 ≤ k) :
    masterRHS 4 κ r M0 M1 t ν h m k ≤ sharpRHS κ r M0 M1 t ν h m k := by
  rw [← sub_nonneg]
  have e : sharpRHS κ r M0 M1 t ν h m k - masterRHS 4 κ r M0 M1 t ν h m k =
      13 / 4 * r ^ 2 * M0 ^ 2 * h ^ 2 + 7 / 2 * r ^ 2 * M0 ^ 2 * m ^ 2 + 2 * r * M1 * h * m
        + (M0 + 3 * r ^ 2 * M0 ^ 2) * h * k + 2 * r * t * M0 * k * m := by
    unfold sharpRHS masterRHS; ring
  rw [e]
  positivity

/-- Young's inequality in the form used: `x y ≤ δ x² + y²/(4δ)`. -/
theorem young (δ x y : ℝ) (hδ : 0 < δ) : x * y ≤ δ * x ^ 2 + 1 / (4 * δ) * y ^ 2 := by
  have h := div_nonneg (sq_nonneg (2 * δ * x - y)) (le_of_lt (mul_pos (by norm_num : (0:ℝ) < 4) hδ))
  have e : δ * x ^ 2 + 1 / (4 * δ) * y ^ 2 - x * y = (2 * δ * x - y) ^ 2 / (4 * δ) := by
    field_simp; ring
  linarith

/-- **`eq:master` ⇒ `eq:reserve`.** Hypotheses are those of HLY's proof with `C = 4`:
`eq:Lambda` (the `+4` is not needed and is dropped), `r² ≤ 2ε` (from `|εφ| ≤ log 2`, see
`rsq_bounds`; the lower bound `ε/2 ≤ r²` is not needed), `|ϑ| ≤ εD₀/2`, `λ_min N ≥ εΛ/2 − ε²D₀²/4` (see `lambdaMin_bound`), and those
parts of `eq:smallA`–`eq:smallC` that the accounting uses. -/
theorem master_to_reserve (κ ε Λ M0 M1 D0 r t ν h m k : ℝ)
    (hκ : 0 < κ) (hε : 0 < ε) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hr : 0 < r) (ht0 : 0 ≤ t)
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 ≤ Λ)
    (hr2 : r ^ 2 ≤ 2 * ε) (ht : t ≤ ε * D0 / 2)
    (hν : ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4 ≤ ν)
    (hA2 : 2 * ε * M0 ≤ 1) (hA3 : ε * D0 * M0 ≤ 1)
    (hB2 : 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ κ)
    (hC1 : ε * D0 ^ 2 ≤ Λ / 4) (hC2 : 2 * ε ^ 3 * D0 ^ 2 ≤ 1)
    (hC3 : 32 * 4 ^ 2 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 ≤ Λ) :
    κ / 2 * h ^ 2 + ε * Λ / 8 * m ^ 2 + 1 / (8 * ε) * k ^ 2 ≤
      masterRHS 4 κ r M0 M1 t ν h m k := by
  have hr2' : 0 < r ^ 2 := by positivity
  have hrM := mul_le_mul_of_nonneg_right hr2 (sq_nonneg M0)
  have htM : t * M0 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ht hM0; linarith
  -- the three diagonal coefficients
  have cH : 3 * κ / 4 ≤ κ - 4 * r ^ 2 * M0 ^ 2 := by linarith
  have ht2 : t ^ 2 ≤ ε ^ 2 * D0 ^ 2 / 4 := by
    have := pow_le_pow_left₀ ht0 ht 2; linarith
  have hinv : 1 / (2 * ε) ≤ 1 / r ^ 2 := one_div_le_one_div_of_le hr2' hr2
  have ht2' : t ^ 2 ≤ 1 / (8 * ε) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right ht2 (by positivity : (0:ℝ) ≤ 8 * ε); linarith
  have cK : 3 / (8 * ε) ≤ 1 / r ^ 2 - t ^ 2 := by
    have : 1 / (2 * ε) = 4 / (8 * ε) := by field_simp; ring
    have : 3 / (8 * ε) = 4 / (8 * ε) - 1 / (8 * ε) := by field_simp; ring
    linarith
  have hM0Λ : 64 * M0 ^ 2 ≤ Λ := by
    have : 0 ≤ 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 := by positivity
    linarith
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hM0Λ
  have cM : ε * Λ / 2 - ε * Λ / 16 - ε * Λ / 8 ≤ ν - 4 * r ^ 2 * M0 ^ 2 := by
    have h1 : ε ^ 2 * D0 ^ 2 / 4 ≤ ε * Λ / 16 := by
      have := mul_le_mul_of_nonneg_left hC1 (by positivity : (0:ℝ) ≤ ε / 4); linarith
    have h2 : 4 * r ^ 2 * M0 ^ 2 ≤ ε * Λ / 8 := by
      have := mul_le_mul_of_nonneg_left hM0Λ (by positivity : (0:ℝ) ≤ ε / 8); linarith
    linarith
  -- Young 1: `4r(M₁ + |ϑ|M₀) h m ≤ κ/8 h² + εΛ/8 m²`
  have y1 : 4 * r * (M1 + t * M0) * h * m ≤ κ / 8 * h ^ 2 + ε * Λ / 8 * m ^ 2 := by
    have hy := young (κ / 8) h (4 * r * (M1 + t * M0) * m) (by positivity)
    have hb : (M1 + t * M0) ^ 2 ≤ (M1 + 1) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    have hq : (4 * r * (M1 + t * M0) * m) ^ 2 ≤ 32 * ε * (M1 + 1) ^ 2 * m ^ 2 := by
      have : (4 * r * (M1 + t * M0) * m) ^ 2 = 16 * r ^ 2 * (M1 + t * M0) ^ 2 * m ^ 2 := by ring
      rw [this]
      have := mul_le_mul hr2 hb (sq_nonneg _) (by positivity)
      have := mul_le_mul_of_nonneg_right this (sq_nonneg m)
      linarith
    have hc : 1 / (4 * (κ / 8)) * (32 * ε * (M1 + 1) ^ 2 * m ^ 2) ≤ ε * Λ / 8 * m ^ 2 := by
      have e : 1 / (4 * (κ / 8)) * (32 * ε * (M1 + 1) ^ 2 * m ^ 2) =
          ε / 16 * (64 * 4 ^ 2 / κ * (M1 + 1) ^ 2) * m ^ 2 := by field_simp; ring
      rw [e]
      have : 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 ≤ Λ := by
        have := mul_nonneg (by norm_num : (0:ℝ) ≤ 16 * 4) (sq_nonneg M0); linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ ε / 16)
      have := mul_le_mul_of_nonneg_right this (sq_nonneg m)
      have := mul_nonneg (mul_nonneg hε.le hΛ0) (sq_nonneg m)
      linarith
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 1 / (4 * (κ / 8)))
    calc 4 * r * (M1 + t * M0) * h * m = h * (4 * r * (M1 + t * M0) * m) := by ring
      _ ≤ _ := hy
      _ ≤ _ := by linarith
  -- Young 2: `4(M₀ + r²M₀²) h k ≤ κ/8 h² + 1/(8ε) k²`
  have y2 : 4 * (M0 + r ^ 2 * M0 ^ 2) * h * k ≤ κ / 8 * h ^ 2 + 1 / (8 * ε) * k ^ 2 := by
    have hy := young (κ / 8) h (4 * (M0 + r ^ 2 * M0 ^ 2) * k) (by positivity)
    have hb : M0 + r ^ 2 * M0 ^ 2 ≤ 2 * M0 := by
      have h' := mul_le_mul_of_nonneg_left hA2 hM0; linarith
    have hq : (4 * (M0 + r ^ 2 * M0 ^ 2) * k) ^ 2 ≤ 64 * M0 ^ 2 * k ^ 2 := by
      have h0 : 0 ≤ M0 + r ^ 2 * M0 ^ 2 := by positivity
      have := pow_le_pow_left₀ h0 hb 2
      have := mul_le_mul_of_nonneg_right this (sq_nonneg k)
      linarith
    have hc : 1 / (4 * (κ / 8)) * (64 * M0 ^ 2 * k ^ 2) ≤ 1 / (8 * ε) * k ^ 2 := by
      rw [show 1 / (4 * (κ / 8)) * (64 * M0 ^ 2 * k ^ 2) = 128 * M0 ^ 2 / κ * k ^ 2 by
        field_simp; ring]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg k)
      rw [div_le_div_iff₀ hκ (by positivity)]
      linarith
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 1 / (4 * (κ / 8)))
    calc 4 * (M0 + r ^ 2 * M0 ^ 2) * h * k = h * (4 * (M0 + r ^ 2 * M0 ^ 2) * k) := by ring
      _ ≤ _ := hy
      _ ≤ _ := by linarith
  -- Young 3: `4 r |ϑ| M₀ k m ≤ 1/(8ε) k² + εΛ/16 m²`
  have y3 : 4 * r * t * M0 * k * m ≤ 1 / (8 * ε) * k ^ 2 + ε * Λ / 16 * m ^ 2 := by
    have hy := young (1 / (8 * ε)) k (4 * r * t * M0 * m) (by positivity)
    have e1 : 1 / (4 * (1 / (8 * ε))) = 2 * ε := by field_simp; ring
    rw [e1] at hy
    have hq : (4 * r * t * M0 * m) ^ 2 ≤ 8 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 * m ^ 2 := by
      have : (4 * r * t * M0 * m) ^ 2 = 16 * r ^ 2 * t ^ 2 * M0 ^ 2 * m ^ 2 := by ring
      rw [this]
      have := mul_le_mul hr2 ht2 (sq_nonneg _) (by positivity)
      have := mul_le_mul_of_nonneg_right this (mul_nonneg (sq_nonneg M0) (sq_nonneg m))
      linarith
    have hc : 2 * ε * (8 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 * m ^ 2) ≤ ε * Λ / 16 * m ^ 2 := by
      have := mul_le_mul_of_nonneg_left hC3 (by positivity : (0:ℝ) ≤ ε / 32)
      have := mul_le_mul_of_nonneg_right this (sq_nonneg m)
      have := mul_nonneg (mul_nonneg hε.le hΛ0) (sq_nonneg m)
      linarith
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 2 * ε)
    calc 4 * r * t * M0 * k * m = k * (4 * r * t * M0 * m) := by ring
      _ ≤ _ := hy
      _ ≤ _ := by linarith
  -- assemble
  unfold masterRHS
  have eh := mul_le_mul_of_nonneg_right cH (sq_nonneg h)
  have ek := mul_le_mul_of_nonneg_right cK (sq_nonneg k)
  have em := mul_le_mul_of_nonneg_right cM (sq_nonneg m)
  have e8 : 3 / (8 * ε) * k ^ 2 = 1 / (8 * ε) * k ^ 2 + 1 / (8 * ε) * k ^ 2 + 1 / (8 * ε) * k ^ 2 := by
    ring
  linarith [eh, ek, em, y1, y2, y3, e8]

/-- **`eq:reserve` ⇒ `eq:southlowerbound`** on a unit decomposable bivector. -/
theorem southlowerbound (κ ε Λ h m k : ℝ) (hunit : h ^ 2 + m ^ 2 + k ^ 2 = 1) :
    min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε)) ≤
      κ / 2 * h ^ 2 + ε * Λ / 8 * m ^ 2 + 1 / (8 * ε) * k ^ 2 := by
  set c := min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε))
  have h1 : c ≤ κ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : c ≤ ε * Λ / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : c ≤ 1 / (8 * ε) := min_le_right _ _
  have := mul_le_mul_of_nonneg_right h1 (sq_nonneg h)
  have := mul_le_mul_of_nonneg_right h2 (sq_nonneg m)
  have := mul_le_mul_of_nonneg_right h3 (sq_nonneg k)
  have e : c * h ^ 2 + c * m ^ 2 + c * k ^ 2 = c := by
    rw [← mul_add, ← mul_add, hunit, mul_one]
  linarith

/-- The positive lower bound `c_S = min{κ/2, εΛ/8, 1/(8ε)} > 0`. -/
theorem cS_pos (κ ε Λ : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hΛ : 0 < Λ) :
    0 < min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε)) := by
  apply lt_min (lt_min (by positivity) (by positivity)) (by positivity)

/-! ### The fibre radius `r² = ε e^{εφ}` -/

/-- `|εφ| ≤ log 2 ⇒ ε/2 ≤ ε e^{εφ} ≤ 2ε`. -/
theorem rsq_bounds (ε φ : ℝ) (hε : 0 < ε) (hφ : |ε * φ| ≤ Real.log 2) :
    ε / 2 ≤ ε * Real.exp (ε * φ) ∧ ε * Real.exp (ε * φ) ≤ 2 * ε := by
  have h1 := neg_abs_le (ε * φ)
  have h2 := le_abs_self (ε * φ)
  have hu : Real.exp (ε * φ) ≤ 2 := by
    calc Real.exp (ε * φ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hl : 1 / 2 ≤ Real.exp (ε * φ) := by
    calc (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      _ ≤ Real.exp (ε * φ) := Real.exp_le_exp.2 (by linarith)
  constructor <;> nlinarith

/-- The fibre radius `r(s) = √ε · e^{εφ(s)/2}` along a curve, so that `r² = ε e^{εφ}`. -/
noncomputable def fibreR (ε : ℝ) (φ : ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt ε * Real.exp (ε * φ s / 2)

/-- **The fibre-radius identities along a curve.** Let `φ` be twice differentiable along a
(unit-speed geodesic) parameter `s`, with derivatives `φ₁`, `φ₂`, and `r = fibreR ε φ`. Then
`r > 0`, `r² = εe^{εφ}` (`eq:smallradius`), `r' = r·(ε/2)φ₁` (i.e. `ϑ = d log r = (ε/2)dφ`), and
`r'' = r·((ε/2)φ₂ + (ε²/4)φ₁²)`, i.e. `−r''/r = −(ε/2)φ₂ − (ε²/4)φ₁²`. Along a unit-speed
geodesic `γ`, `(r∘γ)'' = Hess r(γ',γ')`, so this is
`N(γ',γ') = −r⁻¹Hess r(γ',γ') = −(ε/2)Hess φ(γ',γ') − (ε²/4)(dφ γ')²`. -/
theorem fibreRadius_derivs (ε : ℝ) (hε : 0 < ε) (φ φ₁ φ₂ : ℝ → ℝ)
    (h1 : ∀ s, HasDerivAt φ (φ₁ s) s) (h2 : ∀ s, HasDerivAt φ₁ (φ₂ s) s) (s : ℝ) :
    0 < fibreR ε φ s ∧ fibreR ε φ s ^ 2 = ε * Real.exp (ε * φ s) ∧
    HasDerivAt (fibreR ε φ) (fibreR ε φ s * (ε / 2 * φ₁ s)) s ∧
    HasDerivAt (fun s => fibreR ε φ s * (ε / 2 * φ₁ s))
      (fibreR ε φ s * (ε / 2 * φ₂ s + ε ^ 2 / 4 * φ₁ s ^ 2)) s := by
  have hr : ∀ s, HasDerivAt (fibreR ε φ) (fibreR ε φ s * (ε / 2 * φ₁ s)) s := by
    intro s
    have := (((h1 s).const_mul ε).div_const 2).exp.const_mul (Real.sqrt ε)
    unfold fibreR
    exact this.congr_deriv (by ring)
  refine ⟨by unfold fibreR; positivity, ?_, hr s, ?_⟩
  · unfold fibreR
    rw [mul_pow, Real.sq_sqrt hε.le, ← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * (ε * φ s / 2) = ε * φ s by push_cast; ring]
  · have := (hr s).mul ((h2 s).const_mul (ε / 2))
    exact this.congr_deriv (by ring)

/-- `|ϑ| = (ε/2)|dφ| ≤ εD₀/2` when `|dφ| ≤ D₀`. -/
theorem theta_bound (ε dφ D0 : ℝ) (hε : 0 < ε) (hd : |dφ| ≤ D0) : |ε / 2 * dφ| ≤ ε * D0 / 2 := by
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < ε / 2)]
  nlinarith

/-- `λ_min N ≥ εΛ/2 − ε²D₀²/4`: for a unit vector `x`, with `Hess φ(x,x) ≤ −Λ` and `|dφ(x)| ≤ D₀`,
`N(x,x) = −(ε/2)Hess φ(x,x) − (ε²/4)dφ(x)² ≥ εΛ/2 − ε²D₀²/4`. -/
theorem lambdaMin_bound (ε Λ D0 hess dx : ℝ) (hε : 0 < ε) (hH : hess ≤ -Λ) (hd : |dx| ≤ D0) :
    ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4 ≤ -(ε / 2) * hess - ε ^ 2 / 4 * dx ^ 2 := by
  have : dx ^ 2 ≤ D0 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  nlinarith [sq_nonneg ε]

/-! ### Non-vacuity: a non-degenerate admissible parameter set

`κ = M₀ = M₁ = D₀ = 1`, `Λ = 5000` (≥ `16·4·1 + 64·16·4 + 4 = 4164`), `ε = 1/2048`, `φ ≡ 1`
at the point, `|ϑ| = εD₀/2`, `λ_min N = εΛ/2 − ε²/4`. Every hypothesis of
`master_to_reserve`, including `eq:Lambda` *with* its `+4`, is discharged. -/

example (h m k : ℝ) :
    1 / 2 * h ^ 2 + (1 / 2048) * 5000 / 8 * m ^ 2 + 1 / (8 * (1 / 2048)) * k ^ 2 ≤
      masterRHS 4 1 (Real.sqrt ((1 / 2048) * Real.exp ((1 / 2048) * 1))) 1 1 ((1 / 2048) * 1 / 2)
        ((1 / 2048) * 5000 / 2 - (1 / 2048) ^ 2 * 1 ^ 2 / 4) h m k := by
  have hrb := rsq_bounds (1 / 2048) 1 (by norm_num) (by
    rw [mul_one, abs_of_pos (by norm_num)]
    have := Real.log_two_gt_d9; linarith)
  have hsq : Real.sqrt ((1 / 2048) * Real.exp ((1 / 2048) * 1)) ^ 2 =
      (1 / 2048) * Real.exp ((1 / 2048) * 1) := Real.sq_sqrt (by positivity)
  have hΛ : 16 * 4 * (1:ℝ) ^ 2 + 64 * 4 ^ 2 / 1 * (1 + 1) ^ 2 + 4 ≤ 5000 := by norm_num
  exact master_to_reserve 1 (1 / 2048) 5000 1 1 1 _ _ _ h m k one_pos (by norm_num) zero_le_one
    zero_le_one (Real.sqrt_pos.2 (by positivity)) (by norm_num)
    (by linarith) (by rw [hsq]; exact hrb.2) le_rfl le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end ExoticSpheres8And10
