/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Analysis.Entire
import ExoticSpheres8And10.Curvature.Gluing.Charts

/-! # Infrastructure: geodesic polar coordinates are smooth at the centre

[GG] identifies `U_α` with the closed disk of radius `R_α` by geodesic polar coordinates
`ζ_N = t x`, whose inverse is `expN(Y) = cos|Y| e + sin|Y| Y/|Y|`. The formula is singular at
`Y = 0`. Here it is written as a smooth composite:
* `muR s = sinc(√s/2)/cos(√s/2)`, through `S4_Entire`'s `sincSq`, `cosSq`, so that
  `r μ(r²) = 2 tan(r/2)` (`mul_muR`);
* `radialR Y = μ(|Y|²) Y`, the geodesic-to-stereographic radial map;
* **`stereoInv_radialR`**: `stereoInv(radialR Y / 2) = expN Y`, by the half-angle identities;
* `injective_fderiv_radialR`: `d(radialR)` is injective on `|Y| < π`, since `μ > 0` and
  `(rμ(r²))' = sec²(r/2) > 0`.
-/

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

namespace ExoticSpheres8And10

noncomputable section

/-- `μ(s) = sinc(√s/2)/cos(√s/2)`. -/
def muR (s : ℝ) : ℝ := sincSq (s / 4) / cosSq (s / 4)

theorem cos_half_pos {r : ℝ} (hr : |r| < π) : 0 < Real.cos (r / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_lt.1 hr], by linarith [abs_lt.1 hr]⟩

theorem cosSq_quarter (r : ℝ) : cosSq (r ^ 2 / 4) = Real.cos (r / 2) := by
  rw [show r ^ 2 / 4 = (r / 2) ^ 2 by ring, cosSq_sq]

theorem sincSq_quarter_mul (r : ℝ) : r / 2 * sincSq (r ^ 2 / 4) = Real.sin (r / 2) := by
  rw [show r ^ 2 / 4 = (r / 2) ^ 2 by ring, sincSq_sq]

/-- **`r μ(r²) = 2 tan(r/2)`** on `|r| < π`. -/
theorem mul_muR {r : ℝ} (hr : |r| < π) : r * muR (r ^ 2) = 2 * Real.tan (r / 2) := by
  have hc := cos_half_pos hr
  rw [muR, cosSq_quarter, Real.tan_eq_sin_div_cos, ← sincSq_quarter_mul]
  field_simp

theorem sincSq_pos {x : ℝ} (hx : |x| < π) : 0 < sincSq (x ^ 2) := by
  rcases eq_or_ne x 0 with h | h
  · rw [h]; simp [sincSq_zero]
  · have e := sincSq_sq x
    have hs : 0 < x * Real.sin x := by
      rcases lt_or_gt_of_ne h with h1 | h1
      · have : Real.sin x < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h1 (by linarith [abs_lt.1 hx])
        nlinarith
      · have : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [abs_lt.1 hx])
        nlinarith
    have : 0 < x * (x * sincSq (x ^ 2)) := by rw [e]; exact hs
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith

theorem muR_pos {s : ℝ} (h0 : 0 ≤ s) (hs : s < π ^ 2) : 0 < muR s := by
  set r := √s
  have hr : r ^ 2 = s := Real.sq_sqrt h0
  have hrπ : |r| < π := by
    rw [abs_of_nonneg (Real.sqrt_nonneg s)]
    exact (Real.sqrt_lt' Real.pi_pos).2 hs
  rw [← hr, muR, cosSq_quarter]
  have h1 : 0 < sincSq (r ^ 2 / 4) := by
    rw [show r ^ 2 / 4 = (r / 2) ^ 2 by ring]
    exact sincSq_pos (by rw [abs_div, abs_two]; linarith [abs_nonneg r, Real.pi_pos])
  exact div_pos h1 (cos_half_pos hrπ)

theorem contDiffAt_muR {s : ℝ} (h0 : 0 ≤ s) (hs : s < π ^ 2) : ContDiffAt ℝ ∞ muR s := by
  have hc : cosSq (s / 4) ≠ 0 := by
    set r := √s
    have hr : r ^ 2 = s := Real.sq_sqrt h0
    have hrπ : |r| < π := by
      rw [abs_of_nonneg (Real.sqrt_nonneg s)]
      exact (Real.sqrt_lt' Real.pi_pos).2 hs
    rw [← hr, cosSq_quarter]; exact (cos_half_pos hrπ).ne'
  exact ((contDiff_sincSq.comp (contDiff_id.div_const 4)).contDiffAt).div
    ((contDiff_cosSq.comp (contDiff_id.div_const 4)).contDiffAt) hc

/-- **`μ + 2sμ' > 0`** on `[0, π²)`: it is `(rμ(r²))' = sec²(r/2)` at `r = √s`. -/
theorem muR_add_deriv_pos {s : ℝ} (h0 : 0 ≤ s) (hs : s < π ^ 2) :
    0 < muR s + 2 * s * deriv muR s := by
  set r := √s
  have hr : r ^ 2 = s := Real.sq_sqrt h0
  have hrπ : |r| < π := by
    rw [abs_of_nonneg (Real.sqrt_nonneg s)]
    exact (Real.sqrt_lt' Real.pi_pos).2 hs
  have hmu := (contDiffAt_muR h0 hs).differentiableAt (by simp)
  -- the two derivatives of `r ↦ r μ(r²)`
  have hmu2 : DifferentiableAt ℝ muR (r ^ 2) := by rw [hr]; exact hmu
  have hd1 := (hasDerivAt_id r).mul
    (HasDerivAt.comp r (h := fun x : ℝ => x ^ 2) hmu2.hasDerivAt (hasDerivAt_pow 2 r))
  have hcr := cos_half_pos hrπ
  have hd2 : HasDerivAt (fun x => 2 * Real.tan (x / 2)) (2 * (1 / Real.cos (r / 2) ^ 2 * (1 / 2)))
      r := by
    have := (Real.hasDerivAt_tan hcr.ne').comp r ((hasDerivAt_id r).div_const 2)
    exact (this.const_mul 2).congr_deriv (by simp)
  have heq : (fun x => x * muR (x ^ 2)) =ᶠ[𝓝 r] fun x => 2 * Real.tan (x / 2) := by
    have : {x : ℝ | |x| < π} ∈ 𝓝 r :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hrπ
    filter_upwards [this] with x hx
    exact mul_muR hx
  have hu := hd1.unique (hd2.congr_of_eventuallyEq heq)
  have hpos : 0 < 2 * (1 / Real.cos (r / 2) ^ 2 * (1 / 2)) := by positivity
  simp only [id, Function.comp_apply, one_mul, Nat.cast_ofNat, pow_one] at hu
  rw [← hr]
  nlinarith [hu]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] {e : W}

/-- The radial map `Y ↦ μ(|Y|²) Y` on `V = e^⊥`. -/
def radialR (Y : Vs e) : Vs e := muR (‖Y‖ ^ 2) • Y

theorem contDiffAt_radialR {Y : Vs e} (hY : ‖Y‖ < π) : ContDiffAt ℝ ∞ (radialR (e := e)) Y := by
  have hs : ‖Y‖ ^ 2 < π ^ 2 := by
    have := norm_nonneg Y; nlinarith [Real.pi_pos]
  exact ((contDiffAt_muR (by positivity) hs).comp Y (contDiff_norm_sq ℝ).contDiffAt).smul
    contDiffAt_id

theorem fderiv_radialR_apply {Y : Vs e} (hY : ‖Y‖ < π) (h : Vs e) :
    fderiv ℝ (radialR (e := e)) Y h =
      muR (‖Y‖ ^ 2) • h + (deriv muR (‖Y‖ ^ 2) * (2 * ⟪Y, h⟫)) • Y := by
  have hs : ‖Y‖ ^ 2 < π ^ 2 := by
    have := norm_nonneg Y; nlinarith [Real.pi_pos]
  have hmu := ((contDiffAt_muR (by positivity) hs).differentiableAt (by simp)).hasDerivAt
  have h1 := (hmu.comp_hasFDerivAt Y (hasStrictFDerivAt_norm_sq Y).hasFDerivAt).smul
    (hasFDerivAt_id Y)
  rw [show radialR (e := e) = (muR ∘ fun x : Vs e => ‖x‖ ^ 2) • id from rfl, h1.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, Function.comp_apply, id,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]

/-- **`d(radialR)` is injective** on `|Y| < π`. -/
theorem injective_fderiv_radialR {Y : Vs e} (hY : ‖Y‖ < π) :
    Injective (fderiv ℝ (radialR (e := e)) Y) := by
  have hs : ‖Y‖ ^ 2 < π ^ 2 := by
    have := norm_nonneg Y; nlinarith [Real.pi_pos]
  have hμ := muR_pos (by positivity) hs
  have hμ' := muR_add_deriv_pos (by positivity) hs
  rw [injective_iff_map_eq_zero]
  intro h hh
  rw [fderiv_radialR_apply hY] at hh
  have h1 := congrArg (fun w => ⟪Y, w⟫) hh
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, inner_zero_right]
    at h1
  have hYh : ⟪Y, h⟫ = 0 := by
    have : (muR (‖Y‖ ^ 2) + 2 * ‖Y‖ ^ 2 * deriv muR (‖Y‖ ^ 2)) * ⟪Y, h⟫ = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h2 | h2
    · linarith
    · exact h2
  rw [hYh, mul_zero, mul_zero, zero_smul, add_zero] at hh
  exact (smul_eq_zero.1 hh).resolve_left hμ.ne'

theorem coe_radialR (Y : Vs e) : ((radialR Y : Vs e) : W) = muR (‖Y‖ ^ 2) • (Y : W) := rfl

/-- **The radial map is geodesic polar coordinates in stereographic form**:
`stereoInv(radialR Y / 2) = expN Y` for `|Y| < π`. -/
theorem stereoInv_radialR {Y : Vs e} (hY : ‖Y‖ < π) :
    stereoInv e ((1 / 2 : ℝ) • ((radialR Y : Vs e) : W)) = expN e (Y : W) := by
  rw [coe_radialR]
  rcases eq_or_ne Y 0 with h0 | h0
  · subst h0; simp [stereoInv, expN]
  set r := ‖Y‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 h0
  have hrπ : |r| < π := by rw [abs_of_pos hr]; exact hY
  have hc := cos_half_pos hrπ
  set sn := Real.sin (r / 2)
  set cs := Real.cos (r / 2)
  have hsc : sn ^ 2 + cs ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hmu : muR (r ^ 2) = 2 * (sn / cs) / r := by
    have := mul_muR hrπ
    rw [Real.tan_eq_sin_div_cos] at this
    rw [eq_div_iff hr.ne', mul_comm]; exact this
  have hcosr : Real.cos r = cs ^ 2 - sn ^ 2 := by
    have : r = 2 * (r / 2) := by ring
    rw [this, Real.cos_two_mul]; nlinarith
  have hsinr : Real.sin r = 2 * sn * cs := by
    have : r = 2 * (r / 2) := by ring
    rw [this, Real.sin_two_mul]
  have hYW : ‖(Y : W)‖ = r := rfl
  have hv : ‖(1 / 2 : ℝ) • muR (r ^ 2) • (Y : W)‖ = sn / cs := by
    rw [norm_smul, norm_smul, hYW, hmu, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hpos : 0 ≤ 2 * (sn / cs) / r := by
      rw [← hmu]; exact (muR_pos (by positivity) (by nlinarith [abs_lt.1 hrπ])).le
    rw [abs_of_nonneg hpos]
    field_simp
  have h1t : 1 + (sn / cs) ^ 2 = 1 / cs ^ 2 := by
    field_simp; linarith
  rw [stereoInv, hv, expN, hYW, hcosr, hsinr, hmu, h1t]
  simp only [smul_add, smul_smul]
  congr 1
  · congr 1; field_simp
  · congr 1; field_simp

end

end ExoticSpheres8And10
