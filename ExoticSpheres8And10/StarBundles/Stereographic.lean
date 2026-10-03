/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.StarBundles.Step2

/-! # §3: stereographic coordinates on `U_N`

[D] Step 3 parametrises `U_N` by `exp_{o_N} : B_π(0) ⊂ V → U_N` and transports along
`τ ↦ exp_{o_N}(τ v)`. We use instead the inverse stereographic projection from `o_S = −e`,
`φ(v) = ((1 − ‖v‖²)e + 2v)/(1 + ‖v‖²)`, a `ρ`-equivariant diffeomorphism `V ≅ U_N` sending
`0 ↦ o_N` and each ray `τ ↦ τv` onto a meridian (reparametrised). Horizontal lifts are invariant
under reparametrisation, so this gives the same sections; its advantage is that `φ` is a rational
map, smooth at the centre without the `sinc` expansion.

* `stereoInv`, `stereo`: the two maps (ambient formulas) and `stereo_stereoInv`,
  `stereoInv_stereo`;
* `stereoInv_map`, `stereo_map`: equivariance under isometries fixing `e`.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section Stereo

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W)

/-- The inverse stereographic projection from `−e`. -/
def stereoInv (v : W) : W := (1 + ‖v‖ ^ 2)⁻¹ • ((1 - ‖v‖ ^ 2) • e + (2 : ℝ) • v)

/-- The stereographic projection from `−e` onto `V = e^⊥`. -/
def stereo (ζ : W) : W := (1 + ⟪ζ, e⟫)⁻¹ • (ζ - ⟪ζ, e⟫ • e)

theorem contDiff_stereoInv : ContDiff ℝ ∞ (stereoInv e) := by
  have h1 : ContDiff ℝ ∞ fun v : W => (1 + ‖v‖ ^ 2)⁻¹ :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).inv fun v => by positivity
  exact h1.smul (((contDiff_const.sub (contDiff_norm_sq ℝ)).smul contDiff_const).add
    (contDiff_const.smul contDiff_id))

theorem contDiffAt_stereo {ζ : W} (h : ⟪ζ, e⟫ ≠ -1) : ContDiffAt ℝ ∞ (stereo e) ζ := by
  have hi : ContDiff ℝ ∞ fun ζ : W => ⟪ζ, e⟫ := contDiff_id.inner ℝ contDiff_const
  have h1 : ContDiffAt ℝ ∞ (fun ζ : W => (1 + ⟪ζ, e⟫)⁻¹) ζ :=
    ((contDiff_const.add hi).contDiffAt).inv (by intro h'; apply h; linarith)
  exact h1.smul ((contDiff_id.sub (hi.smul contDiff_const)).contDiffAt)

theorem stereoInv_map (T : W →ₗᵢ[ℝ] W) (hT : T e = e) (v : W) :
    stereoInv e (T v) = T (stereoInv e v) := by
  rw [stereoInv, stereoInv, T.norm_map, map_smul, map_add, map_smul, map_smul, hT]

theorem stereo_map (T : W →ₗᵢ[ℝ] W) (hT : T e = e) (ζ : W) : stereo e (T ζ) = T (stereo e ζ) := by
  have hi : ⟪T ζ, e⟫ = ⟪ζ, e⟫ := by rw [← hT, T.inner_map_map, hT]
  rw [stereo, stereo, hi, map_smul, map_sub, map_smul, hT]

variable {e} (he : ‖e‖ = 1)
include he

theorem inner_stereo (ζ : W) : ⟪stereo e ζ, e⟫ = 0 := by
  rw [stereo, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he]; ring

theorem inner_stereoInv {v : W} (hv : ⟪v, e⟫ = 0) :
    ⟪stereoInv e v, e⟫ = (1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2) := by
  rw [stereoInv, real_inner_smul_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, he, hv]
  field_simp
  ring

theorem norm_stereoInv {v : W} (hv : ⟪v, e⟫ = 0) : ‖stereoInv e v‖ = 1 := by
  have hpos : 0 < 1 + ‖v‖ ^ 2 := by positivity
  have hsq : ‖(1 - ‖v‖ ^ 2) • e + (2 : ℝ) • v‖ ^ 2 = (1 + ‖v‖ ^ 2) ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, real_inner_comm, hv,
      norm_smul, norm_smul, he, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
      sq_abs]
    ring
  have hn : ‖(1 - ‖v‖ ^ 2) • e + (2 : ℝ) • v‖ = 1 + ‖v‖ ^ 2 :=
    (pow_left_inj₀ (norm_nonneg _) hpos.le two_ne_zero).1 hsq
  rw [stereoInv, norm_smul, hn, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

theorem stereoInv_ne_neg {v : W} (hv : ⟪v, e⟫ = 0) : stereoInv e v ≠ -e := by
  intro h
  have h1 := inner_stereoInv he hv
  rw [h, inner_neg_left, real_inner_self_eq_norm_sq, he] at h1
  have hpos : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [eq_div_iff hpos.ne'] at h1
  norm_num at h1; linarith

theorem stereo_stereoInv {v : W} (hv : ⟪v, e⟫ = 0) : stereo e (stereoInv e v) = v := by
  have hpos : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [stereo, inner_stereoInv he hv, stereoInv]
  have h1 : 1 + (1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2) = 2 / (1 + ‖v‖ ^ 2) := by field_simp; ring
  rw [h1]
  have h2 : (1 + ‖v‖ ^ 2)⁻¹ • ((1 - ‖v‖ ^ 2) • e + (2 : ℝ) • v) -
      ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2)) • e = (2 / (1 + ‖v‖ ^ 2)) • v := by
    rw [smul_add, smul_smul, smul_smul]; rw [div_eq_inv_mul, div_eq_inv_mul]; abel
  rw [h2, smul_smul, inv_div, div_mul_div_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    div_self hpos.ne', one_smul]

theorem stereoInv_stereo {ζ : W} (hζ : ‖ζ‖ = 1) (h : ⟪ζ, e⟫ ≠ -1) :
    stereoInv e (stereo e ζ) = ζ := by
  set c := ⟪ζ, e⟫ with hc
  have hc1 : -1 < c := by
    have := abs_real_inner_le_norm ζ e
    rw [hζ, he, one_mul] at this
    exact lt_of_le_of_ne (abs_le.1 this).1 (Ne.symm h)
  have hpos : 0 < 1 + c := by linarith
  have hw : ‖ζ - c • e‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hζ, he, Real.norm_eq_abs, mul_one,
      sq_abs]; ring
  have hn : ‖stereo e ζ‖ ^ 2 = (1 - c) / (1 + c) := by
    rw [stereo, norm_smul, mul_pow, hw, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_pow]
    field_simp; ring
  rw [stereoInv, hn, stereo]
  have e1 : 1 + (1 - c) / (1 + c) = 2 / (1 + c) := by field_simp; ring
  have e2 : 1 - (1 - c) / (1 + c) = 2 * c / (1 + c) := by field_simp; ring
  rw [e1, e2, smul_smul, inv_div]
  rw [smul_add, smul_smul, smul_smul]
  have hpos' : (1 + ⟪ζ, e⟫) ≠ 0 := hpos.ne'
  have e3 : (1 + c) / 2 * (2 * c / (1 + c)) = c := by field_simp
  have e4 : (1 + c) / 2 * (2 * (1 + ⟪ζ, e⟫)⁻¹) = 1 := by rw [← hc]; field_simp
  rw [e3, e4, one_smul, hc]
  abel

end Stereo

end

end ExoticSpheres8And10
