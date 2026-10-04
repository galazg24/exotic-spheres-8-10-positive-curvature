/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.RoundMetric

/-! # Infrastructure: inverse stereographic projection and the round metric

For a unit vector `e` of a real inner product space `W` and `x ⊥ e`,

  `σ_e(x) = (4 + |x|²)⁻¹ ((4 − |x|²) e + 4x)`

is the inverse stereographic projection from `−e`, onto the unit sphere. For `x, a, b ⊥ e`:

* `norm_stereo`: `|σ_e(x)| = 1`;
* `hasFDerivAt_stereo`: `dσ_e(x) a = dst e x a`, explicitly;
* `inner_stereo_dst`: `⟪σ_e(x), dσ_e(x) a⟫ = 0`;
* **`inner_dst_dst`**: `⟪dσ_e(x) a, dσ_e(x) b⟫ = ψR(x) ⟪a, b⟫`. The pullback of the round
  metric is `HR`, the metric of `S4_Round`.
-/

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped RealInnerProductSpace ContDiff

noncomputable section

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Inverse stereographic projection from `−e`. -/
def stereoE (e x : W) : W := (4 + ‖x‖ ^ 2)⁻¹ • ((4 - ‖x‖ ^ 2) • e + (4 : ℝ) • x)

/-- Its differential, explicitly. -/
def dst (e x a : W) : W :=
  (-((4 + ‖x‖ ^ 2) ^ 2)⁻¹) • (2 * ⟪x, a⟫) • ((4 - ‖x‖ ^ 2) • e + (4 : ℝ) • x) +
    (4 + ‖x‖ ^ 2)⁻¹ • ((-(2 * ⟪x, a⟫)) • e + (4 : ℝ) • a)

theorem dst_add (e x a b : W) : dst e x (a + b) = dst e x a + dst e x b := by
  simp only [dst, inner_add_right]
  module

theorem dst_smul (e x a : W) (c : ℝ) : dst e x (c • a) = c • dst e x a := by
  simp only [dst, real_inner_smul_right]
  module

/-- `dσ_e(x)` as a continuous linear map. -/
def dstL (e x : W) : W →L[ℝ] W :=
  { toFun := dst e x
    map_add' := dst_add e x
    map_smul' := fun c a => dst_smul e x a c
    cont := by
      unfold dst
      fun_prop }

@[simp] theorem dstL_apply (e x a : W) : dstL e x a = dst e x a := rfl

theorem hasFDerivAt_stereo (e x : W) : HasFDerivAt (stereoE e) (dstL e x) x := by
  have hN2 : HasFDerivAt (fun y : W => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hD : HasFDerivAt (fun y : W => 4 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    HasFDerivAt.const_add 4 hN2
  have hDne : (4 + ‖x‖ ^ 2) ≠ 0 := by positivity
  have hDi : HasFDerivAt (fun y : W => (4 + ‖y‖ ^ 2)⁻¹)
      ((-((4 + ‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)) x :=
    (hasDerivAt_inv hDne).comp_hasFDerivAt x hD
  have hN : HasFDerivAt (fun y : W => (4 - ‖y‖ ^ 2) • e + (4 : ℝ) • y)
      ((-(2 • innerSL ℝ x)).smulRight e + (4 : ℝ) • ContinuousLinearMap.id ℝ W) x :=
    (HasFDerivAt.smul_const (HasFDerivAt.const_sub hN2 4) e).add
      ((hasFDerivAt_id x).const_smul (4 : ℝ))
  have h := hDi.smul hN
  refine h.congr_fderiv ?_
  ext a
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, dstL_apply, dst, two_smul, smul_eq_mul]
  module

theorem contDiff_stereo (e : W) : ContDiff ℝ ∞ (stereoE e) := by
  unfold stereoE
  refine ContDiff.smul ((contDiff_const.add (contDiff_norm_sq ℝ)).inv fun x => by positivity) ?_
  exact ((contDiff_const.sub (contDiff_norm_sq ℝ)).smul contDiff_const).add
    (contDiff_const.smul contDiff_id)

variable {e x : W}

theorem norm_stereo_sq (he : ‖e‖ = 1) (hx : ⟪x, e⟫ = 0) : ‖stereoE e x‖ ^ 2 = 1 := by
  have hD : (4 + ‖x‖ ^ 2) ≠ 0 := by positivity
  have hx' : ⟪e, x⟫ = 0 := by rw [real_inner_comm]; exact hx
  have hs : ‖stereoE e x‖ ^ 2 = ⟪stereoE e x, stereoE e x⟫ := (real_inner_self_eq_norm_sq _).symm
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hxx : ⟪x, x⟫ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  rw [hs]
  simp only [stereoE, real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, hee, hxx, hx, hx']
  field_simp
  ring

theorem norm_stereo (he : ‖e‖ = 1) (hx : ⟪x, e⟫ = 0) : ‖stereoE e x‖ = 1 := by
  have := norm_stereo_sq he hx
  have h0 := norm_nonneg (stereoE e x)
  nlinarith [sq_nonneg (‖stereoE e x‖ - 1)]

theorem inner_stereo_dst (he : ‖e‖ = 1) (hx : ⟪x, e⟫ = 0) (a : W) (ha : ⟪a, e⟫ = 0) :
    ⟪stereoE e x, dst e x a⟫ = 0 := by
  have hD : (4 + ‖x‖ ^ 2) ≠ 0 := by positivity
  have hx' : ⟪e, x⟫ = 0 := by rw [real_inner_comm]; exact hx
  have ha' : ⟪e, a⟫ = 0 := by rw [real_inner_comm]; exact ha
  simp only [stereoE, dst, real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, real_inner_self_eq_norm_sq, he, hx, ha, hx', ha']
  field_simp
  ring

/-- **The pullback of the round metric under `σ_e` is `HR`.** -/
theorem inner_dst_dst (he : ‖e‖ = 1) (hx : ⟪x, e⟫ = 0) (a b : W) (ha : ⟪a, e⟫ = 0)
    (hb : ⟪b, e⟫ = 0) : ⟪dst e x a, dst e x b⟫ = ψR x * ⟪a, b⟫ := by
  have hD : (4 + ‖x‖ ^ 2) ≠ 0 := by positivity
  have hx' : ⟪e, x⟫ = 0 := by rw [real_inner_comm]; exact hx
  have ha' : ⟪e, a⟫ = 0 := by rw [real_inner_comm]; exact ha
  have hb' : ⟪e, b⟫ = 0 := by rw [real_inner_comm]; exact hb
  have hax : ⟪a, x⟫ = ⟪x, a⟫ := real_inner_comm x a
  have hbx : ⟪b, x⟫ = ⟪x, b⟫ := real_inner_comm x b
  simp only [dst, ψR, real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, real_inner_self_eq_norm_sq, he, hx, ha, hb, hx', ha', hb', hax, hbx]
  field_simp
  ring

theorem stereo_zero (e : W) : stereoE e 0 = e := by
  simp [stereoE]

theorem dst_zero (e a : W) : dst e 0 a = a := by
  simp [dst]

end

end ExoticSpheres8And10
