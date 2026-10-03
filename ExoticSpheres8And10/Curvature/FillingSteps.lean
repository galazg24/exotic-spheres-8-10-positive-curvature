/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.ProfilesExistence
import ExoticSpheres8And10.Curvature.Northern.ProfilesCentre
import ExoticSpheres8And10.Curvature.Boundary.ShapeSum

/-! # §4: the remaining finite-dimensional steps of the two fillings

§4 of [D] adds several explicit computations to the text formalised in A4–A8. This
file formalises those that are finite-dimensional algebra or one-variable calculus:

* `starHorizontal_iff`: the star-horizontal distribution is the graph `U = TX`,
  `T = −(F/r)K_y^*` ([D] "The star-horizontal distribution");
* `starGram_ge`, `starVector_injective`: the Gram matrix `F²K^*K + r² ≥ r²`, so the star orbits
  are nonsingular even where `K_y` drops rank;
* `maurerCartan`, `curvature_chi`: `dϑ + ϑ∧ϑ = 0` for `ϑ = θ⁻¹dθ`, and
  `Ω_N = dχ∧ϑ + χ(χ−1)ϑ∧ϑ` for `A_N = χϑ` (southern filling);
* `height_geodesic`, `negHess_phi_ge`: `(cos t)'' = −cos t` along unit-speed great circles, and
  `−Hess φ ≥ A₀|cos a| g_B` for `φ = −A₀ cos t` on `t ≥ a > π/2`;
* `rS`, `bdata`, `rS_reflect`: the southern warping function, its boundary data `eq:bdata`, and
  its smooth even extension across `o_S`;
* `eventually_north_params`, `hly_parameter_choice`: the parameter order of the proof of
  `thm:HLYgeneral`. For every `ε_S > 0` there is `ε ∈ (0, ε_S)` for which the northern
  filling is positive on every star-horizontal plane and `c_B > 0`.
-/

namespace ExoticSpheres8And10

open Set Filter Topology Real

open scoped RealInnerProductSpace

open Quaternion

noncomputable section

/-! ### The star-horizontal distribution -/

section Horizontal

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [CompleteSpace Vv]

/-- **The star-horizontal space is a graph.** In scaled orthonormal components the star vector of
`ξ` is `(F K_y ξ, r ξ)`, and `X + U` is orthogonal to all of them iff `U = TX`,
`T = −(F/r) K_y^*`. -/
theorem starHorizontal_iff (K : Vv →L[ℝ] H) {F r : ℝ} (hr : r ≠ 0) (X : H) (U : Vv) :
    (∀ ξ : Vv, ⟪X, F • K ξ⟫ + ⟪U, r • ξ⟫ = 0) ↔
      U = (-(F / r) • ContinuousLinearMap.adjoint K) X := by
  set a := ContinuousLinearMap.adjoint K X
  constructor
  · intro h
    have h' : ∀ ξ, ⟪F • a + r • U, ξ⟫ = 0 := fun ξ => by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left]
      have := h ξ
      rwa [real_inner_smul_right, real_inner_smul_right] at this
    have hz : F • a + r • U = 0 := inner_self_eq_zero.1 (h' _)
    have h2 : r • U = -(F • a) := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hz
    rw [ContinuousLinearMap.smul_apply]
    calc U = r⁻¹ • (r • U) := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
      _ = -(F / r) • a := by rw [h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  · rintro rfl ξ
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
    field_simp
    ring

omit [CompleteSpace H] [CompleteSpace Vv] in
/-- **The Gram matrix of the star vectors** is `F²K^*K + r² ≥ r²`. -/
theorem starGram_ge (K : Vv →L[ℝ] H) (F r : ℝ) (ξ : Vv) :
    r ^ 2 * ‖ξ‖ ^ 2 ≤ ‖F • K ξ‖ ^ 2 + ‖r • ξ‖ ^ 2 := by
  rw [norm_smul r, mul_pow, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg ‖F • K ξ‖]

omit [CompleteSpace H] [CompleteSpace Vv] in
/-- The star orbits are nonsingular: `ξ ↦ (F K_y ξ, r ξ)` is injective for `r ≠ 0`. -/
theorem starVector_injective (K : Vv →L[ℝ] H) (F : ℝ) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective fun ξ : Vv => (F • K ξ, r • ξ) := by
  intro ξ ξ' h
  have := congrArg Prod.snd h
  exact smul_right_injective Vv hr this

end Horizontal

/-! ### The curvature of the southern connection -/

section MaurerCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exterior derivative of an `ℍ`-valued 1-form, `dα(v,w) = ∂_v(α(w)) − ∂_w(α(v))`. -/
def dForm (α : E → E → ℍ[ℝ]) (x v w : E) : ℍ[ℝ] :=
  fderiv ℝ (fun y => α y w) x v - fderiv ℝ (fun y => α y v) x w

/-- The Maurer–Cartan form `ϑ = θ⁻¹dθ`. -/
def mcForm (θ : E → ℍ[ℝ]) (y w : E) : ℍ[ℝ] := (θ y)⁻¹ * fderiv ℝ θ y w

theorem hasFDerivAt_mcForm {θ : E → ℍ[ℝ]} {x : E} (hθ : ContDiffAt ℝ 2 θ x) (hx : θ x ≠ 0)
    (w : E) : HasFDerivAt (fun y => mcForm θ y w)
      ((θ x)⁻¹ • ((ContinuousLinearMap.apply ℝ ℍ[ℝ] w).comp (fderiv ℝ (fderiv ℝ θ) x)) +
        ((-(ContinuousLinearMap.mulLeftRight ℝ ℍ[ℝ] (θ x)⁻¹ (θ x)⁻¹)).comp
          (fderiv ℝ θ x)).smulRight (fderiv ℝ θ x w)) x := by
  have hd1 : DifferentiableAt ℝ θ x := hθ.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ θ) x :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hinv : HasFDerivAt (fun y => (θ y)⁻¹)
      ((-(ContinuousLinearMap.mulLeftRight ℝ ℍ[ℝ] (θ x)⁻¹ (θ x)⁻¹)).comp (fderiv ℝ θ x)) x :=
    (hasFDerivAt_inv' hx).comp x hd1.hasFDerivAt
  have hw : HasFDerivAt (fun y => fderiv ℝ θ y w)
      ((ContinuousLinearMap.apply ℝ ℍ[ℝ] w).comp (fderiv ℝ (fderiv ℝ θ) x)) x :=
    (ContinuousLinearMap.apply ℝ ℍ[ℝ] w).hasFDerivAt.comp x hd2.hasFDerivAt
  exact hinv.mul' hw

/-- **The Maurer–Cartan equation** `dϑ + ϑ∧ϑ = 0` for `ϑ = θ⁻¹dθ`, where
`(ϑ∧ϑ)(v,w) = ϑ(v)ϑ(w) − ϑ(w)ϑ(v)`. -/
theorem maurerCartan {θ : E → ℍ[ℝ]} {x : E} (hθ : ContDiffAt ℝ 2 θ x) (hx : θ x ≠ 0)
    (v w : E) :
    dForm (mcForm θ) x v w =
      -(mcForm θ x v * mcForm θ x w - mcForm θ x w * mcForm θ x v) := by
  have hsymm := hθ.isSymmSndFDerivAt (by simp [minSmoothness])
  rw [dForm, (hasFDerivAt_mcForm hθ hx w).fderiv, (hasFDerivAt_mcForm hθ hx v).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul, mcForm]
  rw [hsymm v w]
  noncomm_ring

/-- **The curvature of `A_N = χϑ`** ([D] southern filling):
`Ω_N = dA_N + A_N∧A_N = dχ∧ϑ + χ(χ−1) ϑ∧ϑ`. -/
theorem curvature_chi {θ : E → ℍ[ℝ]} {χ : E → ℝ} {x : E} (hθ : ContDiffAt ℝ 2 θ x)
    (hx : θ x ≠ 0) (hχ : DifferentiableAt ℝ χ x) (v w : E) :
    dForm (fun y w => χ y • mcForm θ y w) x v w +
        ((χ x • mcForm θ x v) * (χ x • mcForm θ x w) -
          (χ x • mcForm θ x w) * (χ x • mcForm θ x v)) =
      (fderiv ℝ χ x v • mcForm θ x w - fderiv ℝ χ x w • mcForm θ x v) +
        (χ x * (χ x - 1)) • (mcForm θ x v * mcForm θ x w - mcForm θ x w * mcForm θ x v) := by
  have hMC := maurerCartan hθ hx v w
  rw [dForm] at hMC
  have hv' : HasFDerivAt (fun y => χ y • mcForm θ y v)
      (χ x • fderiv ℝ (fun y => mcForm θ y v) x + (fderiv ℝ χ x).smulRight (mcForm θ x v)) x :=
    hχ.hasFDerivAt.smul (hasFDerivAt_mcForm hθ hx v).differentiableAt.hasFDerivAt
  have hw' : HasFDerivAt (fun y => χ y • mcForm θ y w)
      (χ x • fderiv ℝ (fun y => mcForm θ y w) x + (fderiv ℝ χ x).smulRight (mcForm θ x w)) x :=
    hχ.hasFDerivAt.smul (hasFDerivAt_mcForm hθ hx w).differentiableAt.hasFDerivAt
  rw [dForm, hv'.fderiv, hw'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  set P := mcForm θ x v
  set Q := mcForm θ x w
  set Dv := fderiv ℝ (fun y => mcForm θ y w) x v
  set Dw := fderiv ℝ (fun y => mcForm θ y v) x w
  have e1 : χ x • Dv = χ x • Dw - χ x • (P * Q - Q * P) := by
    rw [← smul_sub, show Dv = Dw - (P * Q - Q * P) by rw [← neg_neg (P * Q - Q * P), ← hMC]; abel]
  rw [show χ x • Dv + fderiv ℝ χ x v • Q - (χ x • Dw + fderiv ℝ χ x w • P) =
    χ x • Dv - χ x • Dw + (fderiv ℝ χ x v • Q - fderiv ℝ χ x w • P) by abel, e1]
  rw [mul_sub, sub_smul, smul_sub, smul_sub, mul_one]
  module

end MaurerCartan

/-! ### The Hessian of the height on the round sphere -/

section Height

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Along the great circle `γ(s) = cos s ζ + sin s w`, the height `f = ⟪·, e⟫` satisfies
`(f∘γ)'' = −f∘γ`. For unit `ζ` and unit `w ⊥ ζ` this is a unit-speed geodesic, and the
identity is `Hess(cos t) = −cos t · g_B`. -/
theorem height_geodesic (e ζ w : W) (s : ℝ) :
    HasDerivAt (fun s => ⟪cos s • ζ + sin s • w, e⟫) (⟪-sin s • ζ + cos s • w, e⟫) s ∧
    HasDerivAt (fun s => ⟪-sin s • ζ + cos s • w, e⟫) (-⟪cos s • ζ + sin s • w, e⟫) s := by
  have h1 : (fun s => ⟪cos s • ζ + sin s • w, e⟫) = fun s => cos s * ⟪ζ, e⟫ + sin s * ⟪w, e⟫ := by
    funext s; rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h2 : (fun s => ⟪-sin s • ζ + cos s • w, e⟫) =
      fun s => -sin s * ⟪ζ, e⟫ + cos s * ⟪w, e⟫ := by
    funext s; rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [h1, h2, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left]
  constructor
  · exact ((hasDerivAt_cos s).mul_const _).add ((hasDerivAt_sin s).mul_const _) |>.congr_deriv
      (by ring)
  · exact (((hasDerivAt_sin s).neg).mul_const _).add ((hasDerivAt_cos s).mul_const _)
      |>.congr_deriv (by ring)

/-- **`−Hess φ ≥ A₀|cos a| g_B`** for `φ = −A₀ cos t` on `U_S = {t ≥ a}`, `π/2 < a`: along a
unit-speed geodesic through a point of height `cos t`, `−(φ∘γ)'' = −A₀ cos t`, and
`−cos t ≥ |cos a|` for `a ≤ t ≤ π`. -/
theorem negHess_phi_ge {a t A0 : ℝ} (ha : π / 2 < a) (hat : a ≤ t) (htπ : t ≤ π)
    (hA0 : 0 ≤ A0) : A0 * |cos a| ≤ -A0 * cos t := by
  have hca : cos a < 0 := cos_neg_of_pi_div_two_lt_of_lt ha (by linarith [pi_pos])
  have hct : cos t ≤ cos a :=
    cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) htπ hat
  rw [abs_of_neg hca]
  nlinarith

end Height

/-! ### The southern warping function and the boundary data `eq:bdata` -/

section Bdata

/-- `r_S(t) = √ε e^{−εA₀ cos t/2}`, so that `r_S² = ε e^{−εA₀ cos t}` (`eq:south`). -/
def rS (ε A0 t : ℝ) : ℝ := √ε * exp (-(ε * A0 * cos t) / 2)

theorem rS_sq {ε : ℝ} (hε : 0 ≤ ε) (A0 t : ℝ) : rS ε A0 t ^ 2 = ε * exp (-(ε * A0 * cos t)) := by
  rw [rS, mul_pow, sq_sqrt hε, ← exp_nat_mul]; congr 2; push_cast; ring

theorem rS_pos {ε : ℝ} (hε : 0 < ε) (A0 t : ℝ) : 0 < rS ε A0 t := by
  unfold rS; have := sqrt_pos.2 hε; positivity

theorem hasDerivAt_rS (ε A0 t : ℝ) :
    HasDerivAt (rS ε A0) (rS ε A0 t * (ε * A0 * sin t / 2)) t := by
  have h1 : HasDerivAt (fun y => -(ε * A0 * cos y) / 2) (-(ε * A0 * -sin t) / 2) t :=
    (((hasDerivAt_cos t).const_mul (ε * A0)).neg).div_const 2
  have h := h1.exp.const_mul √ε
  refine (h.congr_deriv ?_)
  simp only [rS]; ring

/-- **`eq:bdata`.** For `π/2 < a < π`: `F_a = sin a > 0`, `r_a² = εe^{εA₀|cos a|}`,
`q_s = r_S'(a)/r_a = ½εA₀F_a`, and `μ_S = (sin)'(a)/sin a = cot a < 0`. -/
theorem bdata {a ε A0 : ℝ} (ha : π / 2 < a) (haπ : a < π) (hε : 0 < ε) :
    0 < sin a ∧ rS ε A0 a ^ 2 = ε * exp (ε * A0 * |cos a|) ∧
    deriv (rS ε A0) a / rS ε A0 a = ε * A0 * sin a / 2 ∧
    deriv sin a / sin a = cos a / sin a ∧ cos a / sin a < 0 := by
  have hs : 0 < sin a := sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) haπ
  have hc : cos a < 0 := cos_neg_of_pi_div_two_lt_of_lt ha (by linarith [pi_pos])
  refine ⟨hs, ?_, ?_, by rw [Real.deriv_sin], div_neg_of_neg_of_pos hc hs⟩
  · rw [rS_sq hε.le, abs_of_neg hc]; congr 2; ring
  · rw [(hasDerivAt_rS ε A0 a).deriv, mul_div_cancel_left₀ _ (rS_pos hε A0 a).ne']

/-- **Smoothness across `o_S`.** With `τ = π − t`, `r_S(π − τ) = √ε e^{εA₀ cos τ/2}`, a smooth
even function of `τ`. -/
theorem rS_reflect (ε A0 τ : ℝ) :
    rS ε A0 (π - τ) = √ε * exp (ε * A0 * cos τ / 2) ∧ rS ε A0 (π - -τ) = rS ε A0 (π - τ) := by
  refine ⟨?_, ?_⟩
  · rw [rS, cos_pi_sub]; congr 2; ring
  · rw [rS, rS, cos_pi_sub, cos_pi_sub, cos_neg]

end Bdata

/-! ### The parameter order in the proof of `thm:HLYgeneral` -/

section Parameters

/-- **"For sufficiently small `ε`, `q_s ℓ_N ≤ ½` and `d < 1`"**, with `q_s = ½εA₀F_a`,
`r_a = √(εe^{εA₀|cos a|})` and `d = r_a q_s`, all other parameters fixed. -/
theorem eventually_north_params (A0 Fa a ℓ : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * A0 * Fa / 2 * ℓ ≤ 1 / 2 ∧
      √(ε * exp (ε * A0 * |cos a|)) * (ε * A0 * Fa / 2) < 1 := by
  have h1 : Tendsto (fun ε : ℝ => ε * A0 * Fa / 2 * ℓ) (𝓝 0) (𝓝 0) := by
    have : Continuous fun ε : ℝ => ε * A0 * Fa / 2 * ℓ := by fun_prop
    simpa using this.tendsto 0
  have h2 : Tendsto (fun ε : ℝ => √(ε * exp (ε * A0 * |cos a|)) * (ε * A0 * Fa / 2)) (𝓝 0)
      (𝓝 0) := by
    have : Continuous fun ε : ℝ => √(ε * exp (ε * A0 * |cos a|)) * (ε * A0 * Fa / 2) := by
      fun_prop
    simpa using this.tendsto 0
  have e1 := (h1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).mono
    fun _ h => h.le
  have e2 := h2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  exact nhdsWithin_le_nhds (e1.and e2)

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [CompleteSpace Vv]

/-- **The parameter choice of the proof of `thm:HLYgeneral`**, quantitative part. Fix
`π/2 < a < π`, `A₀ > 0`, `C_η ≥ |η'|` and `δ` satisfying `eq:delta` with `F_a = sin a`, so that
`ℓ_N = ∫_0^{F_a} e^{z²/2δ²}dz` is fixed. Then for every `ε_S > 0` there is `ε ∈ (0, ε_S)` such
that, with `r_a = r_S(a)`, `q_s = ½εA₀F_a` and `d = r_a q_s`:
* the northern numerator `eq:fullcurvature` is positive on every independent star-horizontal
  pair at every `s ∈ (0, ℓ_N]`, for every `K` with `‖K‖ ≤ 2`;
* the boundary constant `c_B = r_a²/(r_a²+4F_a²)(μ_N − μ_S)` is positive, where
  `μ_N = F'(ℓ_N)/F_a` and `μ_S = cot a`.

The Riemannian steps are imported and are not part of this statement: `fact:prop31` for the
south (which supplies `ε_S`), the curvature formula `eq:fullcurvature`, O'Neill's formula, and
`prop:gluing`. -/
theorem hly_parameter_choice (Cη : ℝ) (hC0 : 0 ≤ Cη) (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    {a A0 δ : ℝ} (ha : π / 2 < a) (haπ : a < π) (hA0 : 0 < A0) (hδ : 0 < δ)
    (hδ3 : δ ^ 3 ≤ 1 / (128 * A0 * sin a * (1 + Cη))) {εS : ℝ} (hεS : 0 < εS) :
    ∃ ε, 0 < ε ∧ ε < εS ∧
      (∀ s ∈ Ioc 0 (Gδ δ (sin a)), ∀ (K : Vv →L[ℝ] H), ‖K‖ ≤ 2 → ∀ (X Y : H) (lam mu : ℝ),
        LinearIndependent ℝ
          ![((lam, X, (-(Fprof δ s / rprof (rS ε A0 a) (rS ε A0 a * (ε * A0 * sin a / 2)) δ
              (Gδ δ (sin a)) s) • ContinuousLinearMap.adjoint K) X) : ℝ × H × Vv),
            (mu, Y, (-(Fprof δ s / rprof (rS ε A0 a) (rS ε A0 a * (ε * A0 * sin a / 2)) δ
              (Gδ δ (sin a)) s) • ContinuousLinearMap.adjoint K) Y)] →
        0 < northNumerator (Fprof δ s)
          (rprof (rS ε A0 a) (rS ε A0 a * (ε * A0 * sin a / 2)) δ (Gδ δ (sin a)) s)
          (exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)))
          (rS ε A0 a * (ε * A0 * sin a / 2) * etaCut (s / δ))
          (-(Fprof δ s / δ ^ 2) * exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) ^ 2)
          (rS ε A0 a * (ε * A0 * sin a / 2) * (deriv etaCut (s / δ) * (1 / δ)))
          (-(Fprof δ s / rprof (rS ε A0 a) (rS ε A0 a * (ε * A0 * sin a / 2)) δ
            (Gδ δ (sin a)) s) • ContinuousLinearMap.adjoint K) X Y lam mu) ∧
      0 < rS ε A0 a ^ 2 / (rS ε A0 a ^ 2 + 4 * sin a ^ 2) *
        (exp (-(sin a) ^ 2 / (2 * δ ^ 2)) / sin a - cos a / sin a) := by
  obtain ⟨hFa, -, -, -, hμS⟩ := bdata (A0 := A0) ha haπ hεS
  set ℓ := Gδ δ (sin a)
  have hev := (eventually_north_params A0 (sin a) a ℓ).and
    (Ioo_mem_nhdsGT hεS)
  obtain ⟨ε, ⟨hql, hd1⟩, hε0, hεε⟩ := hev.exists
  have hεpos : 0 < ε := hε0
  have hra := rS_pos hεpos A0 a
  have hra2 : rS ε A0 a ^ 2 = ε * exp (ε * A0 * |cos a|) := (bdata ha haπ hεpos).2.1
  have hsq : rS ε A0 a = √(ε * exp (ε * A0 * |cos a|)) := by
    rw [← hra2, sqrt_sq hra.le]
  refine ⟨ε, hεpos, hεε, fun s hs K hK X Y lam mu hind => ?_, ?_⟩
  · exact northern_filling_pos Cη hC0 hC a ε A0 (sin a) δ (rS ε A0 a) (ε * A0 * sin a / 2) _
      hεpos hA0 hFa hδ hδ3 hra hra2 rfl rfl hql (by rw [hsq]; exact hd1) s hs K hK X Y lam mu
      hind
  · have hN : 0 < exp (-(sin a) ^ 2 / (2 * δ ^ 2)) / sin a := div_pos (exp_pos _) hFa
    have : 0 < exp (-(sin a) ^ 2 / (2 * δ ^ 2)) / sin a - cos a / sin a := by linarith
    positivity

/-- `μ_N = F'(ℓ_N)/F_a = e^{−F_a²/2δ²}/F_a`: the northern boundary slope in
`hly_parameter_choice` is the derivative of the profile at `ℓ_N`. -/
theorem muN_eq (δ Fa : ℝ) :
    Fprof δ (Gδ δ Fa) = Fa ∧
      HasDerivAt (Fprof δ) (exp (-(Fa) ^ 2 / (2 * δ ^ 2))) (Gδ δ Fa) := by
  have h := hasDerivAt_Fprof δ (Gδ δ Fa)
  rw [Fprof_G] at h
  exact ⟨Fprof_G δ Fa, h⟩

end Parameters

end

end ExoticSpheres8And10
