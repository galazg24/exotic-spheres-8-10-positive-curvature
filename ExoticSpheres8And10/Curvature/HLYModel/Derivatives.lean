/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.HLYModel.Christoffel

/-! # §4, HLY model: frame derivatives of the curvature components

* `qe_struct`: `⟪q_d q_c, q_a⟫ + ⟪q_d, q_c q_a⟫ = cst_{dca}` for the units `q = i, j, k`;
* `vert_identity`: for imaginary `W`, `⟪W q_c, q_a⟫ + ⟪W, q_c q_a⟫ = Σ_d ⟪W, q_d⟫ cst_{dca}`;
* **`fderiv_Ωc_vert`**: the vertical derivative
  `E_c(Ω_{ij}^a) = r⁻¹ Σ_d Ω_{ij}^d cst_{dca}` ([HLY] `eq:verticalderivative`,
  `E_a(Ω^b) = −r⁻¹ c_{ac}^{b} Ω^c`);
* `fderiv_fst_apply`: a function of the base point is differentiated by the base component.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

theorem qe_struct (d c a : Fin 3) :
    ⟪qe d * qe c, qe a⟫ + ⟪qe d, qe c * qe a⟫ = Prop31Algebra.cst d c a := by
  rw [inner_quat, inner_quat]
  fin_cases d <;> fin_cases c <;> fin_cases a <;>
    simp [qe, Prop31Algebra.cst, Prop31Algebra.lc, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> norm_num

theorem vert_identity {W : Quaternion ℝ} (hW : W.re = 0) (c a : Fin 3) :
    ⟪W * qe c, qe a⟫ + ⟪W, qe c * qe a⟫ = ∑ d, ⟪W, qe d⟫ * Prop31Algebra.cst d c a := by
  conv_lhs => rw [← sum_inner_qe hW]
  rw [Finset.sum_mul, sum_inner, sum_inner]
  simp only [smul_mul_assoc, real_inner_smul_left, ← Finset.sum_add_distrib, ← mul_add, qe_struct]

section Deriv

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

theorem fderiv_fst_apply {φ : K → ℝ} (hφ : ContDiff ℝ ∞ φ) (z v : K × Quaternion ℝ) :
    fderiv ℝ (fun z : K × Quaternion ℝ => φ z.1) z v = fderiv ℝ φ z.1 v.1 := by
  have h : HasFDerivAt (fun z : K × Quaternion ℝ => φ z.1) _ z :=
    ((hφ.differentiable (by simp)) z.1).hasFDerivAt.comp z (hasFDerivAt_fst (p := z))
  rw [h.fderiv]
  rfl

/-- The vertical derivative of `Ω_{ij}^a`, at a point `(x, u)` with `|u| = 1`. -/
theorem fderiv_Ωc_vert (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (i j : Fin n)
    (a c : Fin 3) (z : K × Quaternion ℝ) (hz : Quaternion.normSq z.2 = 1) (s : ℝ) :
    fderiv ℝ (Ωc b A i j a) z ((0 : K), s • (z.2 * qe c)) =
      s * ∑ d, Ωc b A i j d z * Prop31Algebra.cst d c a := by
  set G : K → Quaternion ℝ := fun x => curvA A x (eb b i x) (eb b j x)
  have hG : ContDiff ℝ ∞ G := contDiff_curvA hA i j
  have hGd : HasFDerivAt (fun y : K × Quaternion ℝ => G y.1) ((fderiv ℝ G z.1).comp
      (ContinuousLinearMap.fst ℝ K (Quaternion ℝ))) z :=
    ((hG.differentiable (by simp)) z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hs : HasFDerivAt (fun y : K × Quaternion ℝ => y.2) (ContinuousLinearMap.snd ℝ K (Quaternion ℝ)) z :=
    hasFDerivAt_snd
  have h1 := hGd.mul' hs
  have h2 := hs.mul_const' (qe a)
  have h3 : HasFDerivAt (fun y : K × Quaternion ℝ => ⟪G y.1 * y.2, y.2 * qe a⟫) _ z :=
    h1.inner ℝ h2
  have e : Ωc b A i j a = fun y : K × Quaternion ℝ => ⟪G y.1 * y.2, y.2 * qe a⟫ := rfl
  rw [e, h3.fderiv]
  simp only [fderivInnerCLM_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Pi.mul_apply, op_smul_eq_mul, map_zero, zero_mul, smul_zero,
    add_zero, smul_eq_mul]
  -- reduce to the imaginary quaternion `W = ū G u`
  set u := z.2
  set W := star u * G z.1 * u
  have hu : star u * u = 1 := by rw [Quaternion.star_mul_self, hz]; rfl
  have hW : W.re = 0 := by rw [re_star_mul_mul, re_curvA hA hAim, zero_mul]
  have hstar : Quaternion.normSq (star u) = 1 := by rw [Quaternion.normSq_star, hz]
  have iso : ∀ p q : Quaternion ℝ, ⟪p, q⟫ = ⟪star u * p, star u * q⟫ := fun p q =>
    (inner_mul_left_unit' (star u) p q hstar).symm
  have hd : ∀ d, Ωc b A i j d z = ⟪W, qe d⟫ := fun d => by
    rw [Ωc, iso, ← mul_assoc (star u) u (qe d), hu, one_mul]
    simp only [W, mul_assoc]
    rfl
  have hv := vert_identity hW c a
  simp only [hd]
  rw [← hv, iso (G z.1 * (s • (u * qe c))), iso (G z.1 * u) ((s • (u * qe c)) * qe a)]
  simp only [mul_smul_comm, smul_mul_assoc, real_inner_smul_left, real_inner_smul_right]
  rw [show star u * (G z.1 * (u * qe c)) = W * qe c by simp only [W, mul_assoc],
    show star u * (u * qe c * qe a) = qe c * qe a by
      rw [mul_assoc, ← mul_assoc, hu, one_mul],
    show star u * (u * qe a) = qe a by rw [← mul_assoc, hu, one_mul],
    show star u * (G z.1 * u) = W by simp only [W, mul_assoc]]
  ring

end Deriv

end

end ExoticSpheres8And10
