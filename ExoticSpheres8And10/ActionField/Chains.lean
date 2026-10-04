/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.PolarBundles.Orientation
import ExoticSpheres8And10.Curvature.Criterion
import ExoticSpheres8And10.Curvature.Northern.Profiles

/-! # Chains: connecting three of the formalisation targets (see `docs/targets.md`)

1. **A1 ⇒ A5/A6.** The pointwise bound `‖K ξ‖² ≤ 4‖ξ‖²` gives `‖K‖ ≤ 2`, and then
   `T = −(F/r) K^*` has `‖T‖ ≤ 2F/r` ([GG] §4.3, "By the hypothesis `‖K‖_op ≤ 2`,
   `‖T‖_op ≤ 2F/r`"), using `‖K^*‖ = ‖K‖`.
2. **A3(c) ⇒ (d).** For a unit-quaternion-valued `θ`, `dθ θ⁻¹` is imaginary, so
   `β = dθ θ⁻¹` is a linear map into `Im ℍ`; with (c) this gives `det(Id − Kβ) = 1` as one
   theorem from the differentiated equivariance.
3. **A7 ⇒ `eq:northcriterion` ⇒ A6.** At a point of the northern profile satisfying the
   hypotheses of A7(b) and (c), every independent horizontal pair has positive numerator
   `eq:fullcurvature`, with `T = −(F/r)K^*` for any `K` with `‖K‖ ≤ 2`.
-/

namespace ExoticSpheres8And10

open scoped RealInnerProductSpace

/-! ## 1. `‖K‖ ≤ 2 ⇒ ‖−(F/r)K^*‖ ≤ 2F/r` -/

section Adjoint

variable {E F' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [CompleteSpace F']

omit [CompleteSpace E] [CompleteSpace F'] in
/-- A pointwise bound `‖Kξ‖² ≤ 4‖ξ‖²` (the form of A1) is `‖K‖ ≤ 2`. -/
theorem opNorm_le_two_of_sq (K : E →L[ℝ] F') (h : ∀ ξ, ‖K ξ‖ ^ 2 ≤ 4 * ‖ξ‖ ^ 2) : ‖K‖ ≤ 2 :=
  K.opNorm_le_bound (by norm_num) fun ξ => by
    have h2 : ‖K ξ‖ ^ 2 ≤ (2 * ‖ξ‖) ^ 2 := by nlinarith [h ξ]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- **[GG] §4.3.** If `‖K‖ ≤ 2`, `F ≥ 0`, `r > 0`, then `T = −(F/r) K^*` has `‖T‖ ≤ 2F/r`. -/
theorem norm_graphT_le (K : E →L[ℝ] F') (hK : ‖K‖ ≤ 2) {F r : ℝ} (hF : 0 ≤ F) (hr : 0 < r) :
    ‖-(F / r) • ContinuousLinearMap.adjoint K‖ ≤ 2 * F / r := by
  rw [norm_smul, LinearIsometryEquiv.norm_map, norm_neg, Real.norm_of_nonneg (by positivity)]
  calc F / r * ‖K‖ ≤ F / r * 2 := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = 2 * F / r := by ring

end Adjoint

/-! ## 2. `dθ θ⁻¹ ∈ Im ℍ` for unit-valued `θ`, and the composite orientation theorem -/

section Orientation

open Quaternion

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- If `θ` is differentiable at `y` and `‖θ‖ ≡ 1`, then `⟪θ(y), dθ_y v⟫ = 0` for every `v`. -/
theorem inner_self_dtheta_eq_zero (θ : Y → ℍ[ℝ]) (Dθ : Y →L[ℝ] ℍ[ℝ]) (y : Y)
    (hθ : HasFDerivAt θ Dθ y) (hunit : ∀ z, ‖θ z‖ = 1) (v : Y) : ⟪θ y, Dθ v⟫ = 0 := by
  have h1 := hθ.inner ℝ hθ
  have hconst : (fun t => ⟪θ t, θ t⟫) = fun _ => (1 : ℝ) := by
    funext t; rw [real_inner_self_eq_norm_sq, hunit, one_pow]
  rw [hconst] at h1
  have h0 := h1.unique (hasFDerivAt_const (1 : ℝ) y)
  have hv := congrArg (fun L => L v) h0
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.zero_apply] at hv
  have hc := real_inner_comm (θ y) (Dθ v)
  linarith

/-- **`dθ θ⁻¹` is imaginary** for a unit-valued differentiable `θ`. -/
theorem re_dtheta_mul_inv (θ : Y → ℍ[ℝ]) (Dθ : Y →L[ℝ] ℍ[ℝ]) (y : Y)
    (hθ : HasFDerivAt θ Dθ y) (hunit : ∀ z, ‖θ z‖ = 1) (v : Y) : (Dθ v * (θ y)⁻¹).re = 0 := by
  have hn : Quaternion.normSq (θ y) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hunit, one_mul]
  rw [Quaternion.inv_def, hn, inv_one, one_smul, ← Quaternion.inner_def,
    real_inner_comm]
  exact inner_self_dtheta_eq_zero θ Dθ y hθ hunit v

/-- `β = dθ θ⁻¹` in the coordinates `i, j, k` of `Im ℍ`. -/
noncomputable def betaCoord (Dθ : Y →L[ℝ] ℍ[ℝ]) (θy : ℍ[ℝ]) : Y →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![(Dθ v * θy⁻¹).imI, (Dθ v * θy⁻¹).imJ, (Dθ v * θy⁻¹).imK]
  map_add' v w := by
    funext i; fin_cases i <;> simp [add_mul]
  map_smul' c v := by
    funext i; fin_cases i <;> simp [Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul]

theorem imEmb_betaCoord (θ : Y → ℍ[ℝ]) (Dθ : Y →L[ℝ] ℍ[ℝ]) (y : Y)
    (hθ : HasFDerivAt θ Dθ y) (hunit : ∀ z, ‖θ z‖ = 1) (v : Y) :
    imEmb (betaCoord Dθ (θ y) v) = Dθ v * (θ y)⁻¹ := by
  have hre := re_dtheta_mul_inv θ Dθ y hθ hunit v
  ext <;> simp [imEmb, betaCoord, hre]

/-- **A3, composite.** Let `θ : Y → ℍ` be unit-valued and differentiable at `y`, with `Y`
finite-dimensional, and `K : Im ℍ → Y` linear such that for each `v` the orbit of `y` under a
curve of units `q` with `q 0 = 1`, `q' 0 = v` (as an imaginary quaternion) has velocity `K v`
and satisfies the equivariance `θ(γ τ) = q(τ) θ(y) q(τ)⁻¹`. Then, with `β = dθ θ⁻¹`,
`det(Id − Kβ) = 1` ([GG] `lem:attaching`(3): `det(Id − K_y β_y) = det Ad_{θ(y)} = 1`). -/
theorem det_id_sub_K_beta_of_equivariance [FiniteDimensional ℝ Y]
    (θ : Y → ℍ[ℝ]) (Dθ : Y →L[ℝ] ℍ[ℝ]) (y : Y) (hθ : HasFDerivAt θ Dθ y)
    (hunit : ∀ z, ‖θ z‖ = 1) (K : (Fin 3 → ℝ) →ₗ[ℝ] Y)
    (horbit : ∀ v, ∃ (γ : ℝ → Y) (q : ℝ → ℍ[ℝ]), γ 0 = y ∧ HasDerivAt γ (K v) 0 ∧ q 0 = 1 ∧
      HasDerivAt q (imEmb v) 0 ∧ (∀ τ, q τ ≠ 0) ∧ ∀ τ, θ (γ τ) = q τ * θ y * (q τ)⁻¹) :
    LinearMap.det (LinearMap.id - K ∘ₗ betaCoord Dθ (θ y)) = 1 := by
  have hθy : θ y ≠ 0 := by
    intro h; have := hunit y; rw [h, norm_zero] at this; exact zero_ne_one this
  refine det_id_sub_K_beta K (betaCoord Dθ (θ y)) (θ y) hθy fun v => ?_
  obtain ⟨γ, q, hγ0, hγ, hq0, hq, hqne, hequiv⟩ := horbit v
  rw [imEmb_betaCoord θ Dθ y hθ hunit]
  exact beta_K θ Dθ y hθ hθy γ (K v) hγ0 hγ q (imEmb v) hq0 hq hqne hequiv

end Orientation

/-! ## 3. The northern chain: A7(b), (c) ⇒ `eq:northcriterion` ⇒ A6 -/

section North

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [CompleteSpace Vv]

/-- **Northern filling, pointwise.** At a parameter value `s` of [GG]'s northern profile:
`F' = e^{−F²/(2δ²)}`, `F'' = −(F/δ²)F'²`, `0 ≤ r' ≤ d < 1`, `0 ≤ r''`, `r'' ≤ (d/δ)C_η`,
`r'' ≠ 0 ⇒ s ≤ δ/2` (the support of `η'`), `F ≤ s`, `eq:delta`'s `δ³` bound and
`d/r³ ≤ 4A₀F_a`. Then for every `K : Vv → H` with `‖K‖ ≤ 2`, with `T = −(F/r)K^*`, the numerator
`eq:fullcurvature` of every linearly independent star-horizontal pair is positive. -/
theorem north_numerator_pos_of_profile (F Fp Fpp s δ A0 Fa Ceta d r rp rpp : ℝ)
    (hF : 0 < F) (hδ : 0 < δ) (hA0 : 0 < A0) (hFa : 0 < Fa) (hC : 0 ≤ Ceta) (hr : 0 < r)
    (hFp : Fp = Real.exp (-F ^ 2 / (2 * δ ^ 2))) (hFpp : Fpp = -(F / δ ^ 2) * Fp ^ 2)
    (hδ3 : δ ^ 3 ≤ 1 / (128 * A0 * Fa * (1 + Ceta))) (hd : d / r ^ 3 ≤ 4 * A0 * Fa)
    (hrp0 : 0 ≤ rp) (hrpd : rp ≤ d) (hd1 : d < 1)
    (hrpp0 : 0 ≤ rpp) (hrpp : rpp ≤ d / δ * Ceta) (hsupp : rpp ≠ 0 → s ≤ δ / 2) (hFs : F ≤ s)
    (K : Vv →L[ℝ] H) (hK : ‖K‖ ≤ 2) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ
      ![((lam, X, (-(F / r) • ContinuousLinearMap.adjoint K) X) : ℝ × H × Vv),
        (mu, Y, (-(F / r) • ContinuousLinearMap.adjoint K) Y)]) :
    0 < northNumerator F r Fp rp Fpp rpp (-(F / r) • ContinuousLinearMap.adjoint K) X Y lam mu := by
  have hFp0 : 0 ≤ Fp := by rw [hFp]; exact (Real.exp_pos _).le
  have hc1 := angular_chain F Fp δ A0 Fa Ceta d r rp hF hδ hA0 hFa hC hr hFp hδ3 hd hrpd
  have hc2 : 4 * F ^ 2 * max rpp 0 / r ^ 3 < -Fpp / F := by
    rw [max_eq_left hrpp0]
    by_cases h0 : rpp = 0
    · -- off the support of `r''`: `−F''/F = F'²/δ² > 0`
      rw [h0, mul_zero, zero_div, hFpp]
      have : 0 < Fp := by rw [hFp]; exact Real.exp_pos _
      have e : -(-(F / δ ^ 2) * Fp ^ 2) / F = Fp ^ 2 / δ ^ 2 := by field_simp
      rw [e]; positivity
    · exact radial_chain F Fp Fpp s δ A0 Fa Ceta d r rpp hF hδ hA0 hFa hC hr hFp hδ3 hd hFs
        (hsupp h0) hrpp hFpp
  exact northNumerator_pos F r Fp rp Fpp rpp hF hr hFp0 hrp0 (by linarith) hc1 hc2 _
    (norm_graphT_le K hK hF.le hr) X Y lam mu hind

end North

/-! ## Non-vacuity -/

open Quaternion

example : ‖-(1 / 1 : ℝ) • ContinuousLinearMap.adjoint (0 : ℝ →L[ℝ] ℝ)‖ ≤ 2 * 1 / 1 :=
  norm_graphT_le 0 (by simp) zero_le_one one_pos

/-- (2) fires: `θ ≡ 1` on `Y = ℍ`, `K = 0`, the constant orbit `γ ≡ y`, and the curve of units
`q(τ) = 1 + τ v`. (Degenerate in `θ`, but every hypothesis, including `‖θ‖ ≡ 1` and the
equivariance, is genuinely satisfied.) -/
example (y : ℍ[ℝ]) :
    LinearMap.det (LinearMap.id - (0 : (Fin 3 → ℝ) →ₗ[ℝ] ℍ[ℝ]) ∘ₗ betaCoord 0 1) = 1 :=
  det_id_sub_K_beta_of_equivariance (fun _ => (1 : ℍ[ℝ])) 0 y (hasFDerivAt_const _ _)
    (fun _ => by simp) 0 fun v =>
      ⟨fun _ => y, fun τ => 1 + τ • imEmb v, rfl, by simpa using hasDerivAt_const (0 : ℝ) y,
        by simp, (curve_one_add_smul (imEmb v) rfl).1, (curve_one_add_smul (imEmb v) rfl).2,
        fun τ => by simp [mul_inv_cancel₀ ((curve_one_add_smul (imEmb v) rfl).2 τ)]⟩

/-- (3) fires at `δ = 1/8`, `A₀ = F_a = 1`, `C_η = 0`, `r = 1`, `d = 1/2`, `r' = 1/2`, `r'' = 0`,
`F = s = 1/16`, with `K = 0` on `H = Vv = ℝ` and the independent pair `(0,1,0), (1,0,0)`. -/
example : 0 < northNumerator (1 / 16) 1 (Real.exp (-(1 / 16) ^ 2 / (2 * (1 / 8) ^ 2))) (1 / 2)
    (-((1 / 16) / (1 / 8) ^ 2) * Real.exp (-(1 / 16) ^ 2 / (2 * (1 / 8) ^ 2)) ^ 2) 0
    (-((1 / 16 : ℝ) / 1) • ContinuousLinearMap.adjoint (0 : ℝ →L[ℝ] ℝ)) 1 0 0 1 := by
  apply north_numerator_pos_of_profile (1 / 16) _ _ (1 / 16) (1 / 8) 1 1 0 (1 / 2) 1 (1 / 2) 0
    (by norm_num) (by norm_num) one_pos one_pos le_rfl one_pos rfl rfl (by norm_num)
    (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num)
    (fun h => absurd rfl h) le_rfl 0 (by simp)
  rw [LinearIndependent.pair_iff]
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun p => p.2.1) h
  simp at h1 h2
  exact ⟨h2, h1⟩

end ExoticSpheres8And10
