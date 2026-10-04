/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.HLYModel.Blocks

/-! # §4, the southern filling: positive curvature of `G_S` on the cap

* `GH_vecF`, `vecF_coords`: the frame is orthonormal and spans, so every tangent vector at
  `(y, u)` is `vecF v`, and `GH(vecF v, vecF w) = v·w`;
* `sec_pos_of_bound`: a D2-type lower bound `m·totalGram ≤ Rm` with `m > 0` gives positive `RiemannianGeometry`
  sectional curvature on every plane at the point;
* `rSy`, `ϑf_rSy`, `dϑy_rSy`, `Ny_rSy`: [GG]'s southern radius `r_S² = ε e^{εφ}`,
  `φ = −A₀ cos t`, in the chart centred at the south pole, where `cos t = −(4−|y|²)/(4+|y|²)`.
  There `ϑ_i = −2εA₀y_i/(4+|y|²)` and `N = (εA₀/2)·(4−|y|²)/(4+|y|²)·I − ϑ⊗ϑ`, which is [GG]'s
  `−Hess φ = −A₀ cos t · g_B` (`eq:south`).
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

section Sec

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

set_option synthInstance.maxHeartbeats 400000 in
theorem GH_vecF (hAim : ∀ x v, (A x v).re = 0) (hr0 : ∀ x, r x ≠ 0) (p : K × S3)
    (v w : Prop31Algebra.Tv n) :
    GH A r p (vecF b A r p v) (vecF b A r p w) = Prop31Algebra.dot v.1 w.1 + Prop31Algebra.dot v.2 w.2 := by
  unfold vecF
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, GH_Fr hAim hr0, kron, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Fintype.sum_sum_type, coef, Sum.elim_inl, Sum.elim_inr, Prop31Algebra.dot, mul_comm (w.1 _),
    mul_comm (w.2 _)]

theorem vecF_coords (hAim : ∀ x v, (A x v).re = 0) (hr0 : ∀ x, r x ≠ 0) (p : K × S3)
    (w : TangentSpace (IN K) p) :
    w = vecF b A r p (fun i => GH A r p w (Fr b A r (.inl i) p),
      fun a => GH A r p w (Fr b A r (.inr a) p)) := by
  conv_lhs => rw [span_of_orthonormal (isPosDef_GH hr0) (fun α β y => GH_Fr (b := b) hAim hr0 α β y)
    (finrank_card b) p w]
  unfold vecF
  refine Finset.sum_congr rfl fun α _ => ?_
  rcases α with i | a <;> rfl

/-- **A D2 bound gives positive sectional curvature at the point.** -/
theorem sec_pos_of_bound (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (p : K × S3) {m : ℝ} (hm : 0 < m)
    (hb : ∀ X Y U V, m * Prop31Algebra.totalGram X Y U V ≤
      riemannTensorAt isSymm_GH (isPosDef_GH (A := A) hr0).isNondegenerate
        (isContMDiffMetricSection_GH hA hr) p (vecF b A r p (X, U)) (vecF b A r p (Y, V))
        (vecF b A r p (Y, V)) (vecF b A r p (X, U)))
    (w₁ w₂ : TangentSpace (IN K) p) (hli : LinearIndependent ℝ ![w₁, w₂]) :
    0 < sectionalCurvatureAt isSymm_GH (isPosDef_GH (A := A) hr0)
      (isContMDiffMetricSection_GH hA hr) p w₁ w₂ := by
  have hg := gramDet_pos isSymm_GH (isPosDef_GH (A := A) hr0) hli
  obtain ⟨v₁, rfl⟩ : ∃ v, w₁ = vecF b A r p v := ⟨_, vecF_coords hAim hr0 p w₁⟩
  obtain ⟨v₂, rfl⟩ : ∃ v, w₂ = vecF b A r p v := ⟨_, vecF_coords hAim hr0 p w₂⟩
  have hG : gramDet (GH A r) p (vecF b A r p v₁) (vecF b A r p v₂) =
      Prop31Algebra.totalGram v₁.1 v₂.1 v₁.2 v₂.2 := by
    unfold gramDet Prop31Algebra.totalGram
    rw [GH_vecF hAim hr0, GH_vecF hAim hr0, GH_vecF hAim hr0]
  have h := hb v₁.1 v₂.1 v₁.2 v₂.2
  rw [Prod.mk.eta, Prod.mk.eta, ← hG] at h
  rw [sectionalCurvatureAt_def]
  exact div_pos (lt_of_lt_of_le (mul_pos hm hg) h) hg

/-- **[HLY] Prop. 3.1 at `(y, u)`, as positive sectional curvature.** -/
theorem hly_sec_pos_at (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hr : ContDiff ℝ ∞ r) (hrpos : ∀ x, 0 < r x) (y : K) (u : S3) (ν M0 M1 ε Λ D0 : ℝ)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hε : 0 < ε)
    (hOm : Prop31Algebra.OmSq (Ωy b A y u) ≤ 2 * M0 ^ 2)
    (hDOm : ∑ i, ∑ j, ∑ k, ∑ a, DΩy b A r y u i j k a ^ 2 ≤ 2 * M1 ^ 2)
    (hν : ∀ x : Fin n → ℝ, ν * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, Ny b r y i j * x i * x j)
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 * (M1 + 1) ^ 2 ≤ Λ)
    (hr2 : r y ^ 2 ≤ 2 * ε) (htD : √(∑ k, ϑy b r y k ^ 2) ≤ ε * D0 / 2)
    (hνΛ : ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4 ≤ ν)
    (hA2 : 2 * ε * M0 ≤ 1) (hA3 : ε * D0 * M0 ≤ 1)
    (hB2 : 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ 1)
    (hC1 : ε * D0 ^ 2 ≤ Λ / 4) (hC2 : 2 * ε ^ 3 * D0 ^ 2 ≤ 1)
    (hC3 : 32 * 4 ^ 2 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 ≤ Λ)
    (w₁ w₂ : TangentSpace (IN K) ((y, u) : K × S3)) (hli : LinearIndependent ℝ ![w₁, w₂]) :
    0 < sectionalCurvatureAt isSymm_GH (isPosDef_GH (A := A) fun x => (hrpos x).ne')
      (isContMDiffMetricSection_GH hA hr) (y, u) w₁ w₂ := by
  have hΛpos : 0 < Λ := by nlinarith [sq_nonneg M0, sq_nonneg (M1 + 1)]
  have hm : 0 < min (min (1 / 2) (ε * Λ / 8)) (1 / (8 * ε)) := by
    refine lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  exact sec_pos_of_bound hA hAim hr (fun x => (hrpos x).ne') (y, u) hm
    (fun X Y U V => hly_prop31_at hA hAim hr hrpos y u ν M0 M1 ε Λ D0 hM0 hM1 hε hOm hDOm hν hΛ
      hr2 htD hνΛ hA2 hA3 hB2 hC1 hC2 hC3 X Y U V) w₁ w₂ hli

end Sec

/-! ## The southern radius in the chart centred at the south pole -/

section Radius

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K}

/-- `φ = −A₀ cos t`: in the chart centred at `o_S`, `cos t = −(4−|y|²)/(4+|y|²)`. -/
def φS (A0 : ℝ) (y : K) : ℝ := A0 * (4 - ‖y‖ ^ 2) / (4 + ‖y‖ ^ 2)

/-- [GG]'s southern radius `r_S = √ε e^{εφ/2}` (`eq:south`). -/
def rSy (ε A0 : ℝ) (y : K) : ℝ := √ε * Real.exp (ε / 2 * φS A0 y)

theorem den_pos (y : K) : 0 < 4 + ‖y‖ ^ 2 := by positivity

theorem hasFDerivAt_inner_right (w y : K) :
    HasFDerivAt (fun x : K => ⟪x, w⟫) (innerSL ℝ w) y := by
  have := (innerSL ℝ w).hasFDerivAt (x := y)
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  simp [real_inner_comm]

theorem contDiff_φS (A0 : ℝ) : ContDiff ℝ ∞ (φS (K := K) A0) :=
  (contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ))).div
    (contDiff_const.add (contDiff_norm_sq ℝ)) fun y => (den_pos y).ne'

theorem contDiff_rSy (ε A0 : ℝ) : ContDiff ℝ ∞ (rSy (K := K) ε A0) :=
  contDiff_const.mul ((contDiff_const.mul (contDiff_φS A0)).exp)

theorem rSy_pos {ε : ℝ} (hε : 0 < ε) (A0 : ℝ) (y : K) : 0 < rSy ε A0 y :=
  mul_pos (Real.sqrt_pos.2 hε) (Real.exp_pos _)

theorem fderiv_φS_apply (A0 : ℝ) (y v : K) :
    fderiv ℝ (φS A0) y v = -(16 * A0) * ⟪y, v⟫ / (4 + ‖y‖ ^ 2) ^ 2 := by
  have hs := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hinv := (hasDerivAt_inv (den_pos y).ne').comp_hasFDerivAt y (hs.const_add 4)
  have h := (((hs.const_sub 4).const_mul A0).mul hinv).congr_of_eventuallyEq (f₁ := φS A0)
    (Eventually.of_forall fun x => by simp only [φS, Pi.mul_apply, Function.comp_apply, div_eq_mul_inv])
  rw [h.fderiv]
  have := (den_pos y).ne'
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, innerSL_apply_apply, smul_eq_mul, two_smul,
    ContinuousLinearMap.add_apply, Function.comp]
  field_simp
  ring

theorem fderiv_rSy_apply (ε A0 : ℝ) (y v : K) :
    fderiv ℝ (rSy ε A0) y v = rSy ε A0 y * (ε / 2 * fderiv ℝ (φS A0) y v) := by
  have hφ : DifferentiableAt ℝ (φS (K := K) A0) y :=
    (contDiff_φS A0).differentiable (by simp) y
  have h := ((hφ.hasFDerivAt.const_mul (ε / 2)).exp).const_mul (√ε)
  have e : rSy (K := K) ε A0 = fun x => √ε * Real.exp (ε / 2 * φS A0 x) := rfl
  rw [e, h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `ϑ_i = e_i(r)/r = −2εA₀ y_i/(4+|y|²)`. -/
theorem ϑf_rSy {ε : ℝ} (hε : 0 < ε) (A0 : ℝ) (i : Fin n) (y : K) :
    ϑf b (rSy ε A0) i y = -2 * ε * A0 * ⟪y, b i⟫ / (4 + ‖y‖ ^ 2) := by
  have hr := (rSy_pos hε A0 y).ne'
  have hd := (den_pos y).ne'
  unfold ϑf
  rw [fderiv_rSy_apply, fderiv_φS_apply, eb, real_inner_smul_right]
  simp only [cfac]
  field_simp
  ring

/-- `e_k(ϑ_i) = −(εA₀/2)(δ_{ki} − 2 y_i y_k/(4+|y|²))`. -/
theorem dϑy_rSy {ε : ℝ} (hε : 0 < ε) (A0 : ℝ) (y : K) (k i : Fin n) :
    dϑy b (rSy ε A0) y k i =
      -(ε * A0 / 2) * (kron k i - 2 * ⟪y, b i⟫ * ⟪y, b k⟫ / (4 + ‖y‖ ^ 2)) := by
  have e : ϑf b (rSy ε A0) i = fun x : K => -2 * ε * A0 * ⟪x, b i⟫ / (4 + ‖x‖ ^ 2) :=
    funext (ϑf_rSy hε A0 i)
  have hs := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hinv := (hasDerivAt_inv (den_pos y).ne').comp_hasFDerivAt y (hs.const_add 4)
  have h := (((hasFDerivAt_inner_right (b i) y).const_mul (-2 * ε * A0)).mul hinv).congr_of_eventuallyEq
    (f₁ := fun x : K => -2 * ε * A0 * ⟪x, b i⟫ / (4 + ‖x‖ ^ 2))
    (Eventually.of_forall fun x => by simp only [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv])
  unfold dϑy
  rw [e, h.fderiv, kron_comm k i]
  have hd := (den_pos y).ne'
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, innerSL_apply_apply,
    smul_eq_mul, two_smul, ContinuousLinearMap.add_apply, eb, real_inner_smul_right,
    real_inner_smul_left, b.inner_eq_ite, kron, cfac, Function.comp]
  field_simp
  ring

/-- **`N = −r⁻¹ Hess r` for [GG]'s southern radius**:
`N_{ij} = (εA₀/2)·(4−|y|²)/(4+|y|²)·δ_{ij} − ϑ_iϑ_j`. That is
`−(ε/2) Hess φ − (ε/2)² dφ⊗dφ`, with `−Hess φ = −A₀ cos t · g_B`. -/
theorem Ny_rSy {ε : ℝ} (hε : 0 < ε) (A0 : ℝ) (y : K) (i j : Fin n) :
    Ny b (rSy ε A0) y i j =
      ε * A0 / 2 * ((4 - ‖y‖ ^ 2) / (4 + ‖y‖ ^ 2)) * kron i j -
        ϑy b (rSy ε A0) y i * ϑy b (rSy ε A0) y j := by
  have hd := (den_pos y).ne'
  have hsum : ∑ k, ΓB b i k j y * ϑy b (rSy ε A0) y k =
      (-(ε * A0) * ⟪y, b j⟫ / (4 + ‖y‖ ^ 2)) * ⟪y, b i⟫ +
        (ε * A0 * kron i j / (4 + ‖y‖ ^ 2)) * ‖y‖ ^ 2 := by
    have hk : ∀ k, ΓB b i k j y * ϑy b (rSy ε A0) y k =
        (-(ε * A0) * ⟪y, b j⟫ / (4 + ‖y‖ ^ 2)) * (kron i k * ⟪y, b k⟫) +
          (ε * A0 * kron i j / (4 + ‖y‖ ^ 2)) * (⟪y, b k⟫ * ⟪y, b k⟫) := by
      intro k
      rw [ΓB_eq, ϑy, ϑf_rSy hε]
      field_simp
      ring
    have hi : ∑ k, kron i k * ⟪y, b k⟫ = ⟪y, b i⟫ := sum_kron_left (fun k => ⟪y, b k⟫) i
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hi, sum_sq_inner]
  unfold Ny
  rw [hsum, dϑy_rSy hε]
  simp only [ϑy, ϑf_rSy hε]
  field_simp
  ring

theorem sum_ϑy_sq {ε : ℝ} (hε : 0 < ε) (A0 : ℝ) (y : K) :
    ∑ k, ϑy b (rSy ε A0) y k ^ 2 = 4 * ε ^ 2 * A0 ^ 2 * ‖y‖ ^ 2 / (4 + ‖y‖ ^ 2) ^ 2 := by
  have hk : ∀ k, ϑy b (rSy ε A0) y k ^ 2 =
      4 * ε ^ 2 * A0 ^ 2 * (⟪y, b k⟫ * ⟪y, b k⟫) / (4 + ‖y‖ ^ 2) ^ 2 := fun k => by
    rw [ϑy, ϑf_rSy hε, div_pow]; ring
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.sum_div, ← Finset.mul_sum, sum_sq_inner]

theorem sum_ϑy_sq_le {ε : ℝ} (hε : 0 < ε) (A0 : ℝ) (y : K) :
    ∑ k, ϑy b (rSy ε A0) y k ^ 2 ≤ (ε * A0 / 2) ^ 2 := by
  rw [sum_ϑy_sq hε, div_le_iff₀ (by positivity)]
  have : 0 ≤ ε ^ 2 * A0 ^ 2 := by positivity
  nlinarith [mul_nonneg this (sq_nonneg (4 - ‖y‖ ^ 2))]

/-- **The `N ≥ ν` bound on the cap** `c₀(4+|y|²) ≤ 4−|y|²`, i.e. `−cos t ≥ c₀`, with
`ν = (εA₀/2)c₀ − (εA₀/2)²`. -/
theorem Ny_rSy_ge {ε : ℝ} (hε : 0 < ε) {A0 c0 : ℝ} (hA0 : 0 ≤ A0) (y : K)
    (hy : c0 * (4 + ‖y‖ ^ 2) ≤ 4 - ‖y‖ ^ 2) (x : Fin n → ℝ) :
    (ε * A0 / 2 * c0 - (ε * A0 / 2) ^ 2) * ∑ i, x i ^ 2 ≤
      ∑ i, ∑ j, Ny b (rSy ε A0) y i j * x i * x j := by
  have hc : c0 ≤ (4 - ‖y‖ ^ 2) / (4 + ‖y‖ ^ 2) := by rw [le_div_iff₀ (den_pos y)]; exact hy
  have h1 : ∀ i j, Ny b (rSy ε A0) y i j * x i * x j =
      ε * A0 / 2 * ((4 - ‖y‖ ^ 2) / (4 + ‖y‖ ^ 2)) * (kron i j * (x i * x j)) -
        (ϑy b (rSy ε A0) y i * x i) * (ϑy b (rSy ε A0) y j * x j) := by
    intro i j; rw [Ny_rSy hε]; ring
  have hk : ∀ i, ∑ j, kron i j * (x i * x j) = x i ^ 2 := fun i =>
    (sum_kron_left (fun j => x i * x j) i).trans (by ring)
  have hexp : ∑ i, ∑ j, Ny b (rSy ε A0) y i j * x i * x j =
      ε * A0 / 2 * ((4 - ‖y‖ ^ 2) / (4 + ‖y‖ ^ 2)) * ∑ i, x i ^ 2 -
        (∑ i, ϑy b (rSy ε A0) y i * x i) ^ 2 := by
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, hk]
    rw [← Finset.sum_mul]
    ring
  rw [hexp]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (ϑy b (rSy ε A0) y) x
  have hϑ := sum_ϑy_sq_le (b := b) hε A0 y
  have hx : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hα : 0 ≤ ε * A0 / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hϑ hx, mul_le_mul_of_nonneg_right hc (mul_nonneg hα hx)]

theorem φS_le {A0 : ℝ} (hA0 : 0 ≤ A0) (y : K) : φS A0 y ≤ A0 := by
  unfold φS
  rw [div_le_iff₀ (den_pos y)]
  nlinarith [sq_nonneg ‖y‖]

theorem rSy_sq_le {ε A0 : ℝ} (hε : 0 < ε) (hA0 : 0 ≤ A0) (hεA : ε * A0 ≤ Real.log 2) (y : K) :
    rSy ε A0 y ^ 2 ≤ 2 * ε := by
  unfold rSy
  rw [mul_pow, Real.sq_sqrt hε.le, ← Real.exp_nat_mul]
  have h1 : (↑(2 : ℕ) : ℝ) * (ε / 2 * φS A0 y) ≤ Real.log 2 := by
    have := φS_le hA0 y
    push_cast
    nlinarith
  have h2 : Real.exp (↑(2 : ℕ) * (ε / 2 * φS A0 y)) ≤ 2 := by
    calc _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 h1
      _ = 2 := Real.exp_log (by norm_num)
  nlinarith

end Radius

/-! ## The curvature bounds `M₀`, `M₁` on the cap, by compactness -/

section Bounds

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ}

/-- The southern cap `{t ≥ a}` in the chart centred at `o_S`: `−cos t ≥ c₀`, `c₀ = |cos a|`. -/
def capS (c0 : ℝ) : Set K := {y | c0 * (4 + ‖y‖ ^ 2) ≤ 4 - ‖y‖ ^ 2}

theorem isCompact_capS {c0 : ℝ} (hc0 : 0 ≤ c0) : IsCompact (capS (K := K) c0) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (by fun_prop) (by fun_prop)) ((Metric.isBounded_closedBall (x := (0 : K))
      (r := 2)).subset fun y hy => ?_)
  have h : ‖y‖ ^ 2 ≤ 4 := by
    have h1 : c0 * (4 + ‖y‖ ^ 2) ≤ 4 - ‖y‖ ^ 2 := hy
    have : 0 ≤ c0 * (4 + ‖y‖ ^ 2) := by positivity
    linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg y]

theorem continuous_ΓB (i j k : Fin n) : Continuous (ΓB b i j k) := by
  rw [show ΓB b i j k = fun x => (⟪x, b k⟫ * kron i j - ⟪x, b j⟫ * kron i k) / 2 from
    funext (ΓB_eq i j k)]
  fun_prop

/-- `DΩ` does not involve the fibre radius. -/
theorem DΩy_indep (r r' : K → ℝ) (y : K) (u : Quaternion ℝ) :
    DΩy b A r y u = DΩy b A r' y u := rfl

theorem continuous_OmSq (hA : ContDiff ℝ ∞ A) :
    Continuous fun z : K × Quaternion ℝ => Prop31Algebra.OmSq (Ωy b A z.1 z.2) := by
  unfold Prop31Algebra.OmSq Ωy
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_finset_sum _ fun a _ => ?_
  exact ((contDiff_Ωc hA i j a).continuous.comp (by fun_prop)).pow 2

theorem continuous_DΩSq (hA : ContDiff ℝ ∞ A) :
    Continuous fun z : K × Quaternion ℝ =>
      ∑ i, ∑ j, ∑ k, ∑ a, DΩy b A (fun _ => 1) z.1 z.2 i j k a ^ 2 := by
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun a _ => ?_
  refine Continuous.pow ?_ 2
  unfold DΩy dΩy Ωy
  have hΩ : ∀ p q c, Continuous (Ωc b A p q c) := fun p q c => (contDiff_Ωc hA p q c).continuous
  have hd : Continuous fun z : K × Quaternion ℝ =>
      fderiv ℝ (Ωc b A j k a) (z.1, z.2) (Fa b A (fun _ => 1) (.inl i) (z.1, z.2)) := by
    have h1 := (contDiff_Ωc (b := b) hA j k a).continuous_fderiv (by simp)
    have h2 := (contDiff_Fa (b := b) hA (r := fun _ => (1 : ℝ)) contDiff_const
      (fun _ => one_ne_zero) (.inl i)).continuous
    exact (h1.comp (by fun_prop)).clm_apply (h2.comp (by fun_prop))
  refine (hd.sub ?_).sub ?_
  · exact continuous_finset_sum _ fun l _ =>
      ((continuous_ΓB i j l).comp continuous_fst).mul ((hΩ l k a).comp (by fun_prop))
  · exact continuous_finset_sum _ fun l _ =>
      ((continuous_ΓB i k l).comp continuous_fst).mul ((hΩ j l a).comp (by fun_prop))

/-- A continuous function is bounded by `2M²` on a compact set, for some `M ≥ 0`. -/
theorem exists_sq_bound {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {f : X → ℝ} (hf : Continuous f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ S, f z ≤ 2 * M ^ 2 := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨√(max C 0 / 2), Real.sqrt_nonneg _, fun z hz => ?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have := (le_abs_self (f z)).trans (hC z hz)
  linarith [le_max_left C 0]

end Bounds

/-! ## [GG]'s southern filling: `G_S` has positive curvature on the cap -/

section Southern

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ}

/-- **[GG] §4, the southern filling** (`eq:south`, via [HLY] Prop. 3.1). For a smooth imaginary
connection potential `A` on the southern chart, and the cap `−cos t ≥ c₀ > 0`:
- there is `Λ₀` (from the curvature bounds `M₀`, `M₁` of `A` on the cap) such that
- for every `Λ ≥ Λ₀` and every `A₀ ≥ 0` with `A₀c₀ ≥ Λ` ([GG]: `A₀|cos a| ≥ Λ`),
- there is `ε_S > 0` such that for `0 < ε < ε_S` the connection metric with
  `r_S = √ε e^{−εA₀ cos t/2}` has **positive `RiemannianGeometry` sectional curvature on every plane** at every
  point of the cap. -/
theorem southern_cap_pos (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) {c0 : ℝ}
    (hc0 : 0 < c0) :
    ∃ Λ0 : ℝ, ∀ Λ, Λ0 ≤ Λ → ∀ A0 : ℝ, 0 ≤ A0 → Λ ≤ A0 * c0 →
      ∃ εS > 0, ∀ ε (hε : 0 < ε), ε < εS → ∀ y ∈ capS (K := K) c0, ∀ u : S3,
        ∀ w₁ w₂ : TangentSpace (IN K) ((y, u) : K × S3), LinearIndependent ℝ ![w₁, w₂] →
          0 < sectionalCurvatureAt isSymm_GH
            (isPosDef_GH (A := A) fun x => (rSy_pos hε A0 x).ne')
            (isContMDiffMetricSection_GH hA (contDiff_rSy ε A0)) (y, u) w₁ w₂ := by
  have hS := (isCompact_capS (K := K) hc0.le).prod (isCompact_sphere (0 : Quaternion ℝ) 1)
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K) :=
    ⟨stdOrthonormalBasis ℝ K⟩
  obtain ⟨M0, hM0, hOm⟩ := exists_sq_bound hS (continuous_OmSq (b := b) hA)
  obtain ⟨M1, hM1, hDOm⟩ := exists_sq_bound hS (continuous_DΩSq (b := b) hA)
  refine ⟨16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 * (M1 + 1) ^ 2, fun Λ hΛ A0 hA0 hΛA => ?_⟩
  have hΛpos : 0 < Λ := by nlinarith [sq_nonneg M0, sq_nonneg (M1 + 1)]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B := 1 + 2 * M0 + A0 * M0 + 1024 * M0 ^ 2 + 4 * A0 ^ 2 / Λ + 2 * A0 ^ 2 +
    512 * A0 ^ 2 * M0 ^ 2 / Λ + A0 / Real.log 2 with hB
  have t1 : 0 ≤ 4 * A0 ^ 2 / Λ := by positivity
  have t2 : 0 ≤ 512 * A0 ^ 2 * M0 ^ 2 / Λ := by positivity
  have t3 : 0 ≤ A0 / Real.log 2 := by positivity
  have t4 : 0 ≤ A0 * M0 := by positivity
  have hB1 : 1 ≤ B := by
    rw [hB]; linarith [sq_nonneg M0, sq_nonneg A0]
  refine ⟨1 / B, by positivity, fun ε hε hεS y hy u w₁ w₂ hli => ?_⟩
  have hεB : ε * B < 1 := by rwa [lt_div_iff₀ (by linarith)] at hεS
  have hε1 : ε < 1 := by
    have := mul_le_mul_of_nonneg_left hB1 hε.le; linarith
  have hε3 : ε ^ 3 ≤ ε := by
    have h2 : ε ^ 2 ≤ 1 := by nlinarith
    calc ε ^ 3 = ε * ε ^ 2 := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h2 hε.le
      _ = ε := mul_one ε
  -- every term of `B`, times `ε`, is below `1`
  have hT : ∀ t, t ≤ B → ε * t ≤ 1 := fun t htB =>
    (mul_le_mul_of_nonneg_left htB hε.le).trans hεB.le
  have hsq0 := sq_nonneg M0
  have hsqA := sq_nonneg A0
  have hBt : ∀ t, t = 2 * M0 ∨ t = A0 * M0 ∨ t = 1024 * M0 ^ 2 ∨ t = 4 * A0 ^ 2 / Λ ∨
      t = 2 * A0 ^ 2 ∨ t = 512 * A0 ^ 2 * M0 ^ 2 / Λ ∨ t = A0 / Real.log 2 → t ≤ B := by
    intro t ht
    rw [hB]
    rcases ht with h | h | h | h | h | h | h <;> rw [h] <;> linarith
  have hA2 : 2 * ε * M0 ≤ 1 := by
    have := hT _ (hBt _ (Or.inl rfl)); linarith
  have hA3 : ε * A0 * M0 ≤ 1 := by
    have := hT _ (hBt _ (Or.inr (Or.inl rfl))); linarith
  have hB2 : 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ 1 := by
    have := hT _ (hBt _ (Or.inr (Or.inr (Or.inl rfl)))); linarith
  have hC1 : ε * A0 ^ 2 ≤ Λ / 4 := by
    have h := hT _ (hBt _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have e : ε * (4 * A0 ^ 2 / Λ) * (Λ / 4) = ε * A0 ^ 2 := by field_simp
    calc ε * A0 ^ 2 = ε * (4 * A0 ^ 2 / Λ) * (Λ / 4) := e.symm
      _ ≤ 1 * (Λ / 4) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = Λ / 4 := one_mul _
  have hC2 : 2 * ε ^ 3 * A0 ^ 2 ≤ 1 := by
    have h := hT _ (hBt _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    have h3 := mul_le_mul_of_nonneg_right hε3 hsqA
    linarith
  have hC3 : 32 * 4 ^ 2 * ε ^ 3 * A0 ^ 2 * M0 ^ 2 ≤ Λ := by
    have h := hT _ (hBt _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    have e : ε * (512 * A0 ^ 2 * M0 ^ 2 / Λ) * Λ = 512 * (ε * (A0 ^ 2 * M0 ^ 2)) := by
      field_simp
    have h3 : ε ^ 3 * (A0 ^ 2 * M0 ^ 2) ≤ ε * (A0 ^ 2 * M0 ^ 2) :=
      mul_le_mul_of_nonneg_right hε3 (by positivity)
    have h4 : ε * (512 * A0 ^ 2 * M0 ^ 2 / Λ) * Λ ≤ 1 * Λ :=
      mul_le_mul_of_nonneg_right h hΛpos.le
    linarith
  have hεA : ε * A0 ≤ Real.log 2 := by
    have h := hT _ (hBt _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
    have e : ε * (A0 / Real.log 2) * Real.log 2 = ε * A0 := by field_simp
    have h4 : ε * (A0 / Real.log 2) * Real.log 2 ≤ 1 * Real.log 2 :=
      mul_le_mul_of_nonneg_right h hl2.le
    linarith
  have hr2 := rSy_sq_le hε hA0 hεA y
  have htD : √(∑ k, ϑy b (rSy ε A0) y k ^ 2) ≤ ε * A0 / 2 := by
    calc _ ≤ √((ε * A0 / 2) ^ 2) := Real.sqrt_le_sqrt (sum_ϑy_sq_le hε A0 y)
      _ = ε * A0 / 2 := Real.sqrt_sq (by positivity)
  have hν := Ny_rSy_ge (b := b) hε hA0 y hy
  have hνΛ : ε * Λ / 2 - ε ^ 2 * A0 ^ 2 / 4 ≤ ε * A0 / 2 * c0 - (ε * A0 / 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hΛA hε.le
    have e : (ε * A0 / 2) ^ 2 = ε ^ 2 * A0 ^ 2 / 4 := by ring
    rw [e]; linarith
  have hmem : ((y, (u : Quaternion ℝ)) : K × Quaternion ℝ) ∈ capS c0 ×ˢ Metric.sphere 0 1 :=
    ⟨hy, u.2⟩
  have hOm' : Prop31Algebra.OmSq (Ωy b A y u) ≤ 2 * M0 ^ 2 := hOm (y, (u : Quaternion ℝ)) hmem
  have hDOm' : ∑ i, ∑ j, ∑ k, ∑ a, DΩy b A (rSy ε A0) y u i j k a ^ 2 ≤ 2 * M1 ^ 2 := by
    rw [DΩy_indep (rSy ε A0) (fun _ => 1)]; exact hDOm (y, (u : Quaternion ℝ)) hmem
  exact hly_sec_pos_at hA hAim (contDiff_rSy ε A0) (rSy_pos hε A0) y u _ M0 M1 ε Λ A0 hM0 hM1 hε
    hOm' hDOm' hν hΛ hr2 htD hνΛ hA2 hA3 hB2 hC1 hC2 hC3 w₁ w₂ hli

/-- The hypotheses of `southern_cap_pos` are satisfiable and its cap is nonempty: the flat
potential, `c₀ = 1/2`, and the south pole `0 ∈ capS c₀`. -/
theorem southern_cap_pos_hyps :
    ContDiff ℝ ∞ (A0 (K := K)) ∧ (∀ x v, (A0 (K := K) x v).re = 0) ∧ (0 : ℝ) < 1 / 2 ∧
      (0 : K) ∈ capS (1 / 2) := by
  refine ⟨contDiff_const, fun _ _ => rfl, by norm_num, ?_⟩
  show 1 / 2 * (4 + ‖(0 : K)‖ ^ 2) ≤ 4 - ‖(0 : K)‖ ^ 2
  simp; norm_num

end Southern

end

end ExoticSpheres8And10
