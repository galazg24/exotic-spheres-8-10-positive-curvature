/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.Filling
import ExoticSpheres8And10.Curvature.Northern.ProfilesCentre
import ExoticSpheres8And10.Curvature.Northern.ProfilesGeneralBound

/-! # §4: the northern curvature for [D]'s actual metric, at every point of the coordinate patch

`S4_NorthD` realised [D]'s profiles by their 2-jets and took round fibres in normal coordinates.
This file removes both simplifications.

* `blend`: a smooth, everywhere-positive function equal to [D]'s `F = Fprof δ` (resp.
  `r = rprof`) on the whole half-line `[s₀/2, ∞)`, obtained with a smooth cutoff. The metric
  below therefore **is** [D]'s northern metric on the open set `{s > s₀/2}`, not merely one with
  the same 2-jet.
* `riemannTensorAt_wG_conformal`, `sectionalCurvatureAt_wG_pos_conformal`: the star-horizontal
  formula at points where the fibre metrics are conformal to the inner product. This holds at
  every point of the round metric `HR`.
* `northern_sectionalCurvature_pos_all`: **for [D]'s parameters, at every point `(s, x, y)` with
  `s ∈ (0, ℓ_N]` and any fibre coordinates `x`, `y`, `RiemannianGeometry`'s sectional curvature of [D]'s northern
  metric is positive on every star-horizontal plane.**
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

/-! ### Extension by a cutoff -/

/-- `η(t/s₀) f(t) + (1 − η(t/s₀))`: equal to `f` on `[s₀/2, ∞)` and to `1` on `(−∞, s₀/4]`. -/
def blend (s₀ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := etaCut (t / s₀) * f t + (1 - etaCut (t / s₀))

theorem blend_eq {s₀ : ℝ} (hs : 0 < s₀) (f : ℝ → ℝ) {t : ℝ} (ht : s₀ / 2 ≤ t) :
    blend s₀ f t = f t := by
  have : etaCut (t / s₀) = 1 := etaCut_one (by rw [le_div_iff₀ hs]; linarith)
  simp [blend, this]

theorem blend_eventuallyEq {s₀ : ℝ} (hs : 0 < s₀) (f : ℝ → ℝ) : blend s₀ f =ᶠ[𝓝 s₀] f := by
  filter_upwards [Ioi_mem_nhds (show s₀ / 2 < s₀ by linarith)] with t ht
  exact blend_eq hs f (le_of_lt ht)

theorem blend_pos {s₀ : ℝ} (hs : 0 < s₀) {f : ℝ → ℝ} (hf : ∀ t, s₀ / 4 < t → 0 < f t) (t : ℝ) :
    0 < blend s₀ f t := by
  have h0 := etaCut_nonneg (t / s₀)
  have h1 := etaCut_le_one (t / s₀)
  by_cases ht : t ≤ s₀ / 4
  · have : etaCut (t / s₀) = 0 := etaCut_zero (by rw [div_le_iff₀ hs]; linarith)
    simp [blend, this]
  · push Not at ht
    have hft := hf t ht
    unfold blend
    by_cases hη : etaCut (t / s₀) ≤ 1 / 2
    · nlinarith
    · push Not at hη; nlinarith

theorem contDiff_blend (s₀ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (blend s₀ f) := by
  unfold blend
  have he : ContDiff ℝ ∞ fun t : ℝ => etaCut (t / s₀) :=
    etaCut_contDiff.comp (contDiff_id.div_const s₀)
  exact (he.mul hf).add (contDiff_const.sub he)

theorem deriv_blend {s₀ : ℝ} (hs : 0 < s₀) (f : ℝ → ℝ) :
    deriv (blend s₀ f) s₀ = deriv f s₀ := (blend_eventuallyEq hs f).deriv_eq

theorem deriv2_blend {s₀ : ℝ} (hs : 0 < s₀) (f : ℝ → ℝ) :
    deriv (deriv (blend s₀ f)) s₀ = deriv (deriv f) s₀ :=
  (blend_eventuallyEq hs f).deriv.deriv_eq

theorem blend_self {s₀ : ℝ} (hs : 0 < s₀) (f : ℝ → ℝ) : blend s₀ f s₀ = f s₀ :=
  blend_eq hs f (by linarith)

theorem contDiff_rprof (ra d δ ℓ : ℝ) : ContDiff ℝ ∞ (rprof ra d δ ℓ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hasDerivAt_rprof ra d δ ℓ s).differentiableAt, ?_⟩
  have e : deriv (rprof ra d δ ℓ) = fun s => d * etaCut (s / δ) :=
    funext fun s => (hasDerivAt_rprof ra d δ ℓ s).deriv
  rw [e]
  exact contDiff_const.mul (etaCut_contDiff.comp (contDiff_id.div_const δ))

theorem rprof_ge_of_le {ra d δ ℓ s : ℝ} (hd : 0 ≤ d) (hs : ℓ ≤ s) : ra ≤ rprof ra d δ ℓ s := by
  unfold rprof
  have : ∫ v in s..ℓ, etaCut (v / δ) ≤ 0 := by
    rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hs fun v _ =>
      etaCut_nonneg (v / δ)
    linarith
  nlinarith

/-! ### Conformal fibres -/

section Conformal

variable {F₁ F₂ : Type} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {F r : ℝ → ℝ} {H₁ : F₁ → F₁ →L[ℝ] F₁ →L[ℝ] ℝ} {H₂ : F₂ → F₂ →L[ℝ] F₂ →L[ℝ] ℝ}
  {Γ₁ : F₁ → F₁ →L[ℝ] F₁ →L[ℝ] F₁} {Γ₂ : F₂ → F₂ →L[ℝ] F₂ →L[ℝ] F₂}

local notation "Ew" => ℝ × F₁ × F₂

/-- The coordinate vector with scaled components `(λ, X, U)` when the fibre metrics are
`c₁⟪·,·⟫`, `c₂⟪·,·⟫` at the point: `(λ, X/(F√c₁), U/(r√c₂))`. -/
def scaledVecC (F r : ℝ → ℝ) (c₁ c₂ s lam : ℝ) (X : F₁) (U : F₂) : Ew :=
  (lam, (F s * √c₁)⁻¹ • X, (r s * √c₂)⁻¹ • U)

theorem riemannTensorAt_wG_conformal (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r)
    (hH₁ : ContDiff ℝ ∞ H₁) (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁)
    (hΓ₂s : ContDiff ℝ ∞ Γ₂) (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0)
    (hs₁ : IsSymm (cmet H₁)) (hs₂ : IsSymm (cmet H₂)) (hp₁ : IsPosDef (cmet H₁))
    (hp₂ : IsPosDef (cmet H₂))
    (hΓ₁ : ∀ x ξ ζ c, H₁ x (Γ₁ x ξ ζ) c = kz H₁ x ξ ζ c)
    (hΓ₂ : ∀ y η θ κ, H₂ y (Γ₂ y η θ) κ = kz H₂ y η θ κ) (p : Ew) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hx : ∀ a b, H₁ p.2.1 a b = c₁ * ⟪a, b⟫) (hy : ∀ a b, H₂ p.2.2 a b = c₂ * ⟪a, b⟫)
    (hK₁ : ∀ ξ ζ, fibreRm H₁ Γ₁ p.2.1 ξ ζ =
      H₁ p.2.1 ξ ξ * H₁ p.2.1 ζ ζ - H₁ p.2.1 ξ ζ ^ 2)
    (hK₂ : ∀ η θ, fibreRm H₂ Γ₂ p.2.2 η θ =
      H₂ p.2.2 η η * H₂ p.2.2 θ θ - H₂ p.2.2 η θ ^ 2)
    (T : F₁ →L[ℝ] F₂) (X Y : F₁) (lam mu : ℝ) :
    riemannTensorAt (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂).isNondegenerate
      (isContMDiffMetricSection_cmet (contDiff2_wG hF hr hH₁ hH₂)) p
      (toTSv p (scaledVecC F r c₁ c₂ p.1 lam X (T X)))
      (toTSv p (scaledVecC F r c₁ c₂ p.1 mu Y (T Y)))
      (toTSv p (scaledVecC F r c₁ c₂ p.1 mu Y (T Y)))
      (toTSv p (scaledVecC F r c₁ c₂ p.1 lam X (T X))) =
    northNumerator (F p.1) (r p.1) (deriv F p.1) (deriv r p.1) (deriv (deriv F) p.1)
      (deriv (deriv r) p.1) T X Y lam mu := by
  rw [riemannTensorAt_wG hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0 hs₁ hs₂ hp₁ hp₂ hΓ₁ hΓ₂ p _ _ 1 1
    (by rw [hK₁, one_mul]) (by rw [hK₂, one_mul])]
  have hF0' := hF0 p.1
  have hr0' := hr0 p.1
  obtain ⟨a₁, ha₁, rfl⟩ : ∃ a, 0 < a ∧ c₁ = a ^ 2 :=
    ⟨√c₁, Real.sqrt_pos.2 hc₁, (Real.sq_sqrt hc₁.le).symm⟩
  obtain ⟨a₂, ha₂, rfl⟩ : ∃ a, 0 < a ∧ c₂ = a ^ 2 :=
    ⟨√c₂, Real.sqrt_pos.2 hc₂, (Real.sq_sqrt hc₂.le).symm⟩
  simp only [scaledVecC]
  rw [Real.sqrt_sq ha₁.le, Real.sqrt_sq ha₂.le]
  have ha₁' := ha₁.ne'
  have ha₂' := ha₂.ne'
  simp only [ map_sub, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hx, hy, northNumerator, wedgeSq, tensorSq,
    ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm X Y, real_inner_comm (T X) (T Y)]
  field_simp

theorem sectionalCurvatureAt_wG_pos_conformal (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r)
    (hH₁ : ContDiff ℝ ∞ H₁) (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁)
    (hΓ₂s : ContDiff ℝ ∞ Γ₂) (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0)
    (hs₁ : IsSymm (cmet H₁)) (hs₂ : IsSymm (cmet H₂)) (hp₁ : IsPosDef (cmet H₁))
    (hp₂ : IsPosDef (cmet H₂))
    (hΓ₁ : ∀ x ξ ζ c, H₁ x (Γ₁ x ξ ζ) c = kz H₁ x ξ ζ c)
    (hΓ₂ : ∀ y η θ κ, H₂ y (Γ₂ y η θ) κ = kz H₂ y η θ κ) (p : Ew) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hx : ∀ a b, H₁ p.2.1 a b = c₁ * ⟪a, b⟫) (hy : ∀ a b, H₂ p.2.2 a b = c₂ * ⟪a, b⟫)
    (hK₁ : ∀ ξ ζ, fibreRm H₁ Γ₁ p.2.1 ξ ζ =
      H₁ p.2.1 ξ ξ * H₁ p.2.1 ζ ζ - H₁ p.2.1 ξ ζ ^ 2)
    (hK₂ : ∀ η θ, fibreRm H₂ Γ₂ p.2.2 η θ =
      H₂ p.2.2 η η * H₂ p.2.2 θ θ - H₂ p.2.2 η θ ^ 2)
    (T : F₁ →L[ℝ] F₂) (X Y : F₁) (lam mu : ℝ)
    (hN : 0 < northNumerator (F p.1) (r p.1) (deriv F p.1) (deriv r p.1) (deriv (deriv F) p.1)
      (deriv (deriv r) p.1) T X Y lam mu)
    (hind : LinearIndependent ℝ ![((lam, X, T X) : ℝ × F₁ × F₂), (mu, Y, T Y)]) :
    0 < sectionalCurvatureAt (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂)
      (isContMDiffMetricSection_cmet (contDiff2_wG hF hr hH₁ hH₂)) p
      (toTSv p (scaledVecC F r c₁ c₂ p.1 lam X (T X)))
      (toTSv p (scaledVecC F r c₁ c₂ p.1 mu Y (T Y))) := by
  rw [sectionalCurvatureAt_def]
  refine div_pos ?_ ?_
  · rw [riemannTensorAt_wG_conformal hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0 hs₁ hs₂ hp₁ hp₂ hΓ₁ hΓ₂ p
      hc₁ hc₂ hx hy hK₁ hK₂]
    exact hN
  · have hk1 : F p.1 * √c₁ ≠ 0 := mul_ne_zero (hF0 p.1) (Real.sqrt_pos.2 hc₁).ne'
    have hk2 : r p.1 * √c₂ ≠ 0 := mul_ne_zero (hr0 p.1) (Real.sqrt_pos.2 hc₂).ne'
    set L : Ew →ₗ[ℝ] Ew := LinearMap.prodMap LinearMap.id
      (LinearMap.prodMap ((F p.1 * √c₁)⁻¹ • LinearMap.id) ((r p.1 * √c₂)⁻¹ • LinearMap.id))
    have hL : LinearMap.ker L = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      have h0 := congrArg Prod.fst hw
      have h1 := congrArg (fun q : Ew => q.2.1) hw
      have h2 := congrArg (fun q : Ew => q.2.2) hw
      simp [L, hF0 p.1, hr0 p.1, (Real.sqrt_pos.2 hc₁).ne', (Real.sqrt_pos.2 hc₂).ne'] at h0 h1 h2
      exact Prod.ext h0 (Prod.ext h1 h2)
    have hli := hind.map' L hL
    have e : L ∘ ![((lam, X, T X) : ℝ × F₁ × F₂), (mu, Y, T Y)] =
        ![scaledVecC F r c₁ c₂ p.1 lam X (T X), scaledVecC F r c₁ c₂ p.1 mu Y (T Y)] := by
      funext i
      fin_cases i <;> rfl
    rw [e] at hli
    exact gramDet_pos (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂) hli

end Conformal

/-! ### [D]'s northern metric at every point -/

section NorthAll

variable {H Vv : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [FiniteDimensional ℝ Vv]

/-- **[D] §4, northern filling, for [D]'s actual metric.** For the parameters of
`northern_filling_pos`, at every `s ∈ (0, ℓ_N]` and every point `(s, x, y)` of the fibre
coordinates, the metric `ds² + F̃(s)² H_round(x) + r̃(s)² H_round(y)` has **positive `RiemannianGeometry` sectional
curvature on every star-horizontal plane**, for every `K` with `‖K‖ ≤ 2`. Here `F̃ = F` and
`r̃ = r` on `[s/2, ∞)`, [D]'s profiles themselves, extended smoothly and positively below `s/2`.
The plane is spanned by the scaled star-horizontal vectors `(λ, X, TX)`, `(μ, Y, TY)`,
`T = −(F/r)K^*`. -/
theorem northern_sectionalCurvature_pos_all (Cη : ℝ) (hC0 : 0 ≤ Cη)
    (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    (a ε A0 Fa δ ra qs d : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa) (hδ : 0 < δ)
    {L : ℝ} (hL : 0 < L) (hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * Fa * (1 + Cη))) (hra : 0 < ra)
    (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) (hqs : qs = ε * A0 * Fa / 2)
    (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2) (hd1 : d < 1)
    (s : ℝ) (hs : s ∈ Ioc 0 (Gδ δ Fa)) (x : H) (y : Vv)
    (K : Vv →L[ℝ] H) (hK : ‖K‖ ≤ L) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ
      ![((lam, X, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X) :
          ℝ × H × Vv),
        (mu, Y, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) Y)]) :
    have hF0 : ∀ t, blend s (Fprof δ) t ≠ 0 := fun t =>
      (blend_pos hs.1 (fun t ht => Fprof_pos (by linarith [hs.1])) t).ne'
    have hr0 : ∀ t, blend s (rprof ra d δ (Gδ δ Fa)) t ≠ 0 := fun t => (blend_pos hs.1 (fun t ht => by
      have hd0 : 0 ≤ d := by rw [hd, hqs]; positivity
      rcases le_or_gt t (Gδ δ Fa) with h | h
      · have hdl : d * Gδ δ Fa ≤ ra / 2 := by
          have : 0 ≤ qs := by rw [hqs]; positivity
          rw [hd]; nlinarith
        have := (rprof_bounds (δ := δ) hd0 (by linarith [hs.1]) h hdl).1
        linarith
      · have := rprof_ge_of_le (ra := ra) (δ := δ) hd0 h.le
        linarith) t).ne'
    0 < sectionalCurvatureAt (isSymm_wG isSymm_HR isSymm_HR)
      (isPosDef_wG hF0 hr0 isPosDef_HR isPosDef_HR)
      (isContMDiffMetricSection_cmet (contDiff2_wG (contDiff_blend s (Fprof_contDiff δ))
        (contDiff_blend s (contDiff_rprof ra d δ (Gδ δ Fa))) contDiff_HR contDiff_HR))
      ((s, x, y) : ℝ × H × Vv)
      (toTSv _ (scaledVecC (blend s (Fprof δ)) (blend s (rprof ra d δ (Gδ δ Fa))) (ψR x) (ψR y) s
        lam X ((-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X)))
      (toTSv _ (scaledVecC (blend s (Fprof δ)) (blend s (rprof ra d δ (Gδ δ Fa))) (ψR x) (ψR y) s
        mu Y ((-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) Y))) := by
  intro hF0 hr0
  have hN := northern_filling_pos_L Cη hC0 hC a ε A0 Fa δ ra qs d L hε hA0 hFa hδ hL hδ3 hra hra2 hqs hd
    hql hd1 s hs K hK X Y lam mu hind
  refine sectionalCurvatureAt_wG_pos_conformal (contDiff_blend s (Fprof_contDiff δ))
    (contDiff_blend s (contDiff_rprof ra d δ (Gδ δ Fa))) contDiff_HR contDiff_HR contDiff_ΓR
    contDiff_ΓR hF0 hr0 isSymm_HR isSymm_HR isPosDef_HR isPosDef_HR HR_ΓR HR_ΓR
    ((s, x, y) : ℝ × H × Vv) (ψR_pos x) (ψR_pos y) (fun a b => HR_apply x a b)
    (fun a b => HR_apply y a b) (fibreRm_round_all x) (fibreRm_round_all y) _ X Y lam mu ?_ hind
  show 0 < northNumerator (blend s (Fprof δ) s) (blend s (rprof ra d δ (Gδ δ Fa)) s)
    (deriv (blend s (Fprof δ)) s) (deriv (blend s (rprof ra d δ (Gδ δ Fa))) s)
    (deriv (deriv (blend s (Fprof δ))) s) (deriv (deriv (blend s (rprof ra d δ (Gδ δ Fa)))) s)
    _ X Y lam mu
  have e1 : deriv (Fprof δ) s = Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) :=
    (hasDerivAt_Fprof δ s).deriv
  have e2 : deriv (deriv (Fprof δ)) s =
      -(Fprof δ s / δ ^ 2) * Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) ^ 2 := by
    have e : deriv (Fprof δ) = fun s => Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) :=
      funext fun s => (hasDerivAt_Fprof δ s).deriv
    rw [e]; exact (hasDerivAt_Fprof' δ s hδ.ne').deriv
  have e3 : deriv (rprof ra d δ (Gδ δ Fa)) s = d * etaCut (s / δ) :=
    (hasDerivAt_rprof ra d δ (Gδ δ Fa) s).deriv
  have e4 : deriv (deriv (rprof ra d δ (Gδ δ Fa))) s = d * (deriv etaCut (s / δ) * (1 / δ)) := by
    have e : deriv (rprof ra d δ (Gδ δ Fa)) = fun s => d * etaCut (s / δ) :=
      funext fun s => (hasDerivAt_rprof ra d δ (Gδ δ Fa) s).deriv
    rw [e]; exact (hasDerivAt_rprof' d δ s).deriv
  rw [blend_self hs.1, blend_self hs.1, deriv_blend hs.1, deriv_blend hs.1, deriv2_blend hs.1,
    deriv2_blend hs.1, e1, e2, e3, e4]
  exact hN

end NorthAll

end

end ExoticSpheres8And10
