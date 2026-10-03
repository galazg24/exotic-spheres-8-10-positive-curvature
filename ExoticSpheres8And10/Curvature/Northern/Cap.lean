/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.Centre
import ExoticSpheres8And10.Curvature.Northern.Submersion

/-! # §4: the northern cap `D_N = P_N / S³_⋆` has positive sectional curvature

[D]'s fibre radius on `V × S³` is `r̃(Y) = r(G_δ(|Y|))`, where `s = G_δ(|Y|)` inverts `|Y| = F(s)`.

* `rD`, with `contDiff_rD` (constant near the centre, since `r' = dη(s/δ)` vanishes for
  `s ≤ δ/4`), `rD_pos`, `rD_invariant`, and `rD_ray` (`r̃(F(t) y) = r(t)`).
* `north_hup`: positivity upstairs on horizontal planes at `(Y, 1)` for every `|Y| ≤ F_a`
  (`north_up_pos` off the centre, `north_centre_pos` at it).
* **`northern_quotient_pos`**: for [D]'s parameters and a star action with `‖K_e‖ ≤ 2` on unit
  vectors, the quotient metric `g_B` on `V` has **positive sectional curvature at every point
  of the closed ball `|Y| ≤ F_a`**, which is the northern cap `D_N`.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### One-dimensional facts -/

theorem contDiff_G (δ : ℝ) : ContDiff ℝ ∞ (Gδ δ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun z => (hasDerivAt_G δ z).differentiableAt, ?_⟩
  have e : deriv (Gδ δ) = fun z => Real.exp (z ^ 2 / (2 * δ ^ 2)) :=
    funext fun z => (hasDerivAt_G δ z).deriv
  rw [e]
  fun_prop

theorem G_nonneg {δ z : ℝ} (hz : 0 ≤ z) : 0 ≤ Gδ δ z := hz.trans (le_G hz)

theorem rprof_eq_start {ra d δ ℓ s : ℝ} (hδ : 0 < δ) (hs0 : 0 ≤ s) (hs : s ≤ δ / 4) :
    rprof ra d δ ℓ s = rprof ra d δ ℓ 0 := by
  unfold rprof
  have hi : ∫ v in (0 : ℝ)..s, etaCut (v / δ) = 0 := by
    have : ∀ v ∈ Set.uIcc (0 : ℝ) s, etaCut (v / δ) = 0 := fun v hv => by
      rw [Set.uIcc_of_le hs0] at hv
      exact etaCut_zero (by rw [div_le_iff₀ hδ]; linarith [hv.2])
    rw [intervalIntegral.integral_congr this]
    simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := s) (c := ℓ)
    ((continuous_eta_div δ).intervalIntegrable _ _) ((continuous_eta_div δ).intervalIntegrable _ _)
  rw [← hsum, hi, zero_add]

section Radius

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **[D]'s fibre radius on `V × S³`**: `r̃(Y) = r(G_δ(|Y|))`. -/
def rD (ra d δ Fa : ℝ) (Y : V) : ℝ := rprof ra d δ (Gδ δ Fa) (Gδ δ ‖Y‖)

theorem rD_eventually_const {ra d δ Fa : ℝ} (hδ : 0 < δ) :
    ∀ᶠ Y in 𝓝 (0 : V), rD ra d δ Fa Y = rprof ra d δ (Gδ δ Fa) 0 := by
  have hU : IsOpen {Y : V | Gδ δ ‖Y‖ < δ / 4} :=
    isOpen_lt ((G_continuous δ).comp continuous_norm) continuous_const
  have h0 : (0 : V) ∈ {Y : V | Gδ δ ‖Y‖ < δ / 4} := by
    show Gδ δ ‖(0 : V)‖ < δ / 4
    rw [norm_zero, G_zero]; positivity
  filter_upwards [hU.mem_nhds h0] with Y hY
  exact rprof_eq_start hδ (G_nonneg (norm_nonneg _)) (le_of_lt hY)

theorem contDiff_rD {ra d δ Fa : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (rD (V := V) ra d δ Fa) := by
  rw [contDiff_iff_contDiffAt]
  intro Y
  by_cases hY : Y = 0
  · subst hY
    exact contDiffAt_const.congr_of_eventuallyEq (rD_eventually_const hδ)
  · exact ((contDiff_rprof ra d δ (Gδ δ Fa)).comp (contDiff_G δ)).contDiffAt.comp Y
      (contDiffAt_norm ℝ hY)

theorem rD_invariant (ra d δ Fa : ℝ) (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (q : S3) (Y : V) :
    rD ra d δ Fa (ρV q Y) = rD ra d δ Fa Y := by
  simp [rD, LinearIsometryEquiv.norm_map]

theorem rD_ray (ra d δ Fa : ℝ) {t : ℝ} (ht : 0 < t) {y : V} (hy : ‖y‖ = 1) :
    rD ra d δ Fa (Fprof δ t • y) = rprof ra d δ (Gδ δ Fa) t := by
  simp only [rD, norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos (Fprof_pos ht), G_Fprof]

end Radius

/-! ### Positivity upstairs at every point of the northern cap -/

section Assembly

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))

theorem rD_pos {ra d δ Fa qs ε A0 : ℝ} (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa)
    (hra : 0 < ra) (hqs : qs = ε * A0 * Fa / 2) (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2)
    (Y : V) : 0 < rD ra d δ Fa Y := by
  have hd0 : 0 ≤ d := by rw [hd, hqs]; positivity
  have hdl : d * Gδ δ Fa ≤ ra / 2 := by
    have : 0 ≤ qs := by rw [hqs]; positivity
    rw [hd]; nlinarith
  have ht := G_nonneg (δ := δ) (norm_nonneg Y)
  rcases le_or_gt (Gδ δ ‖Y‖) (Gδ δ Fa) with h | h
  · have := (rprof_bounds (δ := δ) hd0 ht h hdl).1
    unfold rD; linarith
  · have := rprof_ge_of_le (ra := ra) (δ := δ) hd0 h.le
    unfold rD; linarith

include hρ in
/-- **Positive curvature upstairs on the whole northern cap**, on horizontal planes at `(Y, 1)`,
`|Y| ≤ F_a`. -/
theorem north_hup (Cη : ℝ) (hC0 : 0 ≤ Cη) (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    (a ε A0 Fa δ ra qs d : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa) (hδ : 0 < δ)
    {L : ℝ} (hL : 0 < L) (hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * Fa * (1 + Cη))) (hra : 0 < ra)
    (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) (hqs : qs = ε * A0 * Fa / 2)
    (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2) (hd1 : d < 1)
    (hK : ∀ e : V, ‖e‖ = 1 → ‖KY ρV e‖ ≤ L) (Y : V) (hY : ‖Y‖ ≤ Fa)
    (u v : TangentSpace (IN V) (Y, (1 : S3)))
    (hu : ∀ β, Gs δ (rD ra d δ Fa) Y u (ιv ρV Y β) = 0)
    (hv : ∀ β, Gs δ (rD ra d δ Fa) Y v (ιv ρV Y β) = 0) (hli : LinearIndependent ℝ ![u, v]) :
    0 < sectionalCurvatureAt (isSymm_northMetric δ (rD ra d δ Fa))
      (isPosDef_northMetric δ fun Y => (rD_pos hε hA0 hFa hra hqs hd hql Y).ne')
      (isContMDiffMetricSection_northMetric (contDiff_rD hδ) 2) (Y, 1) u v := by
  have hrt0 : ∀ Y : V, rD ra d δ Fa Y ≠ 0 := fun Y => (rD_pos hε hA0 hFa hra hqs hd hql Y).ne'
  have hu' : ∀ β, northMetric δ (rD ra d δ Fa) (Y, 1) u (ιv ρV Y β) = 0 := fun β =>
    (northMetric_slice δ _ Y u _).trans (hu β)
  have hv' : ∀ β, northMetric δ (rD ra d δ Fa) (Y, 1) v (ιv ρV Y β) = 0 := fun β =>
    (northMetric_slice δ _ Y v _).trans (hv β)
  by_cases hY0 : Y = 0
  · subst hY0
    have hq : Φc ((0 : V), z30) = ((0 : V), (1 : S3)) := by simp [Φc, σ3_z30]
    exact north_centre_pos (ρV := ρV) hδ (contDiff_rD hδ) hrt0 (rD_eventually_const hδ) _ hq u v
      hu' hv' hli
  · have hn : 0 < ‖Y‖ := norm_pos_iff.2 hY0
    set e : V := ‖Y‖⁻¹ • Y with he_def
    have he : ‖e‖ = 1 := by
      rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    set s₀ := Gδ δ ‖Y‖ with hs₀_def
    have hs₀ : s₀ ∈ Ioc 0 (Gδ δ Fa) := by
      refine ⟨?_, (G_strictMono δ).monotone hY⟩
      rw [hs₀_def, ← G_zero δ]; exact G_strictMono δ hn
    have hFe : Fprof δ s₀ • e = Y := by
      rw [hs₀_def, Fprof_G, he_def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hq : Φh δ s₀ e (p0 s₀ e) = (Y, (1 : S3)) := by
      rw [Φh_p0 hs₀.1, hFe]
    exact north_up_pos hρ Cη hC0 hC a ε A0 Fa δ ra qs d hε hA0 hFa hδ hL hδ3 hra hra2 hqs hd hql hd1
      hs₀ he (hK e he) (contDiff_rD hδ) hrt0 (fun t ht y hy => rD_ray ra d δ Fa ht hy) _ hq u v
      (by rw [hFe]; exact hu') (by rw [hFe]; exact hv') hli

include hρ in
/-- **[D] §4: the northern cap has positive sectional curvature.** For [D]'s parameters, and a
smooth star representation whose infinitesimal action has norm `≤ 2` on unit vectors (lem:K), the
quotient metric `g_B` of `(V × S³, G_N)` by the star action has positive sectional curvature at
every `Y` with `|Y| ≤ F_a`. -/
theorem northern_quotient_pos (Cη : ℝ) (hC0 : 0 ≤ Cη) (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    (a ε A0 Fa δ ra qs d : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa) (hδ : 0 < δ)
    {L : ℝ} (hL : 0 < L) (hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * Fa * (1 + Cη))) (hra : 0 < ra)
    (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) (hqs : qs = ε * A0 * Fa / 2)
    (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2) (hd1 : d < 1)
    (hK : ∀ e : V, ‖e‖ = 1 → ‖KY ρV e‖ ≤ L) (Y : V) (hY : ‖Y‖ ≤ Fa)
    (x c : TangentSpace 𝓘(ℝ, V) Y) (hxc : LinearIndependent ℝ ![x, c]) :
    0 < sectionalCurvatureAt isSymm_cmet_gB
      (isPosDef_cmet_gB fun Y => (rD_pos (V := V) hε hA0 hFa hra hqs hd hql Y).ne')
      (isContMDiffMetricSection_cmet ((contDiff_gB ρV δ
        (fun Y => (rD_pos (V := V) hε hA0 hFa hra hqs hd hql Y).ne') (contDiff_rD hδ)).of_le
          two_le_top_nat)) Y x c :=
  northQuot_sectionalCurvature_pos hρ (fun Y => (rD_pos hε hA0 hFa hra hqs hd hql Y).ne')
    (contDiff_rD hδ) (fun q Y => rD_invariant ra d δ Fa ρV q Y) Y
    (fun u v hu hv hli => north_hup hρ Cη hC0 hC a ε A0 Fa δ ra qs d hε hA0 hFa hδ hL hδ3 hra hra2
      hqs hd hql hd1 hK Y hY u v hu hv hli) x c hxc

end Assembly

end

end ExoticSpheres8And10

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Non-vacuity of `northern_quotient_pos`.** All its hypotheses hold simultaneously: [D]'s
parameters (`northern_filling_hyps_satisfiable`, with `A0 = Fa = 1`, `a = π/2`) and the trivial
star representation on `V = ℝ²`, whose infinitesimal action vanishes. -/
theorem northern_quotient_hyps_satisfiable :
    ∃ Cη δ ε ra qs d : ℝ, 0 ≤ Cη ∧ (∀ x, |deriv etaCut x| ≤ Cη) ∧ 0 < δ ∧
      δ ^ 3 ≤ 1 / (128 * 1 * 1 * (1 + Cη)) ∧ 0 < ε ∧ 0 < ra ∧
      ra ^ 2 = ε * Real.exp (ε * 1 * |Real.cos (π / 2)|) ∧ qs = ε * 1 * 1 / 2 ∧ d = ra * qs ∧
      qs * Gδ δ 1 ≤ 1 / 2 ∧ d < 1 ∧
      ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∞
        (fun q : S3 => (((1 : S3 →* (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)))
          q : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) ∧
      ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 →
        ‖KY (1 : S3 →* (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))) e‖ ≤ 2 := by
  obtain ⟨Cη, δ, ε, ra, qs, d, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ :=
    northern_filling_hyps_satisfiable
  refine ⟨Cη, δ, ε, ra, qs, d, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_⟩
  · have e : (fun q : S3 => (((1 : S3 →* (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin 2))) q : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) =
        fun _ => ContinuousLinearMap.id ℝ _ := by
      funext q; ext v; simp
    rw [e]; exact contMDiff_const
  · intro e _
    have h0 : dρ (1 : S3 →* (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))) = 0 := by
      have e1 : ρhat (1 : S3 →* (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))) =
          fun _ => ContinuousLinearMap.id ℝ _ := by
        funext q; ext v; simp [ρhat]
      rw [dρ, e1, mfderiv_const]; rfl
    have : KY (1 : S3 →* (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))) e = 0 := by
      rw [KY, h0, ContinuousLinearMap.comp_zero]
    rw [this, norm_zero]; norm_num

end

end ExoticSpheres8And10
