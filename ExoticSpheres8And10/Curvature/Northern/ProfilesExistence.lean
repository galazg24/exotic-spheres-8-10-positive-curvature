/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.ActionField.Chains

/-! # A7, completed: existence of the northern profiles, and positivity along the whole filling

[GG] §4.3, "Choice of profiles": "Fix `η` smooth and nondecreasing, with `η = 0` on `(−∞,¼]` and
`η = 1` on `[½,∞)`, and put `C_η = sup|η'|` [...]. Let `F' = e^{−F²/(2δ²)}`, `F(0) = 0` and
`ℓ_N = ∫₀^{F_a} e^{z²/(2δ²)}dz`. Set `d = r_aq_s` and `r(s) = r_a − d∫_s^{ℓ_N} η(v/δ)dv`, and require
`q_sℓ_N ≤ ½` and `d < 1`. [...] The inverse of the odd function `F ↦ ∫₀^F e^{z²/(2δ²)}dz` is
smooth [...]."

* `Fprof δ` is the inverse of `G(z) = ∫₀^z e^{t²/(2δ²)}dt`; `hasDerivAt_Fprof`:
  `F' = e^{−F²/(2δ²)}`; `hasDerivAt_Fprof'`: `F'' = −(F/δ²)F'²`; `Fprof_zero`, `Fprof_le`,
  `Fprof_pos`; `Fprof_G`: `F(ℓ_N) = F_a`.
* `etaCut x = smoothTransition(4x − 1)`: smooth, `0` on `(−∞,¼]`, `1` on `[½,∞)`, `0 ≤ η ≤ 1`;
  `exists_Ceta`: `sup|η'| < ∞`; `deriv_etaCut_support`.
* `rprof`: `r' = dη(s/δ)`, `r'' = (d/δ)η'(s/δ)`, `r_a/2 ≤ r ≤ r_a` under `q_sℓ_N ≤ ½`,
  `r(ℓ_N) = r_a`.
* `northern_filling_pos`: for **every** `s ∈ (0, ℓ_N]`, every `K` with `‖K‖ ≤ 2` and every
  independent star-horizontal pair, the numerator `eq:fullcurvature` of the actual profiles is
  positive.
-/

namespace ExoticSpheres8And10

open Real intervalIntegral MeasureTheory Filter Topology Set

/-! ## The profile `F` -/

/-- `G(z) = ∫₀^z e^{t²/(2δ²)} dt`. -/
noncomputable def Gδ (δ z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, Real.exp (t ^ 2 / (2 * δ ^ 2))

theorem continuous_Gintegrand (δ : ℝ) : Continuous fun t : ℝ => Real.exp (t ^ 2 / (2 * δ ^ 2)) := by
  fun_prop

theorem hasDerivAt_G (δ z : ℝ) : HasDerivAt (Gδ δ) (Real.exp (z ^ 2 / (2 * δ ^ 2))) z :=
  ((continuous_Gintegrand δ).integral_hasStrictDerivAt 0 z).hasDerivAt

theorem G_zero (δ : ℝ) : Gδ δ 0 = 0 := by simp [Gδ]

theorem G_strictMono (δ : ℝ) : StrictMono (Gδ δ) :=
  strictMono_of_deriv_pos fun z => by rw [(hasDerivAt_G δ z).deriv]; exact Real.exp_pos _

theorem G_sub_mono (δ : ℝ) : Monotone fun z => Gδ δ z - z := by
  have hd : ∀ z, HasDerivAt (fun z => Gδ δ z - z) (Real.exp (z ^ 2 / (2 * δ ^ 2)) - 1) z :=
    fun z => (hasDerivAt_G δ z).sub (hasDerivAt_id' z)
  apply monotone_of_deriv_nonneg (fun z => (hd z).differentiableAt)
  intro z
  rw [(hd z).deriv]
  have : 1 ≤ Real.exp (z ^ 2 / (2 * δ ^ 2)) := Real.one_le_exp (by positivity)
  linarith

theorem le_G {δ z : ℝ} (hz : 0 ≤ z) : z ≤ Gδ δ z := by
  have := G_sub_mono δ hz; simp only [G_zero, sub_zero] at this; linarith

theorem G_le {δ z : ℝ} (hz : z ≤ 0) : Gδ δ z ≤ z := by
  have := G_sub_mono δ hz; simp only [G_zero, sub_zero] at this; linarith

theorem G_continuous (δ : ℝ) : Continuous (Gδ δ) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_G δ z).continuousAt

theorem G_surjective (δ : ℝ) : Function.Surjective (Gδ δ) := by
  refine (G_continuous δ).surjective ?_ ?_
  · exact tendsto_atTop_mono' atTop (eventually_ge_atTop 0 |>.mono fun z hz => le_G hz)
      tendsto_id
  · exact tendsto_atBot_mono' atBot (eventually_le_atBot 0 |>.mono fun z hz => G_le hz)
      tendsto_id

/-- `G` as an order isomorphism of `ℝ`. -/
noncomputable def Gequiv (δ : ℝ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (Gδ δ) (G_strictMono δ) (G_surjective δ)

/-- **The profile `F`**, the inverse of `G`. -/
noncomputable def Fprof (δ : ℝ) (s : ℝ) : ℝ := (Gequiv δ).symm s

theorem G_Fprof (δ s : ℝ) : Gδ δ (Fprof δ s) = s := (Gequiv δ).apply_symm_apply s

theorem Fprof_G (δ z : ℝ) : Fprof δ (Gδ δ z) = z := (Gequiv δ).symm_apply_apply z

theorem Fprof_zero (δ : ℝ) : Fprof δ 0 = 0 := by
  have := Fprof_G δ 0; rwa [G_zero] at this

theorem Fprof_continuous (δ : ℝ) : Continuous (Fprof δ) := (Gequiv δ).symm.continuous

theorem Fprof_pos {δ s : ℝ} (hs : 0 < s) : 0 < Fprof δ s := by
  have h := (Gequiv δ).symm.strictMono hs
  rw [show (Gequiv δ).symm 0 = Fprof δ 0 from rfl, Fprof_zero] at h
  exact h

/-- `F(s) ≤ s` for `s ≥ 0` (`F' ≤ 1`, `F(0) = 0`). -/
theorem Fprof_le {δ s : ℝ} (hs : 0 ≤ s) : Fprof δ s ≤ s := by
  have h0 : 0 ≤ Fprof δ s := by
    rcases hs.eq_or_lt with h | h
    · rw [← h, Fprof_zero]
    · exact (Fprof_pos h).le
  have := le_G (δ := δ) h0
  rwa [G_Fprof] at this

/-- **`F' = e^{−F²/(2δ²)}`.** -/
theorem hasDerivAt_Fprof (δ s : ℝ) :
    HasDerivAt (Fprof δ) (Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2))) s := by
  have h := HasDerivAt.of_local_left_inverse (Fprof_continuous δ).continuousAt
    (hasDerivAt_G δ (Fprof δ s)) (Real.exp_pos _).ne' (Eventually.of_forall (G_Fprof δ))
  refine h.congr_deriv ?_
  rw [← Real.exp_neg, neg_div]

/-- **`F'' = −(F/δ²)F'²`.** -/
theorem hasDerivAt_Fprof' (δ s : ℝ) (hδ : δ ≠ 0) :
    HasDerivAt (fun s => Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)))
      (-(Fprof δ s / δ ^ 2) * Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) ^ 2) s := by
  have hF := hasDerivAt_Fprof δ s
  have h := ((((hasDerivAt_pow 2 (Fprof δ s)).comp s hF).neg).div_const (2 * δ ^ 2)).exp
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.neg_apply]
  first | (norm_num; field_simp; ring) | (field_simp; ring) | (norm_num; ring)

/-! ## The cutoff `η` -/

/-- `η(x) = smoothTransition(4x − 1)`. -/
noncomputable def etaCut (x : ℝ) : ℝ := Real.smoothTransition (4 * x - 1)

theorem etaCut_contDiff {n : ℕ∞} : ContDiff ℝ n etaCut :=
  (Real.smoothTransition.contDiff (n := n)).comp (by fun_prop : ContDiff ℝ n fun x : ℝ => 4 * x - 1)

theorem etaCut_zero {x : ℝ} (hx : x ≤ 1 / 4) : etaCut x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem etaCut_one {x : ℝ} (hx : 1 / 2 ≤ x) : etaCut x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem etaCut_nonneg (x : ℝ) : 0 ≤ etaCut x := Real.smoothTransition.nonneg _
theorem etaCut_le_one (x : ℝ) : etaCut x ≤ 1 := Real.smoothTransition.le_one _
theorem etaCut_continuous : Continuous etaCut := etaCut_contDiff (n := 0).continuous

theorem etaCut_differentiable : Differentiable ℝ etaCut :=
  (etaCut_contDiff (n := 1)).differentiable (by norm_num)

/-- `η'` vanishes outside `[¼, ½]`. -/
theorem deriv_etaCut_support {x : ℝ} (h : deriv etaCut x ≠ 0) : 1 / 4 ≤ x ∧ x ≤ 1 / 2 := by
  by_contra hc
  apply h
  rcases not_and_or.1 hc with h1 | h1
  · push Not at h1
    have : etaCut =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [gt_mem_nhds h1] with y hy using etaCut_zero hy.le
    rw [this.deriv_eq, deriv_const]
  · push Not at h1
    have : etaCut =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [lt_mem_nhds h1] with y hy using etaCut_one hy.le
    rw [this.deriv_eq, deriv_const]

/-- **`C_η = sup|η'|` is finite.** -/
theorem exists_Ceta : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv etaCut x| ≤ C := by
  have hc : Continuous (deriv etaCut) := (etaCut_contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ) / 4) (b := 1 / 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases h : deriv etaCut x = 0
  · rw [h, abs_zero]; exact le_max_right _ _
  · have := hC x (deriv_etaCut_support h)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-! ## The profile `r` -/

/-- `r(s) = r_a − d ∫_s^ℓ η(v/δ) dv`. -/
noncomputable def rprof (ra d δ ℓ s : ℝ) : ℝ := ra - d * ∫ v in s..ℓ, etaCut (v / δ)

theorem continuous_eta_div (δ : ℝ) : Continuous fun v => etaCut (v / δ) :=
  etaCut_continuous.comp (by fun_prop)

/-- **`r' = dη(s/δ)`.** -/
theorem hasDerivAt_rprof (ra d δ ℓ s : ℝ) :
    HasDerivAt (rprof ra d δ ℓ) (d * etaCut (s / δ)) s := by
  have h : HasDerivAt (fun u => ∫ v in ℓ..u, etaCut (v / δ)) (etaCut (s / δ)) s :=
    ((continuous_eta_div δ).integral_hasStrictDerivAt ℓ s).hasDerivAt
  have e : rprof ra d δ ℓ = fun u => ra + d * ∫ v in ℓ..u, etaCut (v / δ) := by
    funext u; simp only [rprof]; rw [integral_symm]; ring
  rw [e]
  exact (h.const_mul d).const_add ra

/-- **`r'' = (d/δ)η'(s/δ)`.** -/
theorem hasDerivAt_rprof' (d δ s : ℝ) :
    HasDerivAt (fun s => d * etaCut (s / δ)) (d * (deriv etaCut (s / δ) * (1 / δ))) s := by
  have h1 : HasDerivAt (fun s : ℝ => s / δ) (1 / δ) s := (hasDerivAt_id' s).div_const δ
  have h2 := (etaCut_differentiable (s / δ)).hasDerivAt.comp s h1
  exact h2.const_mul d

theorem integral_eta_bounds {δ ℓ s : ℝ} (hs : s ≤ ℓ) :
    0 ≤ ∫ v in s..ℓ, etaCut (v / δ) ∧ ∫ v in s..ℓ, etaCut (v / δ) ≤ ℓ - s := by
  have hint := (continuous_eta_div δ).intervalIntegrable (μ := volume) s ℓ
  constructor
  · exact integral_nonneg hs fun v _ => etaCut_nonneg _
  · have := integral_mono_on hs hint (intervalIntegrable_const (c := (1 : ℝ)))
      (fun v _ => etaCut_le_one (v / δ))
    simpa using this

/-- **`r_a/2 ≤ r ≤ r_a`** on `[0, ℓ]` under `d ℓ ≤ r_a/2` (i.e. `q_sℓ_N ≤ ½`). -/
theorem rprof_bounds {ra d δ ℓ s : ℝ} (hd : 0 ≤ d) (hs0 : 0 ≤ s) (hsℓ : s ≤ ℓ)
    (hdl : d * ℓ ≤ ra / 2) : ra / 2 ≤ rprof ra d δ ℓ s ∧ rprof ra d δ ℓ s ≤ ra := by
  obtain ⟨h1, h2⟩ := integral_eta_bounds (δ := δ) hsℓ
  simp only [rprof]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h2 hd]
  · nlinarith [mul_nonneg hd h1]

theorem rprof_end (ra d δ ℓ : ℝ) : rprof ra d δ ℓ ℓ = ra := by simp [rprof]

/-! ## The northern filling is positive at every `s ∈ (0, ℓ_N]` -/

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [CompleteSpace Vv]

/-- **[GG] §4.3, northern filling, all `s`.** Let `C_η ≥ |η'|`, and let the parameters satisfy
`eq:delta` (`δ³ ≤ 1/(128A₀F_a(1+C_η))`), `eq:bdata` (`r_a² = εe^{εA₀|cos a|}`, `q_s = ½εA₀F_a`),
`d = r_aq_s`, `q_sℓ_N ≤ ½` and `d < 1`, with `ℓ_N = G(F_a)`. Then at every `s ∈ (0, ℓ_N]`, with
`F = Fprof δ`, `r = rprof r_a d δ ℓ_N` and their derivatives (`hasDerivAt_Fprof`,
`hasDerivAt_Fprof'`, `hasDerivAt_rprof`, `hasDerivAt_rprof'`), every `K` with `‖K‖ ≤ 2` and every
independent star-horizontal pair has positive numerator `eq:fullcurvature`. -/
theorem northern_filling_pos (Cη : ℝ) (hC0 : 0 ≤ Cη) (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    (a ε A0 Fa δ ra qs d : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa) (hδ : 0 < δ)
    (hδ3 : δ ^ 3 ≤ 1 / (128 * A0 * Fa * (1 + Cη))) (hra : 0 < ra)
    (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) (hqs : qs = ε * A0 * Fa / 2)
    (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2) (hd1 : d < 1)
    (s : ℝ) (hs : s ∈ Ioc 0 (Gδ δ Fa))
    (K : Vv →L[ℝ] H) (hK : ‖K‖ ≤ 2) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ
      ![((lam, X, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X) :
          ℝ × H × Vv),
        (mu, Y, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) Y)]) :
    0 < northNumerator (Fprof δ s) (rprof ra d δ (Gδ δ Fa) s)
      (Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2))) (d * etaCut (s / δ))
      (-(Fprof δ s / δ ^ 2) * Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) ^ 2)
      (d * (deriv etaCut (s / δ) * (1 / δ)))
      (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X Y lam mu := by
  set ℓ := Gδ δ Fa
  set F := Fprof δ s
  set r := rprof ra d δ ℓ s
  set Fp := Real.exp (-F ^ 2 / (2 * δ ^ 2))
  set Fpp := -(F / δ ^ 2) * Fp ^ 2
  set rp := d * etaCut (s / δ)
  set rpp := d * (deriv etaCut (s / δ) * (1 / δ))
  have hqs0 : 0 ≤ qs := by rw [hqs]; positivity
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hF : 0 < F := Fprof_pos hs.1
  have hdl : d * ℓ ≤ ra / 2 := by rw [hd]; nlinarith
  obtain ⟨hr1, hr2⟩ := rprof_bounds (δ := δ) hd0 hs.1.le hs.2 hdl
  have hr : 0 < r := by linarith
  have hdr := (d_over_r_cubed_bound ε A0 Fa a ra r d qs hε hA0 hFa hra hr1 hd hqs hra2)
  have hdr3 : d / r ^ 3 ≤ 4 * A0 * Fa := hdr.1.trans (hdr.2.1 ▸ hdr.2.2)
  have hrp0 : 0 ≤ rp := mul_nonneg hd0 (etaCut_nonneg _)
  have hrpd : rp ≤ d := by
    have := etaCut_le_one (s / δ); nlinarith
  have hFp0 : 0 ≤ Fp := (Real.exp_pos _).le
  have hc1 := angular_chain F Fp δ A0 Fa Cη d r rp hF hδ hA0 hFa hC0 hr rfl hδ3 hdr3 hrpd
  have hc2 : 4 * F ^ 2 * max rpp 0 / r ^ 3 < -Fpp / F := by
    have hpos : 0 < -Fpp / F := by
      have e : -Fpp / F = Fp ^ 2 / δ ^ 2 := by simp only [Fpp]; field_simp
      rw [e]; have : 0 < Fp := Real.exp_pos _; positivity
    by_cases h0 : rpp ≤ 0
    · rw [max_eq_right h0]; simpa using hpos
    · push Not at h0
      rw [max_eq_left h0.le]
      have hne : deriv etaCut (s / δ) ≠ 0 := by
        intro h; simp [rpp, h] at h0
      have hsup := (deriv_etaCut_support hne).2
      have hsδ : s ≤ δ / 2 := by
        rw [div_le_iff₀ hδ] at hsup; linarith
      have hrppb : rpp ≤ d / δ * Cη := by
        have := (abs_le.1 (hC (s / δ))).2
        have e : rpp = d / δ * deriv etaCut (s / δ) := by simp only [rpp]; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      exact radial_chain F Fp Fpp s δ A0 Fa Cη d r rpp hF hδ hA0 hFa hC0 hr rfl hδ3 hdr3
        (Fprof_le hs.1.le) hsδ hrppb rfl
  exact northNumerator_pos F r Fp rp Fpp rpp hF hr hFp0 hrp0 (by linarith) hc1 hc2 _
    (norm_graphT_le K hK hF.le hr) X Y lam mu hind

/-- **Non-vacuity of `northern_filling_pos`.** All its parameter hypotheses are jointly
satisfiable: `A₀ = F_a = 1`, `a = π/2`, `δ = min(½, 1/(128(1+C_η)))`, `ε = min(1, 1/ℓ_N)`,
`r_a = √ε`, `q_s = ε/2`, `d = r_a q_s`; and `s = ℓ_N ∈ (0, ℓ_N]`. (The `K`, pair hypotheses are
satisfiable as in `Chains.lean`.) -/
theorem northern_filling_hyps_satisfiable :
    ∃ Cη δ ε ra qs d : ℝ, 0 ≤ Cη ∧ (∀ x, |deriv etaCut x| ≤ Cη) ∧ 0 < δ ∧
      δ ^ 3 ≤ 1 / (128 * 1 * 1 * (1 + Cη)) ∧ 0 < ε ∧ 0 < ra ∧
      ra ^ 2 = ε * Real.exp (ε * 1 * |Real.cos (π / 2)|) ∧ qs = ε * 1 * 1 / 2 ∧ d = ra * qs ∧
      qs * Gδ δ 1 ≤ 1 / 2 ∧ d < 1 ∧ Gδ δ 1 ∈ Ioc 0 (Gδ δ 1) := by
  obtain ⟨Cη, hC0, hC⟩ := exists_Ceta
  set δ := min (1 / 2 : ℝ) (1 / (128 * (1 + Cη))) with hδdef
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (128 * (1 + Cη)) := min_le_right _ _
  set ℓ := Gδ δ 1
  have hℓ : 1 ≤ ℓ := le_G (δ := δ) zero_le_one
  set ε := min (1 : ℝ) (1 / ℓ) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεℓ : ε ≤ 1 / ℓ := min_le_right _ _
  refine ⟨Cη, δ, ε, Real.sqrt ε, ε * 1 * 1 / 2, Real.sqrt ε * (ε * 1 * 1 / 2), hC0, hC, hδ, ?_,
    hε, Real.sqrt_pos.2 hε, ?_, rfl, rfl, ?_, ?_, ⟨by linarith, le_rfl⟩⟩
  · have h3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
    calc δ ^ 3 ≤ δ := h3
      _ ≤ 1 / (128 * (1 + Cη)) := hδ2
      _ = 1 / (128 * 1 * 1 * (1 + Cη)) := by ring
  · rw [Real.sq_sqrt hε.le, Real.cos_pi_div_two, abs_zero, mul_zero, Real.exp_zero, mul_one]
  · have : ε * ℓ ≤ 1 := by
      calc ε * ℓ ≤ 1 / ℓ * ℓ := mul_le_mul_of_nonneg_right hεℓ (by linarith)
        _ = 1 := by field_simp
    linarith
  · have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε1
    nlinarith [Real.sqrt_nonneg ε]

end ExoticSpheres8And10
