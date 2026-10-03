/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Northern.Chart

/-! # §4: positive curvature upstairs on the northern piece, away from the centre

At a point `q = Φ̂(s₀, 0, z30)` of `V × S³` (so `q = (F(s₀) e, 1)`), every plane of `T_q` that is
horizontal for the star action has positive sectional curvature for [D]'s northern metric.

* `sectionalCurvatureAt_Φh`: `K_{wG}(p₀; û, v̂) = K_{G_N}(Φ̂ p₀; dΦ̂ û, dΦ̂ v̂)`, where `wG` is the
  metric of `S4_NorthLocal`. The proof is germ locality (`Gh = wG` near `p₀`) followed by
  naturality (`Gh = Φ̂^* G_N`).
* `mfderiv_Φh_p0`: `dΦ̂_{p₀}(λ, X, U) = (F'λ e + F X, U)`.
* The vertical vectors `(K_Y β, β)` at `q` are the images of `(0, K_e β, β)`.
* A horizontal `u = dΦ̂ û` therefore has `û = (λ, X/F, TX/r)` with `T = −(F/r)K_e^*`. This is
  exactly `S4_NorthLocal`'s scaled star-horizontal vector.
* **`north_up_pos`**: positivity on every horizontal plane at `q`, under [D]'s parameter
  choices, for `s₀ ∈ (0, ℓ_N]` and `‖K_e‖ ≤ 2`.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Up

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {δ s₀ : ℝ} {e : V} {R : ℝ → ℝ} {rt : V → ℝ}

/-- **Curvature transfer** from `S4_NorthLocal`'s coordinates to `V × S³`. -/
theorem sectionalCurvatureAt_Φh (hδ : δ ≠ 0) (hs : 0 < s₀) (he : ‖e‖ = 1)
    (hR : ContDiff ℝ ∞ R) (hR0 : ∀ t, 0 < t → R t ≠ 0)
    (hRt : ∀ t, 0 < t → ∀ y : V, ‖y‖ = 1 → rt (Fprof δ t • y) = R t)
    (hrt : ContDiff ℝ ∞ rt) (hrt0 : ∀ Y, rt Y ≠ 0)
    (hbF : ∀ t, blend s₀ (Fprof δ) t ≠ 0) (hbR : ∀ t, blend s₀ R t ≠ 0)
    (x0 : Hs e) (z0 : E3) (u v : TangentSpace 𝓘(ℝ, Mc e) ((s₀, x0, z0) : Mc e)) :
    sectionalCurvatureAt (isSymm_wG (F := blend s₀ (Fprof δ)) (r := blend s₀ R) isSymm_HR isSymm_HR)
      (isPosDef_wG hbF hbR isPosDef_HR isPosDef_HR)
      (isContMDiffMetricSection_cmet (contDiff2_wG (contDiff_blend s₀ (Fprof_contDiff δ))
        (contDiff_blend s₀ hR) contDiff_HR contDiff_HR))
      ((s₀, x0, z0) : Mc e) u v =
    sectionalCurvatureAt (isSymm_northMetric δ rt) (isPosDef_northMetric δ hrt0)
      (isContMDiffMetricSection_northMetric hrt 2) (Φh δ s₀ e (s₀, x0, z0))
      (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) (s₀, x0, z0) u)
      (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) (s₀, x0, z0) v) := by
  have hgGh : IsContMDiffMetricSection (Mc e) 2 (cmet (Gh δ s₀ e R)) :=
    isContMDiffMetricSection_cmet ((contDiff_Gh hR).of_le (WithTop.coe_le_coe.mpr le_top))
  have hgerm : ∀ᶠ y in 𝓝 ((s₀, x0, z0) : Mc e),
      cmet (wG (blend s₀ (Fprof δ)) (blend s₀ R) HR HR) y = cmet (Gh δ s₀ e R) y :=
    (Gh_eventuallyEq hs x0 z0).mono fun y hy => by
      show wG (blend s₀ (Fprof δ)) (blend s₀ R) HR HR y = Gh δ s₀ e R y
      exact hy.symm
  have h1 := sectionalCurvatureAt_congr_metric
    (isSymm_wG (F := blend s₀ (Fprof δ)) (r := blend s₀ R) (F₁ := Hs e) (F₂ := E3)
      isSymm_HR isSymm_HR)
    (isPosDef_wG hbF hbR isPosDef_HR isPosDef_HR)
    (isContMDiffMetricSection_cmet (contDiff2_wG (contDiff_blend s₀ (Fprof_contDiff δ))
        (contDiff_blend s₀ hR) contDiff_HR contDiff_HR))
    isSymm_Gh (isPosDef_Gh hs hR0) hgGh hgerm u v
  have h2 := sectionalCurvatureAt_pullback (f := Φh δ s₀ e) (gM := cmet (Gh δ s₀ e R))
    (gN := northMetric δ rt) contMDiff_Φh
    (isInvertible_mfderiv_Φh (R := R) (rt := rt) hδ hs he hR0 hRt)
    (fun x a b => hpull_Φh hδ hs he hRt x a b) isSymm_Gh (isPosDef_Gh hs hR0) hgGh
    (isSymm_northMetric δ rt) (isPosDef_northMetric δ hrt0)
    (isContMDiffMetricSection_northMetric hrt 2) ((s₀, x0, z0) : Mc e) u v
  exact h1.trans h2

/-- The differential of `Φ̂`, componentwise. -/
theorem mfderiv_Φh_apply (p : Mc e) (a : TangentSpace 𝓘(ℝ, Mc e) p) :
    mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p a =
      ((D1 δ s₀ e p a, mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 p.2.2 a.2.2) : V × E3) := by
  have h1 : MDifferentiableAt 𝓘(ℝ, Mc e) 𝓘(ℝ, V)
      (fun p : Mc e => Fh δ s₀ p.1 • stereoE e (p.2.1 : V)) p :=
    ((contDiff_Φh_fst (δ := δ) (s₀ := s₀) (e := e)).contMDiff p).mdifferentiableAt (by simp)
  set L : Mc e →L[ℝ] E3 :=
    (ContinuousLinearMap.snd ℝ (Hs e) E3).comp (ContinuousLinearMap.snd ℝ ℝ (Hs e × E3))
  have hσ : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 3) σ3 (L p) :=
    (contMDiff_σ3 (L p)).mdifferentiableAt (by simp)
  have hL : MDifferentiableAt 𝓘(ℝ, Mc e) 𝓘(ℝ, E3) L p := L.mdifferentiableAt
  have h2 : MDifferentiableAt 𝓘(ℝ, Mc e) (𝓡 3) (σ3 ∘ L) p := hσ.comp p hL
  have hc : mfderiv 𝓘(ℝ, Mc e) (𝓡 3) (σ3 ∘ L) p = (mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 (L p)).comp L := by
    rw [mfderiv_comp p hσ hL, L.hasMFDerivAt.mfderiv]
    rfl
  have hpr := mfderiv_prodMk h1 h2
  have e1 : Φh δ s₀ e = fun p : Mc e => (Fh δ s₀ p.1 • stereoE e (p.2.1 : V), (σ3 ∘ L) p) := rfl
  rw [e1, hpr, hc, mfderiv_eq_fderiv]
  refine Prod.ext ?_ rfl
  exact fderiv_Φh_fst p a

/-- The base point `p₀ = (s₀, 0, chart(1))`. -/
abbrev p0 (s₀ : ℝ) (e : V) : Mc e := (s₀, 0, z30)

omit [FiniteDimensional ℝ V] in
theorem Φh_p0 (hs : 0 < s₀) :
    Φh δ s₀ e (p0 s₀ e) = (Fprof δ s₀ • e, (1 : S3)) := by
  simp only [Φh, p0, Fh, reparam_eq hs (by linarith : s₀ / 2 ≤ s₀), ZeroMemClass.coe_zero,
    stereo_zero, σ3_z30]

theorem psiR_zero {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] :
    ψR (0 : K) = 1 := by simp [ψR]

theorem psiR_z30 : ψR z30 = 1 := by rw [z30_eq]; exact psiR_zero

/-- `dΦ̂` at `p₀`: `(λ, X, U) ↦ (F'(s₀)λ e + F(s₀) X, U)`. -/
theorem mfderiv_Φh_p0 (hs : 0 < s₀) (a : TangentSpace 𝓘(ℝ, Mc e) (p0 s₀ e)) :
    mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) (p0 s₀ e) a =
      (((deriv (Fh δ s₀) s₀ * a.1) • e + Fprof δ s₀ • (a.2.1 : V), a.2.2) : V × E3) := by
  rw [mfderiv_Φh_apply]
  have hm : mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 (p0 s₀ e).2.2 = ContinuousLinearMap.id ℝ E3 := mfderiv_σ3
  rw [hm]
  refine Prod.ext ?_ rfl
  simp only [D1, p0, ZeroMemClass.coe_zero, stereo_zero, dst_zero, Fh,
    reparam_eq hs (by linarith : s₀ / 2 ≤ s₀)]

end Up

section Plane

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))

omit [FiniteDimensional ℝ V] in
theorem KY_smul (c : ℝ) (Y : V) : KY ρV (c • Y) = c • KY ρV Y := by
  ext β
  simp [KY]

include hρ in
theorem KY_mem (e : V) (β : E3) : KY ρV e β ∈ (ℝ ∙ e)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact inner_Y_KY hρ e β

/-- `K_e` as a map into `e^⊥`. -/
def Kh (e : V) : E3 →L[ℝ] Hs e := (KY ρV e).codRestrict _ (KY_mem hρ e)

theorem Kh_coe (e : V) (β : E3) : ((Kh hρ e β : Hs e) : V) = KY ρV e β := rfl

theorem norm_Kh_le (e : V) : ‖Kh hρ e‖ ≤ ‖KY ρV e‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun β => by
    show ‖((Kh hρ e β : Hs e) : V)‖ ≤ _
    rw [Kh_coe]
    exact (KY ρV e).le_opNorm β

/-- The vertical vectors in polar coordinates, `(0, K_e β, β)`. -/
def wvP (e : V) (β : E3) : Mc e := (0, Kh hρ e β, β)

theorem mfderiv_Φh_wv {δ s₀ : ℝ} {e : V} (hs : 0 < s₀) (β : E3) :
    mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) (p0 s₀ e) (toTSv (p0 s₀ e) (wvP hρ e β)) =
      ιv ρV (Fprof δ s₀ • e) β := by
  rw [mfderiv_Φh_p0 hs, ιv_apply, KY_smul]
  refine Prod.ext ?_ rfl
  simp only [toTSv, wvP, Kh_coe, mul_zero, zero_smul, zero_add, ContinuousLinearMap.smul_apply]

include hρ in
/-- **Positive curvature upstairs, away from the centre.** For [D]'s parameters (those of
`northern_sectionalCurvature_pos_all`), `s₀ ∈ (0, ℓ_N]`, a unit `e` with `‖K_e‖ ≤ 2`, and a
fibre radius `r̃` equal to [D]'s `r` along rays: every plane at `q = (F(s₀) e, 1)` that is
horizontal for the star action has positive sectional curvature for [D]'s northern metric. -/
theorem north_up_pos (Cη : ℝ) (hC0 : 0 ≤ Cη) (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    (a ε A0 Fa δ ra qs d : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa) (hδ : 0 < δ)
    {L : ℝ} (hL : 0 < L) (hδ3 : δ ^ 3 ≤ 1 / (32 * L ^ 2 * A0 * Fa * (1 + Cη))) (hra : 0 < ra)
    (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) (hqs : qs = ε * A0 * Fa / 2)
    (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2) (hd1 : d < 1)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioc 0 (Gδ δ Fa)) {e : V} (he : ‖e‖ = 1) (hK : ‖KY ρV e‖ ≤ L)
    {rt : V → ℝ} (hrt : ContDiff ℝ ∞ rt) (hrt0 : ∀ Y, rt Y ≠ 0)
    (hRt : ∀ t, 0 < t → ∀ y : V, ‖y‖ = 1 → rt (Fprof δ t • y) = rprof ra d δ (Gδ δ Fa) t)
    (q : V × S3) (hq : Φh δ s₀ e (p0 s₀ e) = q) (u v : TangentSpace (IN V) q)
    (hu : ∀ β, northMetric δ rt q u (ιv ρV (Fprof δ s₀ • e) β) = 0)
    (hv : ∀ β, northMetric δ rt q v (ιv ρV (Fprof δ s₀ • e) β) = 0)
    (hli : LinearIndependent ℝ ![u, v]) :
    0 < sectionalCurvatureAt (isSymm_northMetric δ rt) (isPosDef_northMetric δ hrt0)
      (isContMDiffMetricSection_northMetric hrt 2) q u v := by
  subst hq
  set R := rprof ra d δ (Gδ δ Fa) with hRdef
  have hs : 0 < s₀ := (Set.mem_Ioc.mp hs₀).1
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hd0 : 0 ≤ d := by rw [hd, hqs]; positivity
  have hdl : d * Gδ δ Fa ≤ ra / 2 := by
    have : 0 ≤ qs := by rw [hqs]; positivity
    rw [hd]; nlinarith
  have hRpos : ∀ t, 0 ≤ t → 0 < R t := fun t ht => by
    rcases le_or_gt t (Gδ δ Fa) with h | h
    · have := (rprof_bounds (δ := δ) hd0 ht h hdl).1
      linarith
    · have := rprof_ge_of_le (ra := ra) (δ := δ) hd0 h.le
      linarith
  have hR : ContDiff ℝ ∞ R := contDiff_rprof ra d δ (Gδ δ Fa)
  have hR0 : ∀ t, 0 < t → R t ≠ 0 := fun t ht => (hRpos t ht.le).ne'
  have hbF : ∀ t, blend s₀ (Fprof δ) t ≠ 0 := fun t =>
    (blend_pos hs (fun t ht => Fprof_pos (by linarith)) t).ne'
  have hbR : ∀ t, blend s₀ R t ≠ 0 := fun t =>
    (blend_pos hs (fun t ht => hRpos t (by linarith)) t).ne'
  have hF : 0 < Fprof δ s₀ := Fprof_pos hs
  have hRs : 0 < R s₀ := hRpos s₀ hs.le
  -- the differential at `p₀` and the pulled-back vectors
  set L := mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) (p0 s₀ e) with hLdef
  have hLi : L.IsInvertible := isInvertible_mfderiv_Φh (R := R) (rt := rt) hδ0 hs he hR0 hRt _
  set uh := L.inverse u with huh
  set vh := L.inverse v with hvh
  have hLu : L uh = u := hLi.self_apply_inverse u
  have hLv : L vh = v := hLi.self_apply_inverse v
  -- horizontality in polar coordinates
  have hhor : ∀ (w : TangentSpace 𝓘(ℝ, Mc e) (p0 s₀ e)),
      (∀ β, northMetric δ rt (Φh δ s₀ e (p0 s₀ e)) (L w) (ιv ρV (Fprof δ s₀ • e) β) = 0) →
      w.2.2 = (-(Fprof δ s₀ ^ 2 / R s₀ ^ 2)) •
        ContinuousLinearMap.adjoint (Kh hρ e) w.2.1 := by
    intro w hw
    have hz : ∀ β : E3, ⟪Fprof δ s₀ ^ 2 • ContinuousLinearMap.adjoint (Kh hρ e) w.2.1 +
        R s₀ ^ 2 • w.2.2, β⟫ = 0 := fun β => by
      have h1 := hpull_Φh (R := R) hδ0 hs he hRt (p0 s₀ e) w (toTSv (p0 s₀ e) (wvP hρ e β))
      rw [mfderiv_Φh_wv hρ hs, hw β, Gh_apply δ s₀ e R (p0 s₀ e) w (toTSv (p0 s₀ e) (wvP hρ e β))]
        at h1
      simp only [toTSv, wvP, p0, Fh, reparam_eq hs (by linarith : s₀ / 2 ≤ s₀), psiR_zero, psiR_z30,
        mul_zero, zero_add, one_mul] at h1
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left]
      linarith
    have h0 := hz (Fprof δ s₀ ^ 2 • ContinuousLinearMap.adjoint (Kh hρ e) w.2.1 +
      R s₀ ^ 2 • w.2.2)
    rw [inner_self_eq_zero] at h0
    have h2 : R s₀ ^ 2 • w.2.2 = -(Fprof δ s₀ ^ 2 • ContinuousLinearMap.adjoint (Kh hρ e) w.2.1) :=
      eq_neg_of_add_eq_zero_right h0
    have hR2 : R s₀ ^ 2 ≠ 0 := by positivity
    rw [← inv_smul_smul₀ hR2 w.2.2, h2]
    module
  have hu3 := hhor uh (by rw [hLu]; exact hu)
  have hv3 := hhor vh (by rw [hLv]; exact hv)
  -- the scaled star-horizontal form of `S4_NorthLocal`
  set T : Hs e →L[ℝ] E3 := (-(Fprof δ s₀ / R s₀)) • ContinuousLinearMap.adjoint (Kh hρ e) with hT
  have hvec : ∀ w : TangentSpace 𝓘(ℝ, Mc e) (p0 s₀ e),
      w.2.2 = (-(Fprof δ s₀ ^ 2 / R s₀ ^ 2)) • ContinuousLinearMap.adjoint (Kh hρ e) w.2.1 →
      toTSv ((s₀, 0, z30) : Mc e) (scaledVecC (blend s₀ (Fprof δ)) (blend s₀ R) (ψR (0 : Hs e))
        (ψR z30) s₀ w.1 (Fprof δ s₀ • w.2.1) (T (Fprof δ s₀ • w.2.1))) = w := by
    intro w hw3
    show ((w.1, _, _) : Mc e) = w
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show (blend s₀ (Fprof δ) s₀ * √(ψR (0 : Hs e)))⁻¹ • (Fprof δ s₀ • w.2.1) = w.2.1
      rw [blend_eq hs _ (by linarith : s₀ / 2 ≤ s₀), psiR_zero, Real.sqrt_one, mul_one, smul_smul,
        inv_mul_cancel₀ hF.ne', one_smul]
    · show (blend s₀ R s₀ * √(ψR z30))⁻¹ • (T (Fprof δ s₀ • w.2.1)) = w.2.2
      rw [blend_eq hs _ (by linarith : s₀ / 2 ≤ s₀), psiR_z30, Real.sqrt_one, mul_one, hw3, hT,
        ContinuousLinearMap.smul_apply, map_smul]
      have hR' : R s₀ ≠ 0 := hRs.ne'
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
  -- linear independence of the unscaled triples
  set S : Mc e →L[ℝ] Mc e := (ContinuousLinearMap.id ℝ ℝ).prodMap
    ((Fprof δ s₀ • ContinuousLinearMap.id ℝ (Hs e)).prodMap (R s₀ • ContinuousLinearMap.id ℝ E3))
  have hSw : ∀ w : TangentSpace 𝓘(ℝ, Mc e) (p0 s₀ e),
      w.2.2 = (-(Fprof δ s₀ ^ 2 / R s₀ ^ 2)) • ContinuousLinearMap.adjoint (Kh hρ e) w.2.1 →
      ((w.1, Fprof δ s₀ • w.2.1, T (Fprof δ s₀ • w.2.1)) : Mc e) = S w := by
    intro w hw3
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show T (Fprof δ s₀ • w.2.1) = R s₀ • w.2.2
    rw [hw3, hT, ContinuousLinearMap.smul_apply, map_smul, smul_smul, smul_smul]
    have hR' : R s₀ ≠ 0 := hRs.ne'
    congr 1
    field_simp
  have hSinj : LinearMap.ker (S : Mc e →ₗ[ℝ] Mc e) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => ?_
    have h1 : w.1 = 0 := by simpa [S] using congrArg Prod.fst hw
    have h2 : Fprof δ s₀ • w.2.1 = 0 := by simpa [S] using congrArg (fun z : Mc e => z.2.1) hw
    have h3 : R s₀ • w.2.2 = 0 := by simpa [S] using congrArg (fun z : Mc e => z.2.2) hw
    rw [smul_eq_zero] at h2 h3
    exact Prod.ext h1 (Prod.ext (h2.resolve_left hF.ne') (h3.resolve_left hRs.ne'))
  have hlih : LinearIndependent ℝ ![uh, vh] := by
    refine LinearIndependent.of_comp (L : Mc e →L[ℝ] V × E3).toLinearMap ?_
    have : (L : Mc e →L[ℝ] V × E3).toLinearMap ∘ ![uh, vh] = ![u, v] := by
      funext i
      fin_cases i
      · show L uh = u; exact hLu
      · show L vh = v; exact hLv
    rw [this]; exact hli
  have hind : LinearIndependent ℝ ![((uh.1, Fprof δ s₀ • uh.2.1, T (Fprof δ s₀ • uh.2.1)) :
      ℝ × Hs e × E3), (vh.1, Fprof δ s₀ • vh.2.1, T (Fprof δ s₀ • vh.2.1))] := by
    have hm := hlih.map' (S : Mc e →ₗ[ℝ] Mc e) hSinj
    have : (S : Mc e →ₗ[ℝ] Mc e) ∘ ![uh, vh] = ![((uh.1, Fprof δ s₀ • uh.2.1,
        T (Fprof δ s₀ • uh.2.1)) : ℝ × Hs e × E3), (vh.1, Fprof δ s₀ • vh.2.1,
        T (Fprof δ s₀ • vh.2.1))] := by
      funext i
      fin_cases i
      · show S uh = _; exact (hSw uh hu3).symm
      · show S vh = _; exact (hSw vh hv3).symm
    rw [← this]; exact hm
  -- positivity in `S4_NorthLocal`'s coordinates, transferred to `V × S³`
  have hpos := northern_sectionalCurvature_pos_all Cη hC0 hC a ε A0 Fa δ ra qs d hε hA0 hFa hδ
    hL hδ3 hra hra2 hqs hd hql hd1 s₀ hs₀ (0 : Hs e) z30 (Kh hρ e) ((norm_Kh_le hρ e).trans hK)
    (Fprof δ s₀ • uh.2.1) (Fprof δ s₀ • vh.2.1) uh.1 vh.1 hind
  have hpos2 : 0 < sectionalCurvatureAt
      (isSymm_wG (F := blend s₀ (Fprof δ)) (r := blend s₀ R) (F₁ := Hs e) (F₂ := E3)
        isSymm_HR isSymm_HR)
      (isPosDef_wG hbF hbR isPosDef_HR isPosDef_HR)
      (isContMDiffMetricSection_cmet (contDiff2_wG (contDiff_blend s₀ (Fprof_contDiff δ))
        (contDiff_blend s₀ hR) contDiff_HR contDiff_HR))
      ((s₀, 0, z30) : Mc e) uh vh := by
    convert hpos using 2
    · exact (hvec uh hu3).symm
    · exact (hvec vh hv3).symm
  have hfin := sectionalCurvatureAt_Φh (R := R) (rt := rt) hδ0 hs he hR hR0 hRt hrt hrt0 hbF hbR
    (0 : Hs e) z30 uh vh
  have e2 : mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) ((s₀, 0, z30) : Mc e) uh = u := hLu
  have e3 : mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) ((s₀, 0, z30) : Mc e) vh = v := hLv
  rw [e2, e3] at hfin
  exact hpos2.trans_eq hfin

end Plane

end

end ExoticSpheres8And10
