/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Gluing.ChartS3
import ExoticSpheres8And10.Geometry.Germ
import ExoticSpheres8And10.Analysis.Reparametrisation
import ExoticSpheres8And10.Curvature.Northern.Local
import ExoticSpheres8And10.Curvature.Northern.QuotientSubmersion

/-! # §4: polar coordinates on the northern piece, as a local isometry

For a unit vector `e ∈ V`, `s₀ > 0` and [D]'s radial profile `F = Fprof δ`, the map

  `Φ̂(s, x, z) = (F(φ(s)) σ_e(x), σ3(z)) : ℝ × e^⊥ × ℝ³ → V × S³`,

with `φ = reparam s₀`, is a **local isometry from `Gh` to [D]'s northern metric `G_N`**. Here

  `Gh = φ'(s)² ds² + F(φ(s))² HR(x) + R(φ(s))² HR(z)`,

and `r̃(F(t) y) = R(t)` on unit vectors.

* `hpull_Φh`: `Gh = Φ̂^* G_N`. The identity `F'²(1 + F²ψ(F²)) = 1`, from [D]'s ODE
  `F' = e^{−F²/2δ²}`, turns `|dY|² + ψ(|Y|²)⟪Y,dY⟫²` into `ds² + F²HR`.
* `isInvertible_mfderiv_Φh`: `dΦ̂` is invertible everywhere.
* `Gh_eventuallyEq`: near `s = s₀`, `Gh` is `S4_NorthLocal`'s metric
  `wG(blend F, blend R, HR, HR)`.
* **`sectionalCurvatureAt_Φh`**: the sectional curvature of `G_N` at `Φ̂ p₀` is that of
  `S4_NorthLocal`'s metric at `p₀`, by naturality and germ locality.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem mvfderiv_vs {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) f x v = fderiv ℝ f x v := by
  unfold mvfderiv
  rw [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
  rfl

theorem deriv_reparam_eq_one {s₀ t : ℝ} (hs : 0 < s₀) (ht : s₀ / 2 < t) :
    deriv (reparam s₀) t = 1 := by
  have e : reparam s₀ =ᶠ[𝓝 t] id := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact reparam_eq hs hu.le
  rw [e.deriv_eq, deriv_id]

theorem deriv_reparam_pos {s₀ : ℝ} (hs : 0 < s₀) (t : ℝ) : 0 < deriv (reparam s₀) t := by
  rw [(hasDerivAt_reparam t).deriv]; exact reparamDeriv_pos hs t

section Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The orthogonal complement `e^⊥`. -/
abbrev Hs (e : V) : Type := ↥(ℝ ∙ e)ᗮ

/-- The polar model space `ℝ × e^⊥ × ℝ³`. -/
abbrev Mc (e : V) : Type := ℝ × Hs e × E3

theorem inner_Hs_e {e : V} (x : Hs e) : ⟪(x : V), e⟫ = 0 := by
  have h := x.2
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h
  rw [real_inner_comm]; exact h

variable (δ s₀ : ℝ) (e : V) (R : ℝ → ℝ)

/-- The reparametrised radial profile `F ∘ φ`. -/
def Fh (t : ℝ) : ℝ := Fprof δ (reparam s₀ t)

/-- **The polar chart.** -/
def Φh (p : Mc e) : V × S3 := (Fh δ s₀ p.1 • stereoE e (p.2.1 : V), σ3 p.2.2)

/-- **The pulled-back metric**, `φ'² ds² + F(φ)² HR + R(φ)² HR`. -/
def Gh (p : Mc e) : Mc e →L[ℝ] Mc e →L[ℝ] ℝ :=
  wG (Fh δ s₀) (fun t => R (reparam s₀ t)) HR HR p +
    (deriv (reparam s₀) p.1 ^ 2 - 1) • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.fst ℝ ℝ (Hs e × E3)) (ContinuousLinearMap.fst ℝ ℝ (Hs e × E3))

theorem Gh_apply (p a b : Mc e) : Gh δ s₀ e R p a b =
    deriv (reparam s₀) p.1 ^ 2 * (a.1 * b.1) + Fh δ s₀ p.1 ^ 2 * (ψR p.2.1 * ⟪a.2.1, b.2.1⟫) +
      R (reparam s₀ p.1) ^ 2 * (ψR p.2.2 * ⟪a.2.2, b.2.2⟫) := by
  simp only [Gh, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, wG_apply,
    HR_apply, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.coe_fst', smul_eq_mul]
  ring

variable {δ s₀ e R}

theorem contDiff_Fh : ContDiff ℝ ∞ (Fh δ s₀) := (Fprof_contDiff δ).comp contDiff_reparam

theorem contDiff_Gh (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (fun p : Mc e => (Gh δ s₀ e R p : Mc e →L[ℝ] Mc e →L[ℝ] ℝ)) := by
  have hR' : ContDiff ℝ ∞ fun t => R (reparam s₀ t) := hR.comp (contDiff_reparam (s₀ := s₀))
  have h1 := contDiff_wG (F₁ := Hs e) (F₂ := E3) (contDiff_Fh (δ := δ) (s₀ := s₀))
    hR' contDiff_HR contDiff_HR
  have h2 : ContDiff ℝ ∞ fun p : Mc e => deriv (reparam s₀) p.1 ^ 2 - 1 :=
    (((contDiff_deriv' contDiff_reparam).comp contDiff_fst).pow 2).sub contDiff_const
  exact h1.add (h2.smul contDiff_const)

theorem isSymm_Gh : IsSymm (cmet (Gh δ s₀ e R)) := fun p a b => by
  show Gh δ s₀ e R p (fromTS a) (fromTS b) = Gh δ s₀ e R p (fromTS b) (fromTS a)
  rw [Gh_apply, Gh_apply, real_inner_comm (fromTS a).2.1 (fromTS b).2.1,
    real_inner_comm (fromTS a).2.2 (fromTS b).2.2]
  ring

theorem Gh_pos (hs : 0 < s₀) (hR : ∀ t, 0 < t → R t ≠ 0) (p : Mc e) {w : Mc e} (hw : w ≠ 0) :
    0 < Gh δ s₀ e R p w w := by
  rw [Gh_apply]
  have hd := deriv_reparam_pos hs p.1
  have hF : 0 < Fh δ s₀ p.1 := Fprof_pos (reparam_pos hs p.1)
  have hRp : 0 < R (reparam s₀ p.1) ^ 2 := by have := hR _ (reparam_pos hs p.1); positivity
  have h1 : 0 ≤ deriv (reparam s₀) p.1 ^ 2 * (w.1 * w.1) :=
    mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
  have h2 : 0 ≤ Fh δ s₀ p.1 ^ 2 * (ψR p.2.1 * ⟪w.2.1, w.2.1⟫) :=
    mul_nonneg (by positivity) (mul_nonneg (ψR_pos _).le real_inner_self_nonneg)
  have h3 : 0 ≤ R (reparam s₀ p.1) ^ 2 * (ψR p.2.2 * ⟪w.2.2, w.2.2⟫) :=
    mul_nonneg hRp.le (mul_nonneg (ψR_pos _).le real_inner_self_nonneg)
  by_cases a1 : w.1 = 0
  · by_cases a2 : w.2.1 = 0
    · have a3 : w.2.2 ≠ 0 := fun h => hw (Prod.ext a1 (Prod.ext a2 h))
      have : 0 < R (reparam s₀ p.1) ^ 2 * (ψR p.2.2 * ⟪w.2.2, w.2.2⟫) :=
        mul_pos hRp (mul_pos (ψR_pos _) (real_inner_self_pos.2 a3))
      linarith
    · have : 0 < Fh δ s₀ p.1 ^ 2 * (ψR p.2.1 * ⟪w.2.1, w.2.1⟫) :=
        mul_pos (by positivity) (mul_pos (ψR_pos _) (real_inner_self_pos.2 a2))
      linarith
  · have : 0 < deriv (reparam s₀) p.1 ^ 2 * (w.1 * w.1) :=
      mul_pos (by positivity) (mul_self_pos.2 a1)
    linarith

theorem isPosDef_Gh (hs : 0 < s₀) (hR : ∀ t, 0 < t → R t ≠ 0) : IsPosDef (cmet (Gh δ s₀ e R)) :=
  fun p v hv => Gh_pos hs hR p (w := fromTS v) hv

/-- **Near `s₀`, `Gh` is `S4_NorthLocal`'s metric.** -/
theorem Gh_eventuallyEq (hs : 0 < s₀) (x0 : Hs e) (z0 : E3) :
    ∀ᶠ p in 𝓝 ((s₀, x0, z0) : Mc e),
      Gh δ s₀ e R p = wG (blend s₀ (Fprof δ)) (blend s₀ R) HR HR p := by
  have hmem : {p : Mc e | s₀ / 2 < p.1} ∈ 𝓝 ((s₀, x0, z0) : Mc e) :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (show s₀ / 2 < s₀ by linarith)
  filter_upwards [hmem] with p hp
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  rw [Gh_apply, wG_apply, HR_apply, HR_apply, blend_eq hs _ hp.le, blend_eq hs _ hp.le,
    deriv_reparam_eq_one hs hp]
  simp only [Fh, reparam_eq hs hp.le]
  ring

/-! ### The chart map -/

theorem contDiff_Φh_fst :
    ContDiff ℝ ∞ fun p : Mc e => Fh δ s₀ p.1 • stereoE e (p.2.1 : V) := by
  have hx : ContDiff ℝ ∞ (fun p : Mc e => ((p.2.1 : Hs e) : V)) :=
    ((ℝ ∙ e)ᗮ.subtypeL).contDiff.comp (contDiff_fst.comp contDiff_snd)
  exact ((contDiff_Fh (δ := δ) (s₀ := s₀)).comp contDiff_fst).smul ((contDiff_stereo e).comp hx)

theorem contMDiff_Φh : ContMDiff 𝓘(ℝ, Mc e) (IN V) ∞ (Φh δ s₀ e) := by
  have h2 : ContMDiff 𝓘(ℝ, Mc e) (𝓡 3) ∞ (fun p : Mc e => σ3 p.2.2) :=
    contMDiff_σ3.comp (contDiff_snd.comp contDiff_snd).contMDiff
  exact (contDiff_Φh_fst (δ := δ) (s₀ := s₀) (e := e)).contMDiff.prodMk h2

variable (δ s₀ e) in
/-- The differential of the first component. -/
def D1 (p a : Mc e) : V :=
  (deriv (Fh δ s₀) p.1 * a.1) • stereoE e (p.2.1 : V) + Fh δ s₀ p.1 • dst e (p.2.1 : V) (a.2.1 : V)

theorem fderiv_Φh_fst (p a : Mc e) :
    fderiv ℝ (fun p : Mc e => Fh δ s₀ p.1 • stereoE e (p.2.1 : V)) p a = D1 δ s₀ e p a := by
  have hc : HasFDerivAt (fun p : Mc e => Fh δ s₀ p.1)
      (deriv (Fh δ s₀) p.1 • ContinuousLinearMap.fst ℝ ℝ (Hs e × E3)) p :=
    (hasDerivAt_self' (contDiff_Fh (δ := δ) (s₀ := s₀)) p.1).comp_hasFDerivAt p (hasFDerivAt_fst)
  set L : Mc e →L[ℝ] V := (Submodule.subtypeL _).comp
    ((ContinuousLinearMap.fst ℝ (Hs e) E3).comp (ContinuousLinearMap.snd ℝ ℝ (Hs e × E3)))
  have hf : HasFDerivAt (fun p : Mc e => stereoE e (p.2.1 : V)) ((dstL e (p.2.1 : V)).comp L) p :=
    (hasFDerivAt_stereo e (L p)).comp p L.hasFDerivAt
  have h : HasFDerivAt (fun p : Mc e => Fh δ s₀ p.1 • stereoE e (p.2.1 : V)) _ p := hc.smul hf
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, dstL_apply,
    ContinuousLinearMap.coe_fst', L, D1, Submodule.subtypeL_apply, ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  abel

variable (e) in
/-- The differential of the fibre component, into `ℍ`. -/
def D3 (p a : Mc e) : Quaternion ℝ := dst 1 (ι3 p.2.2) (ι3 a.2.2)

theorem fderiv_Φh_snd (p a : Mc e) :
    fderiv ℝ (fun p : Mc e => ((σ3 p.2.2 : S3) : Quaternion ℝ)) p a = D3 e p a := by
  set L : Mc e →L[ℝ] E3 :=
    (ContinuousLinearMap.snd ℝ (Hs e) E3).comp (ContinuousLinearMap.snd ℝ ℝ (Hs e × E3))
  have h : HasFDerivAt (fun p : Mc e => ((σ3 p.2.2 : S3) : Quaternion ℝ)) _ p :=
    (hasFDerivAt_val_σ3 (L p)).comp p L.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem hasDerivAt_Fh (t : ℝ) :
    HasDerivAt (Fh δ s₀) (Real.exp (-(Fh δ s₀ t) ^ 2 / (2 * δ ^ 2)) * reparamDeriv s₀ t) t :=
  (hasDerivAt_Fprof δ (reparam s₀ t)).comp t (hasDerivAt_reparam t)

/-- **`Gh` is the pullback of [D]'s northern metric along `Φ̂`.** -/
theorem hpull_Φh (hδ : δ ≠ 0) {rt : V → ℝ} (hs : 0 < s₀) (he : ‖e‖ = 1)
    (hRt : ∀ t, 0 < t → ∀ y : V, ‖y‖ = 1 → rt (Fprof δ t • y) = R t) (p : Mc e)
    (a b : TangentSpace 𝓘(ℝ, Mc e) p) :
    Gh δ s₀ e R p a b = northMetric δ rt (Φh δ s₀ e p) (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p a)
      (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p b) := by
  have hΦ : MDifferentiableAt 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p :=
    (contMDiff_Φh p).mdifferentiableAt (by simp)
  have hY : ∀ c : TangentSpace 𝓘(ℝ, Mc e) p, mvfderiv (IN V) fY (Φh δ s₀ e p)
      (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p c) = D1 δ s₀ e p c := fun c => by
    rw [← mvfderiv_comp' ((contMDiff_fY _).mdifferentiableAt (by simp)) hΦ]
    show mvfderiv 𝓘(ℝ, Mc e) (fun p : Mc e => Fh δ s₀ p.1 • stereoE e (p.2.1 : V)) p c = _
    rw [mvfderiv_vs]; exact fderiv_Φh_fst p c
  have hU : ∀ c : TangentSpace 𝓘(ℝ, Mc e) p, mvfderiv (IN V) fU (Φh δ s₀ e p)
      (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p c) = D3 e p c := fun c => by
    rw [← mvfderiv_comp' ((contMDiff_fU _).mdifferentiableAt (by simp)) hΦ]
    show mvfderiv 𝓘(ℝ, Mc e) (fun p : Mc e => ((σ3 p.2.2 : S3) : Quaternion ℝ)) p c = _
    rw [mvfderiv_vs]; exact fderiv_Φh_snd p c
  have hY' : ∀ c : TangentSpace 𝓘(ℝ, Mc e) p, (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p c).1 = D1 δ s₀ e p c :=
    fun c => (mvfderiv_fY _ _).symm.trans (hY c)
  rw [northMetric_apply, hY, hY, hU, hU, mvfderiv_fQ, mvfderiv_fQ, hY', hY']
  -- the geometry of the two stereographic charts
  have hx : ⟪(p.2.1 : V), e⟫ = 0 := inner_Hs_e p.2.1
  have hσ : ‖stereoE e (p.2.1 : V)‖ = 1 := norm_stereo he hx
  have hσσ : ⟪stereoE e (p.2.1 : V), stereoE e (p.2.1 : V)⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hσ]; norm_num
  have hσd : ∀ c : Mc e, ⟪stereoE e (p.2.1 : V), dst e (p.2.1 : V) (c.2.1 : V)⟫ = 0 := fun c =>
    inner_stereo_dst he hx _ (inner_Hs_e c.2.1)
  have hdσ : ∀ c : Mc e, ⟪dst e (p.2.1 : V) (c.2.1 : V), stereoE e (p.2.1 : V)⟫ = 0 := fun c => by
    rw [real_inner_comm]; exact hσd c
  have hdd : ⟪dst e (p.2.1 : V) (a.2.1 : V), dst e (p.2.1 : V) (b.2.1 : V)⟫ = ψR p.2.1 * ⟪a.2.1, b.2.1⟫ := by
    rw [inner_dst_dst he hx _ _ (inner_Hs_e a.2.1) (inner_Hs_e b.2.1), Submodule.coe_inner]
    simp only [ψR, Submodule.coe_norm]
  have h33 : ⟪D3 e p a, D3 e p b⟫ = ψR p.2.2 * ⟪a.2.2, b.2.2⟫ := by
    simp only [D3]
    rw [inner_dst_dst norm_one (inner_ι3_one _) _ _ (inner_ι3_one _) (inner_ι3_one _),
      inner_ι3]
    simp only [ψR, norm_ι3]
  have hrt : rt ((Φh δ s₀ e p).1) = R (reparam s₀ p.1) := hRt _ (reparam_pos hs p.1) _ hσ
  have hnorm : ‖(Φh δ s₀ e p).1‖ ^ 2 = Fh δ s₀ p.1 ^ 2 := by
    show ‖Fh δ s₀ p.1 • stereoE e (p.2.1 : V)‖ ^ 2 = _
    rw [norm_smul, hσ, mul_one, Real.norm_eq_abs, sq_abs]
  rw [hrt, hnorm, h33]
  have hdF : deriv (Fh δ s₀) p.1 =
      Real.exp (-(Fh δ s₀ p.1) ^ 2 / (2 * δ ^ 2)) * deriv (reparam s₀) p.1 := by
    rw [(hasDerivAt_Fh p.1).deriv, (hasDerivAt_reparam p.1).deriv]
  have hkey : Real.exp (-(Fh δ s₀ p.1) ^ 2 / (2 * δ ^ 2)) ^ 2 *
      (1 + Fh δ s₀ p.1 ^ 2 * ψδ δ (Fh δ s₀ p.1 ^ 2)) = 1 := by
    rw [mul_ψδ hδ, show (1 : ℝ) + (Real.exp (Fh δ s₀ p.1 ^ 2 / δ ^ 2) - 1) =
      Real.exp (Fh δ s₀ p.1 ^ 2 / δ ^ 2) by ring, sq, ← Real.exp_add, ← Real.exp_add]
    rw [show -(Fh δ s₀ p.1) ^ 2 / (2 * δ ^ 2) + -(Fh δ s₀ p.1) ^ 2 / (2 * δ ^ 2) +
      Fh δ s₀ p.1 ^ 2 / δ ^ 2 = 0 by field_simp; ring, Real.exp_zero]
  have e1 : (Φh δ s₀ e p).1 = Fh δ s₀ p.1 • stereoE e (p.2.1 : V) := rfl
  rw [e1, Gh_apply δ s₀ e R p a b]
  have h1a := hσd a
  have h1b := hσd b
  have h2a := hdσ a
  have h2b := hdσ b
  simp only [D1, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hσσ, h1a, h1b, h2a, h2b, hdd, hdF]
  linear_combination (-(deriv (reparam s₀) p.1 ^ 2 * (a.1 * b.1))) * hkey

theorem mfderiv_Φh_injective (hδ : δ ≠ 0) {rt : V → ℝ} (hs : 0 < s₀) (he : ‖e‖ = 1)
    (hR : ∀ t, 0 < t → R t ≠ 0) (hRt : ∀ t, 0 < t → ∀ y : V, ‖y‖ = 1 → rt (Fprof δ t • y) = R t)
    (p : Mc e) : Injective (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne
  have h1 := Gh_pos (δ := δ) (e := e) hs hR p hne
  have h2 := hpull_Φh (R := R) (rt := rt) hδ hs he hRt p a a
  have h3 : northMetric δ rt (Φh δ s₀ e p) (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p a)
      (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p a) = 0 := by
    rw [ha]; simp
  linarith

theorem finrank_Mc (he : e ≠ 0) : Module.finrank ℝ (Mc e) = Module.finrank ℝ (V × E3) := by
  have hpos : 0 < Module.finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨e, he⟩
  haveI : Fact (Module.finrank ℝ V = (Module.finrank ℝ V - 1) + 1) := ⟨by omega⟩
  have hH : Module.finrank ℝ (Hs e) = Module.finrank ℝ V - 1 :=
    Submodule.finrank_orthogonal_span_singleton he
  simp only [Mc, Module.finrank_prod, hH, Module.finrank_self, finrank_euclideanSpace_fin]
  omega

theorem isInvertible_mfderiv_Φh (hδ : δ ≠ 0) {rt : V → ℝ} (hs : 0 < s₀) (he : ‖e‖ = 1)
    (hR : ∀ t, 0 < t → R t ≠ 0) (hRt : ∀ t, 0 < t → ∀ y : V, ‖y‖ = 1 → rt (Fprof δ t • y) = R t)
    (p : Mc e) : (mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p).IsInvertible := by
  have he0 : e ≠ 0 := by intro h; rw [h, norm_zero] at he; exact zero_ne_one he
  let f : Mc e →L[ℝ] V × E3 := mfderiv 𝓘(ℝ, Mc e) (IN V) (Φh δ s₀ e) p
  have hinj : Injective f := mfderiv_Φh_injective (R := R) (rt := rt) hδ hs he hR hRt p
  let eq := (LinearMap.linearEquivOfInjective f.toLinearMap hinj (finrank_Mc he0)).toContinuousLinearEquiv
  exact ⟨eq, by ext v <;> rfl⟩

end Chart

end

end ExoticSpheres8And10
