/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Northern.Upstairs

/-! # §4: positive curvature upstairs at the centre of the northern piece

At the centre `Y = 0` the polar chart degenerates. Use instead the chart
`Φc(Y, z) = (Y, σ3 z) : V × ℝ³ → V × S³`, in which [GG]'s northern metric is

  `Gw = |dY|² + ψ(|Y|²)⟪Y, dY⟫² + r̃(Y)² HR(z)`   (`hpull_Φc`).

[GG]'s `r̃` is constant, `= r₀`, near `Y = 0`. So near the centre `Gw` is the product metric `G0`,
whose Christoffel symbols are explicit:

  `Γ0((v₁,v₂),(w₁,w₂)) = (c(Y; v₁, w₁) Y, ΓR(v₂, w₂))`,
  `c = (ψ'⟪Y,v⟫⟪Y,w⟫ + ψ⟪v,w⟫)/(1 + ψ|Y|²)`   (`G0_Γ0`, the Koszul identity).

At `(0, z)` this gives `Rm((a,0),(c,0),(c,0),(a,0)) = ψ(0)(|a|²|c|² − ⟪a,c⟫²)` (`riemannTensorAt_G0_centre`),
so `K = ψ(0) = δ⁻² > 0` on the planes `V × 0`. These are the horizontal planes at `(0, 1)`.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Metric

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `b ⊕ w(Y)² HR`, `b = |dY|² + ψ(|Y|²)⟪Y, dY⟫²`. -/
def Gw (δ : ℝ) (w : V → ℝ) (p : V × E3) : (V × E3) →L[ℝ] (V × E3) →L[ℝ] ℝ :=
  bil (ipL V) (ContinuousLinearMap.fst ℝ V E3) +
    ψδ δ (‖p.1‖ ^ 2) • bil mulL ((innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ V E3)) +
    (w p.1 ^ 2) • bil (HR p.2) (ContinuousLinearMap.snd ℝ V E3)

theorem Gw_apply (δ : ℝ) (w : V → ℝ) (p a b : V × E3) :
    Gw δ w p a b = ⟪a.1, b.1⟫ + ψδ δ (‖p.1‖ ^ 2) * (⟪p.1, a.1⟫ * ⟪p.1, b.1⟫) +
      w p.1 ^ 2 * (ψR p.2 * ⟪a.2, b.2⟫) := by
  simp only [Gw, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, bil_apply,
    ipL_apply, mulL_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul, HR_apply]

variable {δ : ℝ} {w : V → ℝ}

theorem contDiff_Gw (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (Gw δ w) := by
  rw [contDiff_clm_apply_iff]; intro a
  rw [contDiff_clm_apply_iff]; intro b
  have e : (fun p => Gw δ w p a b) = fun p : V × E3 => ⟪a.1, b.1⟫ +
      ψδ δ (‖p.1‖ ^ 2) * (⟪p.1, a.1⟫ * ⟪p.1, b.1⟫) + w p.1 ^ 2 * (ψR p.2 * ⟪a.2, b.2⟫) :=
    funext fun p => Gw_apply δ w p a b
  rw [e]
  have hψ : ContDiff ℝ ∞ fun p : V × E3 => ψδ δ (‖p.1‖ ^ 2) :=
    (contDiff_ψδ δ).comp ((contDiff_norm_sq ℝ).comp contDiff_fst)
  have hψR : ContDiff ℝ ∞ fun p : V × E3 => ψR p.2 := by
    have : ContDiff ℝ ∞ fun x : E3 => ψR x := by
      unfold ψR
      exact ((contDiff_const.add ((contDiff_norm_sq ℝ).div_const 4)).pow 2).inv
        fun x => by positivity
    exact this.comp contDiff_snd
  exact (contDiff_const.add (hψ.mul ((contDiff_fst.inner ℝ contDiff_const).mul
    (contDiff_fst.inner ℝ contDiff_const)))).add (((hw.comp contDiff_fst).pow 2).mul
      (hψR.mul contDiff_const))

theorem isSymm_Gw : IsSymm (cmet (Gw δ w)) := fun p a b => by
  show Gw δ w p (fromTS a) (fromTS b) = Gw δ w p (fromTS b) (fromTS a)
  rw [Gw_apply, Gw_apply, real_inner_comm (fromTS a).1 (fromTS b).1,
    real_inner_comm (fromTS a).2 (fromTS b).2]
  ring

theorem Gw_pos (hw : ∀ Y, w Y ≠ 0) (p : V × E3) {a : V × E3} (ha : a ≠ 0) :
    0 < Gw δ w p a a := by
  rw [Gw_apply]
  have hψ := ψδ_nonneg δ (‖p.1‖ ^ 2)
  have hw2 : 0 < w p.1 ^ 2 := by have := hw p.1; positivity
  have h2 : 0 ≤ ψδ δ (‖p.1‖ ^ 2) * (⟪p.1, a.1⟫ * ⟪p.1, a.1⟫) :=
    mul_nonneg hψ (mul_self_nonneg _)
  by_cases h1 : a.1 = 0
  · have h3 : a.2 ≠ 0 := fun h => ha (Prod.ext h1 h)
    have : 0 < w p.1 ^ 2 * (ψR p.2 * ⟪a.2, a.2⟫) :=
      mul_pos hw2 (mul_pos (ψR_pos _) (real_inner_self_pos.2 h3))
    rw [h1]
    simp only [inner_zero_left, inner_zero_right, mul_zero, zero_add]
    exact this
  · have := real_inner_self_pos.2 h1
    have : 0 ≤ w p.1 ^ 2 * (ψR p.2 * ⟪a.2, a.2⟫) :=
      mul_nonneg hw2.le (mul_nonneg (ψR_pos _).le real_inner_self_nonneg)
    linarith

theorem isPosDef_Gw (hw : ∀ Y, w Y ≠ 0) : IsPosDef (cmet (Gw δ w)) :=
  fun p v hv => Gw_pos hw p (a := fromTS v) hv

/-! ### The chart `Φc(Y, z) = (Y, σ3 z)` -/

/-- **The centre chart.** -/
def Φc (p : V × E3) : V × S3 := (p.1, σ3 p.2)

theorem contMDiff_Φc : ContMDiff 𝓘(ℝ, V × E3) (IN V) ∞ (Φc (V := V)) :=
  (contDiff_fst.contMDiff).prodMk (contMDiff_σ3.comp contDiff_snd.contMDiff)

/-- **`Gw` is the pullback of [GG]'s northern metric along `Φc`.** -/
theorem hpull_Φc (p : V × E3) (a b : TangentSpace 𝓘(ℝ, V × E3) p) :
    Gw δ w p a b = northMetric δ w (Φc p) (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p a)
      (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p b) := by
  have hΦ : MDifferentiableAt 𝓘(ℝ, V × E3) (IN V) (Φc (V := V)) p :=
    (contMDiff_Φc p).mdifferentiableAt (by simp)
  have hY : ∀ c : TangentSpace 𝓘(ℝ, V × E3) p, mvfderiv (IN V) fY (Φc p)
      (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p c) = c.1 := fun c => by
    rw [← mvfderiv_comp' ((contMDiff_fY _).mdifferentiableAt (by simp)) hΦ]
    show mvfderiv 𝓘(ℝ, V × E3) (fun p : V × E3 => p.1) p c = _
    rw [mvfderiv_vs]
    have : fderiv ℝ (fun p : V × E3 => p.1) p = ContinuousLinearMap.fst ℝ V E3 := fderiv_fst
    rw [this]; rfl
  have hU : ∀ c : TangentSpace 𝓘(ℝ, V × E3) p, mvfderiv (IN V) fU (Φc p)
      (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p c) = dst 1 (ι3 p.2) (ι3 c.2) := fun c => by
    rw [← mvfderiv_comp' ((contMDiff_fU _).mdifferentiableAt (by simp)) hΦ]
    show mvfderiv 𝓘(ℝ, V × E3) (fun p : V × E3 => ((σ3 p.2 : S3) : Quaternion ℝ)) p c = _
    rw [mvfderiv_vs]
    have h : HasFDerivAt (fun p : V × E3 => ((σ3 p.2 : S3) : Quaternion ℝ))
        (((dstL 1 (ι3 p.2)).comp ι3).comp (ContinuousLinearMap.snd ℝ V E3)) p :=
      (hasFDerivAt_val_σ3 p.2).comp p hasFDerivAt_snd
    rw [h.fderiv]; rfl
  have hY' : ∀ c : TangentSpace 𝓘(ℝ, V × E3) p,
      (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p c).1 = c.1 :=
    fun c => (mvfderiv_fY _ _).symm.trans (hY c)
  rw [northMetric_apply, hY, hY, hU, hU, mvfderiv_fQ, mvfderiv_fQ, hY', hY',
    inner_dst_dst norm_one (inner_ι3_one _) _ _ (inner_ι3_one _) (inner_ι3_one _), inner_ι3,
    Gw_apply δ w p a b]
  have hn : ψR (ι3 p.2) = ψR p.2 := by simp only [ψR, norm_ι3]
  rw [hn]
  rfl

theorem isInvertible_mfderiv_Φc (hw : ∀ Y, w Y ≠ 0) (p : V × E3) :
    (mfderiv 𝓘(ℝ, V × E3) (IN V) (Φc (V := V)) p).IsInvertible := by
  let f : (V × E3) →L[ℝ] (V × E3) := mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p
  have hinj : Injective f := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    by_contra hne
    have h1 := Gw_pos (δ := 1) hw p hne
    have h2 := hpull_Φc (δ := 1) (w := w) p a a
    have h3 : northMetric 1 w (Φc p) (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p a)
        (mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p a) = 0 := by
      have : mfderiv 𝓘(ℝ, V × E3) (IN V) Φc p a = 0 := ha
      rw [this]; simp
    linarith
  let eq := (LinearEquiv.ofInjectiveEndo f.toLinearMap hinj).toContinuousLinearEquiv
  exact ⟨eq, by ext v <;> rfl⟩

/-! ### The product metric near the centre and its Christoffel symbols -/

/-- `c(Y; v, w) = (ψ'⟪Y,v⟫⟪Y,w⟫ + ψ⟪v,w⟫)/(1 + ψ|Y|²)`. -/
def cb (δ : ℝ) (Y v w : V) : ℝ :=
  (deriv (ψδ δ) (‖Y‖ ^ 2) * (⟪Y, v⟫ * ⟪Y, w⟫) + ψδ δ (‖Y‖ ^ 2) * ⟪v, w⟫) /
    (1 + ψδ δ (‖Y‖ ^ 2) * ‖Y‖ ^ 2)

/-- The Christoffel form of `G0 = Gw δ (const r₀)`. -/
def Γ0 (δ : ℝ) (p v w : V × E3) : V × E3 := (cb δ p.1 v.1 w.1 • p.1, ΓR p.2 v.2 w.2)

theorem fderiv_Gw_const_apply (r0 : ℝ) (p v a b : V × E3) :
    fderiv ℝ (Gw δ (fun _ => r0)) p v a b =
      deriv (ψδ δ) (‖p.1‖ ^ 2) * (2 * ⟪p.1, v.1⟫) * (⟪p.1, a.1⟫ * ⟪p.1, b.1⟫) +
        ψδ δ (‖p.1‖ ^ 2) * (⟪v.1, a.1⟫ * ⟪p.1, b.1⟫ + ⟪p.1, a.1⟫ * ⟪v.1, b.1⟫) +
        r0 ^ 2 * fderiv ℝ HR p.2 v.2 a.2 b.2 := by
  have hGd : DifferentiableAt ℝ (Gw (V := V) δ (fun _ : V => r0)) p :=
    ((contDiff_Gw (δ := δ) (w := fun _ : V => r0) contDiff_const).differentiable (by simp)) p
  have hpair := fderiv_pair (A := fun _ => a) (B := fun _ => b) hGd (differentiableAt_const a)
    (differentiableAt_const b) v
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at hpair
  rw [← hpair]
  have e : (fun y => Gw δ (fun _ : V => r0) y a b) = fun y : V × E3 => ⟪a.1, b.1⟫ +
      ψδ δ (‖y.1‖ ^ 2) * (⟪y.1, a.1⟫ * ⟪y.1, b.1⟫) + r0 ^ 2 * HR y.2 a.2 b.2 := by
    funext y; rw [Gw_apply, HR_apply]
  rw [e]
  have hfst : HasFDerivAt (fun y : V × E3 => y.1) (ContinuousLinearMap.fst ℝ V E3) p :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun y : V × E3 => y.2) (ContinuousLinearMap.snd ℝ V E3) p :=
    hasFDerivAt_snd
  have hq : HasFDerivAt (fun y : V × E3 => ‖y.1‖ ^ 2)
      ((2 • innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ V E3)) p :=
    (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt.comp p hfst
  have hψd : HasDerivAt (ψδ δ) (deriv (ψδ δ) (‖p.1‖ ^ 2)) (‖p.1‖ ^ 2) :=
    (((contDiff_ψδ δ).differentiable (by simp)) _).hasDerivAt
  have hψ := hψd.comp_hasFDerivAt p hq
  have hia : HasFDerivAt (fun y : V × E3 => ⟪y.1, a.1⟫)
      ((innerSL ℝ a.1).comp (ContinuousLinearMap.fst ℝ V E3)) p := by
    have := ((innerSL ℝ a.1).hasFDerivAt (x := p.1)).comp p hfst
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp [real_inner_comm]
  have hib : HasFDerivAt (fun y : V × E3 => ⟪y.1, b.1⟫)
      ((innerSL ℝ b.1).comp (ContinuousLinearMap.fst ℝ V E3)) p := by
    have := ((innerSL ℝ b.1).hasFDerivAt (x := p.1)).comp p hfst
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp [real_inner_comm]
  have hH : HasFDerivAt HR (fderiv ℝ HR p.2) p.2 :=
    ((contDiff_HR.differentiable (by simp)) p.2).hasFDerivAt
  have t2 : HasFDerivAt (fun y : V × E3 => HR y.2 a.2 b.2) _ p :=
    ((hH.comp p hsnd).clm_apply (hasFDerivAt_const a.2 p)).clm_apply (hasFDerivAt_const b.2 p)
  have h : HasFDerivAt (fun y : V × E3 => ⟪a.1, b.1⟫ + ψδ δ (‖y.1‖ ^ 2) * (⟪y.1, a.1⟫ * ⟪y.1, b.1⟫)
      + r0 ^ 2 * HR y.2 a.2 b.2) _ p :=
    ((hasFDerivAt_const ⟪a.1, b.1⟫ p).add (hψ.mul (hia.mul hib))).add (t2.const_mul (r0 ^ 2))
  rw [h.fderiv]
  simp [two_smul, real_inner_comm]
  ring

/-- **The Koszul identity for the product metric `G0`.** -/
theorem G0_Γ0 (r0 : ℝ) (p v w z : V × E3) :
    Gw δ (fun _ => r0) p (Γ0 δ p v w) z = kz (Gw δ (fun _ => r0)) p v w z := by
  rw [kz, fderiv_Gw_const_apply, fderiv_Gw_const_apply, fderiv_Gw_const_apply, Gw_apply]
  simp only [Γ0]
  have hHR := HR_ΓR p.2 v.2 w.2 z.2
  rw [kz, HR_apply] at hHR
  rw [hHR]
  have hD : 0 < 1 + ψδ δ (‖p.1‖ ^ 2) * ‖p.1‖ ^ 2 := by
    have := ψδ_nonneg δ (‖p.1‖ ^ 2); positivity
  simp only [real_inner_smul_left, real_inner_smul_right, cb, real_inner_self_eq_norm_sq,
    real_inner_comm v.1 w.1, real_inner_comm v.1 z.1, real_inner_comm w.1 z.1,
    real_inner_comm p.1 z.1]
  have hinv : (1 + ‖p.1‖ ^ 2 * ψδ δ (‖p.1‖ ^ 2)) * (1 + ‖p.1‖ ^ 2 * ψδ δ (‖p.1‖ ^ 2))⁻¹ = 1 :=
    mul_inv_cancel₀ (by nlinarith)
  linear_combination (deriv (ψδ δ) (‖p.1‖ ^ 2) * ⟪p.1, v.1⟫ * ⟪p.1, w.1⟫ * ⟪p.1, z.1⟫ +
    ψδ δ (‖p.1‖ ^ 2) * ⟪v.1, w.1⟫ * ⟪p.1, z.1⟫) * hinv

end Metric

section Centre

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {δ : ℝ}

theorem contDiff_cb (u w : V) : ContDiff ℝ ∞ fun Y : V => cb δ Y u w := by
  unfold cb
  have hq : ContDiff ℝ ∞ fun Y : V => ‖Y‖ ^ 2 := contDiff_norm_sq ℝ
  have hψ := (contDiff_ψδ δ).comp hq
  have hψ' := (contDiff_deriv' (contDiff_ψδ δ)).comp hq
  refine ContDiff.div ((hψ'.mul ((contDiff_id.inner ℝ contDiff_const).mul
    (contDiff_id.inner ℝ contDiff_const))).add (hψ.mul contDiff_const))
    (contDiff_const.add (hψ.mul hq)) fun Y => ?_
  have := ψδ_nonneg δ (‖Y‖ ^ 2)
  positivity

theorem contDiffAt_Γ0 (u w x : V × E3) : ContDiffAt ℝ 1 (fun y => Γ0 δ y u w) x := by
  have h1 : ContDiff ℝ ∞ fun y : V × E3 => cb δ y.1 u.1 w.1 • y.1 :=
    ((contDiff_cb (δ := δ) u.1 w.1).comp contDiff_fst).smul contDiff_fst
  have h2 : ContDiff ℝ ∞ fun y : V × E3 => ΓR y.2 u.2 w.2 :=
    ((contDiff_ΓR.comp contDiff_snd).clm_apply contDiff_const).clm_apply contDiff_const
  exact ((h1.prodMk h2).contDiffAt).of_le (by exact_mod_cast le_top)

theorem cb_zero (b c : V) : cb δ 0 b c = ψδ δ 0 * ⟪b, c⟫ := by
  simp [cb]

theorem ψδ_zero (hδ : δ ≠ 0) : ψδ δ 0 = 1 / δ ^ 2 := by
  simp [ψδ, one_div]

theorem fderiv_Γ0_centre (z0 : E3) (a b c : V) :
    fderiv ℝ (fun y => Γ0 δ y ((b, 0) : V × E3) ((c, 0) : V × E3)) ((0 : V), z0)
      ((a, 0) : V × E3) = ((cb δ 0 b c • a, 0) : V × E3) := by
  have e : (fun y => Γ0 δ y ((b, 0) : V × E3) ((c, 0) : V × E3)) =
      fun y : V × E3 => (cb δ y.1 b c • y.1, (0 : E3)) := funext fun y => by simp [Γ0]
  rw [e]
  have hcb : DifferentiableAt ℝ (fun y : V × E3 => cb δ y.1 b c) ((0 : V), z0) :=
    (((contDiff_cb (δ := δ) b c).comp contDiff_fst).differentiable (by simp)) _
  have h1 : HasFDerivAt (fun y : V × E3 => cb δ y.1 b c • y.1) _ ((0 : V), z0) :=
    hcb.hasFDerivAt.smul hasFDerivAt_fst
  have h : HasFDerivAt (fun y : V × E3 => (cb δ y.1 b c • y.1, (0 : E3))) _ ((0 : V), z0) :=
    h1.prodMk (hasFDerivAt_const (0 : E3) _)
  rw [h.fderiv]
  simp

theorem contDiff2_G0 (r0 : ℝ) : ContDiff ℝ 2 (Gw (V := V) δ (fun _ => r0)) :=
  (contDiff_Gw contDiff_const).of_le (WithTop.coe_le_coe.mpr le_top)

/-- **The curvature of the product metric at the centre**, on planes tangent to `V`:
`Rm((a,0),(c,0),(c,0),(a,0)) = ψ(0)(|a|²|c|² − ⟪a,c⟫²)`. -/
theorem riemannTensorAt_G0_centre {r0 : ℝ} (hr0 : r0 ≠ 0) (z0 : E3) (a c : V) :
    riemannTensorAt (isSymm_Gw (δ := δ) (w := fun _ : V => r0))
      (isPosDef_Gw (δ := δ) (w := fun _ : V => r0) fun _ => hr0).isNondegenerate
      (isContMDiffMetricSection_cmet (contDiff2_G0 (δ := δ) r0)) ((0 : V), z0)
      (toTSv _ ((a, 0) : V × E3)) (toTSv _ ((c, 0) : V × E3)) (toTSv _ ((c, 0) : V × E3))
      (toTSv _ ((a, 0) : V × E3)) = ψδ δ 0 * (‖a‖ ^ 2 * ‖c‖ ^ 2 - ⟪a, c⟫ ^ 2) := by
  refine (riemannTensorAt_cmet (G := Gw δ (fun _ : V => r0)) isSymm_Gw
    (isPosDef_Gw (δ := δ) (w := fun _ : V => r0) fun _ => hr0).isNondegenerate
    (contDiff2_G0 (δ := δ) r0) (G0_Γ0 r0) ((0 : V), z0) ((a, 0) : V × E3) ((c, 0) : V × E3)
    ((c, 0) : V × E3) ((a, 0) : V × E3) (contDiffAt_Γ0 _ _ _) (contDiffAt_Γ0 _ _ _)).trans ?_
  rw [fderiv_Γ0_centre, fderiv_Γ0_centre]
  simp only [Γ0, smul_zero, map_zero, ContinuousLinearMap.zero_apply]
  rw [Gw_apply, cb_zero, cb_zero]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero,
    inner_zero_left, inner_zero_right, mul_zero, add_zero, sub_zero, zero_add, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm a c]
  ring

variable {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}

omit [FiniteDimensional ℝ V] in
theorem KY_zero : KY ρV (0 : V) = 0 := by
  ext β; simp [KY]

theorem mfderiv_Φc_centre (b : TangentSpace 𝓘(ℝ, V × E3) ((0 : V), z30)) :
    mfderiv 𝓘(ℝ, V × E3) (IN V) (Φc (V := V)) ((0 : V), z30) b = b := by
  have h1 : MDifferentiableAt 𝓘(ℝ, V × E3) 𝓘(ℝ, V) (fun p : V × E3 => p.1) ((0 : V), z30) :=
    (((contDiff_fst : ContDiff ℝ ∞ (Prod.fst : V × E3 → V)).contMDiff) _).mdifferentiableAt
      (by simp)
  set L : V × E3 →L[ℝ] E3 := ContinuousLinearMap.snd ℝ V E3
  have hσ : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 3) σ3 (L ((0 : V), z30)) :=
    (contMDiff_σ3 _).mdifferentiableAt (by simp)
  have hL : MDifferentiableAt 𝓘(ℝ, V × E3) 𝓘(ℝ, E3) L ((0 : V), z30) := L.mdifferentiableAt
  have h2 : MDifferentiableAt 𝓘(ℝ, V × E3) (𝓡 3) (σ3 ∘ L) ((0 : V), z30) := hσ.comp _ hL
  have hc : mfderiv 𝓘(ℝ, V × E3) (𝓡 3) (σ3 ∘ L) ((0 : V), z30) =
      (mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 (L ((0 : V), z30))).comp L := by
    rw [mfderiv_comp _ hσ hL, L.hasMFDerivAt.mfderiv]
    rfl
  have hpr := mfderiv_prodMk h1 h2
  have e1 : Φc (V := V) = fun p : V × E3 => (p.1, (σ3 ∘ L) p) := rfl
  have hm : mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 (L ((0 : V), z30)) = ContinuousLinearMap.id ℝ E3 :=
    mfderiv_σ3
  rw [e1, hpr, hc, hm, mfderiv_eq_fderiv]
  have hf : fderiv ℝ (fun p : V × E3 => p.1) ((0 : V), z30) = ContinuousLinearMap.fst ℝ V E3 :=
    fderiv_fst
  rw [hf]
  rfl

/-- **Positive curvature upstairs at the centre.** If `r̃ ≡ r₀` near `0`, every plane at `(0, 1)`
that is horizontal for the star action has sectional curvature `ψ(0) = δ⁻² > 0` for [GG]'s
northern metric. -/
theorem north_centre_pos (hδ : 0 < δ) {rt : V → ℝ} (hrt : ContDiff ℝ ∞ rt)
    (hrt0 : ∀ Y, rt Y ≠ 0) {r0 : ℝ} (hr : ∀ᶠ Y in 𝓝 (0 : V), rt Y = r0) (q : V × S3)
    (hq : Φc ((0 : V), z30) = q) (u v : TangentSpace (IN V) q)
    (hu : ∀ β, northMetric δ rt q u (ιv ρV 0 β) = 0)
    (hv : ∀ β, northMetric δ rt q v (ιv ρV 0 β) = 0) (hli : LinearIndependent ℝ ![u, v]) :
    0 < sectionalCurvatureAt (isSymm_northMetric δ rt) (isPosDef_northMetric δ hrt0)
      (isContMDiffMetricSection_northMetric hrt 2) q u v := by
  subst hq
  have hr0 : r0 ≠ 0 := by rw [← hr.self_of_nhds]; exact hrt0 0
  -- horizontal vectors are tangent to `V`
  have hhor : ∀ w : TangentSpace (IN V) (Φc ((0 : V), z30)),
      (∀ β, northMetric δ rt (Φc ((0 : V), z30)) w (ιv ρV 0 β) = 0) → w.2 = 0 := by
    intro w hw
    have hβ : ∀ β : E3, rt 0 ^ 2 * ⟪w.2, β⟫ = 0 := fun β => by
      have e1 : mfderiv 𝓘(ℝ, V × E3) (IN V) Φc ((0 : V), z30) w = w := mfderiv_Φc_centre w
      have e2 : mfderiv 𝓘(ℝ, V × E3) (IN V) Φc ((0 : V), z30)
          (toTSv ((0 : V), z30) (((0 : V), β) : V × E3)) = ιv ρV 0 β := by
        rw [mfderiv_Φc_centre, ιv_apply, KY_zero]; rfl
      have h1 : Gw δ rt ((0 : V), z30) w ((0 : V), β) =
          northMetric δ rt (Φc ((0 : V), z30)) w (ιv ρV 0 β) := by
        have := hpull_Φc (δ := δ) (w := rt) ((0 : V), z30) w
          (toTSv ((0 : V), z30) (((0 : V), β) : V × E3))
        rw [e1, e2] at this; exact this
      have h1' := h1.trans (hw β)
      have h5 := Gw_apply δ rt ((0 : V), z30) w ((0 : V), β)
      rw [h5] at h1'
      simp only [inner_zero_left, inner_zero_right, mul_zero, zero_add, psiR_z30,
        one_mul] at h1'
      exact h1'
    have := hβ w.2
    rw [real_inner_self_eq_norm_sq] at this
    have hr2 : rt 0 ^ 2 ≠ 0 := pow_ne_zero 2 (hrt0 0)
    have : ‖w.2‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hr2
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  have hu2 := hhor u hu
  have hv2 := hhor v hv
  -- naturality and germ locality
  have hgw : IsContMDiffMetricSection (V × E3) 2 (cmet (Gw δ rt)) :=
    isContMDiffMetricSection_cmet ((contDiff_Gw hrt).of_le (WithTop.coe_le_coe.mpr le_top))
  have hnat := sectionalCurvatureAt_pullback (f := Φc (V := V)) (gM := cmet (Gw δ rt))
    (gN := northMetric δ rt) contMDiff_Φc (isInvertible_mfderiv_Φc hrt0)
    (fun x a b => hpull_Φc x a b) isSymm_Gw (isPosDef_Gw hrt0) hgw
    (isSymm_northMetric δ rt) (isPosDef_northMetric δ hrt0)
    (isContMDiffMetricSection_northMetric hrt 2) ((0 : V), z30) u v
  have eu : mfderiv 𝓘(ℝ, V × E3) (IN V) Φc ((0 : V), z30) u = u := mfderiv_Φc_centre u
  have ev : mfderiv 𝓘(ℝ, V × E3) (IN V) Φc ((0 : V), z30) v = v := mfderiv_Φc_centre v
  rw [eu, ev] at hnat
  have hgerm : ∀ᶠ y in 𝓝 ((0 : V), z30), cmet (Gw δ rt) y = cmet (Gw δ (fun _ => r0)) y := by
    have := (continuous_fst.tendsto ((0 : V), z30)).eventually hr
    filter_upwards [this] with y hy
    show Gw δ rt y = Gw δ (fun _ => r0) y
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    rw [Gw_apply, Gw_apply, hy]
  have hloc := sectionalCurvatureAt_congr_metric isSymm_Gw (isPosDef_Gw hrt0) hgw
    (isSymm_Gw (δ := δ) (w := fun _ : V => r0)) (isPosDef_Gw fun _ => hr0)
    (isContMDiffMetricSection_cmet (contDiff2_G0 (δ := δ) r0)) hgerm u v
  rw [← hnat, hloc]
  -- the computation at the centre
  have key : ∀ a c : V, LinearIndependent ℝ ![toTSv ((0 : V), z30) ((a, 0) : V × E3),
      toTSv ((0 : V), z30) ((c, 0) : V × E3)] →
      0 < sectionalCurvatureAt (isSymm_Gw (δ := δ) (w := fun _ : V => r0))
        (isPosDef_Gw fun _ => hr0) (isContMDiffMetricSection_cmet (contDiff2_G0 (δ := δ) r0))
        ((0 : V), z30) (toTSv ((0 : V), z30) ((a, 0) : V × E3))
        (toTSv ((0 : V), z30) ((c, 0) : V × E3)) := by
    intro a c hac
    have hgram := gramDet_pos (isSymm_Gw (δ := δ) (w := fun _ : V => r0))
      (isPosDef_Gw fun _ => hr0) hac
    rw [sectionalCurvatureAt_def, riemannTensorAt_G0_centre hr0]
    have hg : gramDet (cmet (Gw δ (fun _ : V => r0))) ((0 : V), z30)
        (toTSv ((0 : V), z30) ((a, 0) : V × E3)) (toTSv ((0 : V), z30) ((c, 0) : V × E3)) =
        ‖a‖ ^ 2 * ‖c‖ ^ 2 - ⟪a, c⟫ ^ 2 := by
      simp only [gramDet, cmet_ts, fromTS_toTSv, Gw_apply, inner_zero_left,
        inner_zero_right, mul_zero, add_zero, real_inner_self_eq_norm_sq]
    rw [hg] at hgram ⊢
    rw [mul_div_assoc, div_self hgram.ne', mul_one, ψδ_zero hδ.ne']
    positivity
  have hu' : u = toTSv ((0 : V), z30) ((u.1, 0) : V × E3) := Prod.ext rfl hu2
  have hv' : v = toTSv ((0 : V), z30) ((v.1, 0) : V × E3) := Prod.ext rfl hv2
  have hli' : LinearIndependent ℝ ![toTSv ((0 : V), z30) ((u.1, 0) : V × E3),
      toTSv ((0 : V), z30) ((v.1, 0) : V × E3)] := by
    rw [← hu', ← hv']; exact hli
  calc (0 : ℝ) < _ := key u.1 v.1 hli'
    _ = _ := by rw [← hu', ← hv']

end Centre

end

end ExoticSpheres8And10
