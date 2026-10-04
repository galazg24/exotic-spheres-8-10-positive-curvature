/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Gluing.Cut

/-! # §4: the Reiser–Wraith datum on `X`, from model data

**`PolarData.rwData`** builds an `RWData` on `X = QuotSpace D`, cut along `Σ = {f = 3/5}`.
It uses:
- the metrics `ψN^*G_N` on `U₁` and `ψ₂^*G_S` on `U₂`;
- two smooth positive definite model metrics `G_N`, `G_S` on `V`;
- positivity of `G_N` on `|Y| ≤ 4/5` and of `G_S` on `|y| ≤ 1`;
- the model boundary conditions **through the chart transition** `τ ∘ J`:
  - `hbm`: `G_S(τJY)(dτ dJ c, dτ dJ c') = G_N(Y)(c, c')`;
  - `hbs`: `B^{G_N}_Y(c,c) + B^{G_S}_{τJY}(dτ dJ c, dτ dJ c) ≥ 0`,

  for `|Y| = 4/5`, `c, c' ⊥ Y`.

Every field of `RWData` is then a chart computation: naturality of curvature and of `sff`,
reparametrisation of `f`, and the transition `mfderiv_ψ₂_eq`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

section GlueX3

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

theorem linInd_map_of_invertible {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {L : E →L[ℝ] F} (hL : L.IsInvertible) {u v : E}
    (h : LinearIndependent ℝ ![u, v]) : LinearIndependent ℝ ![L u, L v] := by
  obtain ⟨M, rfl⟩ := hL
  have hinj : LinearMap.ker (M : E →L[ℝ] F).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 M.injective
  have := h.map' _ hinj
  have e1 : ![(M : E →L[ℝ] F) u, (M : E →L[ℝ] F) v] = (M : E →L[ℝ] F).toLinearMap ∘ ![u, v] := by
    funext i; fin_cases i <;> rfl
  rw [e1]; exact this

variable {GN GS : Vs e → Vs e →L[ℝ] Vs e →L[ℝ] ℝ}

namespace PolarData


theorem posN_aux (hNs : ∀ y a b, GN y a b = GN y b a) (hNp : ∀ y a, a ≠ 0 → 0 < GN y a a)
    (hNsm : ContDiff ℝ ∞ GN)
    (hposN : ∀ Y : Vs e, ‖Y‖ ≤ 4 / 5 → ∀ a b : TangentSpace 𝓘(ℝ, Vs e) Y,
      LinearIndependent ℝ ![a, b] →
        0 < sectionalCurvatureAt (g := cmet GN) (fun y a b => hNs y a b)
          (fun y a ha => hNp y a ha) (isContMDiffMetricSection_cmet (hNsm.of_le two_le_top_nat)) Y a b)
    (x : D.U₁) (hx : D.fX x ≤ 3 / 5) (u v : TangentSpace (𝓡 (m + 1)) x)
    (huv : LinearIndependent ℝ ![u, v]) :
    0 < sectionalCurvatureAt (isSymm_pullMet hNs) (isPosDef_pullMet hNp (D.isInvertible_ψN _ _))
      (IsContMDiffMetricSection.of_le'
        (isContMDiffMetricSection_pullMet hNsm (D.ψN (1 / 5) k0_ne).contMDiff) two_le_infty_ω)
      x u v := by
  rw [sectionalCurvatureAt_pullback (gN := cmet GN) (D.ψN (1 / 5) k0_ne).contMDiff
    (D.isInvertible_ψN _ _) (fun _ _ _ => rfl) _ _ _ (fun y a b => hNs y a b) (fun y a ha => hNp y a ha)
    (isContMDiffMetricSection_cmet (hNsm.of_le two_le_top_nat))]
  refine hposN (D.ψN (1 / 5) k0_ne x) (D.norm_ψN_le x hx) _ _ ?_
  obtain ⟨M, hM⟩ := D.isInvertible_ψN (1 / 5) k0_ne x
  rw [LinearIndependent.pair_iff] at huv ⊢
  intro s t hst
  apply huv s t
  apply M.injective
  rw [map_add, map_smul, map_smul, map_zero]
  rw [← hM] at hst
  exact hst


theorem posS_aux (hSs : ∀ y a b, GS y a b = GS y b a) (hSp : ∀ y a, a ≠ 0 → 0 < GS y a a)
    (hSsm : ContDiff ℝ ∞ GS)
    (hposS : ∀ Y : Vs e, ‖Y‖ ≤ 1 → ∀ a b : TangentSpace 𝓘(ℝ, Vs e) Y,
      LinearIndependent ℝ ![a, b] →
        0 < sectionalCurvatureAt (g := cmet GS) (fun y a b => hSs y a b)
          (fun y a ha => hSp y a ha) (isContMDiffMetricSection_cmet (hSsm.of_le two_le_top_nat)) Y a b)
    (x : D.U₂) (hx : 3 / 5 ≤ D.fX x) (u v : TangentSpace (𝓡 (m + 1)) x)
    (huv : LinearIndependent ℝ ![u, v]) :
    0 < sectionalCurvatureAt (isSymm_pullMet hSs) (isPosDef_pullMet hSp D.isInvertible_ψ₂)
      (IsContMDiffMetricSection.of_le'
        (isContMDiffMetricSection_pullMet hSsm D.ψ₂.contMDiff) two_le_infty_ω)
      x u v := by
  rw [sectionalCurvatureAt_pullback (gN := cmet GS) D.ψ₂.contMDiff
    D.isInvertible_ψ₂ (fun _ _ _ => rfl) _ _ _ (fun y a b => hSs y a b) (fun y a ha => hSp y a ha)
    (isContMDiffMetricSection_cmet (hSsm.of_le two_le_top_nat))]
  refine hposS (D.ψ₂ x) (D.norm_ψ₂_le x hx) _ _ ?_
  obtain ⟨M, hM⟩ := D.isInvertible_ψ₂ x
  rw [LinearIndependent.pair_iff] at huv ⊢
  intro s t hst
  apply huv s t
  apply M.injective
  rw [map_add, map_smul, map_smul, map_zero]
  rw [← hM] at hst
  exact hst

theorem bdry_metric_aux
    (hbm : ∀ Y c c' : Vs e, ‖Y‖ = 4 / 5 → ⟪Y, c⟫ = 0 → ⟪Y, c'⟫ = 0 →
      GS (D.τ (Jk (1 / 5) Y)) (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c))
        (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c')) = GN Y c c')
    (x : QuotSpace D) (hx : D.fX x = 3 / 5) (v w : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : mvfderiv (𝓡 (m + 1)) D.fX x v = 0) (hw : mvfderiv (𝓡 (m + 1)) D.fX x w = 0) :
    pullMet (I := 𝓡 (m + 1)) GN (D.ψN (1 / 5) k0_ne) ⟨x, D.subN hx.le⟩ v w =
      pullMet (I := 𝓡 (m + 1)) GS D.ψ₂ ⟨x, D.subS hx.ge⟩ v w := by
  set x₁ : D.U₁ := ⟨x, D.subN hx.le⟩
  have hY := D.norm_ψN_eq x₁ hx
  have hψ1 : D.ψ₁ x₁ ≠ 0 := by
    intro h0; rw [ψN_apply, h0, smul_zero, norm_zero] at hY; norm_num at hY
  set Y := D.ψN (1 / 5) k0_ne x₁
  set c := mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x₁ v
  set c' := mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x₁ w
  have hc : ⟪Y, c⟫ = 0 := D.inner_ψN_of_df x₁ (v := v) hv
  have hc' : ⟪Y, c'⟫ = 0 := D.inner_ψN_of_df x₁ (v := w) hw
  have h1 := D.mfderiv_ψ₂_eq (1 / 5) k0_ne x₁ hψ1 v
  have h2 := D.mfderiv_ψ₂_eq (1 / 5) k0_ne x₁ hψ1 w
  have h3 := D.ψ₂X_eq (1 / 5) k0_ne x₁ hψ1
  have h4 := hbm Y c c' hY hc hc'
  show GN Y c c' = GS (D.ψ₂ ⟨x, D.subS hx.ge⟩)
    (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂ ⟨x, D.subS hx.ge⟩ v)
    (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂ ⟨x, D.subS hx.ge⟩ w)
  rw [← h4, h1, h2, ψ₂_eq]
  show _ = GS (D.ψ₂X x₁.1) _ _
  rw [h3]


theorem bdry_sff_aux (hNs : ∀ y a b, GN y a b = GN y b a) (hNp : ∀ y a, a ≠ 0 → 0 < GN y a a)
    (hNsm : ContDiff ℝ ∞ GN) (hSs : ∀ y a b, GS y a b = GS y b a)
    (hSp : ∀ y a, a ≠ 0 → 0 < GS y a a) (hSsm : ContDiff ℝ ∞ GS)
    (hbs : ∀ Y c : Vs e, ‖Y‖ = 4 / 5 → ⟪Y, c⟫ = 0 →
      0 ≤ sff (g := cmet GN) (IsPosDef.isNondegenerate fun y a ha => hNp y a ha)
          (fun y : Vs e => ‖y‖ ^ 2) Y (toTSv Y c) (toTSv Y c) +
        sff (g := cmet GS) (IsPosDef.isNondegenerate fun y a ha => hSp y a ha)
          (fun y : Vs e => ‖y‖ ^ 2) (D.τ (Jk (1 / 5) Y))
          (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c)))
          (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c))))
    (x : QuotSpace D) (hx : D.fX x = 3 / 5) (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : mvfderiv (𝓡 (m + 1)) D.fX x v = 0) :
    0 ≤ sff (isPosDef_pullMet (I := 𝓡 (m + 1)) hNp (D.isInvertible_ψN (1 / 5) k0_ne)).isNondegenerate
          (fun y : D.U₁ => D.fX y) ⟨x, D.subN hx.le⟩ v v +
        sff (isPosDef_pullMet (I := 𝓡 (m + 1)) hSp D.isInvertible_ψ₂).isNondegenerate
          (fun y : D.U₂ => -D.fX y) ⟨x, D.subS hx.ge⟩ v v := by
  set x₁ : D.U₁ := ⟨x, D.subN hx.le⟩
  have hY := D.norm_ψN_eq x₁ hx
  have hψ1 : D.ψ₁ x₁ ≠ 0 := by
    intro h0; rw [ψN_apply, h0, smul_zero, norm_zero] at hY; norm_num at hY
  have hY0 : D.ψN (1 / 5) k0_ne x₁ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hY; norm_num at hY
  have hpNc : IsPosDef (cmet GN) := fun y a ha => hNp y a ha
  have hpSc : IsPosDef (cmet GS) := fun y a ha => hSp y a ha
  -- the north
  have hevN : ∀ᶠ y in 𝓝 x₁, MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ)
      ((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψN (1 / 5) k0_ne) y ∧
      DifferentiableAt ℝ φN (((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψN (1 / 5) k0_ne) y) ∧
      0 < deriv φN (((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψN (1 / 5) k0_ne) y) :=
    Eventually.of_forall fun y => ⟨(((contDiff_norm_sq ℝ).contMDiff.comp
      (D.ψN (1 / 5) k0_ne).contMDiff) y).mdifferentiableAt (by simp),
      (hasDerivAt_φN (by simp only [comp_apply]; positivity)).differentiableAt,
      by rw [(hasDerivAt_φN (by simp only [comp_apply]; positivity)).deriv]
         exact dφN_pos (by simp only [comp_apply]; positivity)⟩
  have hνN : MDifferentiableAt 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e).tangent
      (fun y => (⟨y, unitNormal hpNc.isNondegenerate (fun y : Vs e => ‖y‖ ^ 2) y⟩ :
        TangentBundle 𝓘(ℝ, Vs e) (Vs e))) (D.ψN (1 / 5) k0_ne x₁) :=
    (cmdiffAt_toTS (contDiffAt_unitNormal_cmet hpNc hNsm (contDiff_norm_sq ℝ)
      (fderiv_normSq_ne hY0))).mdifferentiableAt (by simp)
  have eN : (fun y : D.U₁ => D.fX y) = φN ∘ ((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψN (1 / 5) k0_ne) :=
    D.fX_ψN
  have hN1 : sff (isPosDef_pullMet (I := 𝓡 (m + 1)) hNp
        (D.isInvertible_ψN (1 / 5) k0_ne)).isNondegenerate (fun y : D.U₁ => D.fX y) x₁ v v =
      sff (isPosDef_pullMet (I := 𝓡 (m + 1)) hNp
        (D.isInvertible_ψN (1 / 5) k0_ne)).isNondegenerate
        ((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψN (1 / 5) k0_ne) x₁ v v := by
    rw [eN, sff_comp_of_pos _ hevN]
  have hN2 := sff_pullback (gN := cmet GN)
    (gM := pullMet (I := 𝓡 (m + 1)) GN (D.ψN (1 / 5) k0_ne)) (D.ψN (1 / 5) k0_ne).contMDiff
    (D.isInvertible_ψN _ _) (fun _ _ _ => rfl) (isSymm_pullMet hNs)
    (isPosDef_pullMet (I := 𝓡 (m + 1)) hNp (D.isInvertible_ψN (1 / 5) k0_ne)).isNondegenerate
    (isMDiffMetric_of_isContMDiffMetricSection
      (IsContMDiffMetricSection.of_le' (isContMDiffMetricSection_pullMet hNsm
        (D.ψN (1 / 5) k0_ne).contMDiff) two_le_infty_ω))
    (fun y a b => hNs y a b) hpNc.isNondegenerate
    (isMDiffMetric_cmet (hNsm.of_le (by exact_mod_cast le_top))) (contDiff_norm_sq ℝ).contMDiff
    hνN v v
  -- the south
  set x₂ : D.U₂ := ⟨x, D.mem_U₂_of_ψ₁_ne x₁ hψ1⟩
  have hJ : Jk (1 / 5) (D.ψN (1 / 5) k0_ne x₁) ≠ 0 := by
    rw [Jk]
    refine smul_ne_zero ?_ hY0
    have : ‖D.ψN (1 / 5) k0_ne x₁‖ ≠ 0 := norm_ne_zero_iff.2 hY0
    positivity
  have h3 := D.ψ₂X_eq (1 / 5) k0_ne x₁ hψ1
  have hp : D.ψ₂ x₂ = D.τ (Jk (1 / 5) (D.ψN (1 / 5) k0_ne x₁)) := by
    rw [ψ₂_eq]; exact h3
  have hψ2 : D.ψ₂ x₂ ≠ 0 := by rw [hp]; exact D.τ_ne_zero hJ
  have hevS : ∀ᶠ y in 𝓝 x₂, MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ)
      ((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₂) y ∧
      DifferentiableAt ℝ φL (((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₂) y) ∧
      0 < deriv φL (((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₂) y) :=
    Eventually.of_forall fun y => ⟨(((contDiff_norm_sq ℝ).contMDiff.comp
      D.ψ₂.contMDiff) y).mdifferentiableAt (by simp),
      (hasDerivAt_φL (by simp only [comp_apply]; positivity)).differentiableAt,
      by rw [(hasDerivAt_φL (by simp only [comp_apply]; positivity)).deriv]
         have : (0 : ℝ) < ((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₂) y + 4 := by
           simp only [comp_apply]; positivity
         positivity⟩
  have hνS : MDifferentiableAt 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e).tangent
      (fun y => (⟨y, unitNormal hpSc.isNondegenerate (fun y : Vs e => ‖y‖ ^ 2) y⟩ :
        TangentBundle 𝓘(ℝ, Vs e) (Vs e))) (D.ψ₂ x₂) :=
    (cmdiffAt_toTS (contDiffAt_unitNormal_cmet hpSc hSsm (contDiff_norm_sq ℝ)
      (fderiv_normSq_ne hψ2))).mdifferentiableAt (by simp)
  have eS : (fun y : D.U₂ => -D.fX y) = φL ∘ ((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₂) := D.fX_U₂
  have hS1 : sff (isPosDef_pullMet (I := 𝓡 (m + 1)) hSp D.isInvertible_ψ₂).isNondegenerate
        (fun y : D.U₂ => -D.fX y) x₂ v v =
      sff (isPosDef_pullMet (I := 𝓡 (m + 1)) hSp D.isInvertible_ψ₂).isNondegenerate
        ((fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₂) x₂ v v := by
    rw [eS, sff_comp_of_pos _ hevS]
  have hS2 := sff_pullback (gN := cmet GS)
    (gM := pullMet (I := 𝓡 (m + 1)) GS D.ψ₂) D.ψ₂.contMDiff
    D.isInvertible_ψ₂ (fun _ _ _ => rfl) (isSymm_pullMet hSs)
    (isPosDef_pullMet (I := 𝓡 (m + 1)) hSp D.isInvertible_ψ₂).isNondegenerate
    (isMDiffMetric_of_isContMDiffMetricSection
      (IsContMDiffMetricSection.of_le' (isContMDiffMetricSection_pullMet hSsm
        D.ψ₂.contMDiff) two_le_infty_ω))
    (fun y a b => hSs y a b) hpSc.isNondegenerate
    (isMDiffMetric_cmet (hSsm.of_le (by exact_mod_cast le_top))) (contDiff_norm_sq ℝ).contMDiff
    hνS v v
  have h1 := D.mfderiv_ψ₂_eq (1 / 5) k0_ne x₁ hψ1 v
  have hc := D.inner_ψN_of_df x₁ (v := v) hv
  have hb := hbs _ _ hY hc
  have hS3 : sff hpSc.isNondegenerate (fun y : Vs e => ‖y‖ ^ 2) (D.ψ₂ x₂)
      (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂ x₂ v) (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂ x₂ v) =
      sff hpSc.isNondegenerate (fun y : Vs e => ‖y‖ ^ 2)
        (D.τ (Jk (1 / 5) (D.ψN (1 / 5) k0_ne x₁)))
        (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) (D.ψN (1 / 5) k0_ne x₁))
          (fderiv ℝ (Jk (1 / 5)) (D.ψN (1 / 5) k0_ne x₁)
            (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x₁ v))))
        (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) (D.ψN (1 / 5) k0_ne x₁))
          (fderiv ℝ (Jk (1 / 5)) (D.ψN (1 / 5) k0_ne x₁)
            (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x₁ v)))) := by
    rw [h1]
    exact congrArg (fun y => sff hpSc.isNondegenerate (fun y : Vs e => ‖y‖ ^ 2) y _ _) hp
  exact le_of_le_of_eq hb (congrArg₂ (· + ·) (hN1.trans hN2).symm
    ((hS1.trans hS2).trans hS3).symm)

/-- **The Reiser–Wraith datum on `X`.** -/
def rwData (hNs : ∀ y a b, GN y a b = GN y b a) (hNp : ∀ y a, a ≠ 0 → 0 < GN y a a)
    (hNsm : ContDiff ℝ ∞ GN) (hSs : ∀ y a b, GS y a b = GS y b a)
    (hSp : ∀ y a, a ≠ 0 → 0 < GS y a a) (hSsm : ContDiff ℝ ∞ GS)
    (hposN : ∀ Y : Vs e, ‖Y‖ ≤ 4 / 5 → ∀ a b : TangentSpace 𝓘(ℝ, Vs e) Y,
      LinearIndependent ℝ ![a, b] →
        0 < sectionalCurvatureAt (g := cmet GN) (fun y a b => hNs y a b)
          (fun y a ha => hNp y a ha) (isContMDiffMetricSection_cmet (hNsm.of_le two_le_top_nat)) Y a b)
    (hposS : ∀ Y : Vs e, ‖Y‖ ≤ 1 → ∀ a b : TangentSpace 𝓘(ℝ, Vs e) Y,
      LinearIndependent ℝ ![a, b] →
        0 < sectionalCurvatureAt (g := cmet GS) (fun y a b => hSs y a b)
          (fun y a ha => hSp y a ha) (isContMDiffMetricSection_cmet (hSsm.of_le two_le_top_nat)) Y a b)
    (hbm : ∀ Y c c' : Vs e, ‖Y‖ = 4 / 5 → ⟪Y, c⟫ = 0 → ⟪Y, c'⟫ = 0 →
      GS (D.τ (Jk (1 / 5) Y)) (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c))
        (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c')) = GN Y c c')
    (hbs : ∀ Y c : Vs e, ‖Y‖ = 4 / 5 → ⟪Y, c⟫ = 0 →
      0 ≤ sff (g := cmet GN) (IsPosDef.isNondegenerate fun y a ha => hNp y a ha)
          (fun y : Vs e => ‖y‖ ^ 2) Y (toTSv Y c) (toTSv Y c) +
        sff (g := cmet GS) (IsPosDef.isNondegenerate fun y a ha => hSp y a ha)
          (fun y : Vs e => ‖y‖ ^ 2) (D.τ (Jk (1 / 5) Y))
          (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c)))
          (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c)))) :
    RWData (𝓡 (m + 1)) (QuotSpace D) where
  f := D.fX
  c := 3 / 5
  f_smooth := D.contMDiff_fX
  UN := D.U₁
  US := D.U₂
  subN := fun _ hx => D.subN hx
  subS := fun _ hx => D.subS hx
  gN := pullMet GN (D.ψN (1 / 5) k0_ne)
  gS := pullMet GS D.ψ₂
  sN := isSymm_pullMet hNs
  sS := isSymm_pullMet hSs
  pN := isPosDef_pullMet hNp (D.isInvertible_ψN _ _)
  pS := isPosDef_pullMet hSp D.isInvertible_ψ₂
  hN := isContMDiffMetricSection_pullMet hNsm (D.ψN _ _).contMDiff
  hS := isContMDiffMetricSection_pullMet hSsm D.ψ₂.contMDiff
  regular := fun _ hx => D.regular hx
  posN := fun x hx u v huv => D.posN_aux hNs hNp hNsm hposN x hx u v huv
  posS := fun x hx u v huv => D.posS_aux hSs hSp hSsm hposS x hx u v huv
  bdry_metric := fun x hx v w hv hw => D.bdry_metric_aux hbm x hx v w hv hw
  bdry_sff := fun x hx v hv => D.bdry_sff_aux hNs hNp hNsm hSs hSp hSsm hbs x hx v hv

end PolarData

end GlueX3

end

end ExoticSpheres8And10
