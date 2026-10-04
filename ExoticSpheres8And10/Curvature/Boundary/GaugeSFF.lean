/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.Values

/-! # §4.4: the southern boundary second fundamental form through the gauge

Where `χ = 0` near `y`, the gauge `τ` is a local isometry from the product-connection quotient
`g_0 = SQ.gB (GsW β0 r)` to [GG]'s southern quotient `g_A = SQ.gB (GsH A_S r)` (`gB_τ`). It also
preserves `|y|²`. Hence (**`sff_τ`**) the boundary second fundamental forms correspond:
`B^{g_0}_y(c, c) = B^{g_A}_{τy}(dτ c, dτ c)`.

* `contDiffAt_σh`: `σ̂ = τ⁻¹` is smooth off `0`;
* `isInvertible_fderiv_τ`: `dτ` is invertible off `0`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real Module

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section GaugeSFF

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

namespace PolarData

theorem contDiffAt_σh {y : Vs e} (hy : y ≠ 0) : ContDiffAt ℝ ∞ D.σh y := by
  have h1 : ContMDiffAt 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e →L[ℝ] Vs e) ∞
      (fun y' => ((D.ρVs (D.θS y') : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e)) y :=
    (D.contMDiff_ρVs (D.θS y)).comp y (D.contMDiffAt_θS hy)
  exact (contMDiffAt_iff_contDiffAt.1 h1).clm_apply contDiffAt_id

theorem τ_ne_zero {y : Vs e} (hy : y ≠ 0) : D.τ y ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_τ]; exact norm_ne_zero_iff.2 hy

theorem isInvertible_fderiv_τ {y : Vs e} (hy : y ≠ 0) : (fderiv ℝ D.τ y).IsInvertible := by
  have hτ := (D.contDiffAt_τ hy).differentiableAt (by simp)
  have hσ := (D.contDiffAt_σh (D.τ_ne_zero hy)).differentiableAt (by simp)
  have hcomp : D.σh ∘ D.τ = id := funext D.σh_τ
  have hl : (fderiv ℝ D.σh (D.τ y)).comp (fderiv ℝ D.τ y) = ContinuousLinearMap.id ℝ (Vs e) := by
    rw [← fderiv_comp y hσ hτ, hcomp, fderiv_id]
  have hinj : Injective (fderiv ℝ D.τ y) := fun a b hab => by
    have := congrArg (fderiv ℝ D.σh (D.τ y)) hab
    simpa only [← ContinuousLinearMap.comp_apply, hl, ContinuousLinearMap.id_apply] using this
  exact ⟨(LinearEquiv.ofInjectiveEndo (fderiv ℝ D.τ y).toLinearMap hinj).toContinuousLinearEquiv,
    by ext; rfl⟩

/-- **The southern boundary second fundamental form, through the gauge.** -/
theorem sff_τ {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) {r : Vs e → ℝ} (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ y, r y ≠ 0) (hrρ : ∀ q y, r (D.ρVs q y) = r y) {y : Vs e} (hy : y ≠ 0)
    (hχ0 : ∀ᶠ y' in 𝓝 y, χt (‖y'‖ ^ 2) = 0) (c : Vs e) :
    sff (SQ.isPosDef_cmet_gB' (ρV := D.ρVs)
          (GsW_pos (w := r) β0_pos β0_nonneg hr0)).isNondegenerate
        (fun y : Vs e => ‖y‖ ^ 2) y (toTSv y c) (toTSv y c) =
      sff (SQ.isPosDef_cmet_gB' (ρV := D.ρVs) (GsH_pos (A := D.AS χt) hr0)).isNondegenerate
        (fun y : Vs e => ‖y‖ ^ 2) (D.τ y) (toTSv _ (fderiv ℝ D.τ y c))
        (toTSv _ (fderiv ℝ D.τ y c)) := by
  have hG0 := GsW_pos (w := r) (β := β0) β0_pos β0_nonneg hr0
  have hGA := GsH_pos (A := D.AS χt) hr0
  have hne : ∀ᶠ y' in 𝓝 y, y' ≠ 0 := isOpen_ne.mem_nhds hy
  have hsm0 : ContDiff ℝ ∞ (SQ.gB D.ρVs (GsW β0 r)) :=
    SQ.contDiff_gB D.ρVs hG0 (contDiff_GsW contDiff_β0 hr)
  have hsmA : ContDiff ℝ ∞ (SQ.gB D.ρVs (GsH (D.AS χt) r)) :=
    SQ.contDiff_gB D.ρVs hGA (contDiff_GsH (D.contDiff_AS hχ) hr)
  have hhτ : (fun y : Vs e => ‖y‖ ^ 2) ∘ D.τ = fun y : Vs e => ‖y‖ ^ 2 :=
    funext fun y' => by simp only [Function.comp_apply, norm_τ]
  have hdτ : ∀ᶠ y' in 𝓝 (D.τ y), fderiv ℝ (fun y : Vs e => ‖y‖ ^ 2) y' ≠ 0 :=
    Filter.Eventually.mono (isOpen_ne.mem_nhds (D.τ_ne_zero hy)) fun y' hy' => fderiv_normSq_ne hy'
  have hν := contDiffAt_unitNormal_cmet (SQ.isPosDef_cmet_gB' hGA) hsmA (contDiff_norm_sq ℝ)
    hdτ.self_of_nhds
  have h := sff_pullback_loc (f := D.τ) (I := 𝓘(ℝ, Vs e)) (I' := 𝓘(ℝ, Vs e))
    (gM := cmet (SQ.gB D.ρVs (GsW β0 r))) (gN := cmet (SQ.gB D.ρVs (GsH (D.AS χt) r)))
    (x := y)
    (hne.mono fun y' hy' => (D.contDiffAt_τ hy').contMDiffAt)
    (hne.mono fun y' hy' => by rw [mfderiv_eq_fderiv]; exact D.isInvertible_fderiv_τ hy')
    ((hne.and hχ0).mono fun y' hy' u v => by
      rw [mfderiv_eq_fderiv]
      exact (D.gB_τ hχ hr0 hrρ hy'.1 hy'.2 u v).symm)
    (SQ.isSymm_cmet_gB' (GsW_symm β0_symm)) (SQ.isPosDef_cmet_gB' hG0).isNondegenerate
    (isMDiffMetric_cmet (hsm0.of_le (by simp)))
    (SQ.isSymm_cmet_gB' GsH_symm) (SQ.isPosDef_cmet_gB' hGA).isNondegenerate
    (isMDiffMetric_cmet (hsmA.of_le (by simp)))
    (h := fun y : Vs e => ‖y‖ ^ 2) (contDiff_norm_sq ℝ).contMDiff
    ((cmdiffAt_toTS hν).mdifferentiableAt (by simp))
    (toTSv y c) (toTSv y c)
  rw [hhτ, mfderiv_eq_fderiv] at h
  exact h

end PolarData

end GaugeSFF

end

end ExoticSpheres8And10
