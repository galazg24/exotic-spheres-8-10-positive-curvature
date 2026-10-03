/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Gluing.RWDatum

/-! # §4: [D]'s model data satisfy the boundary hypotheses of `rwData`

For [D]'s northern quotient metric `G_N = gB(ρ, δ, r̃)` and southern quotient metric
`G_S = SQ.gB(GH(A_S, r_S))`, with `ρ₀ = 1` (so `F_a = 4/5`, `λ = 5/4`, `J(Y) = (5/4)Y` on `Σ`):
* **`model_hbm`**: `G_S(τJY)(dτ dJ c, dτ dJ c') = G_N(Y)(c, c')`. Proof: `gB_τ`, then
  `bdry_model_metric`.
* **`model_hbs`**: `B^{G_N} + B^{G_S}(τJ·) ≥ 0`. Proof: `sff_τ`, then `bdry_model_sff`.

Both need `χ = 0` near `|y|² = 1`. We take a cutoff that vanishes on `[1/2, ∞)`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

section GlueX4

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

theorem sff_cmet_congr {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {G₁ G₂ : V → V →L[ℝ] V →L[ℝ] ℝ} (h : G₁ = G₂)
    (hnd₁ : IsNondegenerate (cmet G₁)) (hnd₂ : IsNondegenerate (cmet G₂)) (f : V → ℝ) (y : V)
    (v w : TangentSpace 𝓘(ℝ, V) y) : sff hnd₁ f y v w = sff hnd₂ f y v w := by
  subst h; rfl

theorem l_bdry {Y : Vs e} (hY : ‖Y‖ = 4 / 5) : (4 * (1 / 5) / ‖Y‖ ^ 2 : ℝ) = 1 + 1 ^ 2 / 4 := by
  rw [hY]; norm_num

theorem Jk_bdry {Y : Vs e} (hY : ‖Y‖ = 4 / 5) : Jk (1 / 5) Y = (1 + 1 ^ 2 / 4 : ℝ) • Y := by
  rw [Jk, l_bdry hY]

theorem ne_zero_bdry {Y : Vs e} (hY : ‖Y‖ = 4 / 5) : Y ≠ 0 := by
  intro h; rw [h, norm_zero] at hY; norm_num at hY

namespace PolarData

variable {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) (hχ0 : ∀ s, 1 / 2 ≤ s → χt s = 0)
  {ε A0 ra qs d δ : ℝ} (hε : 0 < ε)
  (hra : ra = √ε * Real.exp (ε / 2 * (A0 * (4 - 1 ^ 2) / (4 + 1 ^ 2))))
  (hw0N : ∀ Y : Vs e, rD ra d δ (4 / 5) Y ≠ 0)

include hχ hχ0 hε hra hw0N in
/-- **The boundary metrics agree** for [D]'s data, through the chart transition. -/
theorem model_hbm (Y c c' : Vs e) (hY : ‖Y‖ = 4 / 5) (hc : ⟪Y, c⟫ = 0) (hc' : ⟪Y, c'⟫ = 0) :
    SQ.gB D.ρVs (GsH (D.AS χt) (rSy ε A0)) (D.τ (Jk (1 / 5) Y))
        (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c))
        (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c')) =
      gB D.ρVs δ (rD ra d δ (4 / 5)) Y c c' := by
  have hY0 := ne_zero_bdry hY
  rw [fderiv_Jk _ hY0 hc, fderiv_Jk _ hY0 hc', l_bdry hY, Jk_bdry hY]
  have hy : (1 + 1 ^ 2 / 4 : ℝ) • Y ≠ 0 := smul_ne_zero (by norm_num) hY0
  have hn := norm_bdry (e := e) one_pos (show (4 / 5 : ℝ) = 4 * 1 / (4 + 1 ^ 2) by norm_num) hY
  have hχ1 : χt (‖(1 + 1 ^ 2 / 4 : ℝ) • Y‖ ^ 2) = 0 := hχ0 _ (by rw [hn]; norm_num)
  rw [D.gB_τ hχ (fun y => (rSy_pos hε A0 y).ne') (fun q y => rSy_ρ ε A0 q y) hy hχ1,
    bdry_model_metric D.contMDiff_ρVs hε one_pos (by norm_num) hra hw0N hY hc hc', gB_eq_SQ]

include hχ hχ0 hε hra hw0N in
/-- **`B_N + B_S ≥ 0`** for [D]'s data, through the chart transition. -/
theorem model_hbs (hδ : 0 < δ) (hqs : qs = ε * A0 * (4 / 5) / 2) (hd : d = ra * qs)
    (hη : 1 / 2 ≤ Gδ δ (4 / 5) / δ)
    (hndN : IsNondegenerate (cmet (gB D.ρVs δ (rD ra d δ (4 / 5)))))
    (hndS : IsNondegenerate (cmet (SQ.gB D.ρVs (GsH (D.AS χt) (rSy ε A0)))))
    (Y c : Vs e) (hY : ‖Y‖ = 4 / 5) (hc : ⟪Y, c⟫ = 0) :
    0 ≤ sff hndN (fun y : Vs e => ‖y‖ ^ 2) Y (toTSv Y c) (toTSv Y c) +
      sff hndS (fun y : Vs e => ‖y‖ ^ 2) (D.τ (Jk (1 / 5) Y))
        (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c)))
        (toTSv _ (fderiv ℝ D.τ (Jk (1 / 5) Y) (fderiv ℝ (Jk (1 / 5)) Y c))) := by
  have hY0 := ne_zero_bdry hY
  rw [fderiv_Jk _ hY0 hc, l_bdry hY, Jk_bdry hY]
  have hy : (1 + 1 ^ 2 / 4 : ℝ) • Y ≠ 0 := smul_ne_zero (by norm_num) hY0
  have hn := norm_bdry (e := e) one_pos (show (4 / 5 : ℝ) = 4 * 1 / (4 + 1 ^ 2) by norm_num) hY
  have hev : ∀ᶠ y' in 𝓝 ((1 + 1 ^ 2 / 4 : ℝ) • Y), χt (‖y'‖ ^ 2) = 0 := by
    have hlt : (1 / 2 : ℝ) < ‖(1 + 1 ^ 2 / 4 : ℝ) • Y‖ ^ 2 := by rw [hn]; norm_num
    filter_upwards [((continuous_norm.pow 2).tendsto _).eventually (lt_mem_nhds hlt)] with y' hy'
    exact hχ0 _ hy'.le
  have h1 := D.sff_τ hχ (contDiff_rSy ε A0) (fun y => (rSy_pos hε A0 y).ne')
    (fun q y => rSy_ρ ε A0 q y) hy hev ((1 + 1 ^ 2 / 4 : ℝ) • c)
  have h2 := bdry_model_sff (ρV := D.ρVs) D.contMDiff_ρVs hε hδ one_pos (by norm_num)
    (show (4 / 5 : ℝ) = 4 * 1 / (4 + 1 ^ 2) by norm_num) hra hqs hd hη hw0N hY hc
  have h3 := sff_cmet_congr (gB_eq_SQ D.ρVs δ (rD ra d δ (4 / 5))) hndN
    (SQ.isPosDef_cmet_gB' (ρV := D.ρVs)
      (GsW_pos (w := rD ra d δ (4 / 5)) (βN_pos δ) (βN_nonneg δ) hw0N)).isNondegenerate
    (fun y : Vs e => ‖y‖ ^ 2) Y (toTSv Y c) (toTSv Y c)
  exact le_of_le_of_eq h2 (congrArg₂ (· + ·) h3.symm h1)

end PolarData

end GlueX4

end

end ExoticSpheres8And10
