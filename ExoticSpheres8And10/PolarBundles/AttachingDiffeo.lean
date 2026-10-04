/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.Boundary.Radial
import ExoticSpheres8And10.Geometry.Boundary.DiskGluing
import ExoticSpheres8And10.PolarBundles.AttachingDisks

/-! # [GG] `lem:attaching` (1) and (3) as diffeomorphisms

`X = P_θ/S³_⋆` (`QuotSpace D`) is a model of the smooth disk gluing `𝔻(a) ∪_σ 𝔻(π − a)` with
product collars (`MB_Gluing`).
* The northern chart `ψ_N = ι₁ ∘ stG ∘ radialR` (geodesic polar coordinates, then the
  stereographic chart, then the northern copy) is a diffeomorphism from the open ball of radius
  `a + ε` in `V` onto an open subset of `X`. The southern chart `ψ_S` is the same in the
  southern copy.
* On the overlap `ψ_N = ψ_S ∘ τ`, with `τ(y) = (π − ‖y‖)σ(y/‖y‖)`. This is `κ_S` in polar
  coordinates (`κS_diskPt`).

Consequences:
* **(1)** `j_N = ψ_N ∘ Lr` on the closed disk, and `D_N = ψ_N(𝔻(a))`. So `j_N` is the
  restriction to the closed disk of a diffeomorphism between open sets. Its inverse
  `Lr⁻¹ ∘ ψ_N⁻¹` is smooth on the open set `ψ_N(B(a + ε)) ⊇ D_N`. The same holds for `S`
  (`lem_attaching_1`).
* **(3)** `X ≃ₘ Y` for every model `Y` of `𝔻(a) ∪_σ 𝔻(π − a)`, of any collar width
  (`lem_attaching_3`).
-/

namespace ExoticSpheres8And10

open Set Function Module Real Topology

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section XModel

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

namespace PolarData

variable (D : PolarData (m := m) e)

/-- `ι₁ : U_N → X` as an open partial homeomorphism (the inverse of the chart `chart₁`). -/
def ι₁PH : OpenPartialHomeomorph (UN e) (QuotSpace D) :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  (chart₁ D.κS).symm

/-- `ι₂ : U_N → X` as an open partial homeomorphism. -/
def ι₂PH : OpenPartialHomeomorph (UN e) (QuotSpace D) :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  (chart₂ D.κS).symm

/-- `stG : V → U_N` as an open partial homeomorphism (a homeomorphism). -/
def stGPH : OpenPartialHomeomorph (Vs e) (UN e) :=
  (stD (m := m) D.e_norm).symm.toHomeomorph.toOpenPartialHomeomorph

/-- The full northern chart `ι₁ ∘ stG ∘ radialR` on the ball of radius `π`. -/
def fullN : OpenPartialHomeomorph (Vs e) (QuotSpace D) :=
  radialPH.trans ((D.stGPH).trans D.ι₁PH)

/-- The full southern chart `ι₂ ∘ stG ∘ radialR` on the ball of radius `π`. -/
def fullS : OpenPartialHomeomorph (Vs e) (QuotSpace D) :=
  radialPH.trans ((D.stGPH).trans D.ι₂PH)

theorem fullN_apply (y : Vs e) : D.fullN y = ι₁ D.κS (stG D.e_norm (radialR y)) := rfl

theorem fullS_apply (y : Vs e) : D.fullS y = ι₂ D.κS (stG D.e_norm (radialR y)) := rfl

theorem fullN_source : D.fullN.source = Metric.ball 0 π := by
  have h : ((D.stGPH).trans D.ι₁PH).source = univ := by
    rw [OpenPartialHomeomorph.trans_source]
    exact eq_univ_of_forall fun _ => ⟨mem_univ _, mem_univ _⟩
  rw [fullN, OpenPartialHomeomorph.trans_source, h, preimage_univ, inter_univ]; rfl

theorem fullS_source : D.fullS.source = Metric.ball 0 π := by
  have h : ((D.stGPH).trans D.ι₂PH).source = univ := by
    rw [OpenPartialHomeomorph.trans_source]
    exact eq_univ_of_forall fun _ => ⟨mem_univ _, mem_univ _⟩
  rw [fullS, OpenPartialHomeomorph.trans_source, h, preimage_univ, inter_univ]; rfl

theorem stG_radialR {y : Vs e} (hy : ‖y‖ < π) :
    stG D.e_norm (radialR y) = D.diskPt (y : W) (inner_Vs_e _) hy :=
  Subtype.ext (Subtype.ext (stereoInv_radialR (e := e) hy))

theorem contMDiffOn_fullN :
    ContMDiffOn 𝓘(ℝ, Vs e) (𝓡 (m + 1)) ∞ D.fullN D.fullN.source := by
  intro y hy
  rw [fullN_source] at hy
  exact (D.contMDiff_ι₁'.contMDiffAt.comp y ((contMDiff_stG (m := m) D.e_norm).contMDiffAt.comp y
    (contDiffAt_radialR (mem_ball_zero_iff.1 hy)).contMDiffAt)).contMDiffWithinAt

theorem contMDiffOn_fullS :
    ContMDiffOn 𝓘(ℝ, Vs e) (𝓡 (m + 1)) ∞ D.fullS D.fullS.source := by
  intro y hy
  rw [fullS_source] at hy
  exact (D.contMDiff_ι₂'.contMDiffAt.comp y ((contMDiff_stG (m := m) D.e_norm).contMDiffAt.comp y
    (contDiffAt_radialR (mem_ball_zero_iff.1 hy)).contMDiffAt)).contMDiffWithinAt

theorem contMDiffOn_fullN_symm :
    ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞ D.fullN.symm D.fullN.target := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  intro x hx
  set y := D.fullN.symm x
  have hy : y ∈ D.fullN.source := D.fullN.map_target hx
  have hxy : D.fullN y = x := D.fullN.right_inv hx
  rw [fullN_source] at hy
  have hr : x ∈ range (ι₁ D.κS) := ⟨_, hxy⟩
  have hc : stF D.e_norm (chart₁ D.κS x) = radialR y := by
    rw [← hxy, fullN_apply, chart₁_ι₁, stF_stG]
  have hT : stF D.e_norm (chart₁ D.κS x) ∈ (radialPH (e := e)).target := by
    rw [hc]; exact (radialPH (e := e)).map_source hy
  have h1 : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞
      (fun x => radialPH.symm (stF D.e_norm (chart₁ D.κS x))) x :=
    (contDiffOn_radialPH_symm.contDiffAt (radialPH.open_target.mem_nhds hT)).contMDiffAt.comp x
      ((contMDiff_stF (m := m) D.e_norm).contMDiffAt.comp x
        (contMDiffAt_chart₁ (𝓡 (m + 1)) D.hκS D.hκSs hr))
  exact h1.contMDiffWithinAt

theorem contMDiffOn_fullS_symm :
    ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞ D.fullS.symm D.fullS.target := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  intro x hx
  set y := D.fullS.symm x
  have hy : y ∈ D.fullS.source := D.fullS.map_target hx
  have hxy : D.fullS y = x := D.fullS.right_inv hx
  rw [fullS_source] at hy
  have hr : x ∈ range (ι₂ D.κS) := ⟨_, hxy⟩
  have hc : stF D.e_norm (chart₂ D.κS x) = radialR y := by
    rw [← hxy, fullS_apply, chart₂_ι₂, stF_stG]
  have hT : stF D.e_norm (chart₂ D.κS x) ∈ (radialPH (e := e)).target := by
    rw [hc]; exact (radialPH (e := e)).map_source hy
  have h1 : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞
      (fun x => radialPH.symm (stF D.e_norm (chart₂ D.κS x))) x :=
    (contDiffOn_radialPH_symm.contDiffAt (radialPH.open_target.mem_nhds hT)).contMDiffAt.comp x
      ((contMDiff_stF (m := m) D.e_norm).contMDiffAt.comp x
        (contMDiffAt_chart₂ (𝓡 (m + 1)) D.hκS D.hκSs hr))
  exact h1.contMDiffWithinAt

/-! ### The collar map is `κ_S` in polar coordinates -/

theorem coe_ne_zero {y : Vs e} (hy0 : y ≠ 0) : (y : W) ≠ 0 := fun h => hy0 (Subtype.ext h)

theorem norm_tauX {a : ℝ} {y : Vs e} (hy0 : y ≠ 0) (hy : ‖y‖ < π) :
    ‖collarTau (V := Vs e) a (π - a) D.sigmaV y‖ = π - ‖y‖ := by
  rw [norm_collarTau hy0 (by linarith)]; ring

theorem tauX_lt {a : ℝ} {y : Vs e} (hy0 : y ≠ 0) (hy : ‖y‖ < π) :
    ‖((collarTau (V := Vs e) a (π - a) D.sigmaV y : Vs e) : W)‖ < π := by
  show ‖collarTau (V := Vs e) a (π - a) D.sigmaV y‖ < π
  rw [D.norm_tauX hy0 hy]; linarith [norm_pos_iff.2 hy0]

/-- **`κ_S(ζ(y)) = ζ(τ(y))`**: the bundle transition is the product-collar map `τ`. -/
theorem κS_diskPt_tau {a : ℝ} {y : Vs e} (hy : ‖y‖ < π) (hy0 : y ≠ 0) :
    D.κS (D.diskPt (y : W) (inner_Vs_e _) hy) =
      D.diskPt (collarTau (V := Vs e) a (π - a) D.sigmaV y : W) (inner_Vs_e _) (D.tauX_lt hy0 hy) := by
  apply Subtype.ext; apply Subtype.ext
  show ζU (D.κS (D.diskPt (y : W) (inner_Vs_e _) hy)) = expN e (collarTau (V := Vs e) a (π - a) D.sigmaV y : W)
  have hang : angS (y : W) (inner_Vs_e _) (coe_ne_zero hy0) = normS y hy0 :=
    Subtype.ext (Subtype.ext rfl)
  rw [D.κS_diskPt (inner_Vs_e _) hy (coe_ne_zero hy0), hang]
  have hy1 : (0 : ℝ) < ‖(y : W)‖ := norm_pos_iff.2 (coe_ne_zero hy0)
  rw [expN_of_sigma hy1 hy _ (D.sigmaV (normS y hy0))]
  rw [collarTau_of_ne hy0]
  show ((a + (π - a) - ‖y‖) • ((D.sigmaV (normS y hy0) : Vs e) : W)) = _
  congr 1; show a + (π - a) - ‖y‖ = π - ‖y‖; ring

theorem diskPt_zero_not_mem (hy : ‖((0 : Vs e) : W)‖ < π) :
    D.diskPt ((0 : Vs e) : W) (inner_Vs_e _) hy ∉ D.κS.source := by
  intro h
  apply h
  show ζU (D.diskPt _ _ _) = e
  rw [ζU_diskPt]; exact expN_zero

/-- **The gluing relation**: `ψ_N(y) = ψ_S(τ y)` for `0 < ‖y‖ < π`. -/
theorem fullN_eq_fullS_tau {a : ℝ} {y : Vs e} (hy : ‖y‖ < π) (hy0 : y ≠ 0) :
    D.fullN y = D.fullS (collarTau (V := Vs e) a (π - a) D.sigmaV y) := by
  rw [fullN_apply, fullS_apply, D.stG_radialR hy, D.stG_radialR (D.tauX_lt hy0 hy),
    ← D.κS_diskPt_tau hy hy0, ι₂_apply (D.diskPt_ne_e (y : W) (inner_Vs_e _) hy (coe_ne_zero hy0))]

/-- If `ψ_N(y) = ψ_S(y')`, then `y ≠ 0` and `y' = τ(y)`. -/
theorem eq_tau_of_fullN_eq_fullS {a : ℝ} {y y' : Vs e} (hy : ‖y‖ < π) (hy' : ‖y'‖ < π)
    (h : D.fullN y = D.fullS y') : y ≠ 0 ∧ y' = collarTau (V := Vs e) a (π - a) D.sigmaV y := by
  rw [fullN_apply, fullS_apply, D.stG_radialR hy, D.stG_radialR hy'] at h
  obtain ⟨hs, hκ⟩ := ι₁_eq_ι₂.1 h
  have hy0 : y ≠ 0 := by
    rintro rfl; exact D.diskPt_zero_not_mem hy hs
  refine ⟨hy0, ?_⟩
  rw [D.κS_diskPt_tau (a := a) hy hy0] at hκ
  exact (Subtype.ext (D.diskPt_injective _ _ _ _ hκ)).symm

/-- Every point of the southern copy with `0 < ‖y'‖ < π` is a northern point. -/
theorem exists_fullN_eq_fullS {a : ℝ} {y' : Vs e} (hy' : ‖y'‖ < π) (hy'0 : y' ≠ 0) :
    ∃ y : Vs e, ‖y‖ = π - ‖y'‖ ∧ D.fullN y = D.fullS y' := by
  set z := D.diskPt (y' : W) (inner_Vs_e _) hy'
  have hz : z ∈ D.κS.target := by
    show ζU z ≠ e
    intro h
    have h1 := D.polarT_diskPt (y' : W) (inner_Vs_e _) hy'
    rw [show ζU (D.diskPt (y' : W) (inner_Vs_e _) hy') = e from h, polarT_e D.e_norm] at h1
    exact coe_ne_zero hy'0 (norm_eq_zero.1 h1.symm)
  set w := D.κS.symm z
  have hw : w ∈ D.κS.source := D.κS.map_target hz
  have hκw : D.κS w = z := D.κS.right_inv hz
  set yv : Vs e := ⟨diskN e (ζU w), mem_Vs_of_inner (inner_diskN D.e_norm (norm_ζU _))⟩
  have hyv : ‖yv‖ < π := by
    show ‖diskN e (ζU w)‖ < π
    rw [norm_diskN_ζU D]; exact polarT_lt_pi D w
  have hdw : D.diskPt (yv : W) (inner_Vs_e _) hyv = w := D.diskPt_diskN w _ _
  have hyv0 : yv ≠ 0 := by
    rintro h0
    have : D.diskPt ((0 : Vs e) : W) (inner_Vs_e _) (by simpa [h0] using hyv) = w := by
      rw [← hdw]; congr 1; rw [h0]
    exact D.diskPt_zero_not_mem _ (this ▸ hw)
  have hN : D.fullN yv = D.fullS y' := by
    rw [fullN_apply, fullS_apply, D.stG_radialR hyv, D.stG_radialR hy', hdw, ← ι₂_apply hw, hκw]
  obtain ⟨-, hτ⟩ := D.eq_tau_of_fullN_eq_fullS (a := a) hyv hy' hN
  refine ⟨yv, ?_, hN⟩
  have := congrArg norm hτ
  rw [D.norm_tauX hyv0 hyv] at this
  linarith

theorem mem_target_iff' {Y : Type*} [TopologicalSpace Y] (f : OpenPartialHomeomorph (Vs e) Y)
    {x : Y} : x ∈ f.target ↔ ∃ y ∈ f.source, f y = x :=
  ⟨fun h => ⟨f.symm x, f.map_target h, f.right_inv h⟩, fun ⟨_, hy, h⟩ => h ▸ f.map_source hy⟩

/-- Every point of `X` is `ψ_N(y)` or `ψ_S(y)` with `‖y‖ < π`. -/
theorem exists_full (x : QuotSpace D) :
    (∃ y : Vs e, ‖y‖ < π ∧ D.fullN y = x) ∨ (∃ y : Vs e, ‖y‖ < π ∧ D.fullS y = x) := by
  induction x using glued_induction with
  | h₁ z =>
    left
    set yv : Vs e := ⟨diskN e (ζU z), mem_Vs_of_inner (inner_diskN D.e_norm (norm_ζU _))⟩
    have hyv : ‖yv‖ < π := by
      show ‖diskN e (ζU z)‖ < π
      rw [norm_diskN_ζU D]; exact polarT_lt_pi D z
    exact ⟨yv, hyv, by rw [fullN_apply, D.stG_radialR hyv]; exact congrArg _ (D.diskPt_diskN _ _ _)⟩
  | h₂ z =>
    right
    set yv : Vs e := ⟨diskN e (ζU z), mem_Vs_of_inner (inner_diskN D.e_norm (norm_ζU _))⟩
    have hyv : ‖yv‖ < π := by
      show ‖diskN e (ζU z)‖ < π
      rw [norm_diskN_ζU D]; exact polarT_lt_pi D z
    exact ⟨yv, hyv, by rw [fullS_apply, D.stG_radialR hyv]; exact congrArg _ (D.diskPt_diskN _ _ _)⟩

/-! ### `X` is a model of `𝔻(a) ∪_σ 𝔻(π − a)` -/

/-- **`X = P_θ/S³_⋆` is a smooth disk gluing `𝔻(a) ∪_σ 𝔻(π − a)` with product collars** of
width `ε = min(a, π − a)`. -/
def xModel (a : ℝ) (ha0 : 0 < a) (haπ : a < π) :
    DiskGluingModel (𝓡 (m + 1)) a (π - a) (min a (π - a)) D.sigmaV (QuotSpace D) where
  ε_pos := lt_min ha0 (by linarith)
  ε_le_a := min_le_left _ _
  ε_le_b := min_le_right _ _
  ψN := D.fullN.restrOpen (Metric.ball 0 (a + min a (π - a))) Metric.isOpen_ball
  ψS := D.fullS.restrOpen (Metric.ball 0 (π - a + min a (π - a))) Metric.isOpen_ball
  source_N := by
    rw [OpenPartialHomeomorph.restrOpen_source, fullN_source]
    exact inter_eq_right.2 (Metric.ball_subset_ball (by linarith [min_le_right a (π - a)]))
  source_S := by
    rw [OpenPartialHomeomorph.restrOpen_source, fullS_source]
    exact inter_eq_right.2 (Metric.ball_subset_ball (by linarith [min_le_left a (π - a)]))
  smooth_N := D.contMDiffOn_fullN.mono inter_subset_left
  smooth_N_symm := D.contMDiffOn_fullN_symm.mono inter_subset_left
  smooth_S := D.contMDiffOn_fullS.mono inter_subset_left
  smooth_S_symm := D.contMDiffOn_fullS_symm.mono inter_subset_left
  cover := by
    set ε := min a (π - a)
    have hεa : ε ≤ a := min_le_left _ _
    have hεb : ε ≤ π - a := min_le_right _ _
    have hε0 : 0 < ε := lt_min ha0 (by linarith)
    refine eq_univ_of_forall fun x => ?_
    rcases D.exists_full x with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · by_cases hr : ‖y‖ < a + ε
      · exact Or.inl ((D.fullN.restrOpen _ Metric.isOpen_ball).map_source
          ⟨by rw [fullN_source]; exact mem_ball_zero_iff.2 hy, mem_ball_zero_iff.2 hr⟩)
      · push_neg at hr
        have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hr; linarith
        refine Or.inr ?_
        rw [D.fullN_eq_fullS_tau (a := a) hy hy0]
        refine (D.fullS.restrOpen _ Metric.isOpen_ball).map_source
          ⟨by rw [fullS_source]; exact mem_ball_zero_iff.2 (D.tauX_lt hy0 hy), ?_⟩
        rw [mem_ball_zero_iff]
        show ‖collarTau (V := Vs e) a (π - a) D.sigmaV y‖ < _
        rw [D.norm_tauX hy0 hy]; linarith
    · by_cases hr : ‖y‖ < π - a + ε
      · exact Or.inr ((D.fullS.restrOpen _ Metric.isOpen_ball).map_source
          ⟨by rw [fullS_source]; exact mem_ball_zero_iff.2 hy, mem_ball_zero_iff.2 hr⟩)
      · push_neg at hr
        have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hr; linarith
        obtain ⟨w, hw, hwx⟩ := D.exists_fullN_eq_fullS (a := a) hy hy0
        refine Or.inl ?_
        rw [← hwx]
        exact (D.fullN.restrOpen _ Metric.isOpen_ball).map_source
          ⟨by rw [fullN_source, mem_ball_zero_iff, hw]; linarith [norm_pos_iff.2 hy0],
            by rw [mem_ball_zero_iff, hw]; linarith⟩
  overlap_N := by
    set ε := min a (π - a)
    have hεa : ε ≤ a := min_le_left _ _
    have hεb : ε ≤ π - a := min_le_right _ _
    intro y hy
    have hyπ : ‖y‖ < π := by
      have := hy.1; rw [fullN_source] at this; exact mem_ball_zero_iff.1 this
    show _ ∈ (D.fullS.restrOpen _ Metric.isOpen_ball).target ↔ _
    rw [mem_target_iff']
    constructor
    · rintro ⟨y', hy', h⟩
      have hy'π : ‖y'‖ < π := by
        have := hy'.1; rw [fullS_source] at this; exact mem_ball_zero_iff.1 this
      obtain ⟨hy0, hτ⟩ := D.eq_tau_of_fullN_eq_fullS (a := a) hyπ hy'π h.symm
      have h1 : ‖y'‖ < π - a + ε := mem_ball_zero_iff.1 hy'.2
      rw [hτ, D.norm_tauX hy0 hyπ] at h1
      linarith
    · intro h
      have hy0 : y ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
      refine ⟨collarTau (V := Vs e) a (π - a) D.sigmaV y,
        ⟨by rw [fullS_source]; exact mem_ball_zero_iff.2 (D.tauX_lt hy0 hyπ), ?_⟩,
        (D.fullN_eq_fullS_tau hyπ hy0).symm⟩
      rw [mem_ball_zero_iff, D.norm_tauX hy0 hyπ]; linarith
  overlap_S := by
    set ε := min a (π - a)
    have hεa : ε ≤ a := min_le_left _ _
    have hεb : ε ≤ π - a := min_le_right _ _
    intro y' hy'
    have hy'π : ‖y'‖ < π := by
      have := hy'.1; rw [fullS_source] at this; exact mem_ball_zero_iff.1 this
    show _ ∈ (D.fullN.restrOpen _ Metric.isOpen_ball).target ↔ _
    rw [mem_target_iff']
    constructor
    · rintro ⟨y, hy, h⟩
      have hyπ : ‖y‖ < π := by
        have := hy.1; rw [fullN_source] at this; exact mem_ball_zero_iff.1 this
      obtain ⟨hy0, hτ⟩ := D.eq_tau_of_fullN_eq_fullS (a := a) hyπ hy'π h
      have h1 : ‖y‖ < a + ε := mem_ball_zero_iff.1 hy.2
      rw [hτ, D.norm_tauX hy0 hyπ]
      linarith
    · intro h
      have hy'0 : y' ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
      obtain ⟨w, hw, hwx⟩ := D.exists_fullN_eq_fullS (a := a) hy'π hy'0
      exact ⟨w, ⟨by rw [fullN_source, mem_ball_zero_iff, hw]; linarith [norm_pos_iff.2 hy'0],
        by rw [mem_ball_zero_iff, hw]; linarith⟩, hwx⟩
  glue := by
    intro y hy h
    have hyπ : ‖y‖ < π := by
      have := hy.1; rw [fullN_source] at this; exact mem_ball_zero_iff.1 this
    have hy0 : y ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at h; linarith [min_le_left a (π - a)]
    exact D.fullN_eq_fullS_tau hyπ hy0

/-! ### (1): `j_N`, `j_S` are restrictions of diffeomorphisms between open sets -/

theorem jN_eq_ψN (a : ℝ) (ha0 : 0 < a) (haπ : a < π) (y : CDisk (m + 1) a) :
    Lr m e y.1 ∈ (D.xModel a ha0 haπ).ψN.source ∧ D.jN a y = (D.xModel a ha0 haπ).ψN (Lr m e y.1) := by
  refine ⟨?_, rfl⟩
  rw [(D.xModel a ha0 haπ).source_N, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  exact (norm_le_of_cdisk ha0.le y).trans_lt (by linarith [lt_min ha0 (sub_pos.2 haπ)])

theorem jS_eq_ψS (a : ℝ) (ha0 : 0 < a) (haπ : a < π) (y : CDisk (m + 1) (π - a)) :
    Lr m e y.1 ∈ (D.xModel a ha0 haπ).ψS.source ∧ D.jS a y = (D.xModel a ha0 haπ).ψS (Lr m e y.1) := by
  refine ⟨?_, rfl⟩
  rw [(D.xModel a ha0 haπ).source_S, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  exact (norm_le_of_cdisk (sub_pos.2 haπ).le y).trans_lt (by linarith [lt_min ha0 (sub_pos.2 haπ)])

theorem image_Lr_cdisk {r : ℝ} (hr : 0 ≤ r) :
    (fun y : CDisk (m + 1) r => Lr m e y.1) '' univ = Metric.closedBall (0 : Vs e) r := by
  ext v
  constructor
  · rintro ⟨y, -, rfl⟩
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]; exact norm_le_of_cdisk hr y
  · intro hv
    rw [mem_closedBall_zero_iff] at hv
    refine ⟨⟨(Lr m e).symm v, ?_⟩, mem_univ _, (Lr m e).apply_symm_apply v⟩
    show ‖_‖ ^ 2 ≤ r ^ 2
    rw [LinearIsometryEquiv.norm_map]; exact pow_le_pow_left₀ (norm_nonneg _) hv 2

theorem DN_eq_ψN_image (a : ℝ) (ha0 : 0 < a) (haπ : a < π) :
    D.DN a = (D.xModel a ha0 haπ).ψN '' Metric.closedBall 0 a := by
  rw [← D.range_jN ha0 haπ, ← image_Lr_cdisk (m := m) (e := e) ha0.le, image_image, image_univ]
  rfl

theorem DS_eq_ψS_image (a : ℝ) (ha0 : 0 < a) (haπ : a < π) :
    D.DS a = (D.xModel a ha0 haπ).ψS '' Metric.closedBall 0 (π - a) := by
  rw [← D.range_jS ha0 haπ, ← image_Lr_cdisk (m := m) (e := e) (sub_pos.2 haπ).le, image_image,
    image_univ]
  rfl

/-- **[GG] `lem:attaching` (1), as diffeomorphisms.** `D_N` is the image of the closed disk
`𝔻(a) ⊆ V` under the chart `ψ_N`. `ψ_N` is a smooth map from the open ball `B(a + ε)` onto the
open set `ψ_N(B(a + ε)) ⊆ X`, with smooth inverse. `j_N = ψ_N ∘ Lr` on the closed disk.
The same holds for `D_S`, `ψ_S`, `j_S` with radius `π − a`. -/
theorem lem_attaching_1 (a : ℝ) (ha0 : 0 < a) (haπ : a < π) :
    let M := D.xModel a ha0 haπ
    (M.ψN.source = Metric.ball 0 (a + min a (π - a)) ∧ IsOpen M.ψN.target ∧
      ContMDiffOn 𝓘(ℝ, Vs e) (𝓡 (m + 1)) ∞ M.ψN M.ψN.source ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞ M.ψN.symm M.ψN.target ∧
      D.DN a = M.ψN '' Metric.closedBall 0 a ∧
      ∀ y : CDisk (m + 1) a, Lr m e y.1 ∈ M.ψN.source ∧ D.jN a y = M.ψN (Lr m e y.1)) ∧
    (M.ψS.source = Metric.ball 0 (π - a + min a (π - a)) ∧ IsOpen M.ψS.target ∧
      ContMDiffOn 𝓘(ℝ, Vs e) (𝓡 (m + 1)) ∞ M.ψS M.ψS.source ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞ M.ψS.symm M.ψS.target ∧
      D.DS a = M.ψS '' Metric.closedBall 0 (π - a) ∧
      ∀ y : CDisk (m + 1) (π - a), Lr m e y.1 ∈ M.ψS.source ∧ D.jS a y = M.ψS (Lr m e y.1)) :=
  ⟨⟨(D.xModel a ha0 haπ).source_N, (D.xModel a ha0 haπ).ψN.open_target,
      (D.xModel a ha0 haπ).smooth_N, (D.xModel a ha0 haπ).smooth_N_symm,
      D.DN_eq_ψN_image a ha0 haπ, D.jN_eq_ψN a ha0 haπ⟩,
    ⟨(D.xModel a ha0 haπ).source_S, (D.xModel a ha0 haπ).ψS.open_target,
      (D.xModel a ha0 haπ).smooth_S, (D.xModel a ha0 haπ).smooth_S_symm,
      D.DS_eq_ψS_image a ha0 haπ, D.jS_eq_ψS a ha0 haπ⟩⟩

/-- **[GG] `lem:attaching` (3), as a diffeomorphism: `P_θ/S³_⋆ ≅ D_N ∪_σ D_S`.** `X` is
diffeomorphic to every smooth disk gluing `𝔻(a) ∪_σ 𝔻(π − a)` with product collars, of any
collar width. The gluing is unique up to diffeomorphism (`diskGluing_unique`), and `X` is one
(`xModel`). -/
theorem lem_attaching_3 (a : ℝ) (ha0 : 0 < a) (haπ : a < π) {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) Y] [IsManifold (𝓡 (m + 1)) ∞ Y] {ε : ℝ}
    (M : DiskGluingModel (𝓡 (m + 1)) a (π - a) ε D.sigmaV Y) :
    Nonempty (QuotSpace D ≃ₘ^∞⟮𝓡 (m + 1), 𝓡 (m + 1)⟯ Y) :=
  diskGluing_unique (D.xModel a ha0 haπ) M

end PolarData

section Model

/-- **Non-vacuity**: the model polar data, with `a = π/2`. -/
example (m : ℕ) := (trivialPolarData m).xModel (π / 2) (by positivity) (by linarith [pi_pos])

example (m : ℕ) := (trivialPolarData m).lem_attaching_1 (π / 2) (by positivity) (by linarith [pi_pos])

/-- `lem_attaching_3` fires: applied to `X` itself, it returns a self-diffeomorphism. -/
example (m : ℕ) : Nonempty (QuotSpace (trivialPolarData m) ≃ₘ^∞⟮𝓡 (m + 1), 𝓡 (m + 1)⟯
    QuotSpace (trivialPolarData m)) :=
  (trivialPolarData m).lem_attaching_3 (π / 2) (by positivity) (by linarith [pi_pos])
    ((trivialPolarData m).xModel (π / 2) (by positivity) (by linarith [pi_pos]))

end Model

end XModel

end

end ExoticSpheres8And10
