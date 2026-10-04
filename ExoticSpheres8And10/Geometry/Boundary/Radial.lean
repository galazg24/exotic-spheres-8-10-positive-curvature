/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.Boundary.PolarCoordinates

/-! # The radial map is a diffeomorphism of the open ball of radius `π` onto its image

`radialR Y = μ(‖Y‖²)Y` is geodesic polar coordinates in stereographic form (`stereoInv_radialR`).
Here it is an `OpenPartialHomeomorph` `radialPH`, with source the ball `‖Y‖ < π`, and both it
and its inverse are smooth:
* `norm_radialR`: `‖radialR Y‖ = 2 tan(‖Y‖/2)`, so `radialR` is injective on the ball
  (`injOn_radialR`);
* the inverse function theorem at every point (the derivative is invertible,
  `injective_fderiv_radialR`) gives local smooth inverses, which agree with the global inverse.
-/

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section Radial

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {e : W}

omit [FiniteDimensional ℝ W] in
theorem norm_radialR {Y : Vs e} (hY : ‖Y‖ < π) : ‖radialR Y‖ = 2 * Real.tan (‖Y‖ / 2) := by
  have hs0 : 0 ≤ ‖Y‖ ^ 2 := by positivity
  have hs : ‖Y‖ ^ 2 < π ^ 2 := by have := norm_nonneg Y; nlinarith [pi_pos]
  rw [radialR, norm_smul, Real.norm_eq_abs, abs_of_pos (muR_pos hs0 hs), mul_comm]
  exact mul_muR (by rw [abs_of_nonneg (norm_nonneg _)]; exact hY)

omit [FiniteDimensional ℝ W] in
/-- **`radialR` is injective on the ball of radius `π`.** -/
theorem injOn_radialR : InjOn (radialR (e := e)) (Metric.ball 0 π) := by
  intro Y hY Y' hY' h
  rw [Metric.mem_ball, dist_zero_right] at hY hY'
  have hmem : ∀ Z : Vs e, ‖Z‖ < π → ‖Z‖ / 2 ∈ Ioo (-(π / 2)) (π / 2) := fun Z hZ =>
    ⟨by linarith [norm_nonneg Z, pi_pos], by linarith⟩
  have hn : ‖Y‖ = ‖Y'‖ := by
    have h1 := congrArg norm h
    rw [norm_radialR hY, norm_radialR hY'] at h1
    have h2 : Real.tan (‖Y‖ / 2) = Real.tan (‖Y'‖ / 2) := by linarith
    have := strictMonoOn_tan.injOn (hmem Y hY) (hmem Y' hY') h2
    linarith
  have hμ := muR_pos (s := ‖Y‖ ^ 2) (by positivity) (by have := norm_nonneg Y; nlinarith [pi_pos])
  have h' : muR (‖Y‖ ^ 2) • Y = muR (‖Y‖ ^ 2) • Y' := by
    have h3 : radialR Y = radialR Y' := h
    unfold radialR at h3
    rwa [← hn] at h3
  exact smul_right_injective _ hμ.ne' h'

/-- The derivative of `radialR` at `Y`, as an equivalence. -/
def dRadialEquiv {Y : Vs e} (hY : ‖Y‖ < π) : Vs e ≃L[ℝ] Vs e :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ (radialR (e := e)) Y).toLinearMap
    (injective_fderiv_radialR hY)).toContinuousLinearEquiv

theorem coe_dRadialEquiv {Y : Vs e} (hY : ‖Y‖ < π) :
    (dRadialEquiv hY : Vs e →L[ℝ] Vs e) = fderiv ℝ (radialR (e := e)) Y := by
  ext1 h; rfl

theorem hasFDerivAt_radialR_equiv {Y : Vs e} (hY : ‖Y‖ < π) :
    HasFDerivAt (radialR (e := e)) (dRadialEquiv hY : Vs e →L[ℝ] Vs e) Y := by
  rw [coe_dRadialEquiv]
  exact ((contDiffAt_radialR hY).differentiableAt (by simp)).hasFDerivAt

/-- A local inverse chart of `radialR` at `Y` (inverse function theorem), with source inside the
ball of radius `π`. -/
def radialLoc {Y : Vs e} (hY : ‖Y‖ < π) : OpenPartialHomeomorph (Vs e) (Vs e) :=
  ((contDiffAt_radialR hY).toOpenPartialHomeomorph radialR (hasFDerivAt_radialR_equiv hY)
    (by simp)).restrOpen (Metric.ball 0 π) Metric.isOpen_ball

theorem radialLoc_coe {Y : Vs e} (hY : ‖Y‖ < π) :
    (radialLoc hY : Vs e → Vs e) = radialR := rfl

theorem mem_radialLoc_source {Y : Vs e} (hY : ‖Y‖ < π) : Y ∈ (radialLoc hY).source := by
  rw [radialLoc, OpenPartialHomeomorph.restrOpen_source]
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, mem_ball_zero_iff.2 hY⟩

theorem radialLoc_source_subset {Y : Vs e} (hY : ‖Y‖ < π) :
    (radialLoc hY).source ⊆ Metric.ball 0 π := by
  rw [radialLoc, OpenPartialHomeomorph.restrOpen_source]; exact inter_subset_right

/-- On the target of a local chart, the global inverse is the local inverse. -/
theorem invFunOn_eq_radialLoc_symm {Y : Vs e} (hY : ‖Y‖ < π) {z : Vs e}
    (hz : z ∈ (radialLoc hY).target) :
    invFunOn radialR (Metric.ball 0 π) z = (radialLoc hY).symm z := by
  have h1 := (radialLoc hY).map_target hz
  have h2 : radialR ((radialLoc hY).symm z) = z := (radialLoc hY).right_inv hz
  conv_lhs => rw [← h2]
  exact injOn_radialR.leftInvOn_invFunOn (radialLoc_source_subset hY h1)

theorem radialLoc_target_subset {Y : Vs e} (hY : ‖Y‖ < π) :
    (radialLoc hY).target ⊆ radialR '' Metric.ball 0 π := fun z hz =>
  ⟨(radialLoc hY).symm z, radialLoc_source_subset hY ((radialLoc hY).map_target hz),
    (radialLoc hY).right_inv hz⟩

theorem radialR_mem_radialLoc_target {Y : Vs e} (hY : ‖Y‖ < π) :
    radialR Y ∈ (radialLoc hY).target :=
  (radialLoc hY).map_source (mem_radialLoc_source hY)

/-- **The radial map on the open ball of radius `π`, with its inverse.** -/
def radialPH : OpenPartialHomeomorph (Vs e) (Vs e) where
  toFun := radialR
  invFun := invFunOn radialR (Metric.ball 0 π)
  source := Metric.ball 0 π
  target := radialR '' Metric.ball 0 π
  map_source' := fun _ hY => mem_image_of_mem _ hY
  map_target' := by
    rintro w ⟨Y, hY, rfl⟩
    rw [injOn_radialR.leftInvOn_invFunOn hY]; exact hY
  left_inv' := fun _ hY => injOn_radialR.leftInvOn_invFunOn hY
  right_inv' := by
    rintro w ⟨Y, hY, rfl⟩
    rw [injOn_radialR.leftInvOn_invFunOn hY]
  open_source := Metric.isOpen_ball
  open_target := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨Y, hY, rfl⟩
    have hY' : ‖Y‖ < π := mem_ball_zero_iff.1 hY
    exact Filter.mem_of_superset
      ((radialLoc hY').open_target.mem_nhds (radialR_mem_radialLoc_target hY'))
      (radialLoc_target_subset hY')
  continuousOn_toFun := fun _ hY =>
    (contDiffAt_radialR (mem_ball_zero_iff.1 hY)).continuousAt.continuousWithinAt
  continuousOn_invFun := by
    rintro w ⟨Y, hY, rfl⟩
    have hY' : ‖Y‖ < π := mem_ball_zero_iff.1 hY
    have hev : invFunOn radialR (Metric.ball 0 π) =ᶠ[𝓝 (radialR Y)] (radialLoc hY').symm := by
      filter_upwards [(radialLoc hY').open_target.mem_nhds (radialR_mem_radialLoc_target hY')]
        with z hz using invFunOn_eq_radialLoc_symm hY' hz
    exact (((radialLoc hY').continuousAt_symm (radialR_mem_radialLoc_target hY')).congr
      hev.symm).continuousWithinAt

theorem radialPH_coe : (radialPH (e := e) : Vs e → Vs e) = radialR := rfl

theorem radialPH_source : (radialPH (e := e)).source = Metric.ball 0 π := rfl

theorem radialPH_target : (radialPH (e := e)).target = radialR '' Metric.ball 0 π := rfl

theorem contDiffOn_radialPH : ContDiffOn ℝ ∞ (radialPH (e := e)) (radialPH (e := e)).source :=
  fun _ hY => (contDiffAt_radialR (mem_ball_zero_iff.1 hY)).contDiffWithinAt

/-- **The inverse of the radial map is smooth.** -/
theorem contDiffOn_radialPH_symm :
    ContDiffOn ℝ ∞ (radialPH (e := e)).symm (radialPH (e := e)).target := by
  rintro w ⟨Y, hY, rfl⟩
  have hY' : ‖Y‖ < π := mem_ball_zero_iff.1 hY
  set B := radialLoc hY'
  have hw : radialR Y ∈ B.target := radialR_mem_radialLoc_target hY'
  have hBY : B.symm (radialR Y) = Y := B.left_inv (mem_radialLoc_source hY')
  have hd : HasFDerivAt B (dRadialEquiv hY' : Vs e →L[ℝ] Vs e) (B.symm (radialR Y)) := by
    rw [hBY]; exact hasFDerivAt_radialR_equiv hY'
  have hc : ContDiffAt ℝ ∞ B (B.symm (radialR Y)) := by
    rw [hBY]; exact contDiffAt_radialR hY'
  have h1 : ContDiffAt ℝ ∞ B.symm (radialR Y) := B.contDiffAt_symm hw hd hc
  have hev : (radialPH (e := e)).symm =ᶠ[𝓝 (radialR Y)] B.symm := by
    filter_upwards [B.open_target.mem_nhds hw] with z hz using invFunOn_eq_radialLoc_symm hY' hz
  exact (h1.congr_of_eventuallyEq hev).contDiffWithinAt

end Radial

end

end ExoticSpheres8And10
