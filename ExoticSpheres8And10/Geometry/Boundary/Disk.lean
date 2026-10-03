/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.Boundary.RegularDomain

/-! # Infrastructure: the closed disk `𝔻(R) ⊆ ℝⁿ` as a smooth manifold with boundary

`CDisk n R = {y | ‖y‖² ≤ R²}` is a `C^∞` manifold with boundary on `𝓡∂ n`, by `MB_RegDom`.
* At interior points, translations give the charts.
* At a boundary point `p`, the chart is the straightening
  `Θ_p(y) = (R² − ‖y‖²)e₀ + Π(A(y − p))`:
  - `A` is the reflection taking `p/R` to `−e₀`;
  - `Π` kills the `e₀`-coordinate;
  - its derivative at `p` is invertible (`injective_dΘ`).
-/

open Set Function Filter Topology

open scoped Manifold ContDiff RealInnerProductSpace

namespace ExoticSpheres8And10

noncomputable section

section Disk

variable {n : ℕ} [NeZero n]

/-- `e₀`. -/
def e0n (n : ℕ) [NeZero n] : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single 0 1

theorem e0n_apply_zero : (e0n n) 0 = 1 := by simp [e0n]

theorem inner_e0n (w : EuclideanSpace ℝ (Fin n)) : ⟪e0n n, w⟫ = w 0 := by
  simp [e0n, EuclideanSpace.inner_single_left]

theorem norm_e0n : ‖e0n n‖ = 1 := by simp [e0n]

/-- The projection killing the `e₀`-coordinate. -/
def piE : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.id ℝ _ - (EuclideanSpace.proj (0 : Fin n)).smulRight (e0n n)

theorem piE_apply (w : EuclideanSpace ℝ (Fin n)) : piE w = w - (w 0) • e0n n := by
  simp [piE]

theorem piE_apply_zero (w : EuclideanSpace ℝ (Fin n)) : (piE w) 0 = 0 := by
  rw [piE_apply]; simp [e0n]

variable (n) in
/-- The closed disk of radius `R`. -/
abbrev CDisk (R : ℝ) : Type := RegDom (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) (R ^ 2)

section Straighten

variable {R : ℝ} (hR : 0 < R) {p : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ = R)

/-- The reflection taking `p/R` to `−e₀`. -/
def reflP (R : ℝ) (p : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ℝ ∙ (R⁻¹ • p - -e0n n))ᗮ.reflection

theorem reflP_reflP (R : ℝ) (p v : EuclideanSpace ℝ (Fin n)) : reflP R p (reflP R p v) = v :=
  Submodule.reflection_reflection _ v

include hR hp in
theorem reflP_p : reflP R p (R⁻¹ • p) = -e0n n := by
  apply Submodule.reflection_sub
  rw [norm_neg, norm_e0n, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, hp,
    inv_mul_cancel₀ hR.ne']

include hR hp in
theorem reflP_e0 : reflP R p (e0n n) = -(R⁻¹ • p) := by
  have h := congrArg (reflP R p) (reflP_p hR hp)
  rw [reflP_reflP, map_neg] at h
  rw [h, neg_neg]

/-- The straightening map at a boundary point. -/
def thetaP (R : ℝ) (p : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (R ^ 2 - ‖y‖ ^ 2) • e0n n + piE (reflP R p (y - p))

theorem thetaP_zero (y : EuclideanSpace ℝ (Fin n)) : (thetaP R p y) 0 = R ^ 2 - ‖y‖ ^ 2 := by
  simp only [thetaP, PiLp.add_apply, PiLp.smul_apply, e0n_apply_zero, piE_apply_zero,
    smul_eq_mul, mul_one, add_zero]

theorem contDiff_thetaP : ContDiff ℝ ∞ (thetaP (n := n) R p) := by
  unfold thetaP
  exact ((contDiff_const.sub (contDiff_norm_sq ℝ)).smul contDiff_const).add
    ((piE.comp (reflP R p).toContinuousLinearEquiv.toContinuousLinearMap).contDiff.comp
      (contDiff_id.sub contDiff_const))

/-- The derivative of the straightening map at `p`. -/
def dThetaP (R : ℝ) (p : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (-(2 • innerSL ℝ p)).smulRight (e0n n) +
    piE.comp (reflP R p).toContinuousLinearEquiv.toContinuousLinearMap

theorem dThetaP_apply (h : EuclideanSpace ℝ (Fin n)) :
    dThetaP R p h = (-(2 * ⟪p, h⟫)) • e0n n + piE (reflP R p h) := by
  simp [dThetaP, two_smul, two_mul]

theorem hasFDerivAt_thetaP : HasFDerivAt (thetaP (n := n) R p) (dThetaP R p) p := by
  have h1 := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_sub (R ^ 2)).smul_const (e0n n)
  have h2 := (piE.comp (reflP R p).toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.comp
    p ((hasFDerivAt_id p).sub_const p)
  refine (h1.add h2).congr_fderiv ?_
  ext1 h
  simp [dThetaP]

include hR hp in
theorem injective_dThetaP : Injective (dThetaP R p) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  rw [dThetaP_apply] at hh
  have h0 := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w 0) hh
  simp only [PiLp.add_apply, PiLp.smul_apply, e0n_apply_zero, piE_apply_zero, smul_eq_mul,
    mul_one, add_zero, PiLp.zero_apply] at h0
  have hph : ⟪p, h⟫ = 0 := by linarith
  rw [hph, mul_zero, neg_zero, zero_smul, zero_add, piE_apply, sub_eq_zero] at hh
  have hh' : h = (reflP R p h 0) • reflP R p (e0n n) := by
    have := congrArg (reflP R p) hh
    rw [reflP_reflP, map_smul] at this
    exact this
  rw [reflP_e0 hR hp] at hh'
  have hc : reflP R p h 0 = 0 := by
    have := congrArg (fun w => ⟪p, w⟫) hh'
    simp only [hph, inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq, hp] at this
    have hR2 : R⁻¹ * R ^ 2 = R := by field_simp
    rw [hR2] at this
    rcases mul_eq_zero.1 this.symm with h1 | h1
    · exact h1
    · exact absurd (neg_eq_zero.1 h1) hR.ne'
  rw [hh', hc, zero_smul]

/-- The derivative, as a continuous linear equivalence. -/
def dThetaPEquiv : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.ofInjectiveEndo (dThetaP R p).toLinearMap
    (injective_dThetaP hR hp)).toContinuousLinearEquiv

theorem coe_dThetaPEquiv : (dThetaPEquiv hR hp : _ →L[ℝ] _) = dThetaP R p := by
  ext1 h; rfl

end Straighten

theorem disk_cover {R : ℝ} (hR : 0 < R) (y : CDisk n R) :
    ∃ C : AdmChart (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) (R ^ 2), y.1 ∈ C.A.source := by
  have hy : ‖y.1‖ ≤ R := by
    have := y.2; exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero).1 this
  rcases hy.lt_or_eq with h | h
  · refine exists_admChart_of_ball (r := R - ‖y.1‖) (by linarith) fun z hz => ?_
    have : ‖z‖ < R := by
      have h1 : dist z y.1 < R - ‖y.1‖ := hz
      have := norm_le_norm_add_norm_sub' z y.1
      rw [dist_eq_norm] at h1; linarith [norm_sub_rev z y.1]
    exact pow_lt_pow_left₀ this (norm_nonneg _) two_ne_zero
  · refine exists_admChart_of_ift (contDiff_thetaP (R := R) (p := y.1)) (fun z => ?_)
      (fun z => ?_) (f' := dThetaPEquiv hR h) ?_
    · rw [thetaP_zero, sub_nonneg]
    · rw [thetaP_zero, sub_pos]
    · rw [coe_dThetaPEquiv]; exact hasFDerivAt_thetaP

/-- **The closed disk is a charted space on the half space.** -/
instance diskChartedSpace (R : ℝ) [Fact (0 < R)] : ChartedSpace (EuclideanHalfSpace n) (CDisk n R) :=
  regDomChartedSpace _ _ (disk_cover (Fact.out : 0 < R))

/-- **The closed disk is a `C^∞` manifold with boundary.** -/
instance diskIsManifold (R : ℝ) [Fact (0 < R)] : IsManifold (𝓡∂ n) ∞ (CDisk n R) :=
  regDom_isManifold (disk_cover (Fact.out : 0 < R))

theorem contMDiff_val_disk (R : ℝ) [Fact (0 < R)] :
    ContMDiff (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Subtype.val : CDisk n R → _) :=
  contMDiff_val_regDom (disk_cover (Fact.out : 0 < R))

theorem isInvertible_mfderiv_val_disk (R : ℝ) [Fact (0 < R)] (y : CDisk n R) :
    (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Subtype.val : CDisk n R → _) y).IsInvertible :=
  isInvertible_mfderiv_val_regDom (disk_cover (Fact.out : 0 < R)) y

/-- **The boundary of the closed disk is the sphere of radius `R`.** -/
theorem isBoundaryPoint_disk_iff (R : ℝ) [Fact (0 < R)] (y : CDisk n R) :
    (𝓡∂ n).IsBoundaryPoint y ↔ ‖y.1‖ = R := by
  have hR : 0 < R := Fact.out
  rw [show (𝓡∂ n).IsBoundaryPoint y ↔ ‖y.1‖ ^ 2 = R ^ 2 from
    isBoundaryPoint_regDom_iff (disk_cover hR) y]
  exact pow_left_inj₀ (norm_nonneg _) hR.le two_ne_zero

end Disk

end

end ExoticSpheres8And10
