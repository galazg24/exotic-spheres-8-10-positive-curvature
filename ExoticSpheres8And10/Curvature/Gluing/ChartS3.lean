/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.Stereographic
import ExoticSpheres8And10.Curvature.Northern.Model

/-! # The chart of `S³` at `1`, as an inverse stereographic projection

`σ3 = (extChartAt (𝓡 3) 1).symm : ℝ³ → S³` is Mathlib's own chart inverse at `1`, the
stereographic projection from `−1`. So tangent coordinates at `1` are the ones of the `S³`
factor of `V × S³`.

* `σ3_val`: `σ3 z = σ_1(ι z)`, with `ι : ℝ³ → ℍ` a linear isometry onto `1^⊥`;
* `contMDiff_σ3`; `z30 = chart(1) = 0` and `σ3 z30 = 1`;
* `mfderiv_σ3`: `dσ3` at `z30` is the identity;
* `hasFDerivAt_val_σ3`: `d(σ3 ·)(z) = dσ_1(ι z) ∘ ι`, as a map into `ℍ`.
-/

open Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The chart inverse `ℝ³ → S³` at `1`. -/
def σ3 : E3 → S3 := (extChartAt (𝓡 3) (1 : S3)).symm

/-- The isometry `(ℝ ∙ (−1))ᗮ ≅ ℝ³` of Mathlib's chart at `1`. -/
def U3 : (ℝ ∙ ((-1 : S3) : Quaternion ℝ))ᗮ ≃ₗᵢ[ℝ] E3 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere (-1 : S3))).repr

/-- `ι : ℝ³ → ℍ`, a linear isometry onto `1^⊥`. -/
def ι3i : E3 →ₗᵢ[ℝ] Quaternion ℝ :=
  (Submodule.subtypeₗᵢ (ℝ ∙ ((-1 : S3) : Quaternion ℝ))ᗮ).comp U3.symm.toLinearIsometry

/-- `ι` as a continuous linear map. -/
def ι3 : E3 →L[ℝ] Quaternion ℝ := ι3i.toContinuousLinearMap

theorem ι3_apply (z : E3) : ι3 z = ((U3.symm z : (ℝ ∙ ((-1 : S3) : Quaternion ℝ))ᗮ) :
    Quaternion ℝ) := rfl

theorem norm_ι3 (z : E3) : ‖ι3 z‖ = ‖z‖ := ι3i.norm_map z

theorem inner_ι3 (a b : E3) : ⟪ι3 a, ι3 b⟫ = ⟪a, b⟫ := ι3i.inner_map_map a b

theorem inner_ι3_one (z : E3) : ⟪ι3 z, (1 : Quaternion ℝ)⟫ = 0 := by
  have h := (U3.symm z).2
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h
  have h' : ⟪(-1 : Quaternion ℝ), ι3 z⟫ = 0 := h
  rw [inner_neg_left, neg_eq_zero] at h'
  rw [real_inner_comm]
  exact h'

theorem norm_one_quat : ‖(1 : Quaternion ℝ)‖ = 1 := norm_one

theorem σ3_val (z : E3) : ((σ3 z : S3) : Quaternion ℝ) = stereoE 1 (ι3 z) := by
  have h : ((σ3 z : S3) : Quaternion ℝ) = ((stereographic' 3 (-1 : S3)).symm z : Quaternion ℝ) :=
    rfl
  rw [h, stereographic'_symm_apply]
  have hι : ((OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere (-1 : S3))).repr.symm z : Quaternion ℝ) = ι3 z := rfl
  have hn : ((-1 : S3) : Quaternion ℝ) = -1 := rfl
  simp only [hι, hn, stereoE]
  module

theorem contMDiff_σ3 : ContMDiff 𝓘(ℝ, E3) (𝓡 3) ∞ σ3 := by
  have h := contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) (1 : S3)
  have ht : (extChartAt (𝓡 3) (1 : S3)).target = univ := by
    rw [extChartAt_target, ModelWithCorners.range_eq_univ, inter_univ]
    show (𝓡 3).symm ⁻¹' (stereographic' 3 (-1 : S3)).target = univ
    rw [stereographic'_target, preimage_univ]
  rw [ht] at h
  exact contMDiffOn_univ.1 h

/-- The chart point of `1`. -/
def z30 : E3 := extChartAt (𝓡 3) (1 : S3) 1

theorem z30_eq : z30 = 0 := by
  show (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere (-(1 : S3)))).repr
      (stereographic (norm_eq_of_mem_sphere (-(1 : S3))) 1) = 0
  have h := stereographic_apply_neg (-(1 : S3))
  rw [neg_neg] at h
  rw [h, map_zero]

theorem σ3_z30 : σ3 z30 = 1 := (extChartAt (𝓡 3) (1 : S3)).left_inv (mem_extChartAt_source _)

theorem mfderiv_σ3 : mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 z30 = ContinuousLinearMap.id ℝ E3 := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 3) (x := (1 : S3))
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  exact h

theorem hasFDerivAt_val_σ3 (z : E3) :
    HasFDerivAt (fun w : E3 => ((σ3 w : S3) : Quaternion ℝ)) ((dstL 1 (ι3 z)).comp ι3) z := by
  have e : (fun w : E3 => ((σ3 w : S3) : Quaternion ℝ)) = stereoE 1 ∘ ι3 :=
    funext fun w => σ3_val w
  rw [e]
  exact (hasFDerivAt_stereo 1 (ι3 z)).comp z ι3.hasFDerivAt

end

end ExoticSpheres8And10
