/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.Boundary.Disk
import ExoticSpheres8And10.Geometry.Boundary.PolarCoordinates
import ExoticSpheres8And10.PolarBundles.Attaching
import ExoticSpheres8And10.PolarBundles.Summary

/-! # [D] `lem:attaching` (1) and (3) with smooth closed disks

`MB_Disk` makes the closed disk `𝔻(R) ⊆ ℝ^{m+1}` a smooth manifold with boundary on
`𝓡∂ (m+1)`. Here:
* `Lr` is a linear isometry `ℝ^{m+1} ≃ V = e^⊥`.
* The disk maps are
  - `jN y = [(Y, 1)]_⋆` on `𝔻(a)`;
  - `jS y = [(Y, 1)]_⋆` on `𝔻(π − a)`, in the southern copy;
  where `Y = Lr y` and the disk coordinate is `ζ = t x` (geodesic polar).

  In the stereographic chart, `Y ↦ ζ` is the radial map `radialR` (`stereoInv_radialR`), so
  `jN = ι₁ ∘ stG ∘ radialR ∘ Lr ∘ val` is a composite of smooth maps with invertible
  differentials.
* **(1)**: each `j_α` is a smooth map of manifolds with boundary, with invertible differential at
  every point, boundary points included. It is a closed topological embedding with image `D_α`.
  So `D_α` is a smooth closed disk in `X = P_θ/S³_⋆`, with inverse `Y ↦ [(Y, 1)]_⋆`.
* The manifold boundary `∂𝔻` is sent onto the equator `D_N ∩ D_S`.
* **(3)**: `X = jN(𝔻(a)) ∪ jS(𝔻(π − a))`, and `jN y = jS y'` exactly when the boundary
  relation `DiskRel` of `S2_Attaching` holds. That relation is `y_S = σ(y_N)` ([D]
  `eq:sigma`). So `X` is `𝔻_N ∪_σ 𝔻_S`, with both disks smoothly embedded.
-/

namespace ExoticSpheres8And10

open Set Function Module Real Topology

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

/-- `0 < π − a` from `a < π`. -/
instance factPiSub (a : ℝ) [h : Fact (a < π)] : Fact (0 < π - a) := ⟨sub_pos.2 h.out⟩

section CompactDisk

variable {n : ℕ} [NeZero n]

theorem norm_le_of_cdisk {R : ℝ} (hR : 0 ≤ R) (y : CDisk n R) : ‖y.1‖ ≤ R :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 y.2

instance compactSpace_cdisk (R : ℝ) [Fact (0 < R)] : CompactSpace (CDisk n R) := by
  have hR : 0 < R := Fact.out
  have hs : {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 ≤ R ^ 2} = Metric.closedBall 0 R := by
    ext y
    rw [mem_setOf_eq, mem_closedBall_zero_iff, pow_le_pow_iff_left₀ (norm_nonneg _) hR.le
      two_ne_zero]
  have : IsCompact {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 ≤ R ^ 2} := by
    rw [hs]; exact isCompact_closedBall _ _
  exact isCompact_iff_compactSpace.1 this

end CompactDisk

section Attach

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

variable (m e) in
/-- A linear isometry `ℝ^{m+1} ≃ V = e^⊥`. -/
def Lr : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] Vs e :=
  ((stdOrthonormalBasis ℝ (Vs e)).reindex
    (finCongr (Fact.out : finrank ℝ (Vs e) = m + 1))).repr.symm

theorem norm_Lr (y : EuclideanSpace ℝ (Fin (m + 1))) : ‖((Lr m e y : Vs e) : W)‖ = ‖y‖ :=
  (Lr m e).norm_map y

theorem mem_Vs_of_inner {Y : W} (hY : ⟪Y, e⟫ = 0) : Y ∈ Vs e := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]; exact hY

/-- `y ↦ Lr y`, from the model disk to `S2_Attaching`'s disk in `V`. -/
def toDiskE {a : ℝ} (ha : 0 ≤ a) (y : CDisk (m + 1) a) : Disk e a :=
  ⟨(Lr m e y.1 : W), inner_Vs_e _, by rw [norm_Lr]; exact norm_le_of_cdisk ha y⟩

theorem toDiskE_injective {a : ℝ} (ha : 0 ≤ a) : Injective (toDiskE (m := m) (e := e) ha) :=
  fun y y' h => by
    have h1 := congrArg (fun Y : Disk e a => (Y : W)) h
    exact Subtype.ext ((Lr m e).injective (Subtype.ext h1))

theorem toDiskE_surjective {a : ℝ} (ha : 0 ≤ a) : Surjective (toDiskE (m := m) (e := e) ha) := by
  intro Y
  refine ⟨⟨(Lr m e).symm ⟨Y, mem_Vs_of_inner (PolarData.Disk_inner Y)⟩, ?_⟩, ?_⟩
  · show ‖_‖ ^ 2 ≤ a ^ 2
    rw [LinearIsometryEquiv.norm_map]
    exact pow_le_pow_left₀ (norm_nonneg _) (PolarData.Disk_norm Y) 2
  · apply Subtype.ext
    show ((Lr m e ((Lr m e).symm ⟨Y, _⟩) : Vs e) : W) = Y
    rw [LinearIsometryEquiv.apply_symm_apply]

namespace PolarData

variable (D : PolarData (m := m) e)

/-- The disk coordinate `y ↦ ζ = expN(Lr y) ∈ U_N`, written stereographically. -/
def diskCoord (b : ℝ) (y : CDisk (m + 1) b) : UN e :=
  stG D.e_norm (radialR (Lr m e y.1))

/-- **The northern disk map** `𝔻(a) → X`, `y ↦ [(Lr y, 1)]_⋆`. -/
def jN (a : ℝ) (y : CDisk (m + 1) a) : QuotSpace D := ι₁ D.κS (D.diskCoord a y)

/-- **The southern disk map** `𝔻(π − a) → X`, `y ↦ [(Lr y, 1)]_⋆` in the southern copy. -/
def jS (a : ℝ) (y : CDisk (m + 1) (π - a)) : QuotSpace D := ι₂ D.κS (D.diskCoord (π - a) y)

theorem diskCoord_eq {b : ℝ} (y : CDisk (m + 1) b) (hπ : ‖((Lr m e y.1 : Vs e) : W)‖ < π) :
    D.diskCoord b y = D.diskPt (Lr m e y.1 : W) (inner_Vs_e _) hπ :=
  Subtype.ext (Subtype.ext (stereoInv_radialR (e := e) hπ))

theorem jN_eq {a : ℝ} (ha0 : 0 < a) (haπ : a < π) (y : CDisk (m + 1) a) :
    D.jN a y = D.diskMapN haπ (toDiskE ha0.le y) :=
  congrArg (ι₁ D.κS) (D.diskCoord_eq y _)

theorem jS_eq {a : ℝ} (ha0 : 0 < a) (haπ : a < π) (y : CDisk (m + 1) (π - a)) :
    D.jS a y = D.diskMapS ha0 (toDiskE (sub_pos.2 haπ).le y) :=
  congrArg (ι₂ D.κS) (D.diskCoord_eq y _)

/-! ### Smoothness -/

theorem norm_Lr_lt {b : ℝ} [Fact (0 < b)] (hb : b < π) (y : CDisk (m + 1) b) :
    ‖Lr m e y.1‖ < π := by
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_le_of_cdisk (Fact.out : 0 < b).le y).trans_lt hb

theorem contMDiff_diskCoord {b : ℝ} [Fact (0 < b)] (hb : b < π) :
    ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (D.diskCoord b) := fun y =>
  ((contMDiff_stG (m := m) D.e_norm).contMDiffAt).comp y
    ((contDiffAt_radialR (norm_Lr_lt (e := e) hb y)).contMDiffAt.comp y
      ((Lr m e).toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.contMDiffAt.comp y
        (contMDiff_val_disk b).contMDiffAt))

theorem ι₁_eq_ch₁ : ι₁ D.κS = (Subtype.val : D.U₁ → QuotSpace D) ∘ D.ch₁.symm := rfl

theorem ι₂_eq_ch₂ : ι₂ D.κS = (Subtype.val : D.U₂ → QuotSpace D) ∘ D.ch₂.symm := rfl

theorem contMDiff_ι₁' : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ (ι₁ D.κS) := by
  rw [ι₁_eq_ch₁]; exact contMDiff_subtype_val.comp D.ch₁.symm.contMDiff

theorem contMDiff_ι₂' : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ (ι₂ D.κS) := by
  rw [ι₂_eq_ch₂]; exact contMDiff_subtype_val.comp D.ch₂.symm.contMDiff

/-- **`jN` is smooth** (as a map of manifolds with boundary). -/
theorem contMDiff_jN (a : ℝ) [Fact (0 < a)] [Fact (a < π)] :
    ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (D.jN a) :=
  D.contMDiff_ι₁'.comp (D.contMDiff_diskCoord Fact.out)

/-- **`jS` is smooth.** -/
theorem contMDiff_jS (a : ℝ) [Fact (0 < a)] [Fact (a < π)] :
    ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (D.jS a) :=
  D.contMDiff_ι₂'.comp (D.contMDiff_diskCoord (by linarith [(Fact.out : 0 < a)]))

/-! ### Invertible differentials -/

theorem isInvertible_mfderiv_stG (y : Vs e) :
    (mfderiv 𝓘(ℝ, Vs e) (𝓡 (m + 1)) (stG D.e_norm) y).IsInvertible :=
  ⟨(stD (m := m) D.e_norm).symm.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩

theorem isInvertible_fderiv_radialR {Y : Vs e} (hY : ‖Y‖ < π) :
    (fderiv ℝ (radialR (e := e)) Y).IsInvertible :=
  ⟨(LinearEquiv.ofInjectiveEndo (fderiv ℝ (radialR (e := e)) Y).toLinearMap
    (injective_fderiv_radialR hY)).toContinuousLinearEquiv, by ext1 h; rfl⟩

theorem isInvertible_mfderiv_ι₁ (z : UN e) :
    (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) (ι₁ D.κS) z).IsInvertible := by
  have hv := hasMFDerivAt_opens_val (I := 𝓡 (m + 1)) D.U₁ (D.ch₁.symm z)
  have hc := (D.ch₁.symm.contMDiff.mdifferentiableAt (by simp) (x := z)).hasMFDerivAt
  rw [ι₁_eq_ch₁, (hv.comp z hc).mfderiv]
  exact ContinuousLinearMap.IsInvertible.comp
    ⟨ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (m + 1))), rfl⟩
    ⟨D.ch₁.symm.mfderivToContinuousLinearEquiv (by simp) z, rfl⟩

theorem isInvertible_mfderiv_ι₂ (z : UN e) :
    (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) (ι₂ D.κS) z).IsInvertible := by
  have hv := hasMFDerivAt_opens_val (I := 𝓡 (m + 1)) D.U₂ (D.ch₂.symm z)
  have hc := (D.ch₂.symm.contMDiff.mdifferentiableAt (by simp) (x := z)).hasMFDerivAt
  rw [ι₂_eq_ch₂, (hv.comp z hc).mfderiv]
  exact ContinuousLinearMap.IsInvertible.comp
    ⟨ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (m + 1))), rfl⟩
    ⟨D.ch₂.symm.mfderivToContinuousLinearEquiv (by simp) z, rfl⟩

theorem isInvertible_mfderiv_diskCoord {b : ℝ} [Fact (0 < b)] (hb : b < π)
    (y : CDisk (m + 1) b) :
    (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (D.diskCoord b) y).IsInvertible := by
  have hy := norm_Lr_lt (e := e) hb y
  have h1 := ((contMDiff_val_disk b).mdifferentiableAt (by simp) (x := y)).hasMFDerivAt
  have h2 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, Vs e) (Lr m e) y.1
      ((Lr m e).toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] Vs e) :=
    ((Lr m e).toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] Vs e).hasFDerivAt.hasMFDerivAt
  have h3 : HasMFDerivAt 𝓘(ℝ, Vs e) 𝓘(ℝ, Vs e) (radialR (e := e)) (Lr m e y.1)
      (fderiv ℝ (radialR (e := e)) (Lr m e y.1)) :=
    ((contDiffAt_radialR hy).differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt
  have h4 := ((contMDiff_stG (m := m) D.e_norm).mdifferentiableAt (by simp)
    (x := radialR (Lr m e y.1))).hasMFDerivAt
  have h21 := h2.comp y h1
  have h321 := h3.comp y h21
  have hall := h4.comp (f := radialR ∘ (Lr m e) ∘ Subtype.val) y h321
  rw [show D.diskCoord b = stG D.e_norm ∘ radialR ∘ (Lr m e) ∘ Subtype.val from rfl, hall.mfderiv]
  have hLr : ContinuousLinearMap.IsInvertible
      ((Lr m e).toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] Vs e) :=
    ⟨(Lr m e).toContinuousLinearEquiv, rfl⟩
  exact ContinuousLinearMap.IsInvertible.comp (D.isInvertible_mfderiv_stG _)
    (ContinuousLinearMap.IsInvertible.comp (isInvertible_fderiv_radialR hy)
      (ContinuousLinearMap.IsInvertible.comp hLr (isInvertible_mfderiv_val_disk b y)))

/-- **`jN` is an immersion**, boundary points included: its differential is invertible. -/
theorem isInvertible_mfderiv_jN (a : ℝ) [Fact (0 < a)] [Fact (a < π)] (y : CDisk (m + 1) a) :
    (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (D.jN a) y).IsInvertible := by
  have hd := (D.contMDiff_diskCoord (b := a) Fact.out).mdifferentiableAt (by simp) (x := y)
  have hi := (D.contMDiff_ι₁').mdifferentiableAt (by simp) (x := D.diskCoord a y)
  rw [show D.jN a = ι₁ D.κS ∘ D.diskCoord a from rfl, mfderiv_comp y hi hd]
  exact (D.isInvertible_mfderiv_ι₁ _).comp (D.isInvertible_mfderiv_diskCoord Fact.out y)

/-- **`jS` is an immersion**, boundary points included. -/
theorem isInvertible_mfderiv_jS (a : ℝ) [Fact (0 < a)] [Fact (a < π)]
    (y : CDisk (m + 1) (π - a)) :
    (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (D.jS a) y).IsInvertible := by
  have hb : π - a < π := by linarith [(Fact.out : 0 < a)]
  have hd := (D.contMDiff_diskCoord hb).mdifferentiableAt (by simp) (x := y)
  have hi := (D.contMDiff_ι₂').mdifferentiableAt (by simp) (x := D.diskCoord (π - a) y)
  rw [show D.jS a = ι₂ D.κS ∘ D.diskCoord (π - a) from rfl, mfderiv_comp y hi hd]
  exact (D.isInvertible_mfderiv_ι₂ _).comp (D.isInvertible_mfderiv_diskCoord hb y)

/-! ### Closed embeddings onto `D_N`, `D_S` -/

theorem jN_injective {a : ℝ} (ha0 : 0 < a) (haπ : a < π) : Injective (D.jN a) := by
  intro y y' h
  rw [D.jN_eq ha0 haπ, D.jN_eq ha0 haπ] at h
  exact toDiskE_injective ha0.le (D.diskMapN_injective haπ h)

theorem jS_injective {a : ℝ} (ha0 : 0 < a) (haπ : a < π) : Injective (D.jS a) := by
  intro y y' h
  rw [D.jS_eq ha0 haπ, D.jS_eq ha0 haπ] at h
  exact toDiskE_injective _ (D.diskMapS_injective ha0 h)

theorem range_jN {a : ℝ} (ha0 : 0 < a) (haπ : a < π) : range (D.jN a) = D.DN a := by
  rw [D.DN_eq haπ]
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨toDiskE ha0.le y, (D.jN_eq ha0 haπ y).symm⟩
  · rintro ⟨Y, rfl⟩
    obtain ⟨y, rfl⟩ := toDiskE_surjective (m := m) ha0.le Y
    exact ⟨y, D.jN_eq ha0 haπ y⟩

theorem range_jS {a : ℝ} (ha0 : 0 < a) (haπ : a < π) : range (D.jS a) = D.DS a := by
  rw [D.DS_eq ha0]
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨toDiskE _ y, (D.jS_eq ha0 haπ y).symm⟩
  · rintro ⟨Y, rfl⟩
    obtain ⟨y, rfl⟩ := toDiskE_surjective (m := m) (sub_pos.2 haπ).le Y
    exact ⟨y, D.jS_eq ha0 haπ y⟩

/-- **`jN` is a closed embedding.** -/
theorem isClosedEmbedding_jN (a : ℝ) [Fact (0 < a)] [Fact (a < π)] :
    Topology.IsClosedEmbedding (D.jN a) :=
  (D.contMDiff_jN a).continuous.isClosedEmbedding (D.jN_injective Fact.out Fact.out)

/-- **`jS` is a closed embedding.** -/
theorem isClosedEmbedding_jS (a : ℝ) [Fact (0 < a)] [Fact (a < π)] :
    Topology.IsClosedEmbedding (D.jS a) :=
  (D.contMDiff_jS a).continuous.isClosedEmbedding (D.jS_injective Fact.out Fact.out)

/-! ### The boundary identification -/

/-- A point of `D_N` that is also in `D_S` lies on the boundary sphere, glued by `σ`. -/
theorem diskRel_of_eq {a : ℝ} (ha0 : 0 < a) (haπ : a < π) (Y : Disk e a) (Y' : Disk e (π - a))
    (hYY : D.diskMapN haπ Y = D.diskMapS ha0 Y') : D.DiskRel ha0 (.inl Y) (.inr Y') := by
  obtain ⟨hs, hκ⟩ := ι₁_eq_ι₂.1 hYY
  have hY0 : (Y : W) ≠ 0 := by
    intro h0
    apply hs
    show ζU (D.diskPt Y (Disk_inner Y) _) = e
    rw [ζU_diskPt, h0, expN_zero]
  have hYπ := lt_of_le_of_lt (Disk_norm Y) haπ
  have hs' : ζ0 (D.diskPt Y (Disk_inner Y) hYπ, (1 : Metric.sphere (0 : Quaternion ℝ) 1)) ≠ e := hs
  have hY'π : ‖(Y' : W)‖ < π := by linarith [(Disk_norm Y')]
  have ht : π - ‖(Y : W)‖ = ‖(Y' : W)‖ := by
    have h1 := D.polarT_κS (D.diskPt Y (Disk_inner Y) hYπ) hs'
    rw [hκ, D.polarT_diskPt, D.polarT_diskPt] at h1
    linarith
  have hnY : ‖(Y : W)‖ = a := le_antisymm (Disk_norm Y) (by linarith [(Disk_norm Y')])
  refine ⟨hnY, ?_⟩
  have hY'0 : (Y' : W) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at ht; linarith
  have h2 := D.polarX_κS (D.diskPt Y (Disk_inner Y) hYπ) hs'
  rw [hκ, ζU_diskPt, polarX_expN D.e_norm (Disk_inner Y') hY'0 hY'π,
    D.xS_diskPt Y (Disk_inner Y) hYπ hY0] at h2
  have hn' : ‖(Y' : W)‖ = π - a := by rw [← ht, hnY]
  calc (Y' : W) = ‖(Y' : W)‖ • (‖(Y' : W)‖⁻¹ • (Y' : W)) :=
        (smul_inv_smul₀ (norm_ne_zero_iff.2 hY'0) _).symm
    _ = _ := by rw [h2, hn']

/-- **(3), the gluing relation**: `jN y = jS y'` iff `y ∈ ∂𝔻(a)` and `y' = (π − a) σ(y/a)`
(`DiskRel`, [D] `eq:sigma`). -/
theorem jN_eq_jS_iff {a : ℝ} (ha0 : 0 < a) (haπ : a < π) (y : CDisk (m + 1) a)
    (y' : CDisk (m + 1) (π - a)) :
    D.jN a y = D.jS a y' ↔
      D.DiskRel ha0 (.inl (toDiskE ha0.le y)) (.inr (toDiskE (sub_pos.2 haπ).le y')) := by
  rw [D.jN_eq ha0 haπ, D.jS_eq ha0 haπ]
  exact ⟨D.diskRel_of_eq ha0 haπ _ _, D.boundary_glue ha0 haπ _ _⟩

/-- **(3), the cover**: `X = jN(𝔻(a)) ∪ jS(𝔻(π − a))`. -/
theorem range_jN_union_range_jS {a : ℝ} (ha0 : 0 < a) (haπ : a < π) :
    range (D.jN a) ∪ range (D.jS a) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨q, rfl⟩ := D.diskGlueMap_surjective ha0 haπ x
  induction q using Quot.ind with
  | mk q =>
  rcases q with Y | Y
  · obtain ⟨y, rfl⟩ := toDiskE_surjective (m := m) ha0.le Y
    exact Or.inl ⟨y, D.jN_eq ha0 haπ y⟩
  · obtain ⟨y, rfl⟩ := toDiskE_surjective (m := m) (sub_pos.2 haπ).le Y
    exact Or.inr ⟨y, D.jS_eq ha0 haπ y⟩

/-- The southern partner `(π − a) σ(Y/a)` of a boundary point `Y` of the northern disk. -/
def partnerS {a : ℝ} (ha0 : 0 < a) (haπ : a < π) (Y : Disk e a) (hY : ‖(Y : W)‖ = a) :
    Disk e (π - a) :=
  ⟨(π - a) • ((D.sigmaV (angS Y (Disk_inner Y) (fun h0 => by
      rw [h0, norm_zero] at hY; linarith)) : Vs e) : W), by
    rw [real_inner_smul_left, inner_Vs_e, mul_zero], by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.2 haπ),
      show ‖((D.sigmaV _ : Vs e) : W)‖ = 1 from mem_sphere_zero_iff_norm.1 (D.sigmaV _).2,
      mul_one]⟩

/-- **The boundary of `𝔻(a)` is mapped onto the equator**: `y ∈ ∂𝔻(a)` (manifold boundary)
iff `jN y ∈ D_S`, i.e. iff `jN y ∈ D_N ∩ D_S`. -/
theorem isBoundaryPoint_iff_jN_mem_DS (a : ℝ) [Fact (0 < a)] [Fact (a < π)]
    (y : CDisk (m + 1) a) :
    (𝓡∂ (m + 1)).IsBoundaryPoint y ↔ D.jN a y ∈ D.DS a := by
  have ha0 : 0 < a := Fact.out
  have haπ : a < π := Fact.out
  rw [isBoundaryPoint_disk_iff, D.DS_eq ha0]
  constructor
  · intro hy
    have hY : ‖((toDiskE (e := e) ha0.le y : Disk e a) : W)‖ = a := by
      show ‖((Lr m e y.1 : Vs e) : W)‖ = a
      rw [norm_Lr]; exact hy
    refine ⟨D.partnerS ha0 haπ _ hY, ?_⟩
    rw [D.jN_eq ha0 haπ]
    exact (D.boundary_glue ha0 haπ _ _ ⟨hY, rfl⟩).symm
  · rintro ⟨Y', hY'⟩
    rw [D.jN_eq ha0 haπ] at hY'
    obtain ⟨hn, -⟩ := D.diskRel_of_eq ha0 haπ _ _ hY'.symm
    rw [← norm_Lr (e := e)]
    exact hn

/-- **The boundary of `𝔻(π − a)` is mapped onto the equator.** -/
theorem isBoundaryPoint_iff_jS_mem_DN (a : ℝ) [Fact (0 < a)] [Fact (a < π)]
    (y : CDisk (m + 1) (π - a)) :
    (𝓡∂ (m + 1)).IsBoundaryPoint y ↔ D.jS a y ∈ D.DN a := by
  have ha0 : 0 < a := Fact.out
  have haπ : a < π := Fact.out
  rw [isBoundaryPoint_disk_iff, ← D.range_jN ha0 haπ]
  constructor
  · intro hy
    -- `y = (π − a) σ(y_N)` for `y_N := σ̂(y/(π − a))`
    have hb : 0 < π - a := sub_pos.2 haπ
    set Y' := toDiskE (e := e) hb.le y
    have hY' : ‖(Y' : W)‖ = π - a := by
      show ‖((Lr m e y.1 : Vs e) : W)‖ = π - a
      rw [norm_Lr]; exact hy
    have hY'0 : (Y' : W) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hY'; linarith
    set v := D.sigmaHatV (angS Y' (Disk_inner Y') hY'0)
    have hv : ‖((v : Vs e) : W)‖ = 1 := mem_sphere_zero_iff_norm.1 v.2
    have hYN : ‖(a • ((v : Vs e) : W))‖ = a := by
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos ha0]
    set YN : Disk e a := ⟨a • ((v : Vs e) : W),
      by rw [real_inner_smul_left, inner_Vs_e, mul_zero], hYN.le⟩
    obtain ⟨y₀, hy₀⟩ := toDiskE_surjective (m := m) ha0.le YN
    refine ⟨y₀, ?_⟩
    rw [D.jN_eq_jS_iff ha0 haπ, hy₀]
    refine ⟨hYN, ?_⟩
    have hang : angS (YN : W) (Disk_inner YN) (fun h0 => by
        have h1 : ‖((YN : Disk e a) : W)‖ = a := hYN
        rw [h0, norm_zero] at h1; linarith) = v := by
      apply Subtype.ext; apply Subtype.ext
      show ‖a • ((v : Vs e) : W)‖⁻¹ • (a • ((v : Vs e) : W)) = ((v : Vs e) : W)
      rw [hYN, inv_smul_smul₀ ha0.ne']
    show (Y' : W) = (π - a) • ((D.sigmaV (angS (YN : W) (Disk_inner YN) _) : Vs e) : W)
    rw [hang, D.sigmaV_sigmaHatV]
    show (Y' : W) = (π - a) • (‖(Y' : W)‖⁻¹ • (Y' : W))
    rw [hY', smul_inv_smul₀ hb.ne']
  · rintro ⟨y₀, hy₀⟩
    obtain ⟨hn, h⟩ := (D.jN_eq_jS_iff ha0 haπ y₀ y).1 hy₀
    have h' : ‖((Lr m e y.1 : Vs e) : W)‖ = π - a := by
      have := congrArg norm h
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.2 haπ),
        show ‖((D.sigmaV _ : Vs e) : W)‖ = 1 from mem_sphere_zero_iff_norm.1 (D.sigmaV _).2,
        mul_one] at this
      exact this
    rw [← norm_Lr (e := e)]; exact h'

/-- **[D] `lem:attaching` (1) and (3), smooth form.** For `0 < a < π`:
* `jN : 𝔻(a) → X` and `jS : 𝔻(π − a) → X` are smooth maps of manifolds with boundary, with
  invertible differentials everywhere, and closed embeddings with images `D_N`, `D_S`;
* the manifold boundary of each disk is mapped onto the equator `D_N ∩ D_S`;
* `X = D_N ∪ D_S`, and `jN y = jS y'` iff `(y, y')` are related by the boundary map `σ`.
-/
theorem lem_attaching_smooth (a : ℝ) [Fact (0 < a)] [Fact (a < π)] :
    (ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (D.jN a) ∧
      (∀ y, (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (D.jN a) y).IsInvertible) ∧
      Topology.IsClosedEmbedding (D.jN a) ∧ range (D.jN a) = D.DN a ∧
      ∀ y, (𝓡∂ (m + 1)).IsBoundaryPoint y ↔ D.jN a y ∈ D.DS a) ∧
    (ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (D.jS a) ∧
      (∀ y, (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (D.jS a) y).IsInvertible) ∧
      Topology.IsClosedEmbedding (D.jS a) ∧ range (D.jS a) = D.DS a ∧
      ∀ y, (𝓡∂ (m + 1)).IsBoundaryPoint y ↔ D.jS a y ∈ D.DN a) ∧
    range (D.jN a) ∪ range (D.jS a) = univ ∧
    ∀ y y', D.jN a y = D.jS a y' ↔
      D.DiskRel Fact.out (.inl (toDiskE (Fact.out : 0 < a).le y))
        (.inr (toDiskE (sub_pos.2 (Fact.out : a < π)).le y')) :=
  ⟨⟨D.contMDiff_jN a, D.isInvertible_mfderiv_jN a, D.isClosedEmbedding_jN a,
      D.range_jN Fact.out Fact.out, D.isBoundaryPoint_iff_jN_mem_DS a⟩,
    ⟨D.contMDiff_jS a, D.isInvertible_mfderiv_jS a, D.isClosedEmbedding_jS a,
      D.range_jS Fact.out Fact.out, D.isBoundaryPoint_iff_jS_mem_DN a⟩,
    D.range_jN_union_range_jS Fact.out Fact.out, D.jN_eq_jS_iff Fact.out Fact.out⟩

end PolarData

end Attach

section Model

instance fact_pi_half_pos : Fact (0 < π / 2) := ⟨by positivity⟩

instance fact_pi_half_lt : Fact (π / 2 < π) := ⟨by linarith [pi_pos]⟩

/-- **Non-vacuity**: every hypothesis is met by the model polar data, with `a = π/2`. -/
example (m : ℕ) := (trivialPolarData m).lem_attaching_smooth (π / 2)

end Model

end

end ExoticSpheres8And10
