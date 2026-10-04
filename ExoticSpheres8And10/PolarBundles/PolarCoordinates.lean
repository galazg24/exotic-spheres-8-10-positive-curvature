/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # §2: geodesic polar coordinates on `S(W)` and the caps as closed disks

[GG] §2: "Every `ζ ∈ S^n ∖ {o_N, o_S}` can be written
uniquely as `ζ = (cos t)e + (sin t)x`, `0 < t < π`, `x ∈ S(V)`. [...] Since `ρ` fixes `e` and
preserves `V`, it preserves the radial coordinate `t` and acts on the angular variable through
`ρ|_V`." And: "We identify `U_α` with the closed disk of radius `R_α` in `V` by the
geodesic-polar coordinates `ζ_N = t x`, `ζ_S = (π − t) x`."

`W` is any real inner product space with a unit vector `e`; `V = e^⊥`.

* `polar_decomp`, `polarX_mem`, `polar_unique`: existence and uniqueness of `(t, x)`;
* `polarT_map`, `polarX_map`: a linear isometry fixing `e` preserves `t` and acts on `x`;
* `capHomeo`: for `0 ≤ a < π` and `W` finite-dimensional, `{ζ ∈ S(W) : t(ζ) ≤ a}` is
  homeomorphic to the closed disk `{Y ∈ V : ‖Y‖ ≤ a}` via `ζ ↦ t x`, with inverse
  `Y ↦ cos‖Y‖ e + sin‖Y‖ Y/‖Y‖`; the southern cap is the same statement for `−e`
  (`diskN_neg`: `ζ_S` for `e` is `ζ_N` for `−e`).
-/

namespace ExoticSpheres8And10

open Real Set Filter Topology Metric

open scoped RealInnerProductSpace

section Polar

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W)

/-- The radial coordinate `t = arccos⟪ζ, e⟫` (geodesic distance from `e` on the sphere). -/
noncomputable def polarT (ζ : W) : ℝ := arccos ⟪ζ, e⟫

/-- The angular coordinate `x = (ζ − cos t e)/sin t` (junk `0` at the poles). -/
noncomputable def polarX (ζ : W) : W := (sin (polarT e ζ))⁻¹ • (ζ - cos (polarT e ζ) • e)

/-- `ζ_N = t x`. -/
noncomputable def diskN (ζ : W) : W := polarT e ζ • polarX e ζ

/-- `Y ↦ cos‖Y‖ e + sin‖Y‖ Y/‖Y‖`, the inverse of `ζ_N`. -/
noncomputable def expN (Y : W) : W := cos ‖Y‖ • e + sin ‖Y‖ • (‖Y‖⁻¹ • Y)

variable {e}

/-! ### Equivariance (no hypothesis on `e` needed) -/

theorem polarT_map (R : W →ₗᵢ[ℝ] W) (hR : R e = e) (ζ : W) : polarT e (R ζ) = polarT e ζ := by
  rw [polarT, polarT, ← R.inner_map_map ζ e, hR]

theorem polarX_map (R : W →ₗᵢ[ℝ] W) (hR : R e = e) (ζ : W) :
    polarX e (R ζ) = R (polarX e ζ) := by
  rw [polarX, polarX, polarT_map R hR, map_smul, map_sub, map_smul, hR]

theorem diskN_map (R : W →ₗᵢ[ℝ] W) (hR : R e = e) (ζ : W) : diskN e (R ζ) = R (diskN e ζ) := by
  rw [diskN, diskN, polarT_map R hR, polarX_map R hR, map_smul]

theorem inner_map_e (R : W →ₗᵢ[ℝ] W) (hR : R e = e) {x : W} (hx : ⟪x, e⟫ = 0) :
    ⟪R x, e⟫ = 0 := by
  rw [← hR, R.inner_map_map, hx]

/-! ### Existence and uniqueness -/

variable (he : ‖e‖ = 1)
include he

theorem inner_bounds {ζ : W} (hζ : ‖ζ‖ = 1) : -1 ≤ ⟪ζ, e⟫ ∧ ⟪ζ, e⟫ ≤ 1 := by
  have := abs_real_inner_le_norm ζ e
  rw [hζ, he, one_mul] at this
  exact abs_le.1 this

theorem inner_ne_one {ζ : W} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ e) : ⟪ζ, e⟫ ≠ 1 := by
  intro h
  apply h1
  have : ‖ζ - e‖ ^ 2 = 0 := by rw [norm_sub_sq_real, hζ, he, h]; ring
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

theorem inner_ne_neg_one {ζ : W} (hζ : ‖ζ‖ = 1) (h2 : ζ ≠ -e) : ⟪ζ, e⟫ ≠ -1 := by
  intro h
  apply h2
  have : ‖ζ + e‖ ^ 2 = 0 := by rw [norm_add_sq_real, hζ, he, h]; ring
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

theorem cos_polarT {ζ : W} (hζ : ‖ζ‖ = 1) : cos (polarT e ζ) = ⟪ζ, e⟫ :=
  cos_arccos (inner_bounds he hζ).1 (inner_bounds he hζ).2

theorem polarT_mem {ζ : W} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ e) (h2 : ζ ≠ -e) :
    0 < polarT e ζ ∧ polarT e ζ < π :=
  ⟨arccos_pos.2 (lt_of_le_of_ne (inner_bounds he hζ).2 (inner_ne_one he hζ h1)),
    arccos_lt_pi.2 (lt_of_le_of_ne' (inner_bounds he hζ).1 (inner_ne_neg_one he hζ h2))⟩

theorem sin_polarT_pos {ζ : W} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ e) (h2 : ζ ≠ -e) :
    0 < sin (polarT e ζ) :=
  sin_pos_of_pos_of_lt_pi (polarT_mem he hζ h1 h2).1 (polarT_mem he hζ h1 h2).2

theorem sin_polarT_sq {ζ : W} (hζ : ‖ζ‖ = 1) : sin (polarT e ζ) ^ 2 = 1 - ⟪ζ, e⟫ ^ 2 := by
  rw [sin_sq, cos_polarT he hζ]

/-- `x ∈ V`. -/
theorem inner_polarX {ζ : W} (hζ : ‖ζ‖ = 1) : ⟪polarX e ζ, e⟫ = 0 := by
  rw [polarX, inner_smul_left, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, he,
    cos_polarT he hζ]
  simp

/-- `‖x‖ = 1`, i.e. `x ∈ S(V)`. -/
theorem norm_polarX {ζ : W} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ e) (h2 : ζ ≠ -e) : ‖polarX e ζ‖ = 1 := by
  have hs := sin_polarT_pos he hζ h1 h2
  have hsq : ‖ζ - cos (polarT e ζ) • e‖ ^ 2 = sin (polarT e ζ) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hζ, he, cos_polarT he hζ,
      sin_polarT_sq he hζ, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hn : ‖ζ - cos (polarT e ζ) • e‖ = sin (polarT e ζ) :=
    (pow_left_inj₀ (norm_nonneg _) hs.le two_ne_zero).1 hsq
  rw [polarX, norm_smul, hn, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_cancel₀ hs.ne']

/-- **Existence:** `ζ = (cos t)e + (sin t)x`. -/
theorem polar_decomp {ζ : W} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ e) (h2 : ζ ≠ -e) :
    ζ = cos (polarT e ζ) • e + sin (polarT e ζ) • polarX e ζ := by
  rw [polarX, smul_smul, mul_inv_cancel₀ (sin_polarT_pos he hζ h1 h2).ne', one_smul,
    add_sub_cancel]

/-- **Uniqueness:** if `ζ = (cos t)e + (sin t)x` with `0 < t < π` and `x ⊥ e`, then `t` and `x`
are the polar coordinates of `ζ`. -/
theorem polar_unique {ζ x : W} {t : ℝ} (ht0 : 0 < t) (htπ : t < π) (hx : ⟪x, e⟫ = 0)
    (hζ : ζ = cos t • e + sin t • x) : polarT e ζ = t ∧ polarX e ζ = x := by
  have hin : ⟪ζ, e⟫ = cos t := by
    rw [hζ, inner_add_left, real_inner_smul_left, real_inner_smul_left, hx,
      real_inner_self_eq_norm_sq, he]
    ring
  have hT : polarT e ζ = t := by rw [polarT, hin, arccos_cos ht0.le htπ.le]
  refine ⟨hT, ?_⟩
  rw [polarX, hT, hζ, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (sin_pos_of_pos_of_lt_pi ht0 htπ).ne', one_smul]

theorem polarT_e : polarT e e = 0 := by
  rw [polarT, real_inner_self_eq_norm_sq, he, one_pow, arccos_one]

theorem polarT_neg_e : polarT e (-e) = π := by
  rw [polarT, inner_neg_left, real_inner_self_eq_norm_sq, he, one_pow, arccos_neg_one]

theorem diskN_e : diskN e e = 0 := by rw [diskN, polarT_e he, zero_smul]

/-- `ζ_N ∈ V`. -/
theorem inner_diskN {ζ : W} (hζ : ‖ζ‖ = 1) : ⟪diskN e ζ, e⟫ = 0 := by
  rw [diskN, real_inner_smul_left, inner_polarX he hζ, mul_zero]

/-- `‖ζ_N‖ = t`. -/
theorem norm_diskN {ζ : W} (hζ : ‖ζ‖ = 1) (h2 : ζ ≠ -e) : ‖diskN e ζ‖ = polarT e ζ := by
  by_cases h1 : ζ = e
  · rw [h1, diskN_e he, norm_zero, polarT_e he]
  rw [diskN, norm_smul, norm_polarX he hζ h1 h2, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ polarT e ζ from arccos_nonneg _)]

omit he in
theorem expN_zero : expN e 0 = e := by simp [expN]

theorem norm_expN {Y : W} (hY : ⟪Y, e⟫ = 0) : ‖expN e Y‖ = 1 := by
  by_cases h0 : Y = 0
  · rw [h0, expN_zero, he]
  have hn : 0 < ‖Y‖ := norm_pos_iff.2 h0
  have hsq : ‖expN e Y‖ ^ 2 = 1 := by
    rw [expN, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_comm, hY, norm_smul, norm_smul, norm_smul, he,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hn,
      inv_mul_cancel₀ hn.ne']
    simp only [mul_zero, mul_one, sq_abs, add_zero]
    rw [cos_sq_add_sin_sq]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [hsq, one_pow])

theorem expN_diskN {ζ : W} (hζ : ‖ζ‖ = 1) (h2 : ζ ≠ -e) : expN e (diskN e ζ) = ζ := by
  by_cases h1 : ζ = e
  · rw [h1, diskN_e he, expN_zero]
  have ht := polarT_mem he hζ h1 h2
  rw [expN, norm_diskN he hζ h2, diskN, inv_smul_smul₀ ht.1.ne']
  exact (polar_decomp he hζ h1 h2).symm

theorem polarT_expN {Y : W} (hY : ⟪Y, e⟫ = 0) (hYπ : ‖Y‖ < π) : polarT e (expN e Y) = ‖Y‖ := by
  by_cases h0 : Y = 0
  · rw [h0, expN_zero, polarT_e he, norm_zero]
  have hn : 0 < ‖Y‖ := norm_pos_iff.2 h0
  exact (polar_unique he (ζ := expN e Y) (x := ‖Y‖⁻¹ • Y) hn hYπ
    (by rw [real_inner_smul_left, hY, mul_zero]) rfl).1

theorem diskN_expN {Y : W} (hY : ⟪Y, e⟫ = 0) (hYπ : ‖Y‖ < π) : diskN e (expN e Y) = Y := by
  by_cases h0 : Y = 0
  · rw [h0, expN_zero, diskN_e he]
  have hn : 0 < ‖Y‖ := norm_pos_iff.2 h0
  obtain ⟨hT, hX⟩ := polar_unique he (ζ := expN e Y) (x := ‖Y‖⁻¹ • Y) hn hYπ
    (by rw [real_inner_smul_left, hY, mul_zero]) rfl
  rw [diskN, hT, hX, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

omit he in
/-- `expN` is continuous, including at `0`: `sin‖Y‖ Y/‖Y‖ = sinc(‖Y‖) Y`. -/
theorem continuous_expN : Continuous (expN e) := by
  have hds : Continuous (dslope sin (0 : ℝ)) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope univ_mem).2 ⟨continuous_sin.continuousOn,
      differentiable_sin 0⟩
  have heq : expN e = fun Y => cos ‖Y‖ • e + dslope sin 0 ‖Y‖ • Y := by
    funext Y
    by_cases h0 : Y = 0
    · simp [expN, h0]
    rw [expN, dslope_of_ne _ (norm_ne_zero_iff.2 h0), slope_def_field, sin_zero, sub_zero,
      sub_zero, smul_smul, div_eq_mul_inv]
  rw [heq]
  exact ((continuous_cos.comp continuous_norm).smul continuous_const).add
    ((hds.comp continuous_norm).smul continuous_id)

/-! ### The caps as closed disks -/

omit he in
/-- `ζ_S = (π − t) x` for `e` is `ζ_N` for `−e`: the southern cap is the northern cap of `−e`. -/
theorem diskN_neg (ζ : W) : diskN (-e) ζ = (π - polarT e ζ) • polarX e ζ := by
  have hT : polarT (-e) ζ = π - polarT e ζ := by rw [polarT, polarT, inner_neg_right, arccos_neg]
  rw [diskN, polarX, polarX, hT, sin_pi_sub, cos_pi_sub, neg_smul, smul_neg, neg_neg]

omit he in
theorem polarT_neg (ζ : W) : polarT (-e) ζ = π - polarT e ζ := by
  rw [polarT, polarT, inner_neg_right, arccos_neg]

/-- The cap `{ζ ∈ S(W) : t(ζ) ≤ a}`. -/
def Cap (e : W) (a : ℝ) : Set W := {ζ | ‖ζ‖ = 1 ∧ polarT e ζ ≤ a}

/-- The closed disk `{Y ∈ V : ‖Y‖ ≤ a}`. -/
def Disk (e : W) (a : ℝ) : Set W := {Y | ⟪Y, e⟫ = 0 ∧ ‖Y‖ ≤ a}

omit he in
theorem isCompact_Disk [FiniteDimensional ℝ W] (a : ℝ) : IsCompact (Disk e a) := by
  have : Disk e a = closedBall 0 a ∩ {Y | ⟪Y, e⟫ = 0} := by
    ext Y; simp [Disk, and_comm]
  rw [this]
  exact (isCompact_closedBall 0 a).inter_right
    (isClosed_eq (f := fun Y : W => ⟪Y, e⟫) (g := fun _ => (0 : ℝ)) (by fun_prop) continuous_const)

/-- **The cap is the closed disk** (as sets, via `ζ_N` and its inverse). -/
noncomputable def capEquiv {a : ℝ} (ha0 : 0 ≤ a) (haπ : a < π) : Disk e a ≃ Cap e a where
  toFun Y := ⟨expN e Y, norm_expN he Y.2.1, by
    rw [polarT_expN he Y.2.1 (lt_of_le_of_lt Y.2.2 haπ)]; exact Y.2.2⟩
  invFun ζ := ⟨diskN e ζ, inner_diskN he ζ.2.1, by
    have h2 : (ζ : W) ≠ -e := fun h => by
      have := ζ.2.2; rw [h, polarT_neg_e he] at this; linarith
    rw [norm_diskN he ζ.2.1 h2]; exact ζ.2.2⟩
  left_inv Y := Subtype.ext (diskN_expN he Y.2.1 (lt_of_le_of_lt Y.2.2 haπ))
  right_inv ζ := Subtype.ext (expN_diskN he ζ.2.1 fun h => by
    have := ζ.2.2; rw [h, polarT_neg_e he] at this; linarith)

/-- **[GG] §2: the cap `U_N = {t ≤ a}` is homeomorphic to the closed disk of radius `a` in `V`**
via `Y ↦ cos‖Y‖ e + sin‖Y‖ Y/‖Y‖`, with inverse `ζ ↦ ζ_N = t x`. -/
noncomputable def capHomeo [FiniteDimensional ℝ W] {a : ℝ} (ha0 : 0 ≤ a) (haπ : a < π) :
    Disk e a ≃ₜ Cap e a :=
  haveI : CompactSpace (Disk e a) := isCompact_iff_compactSpace.1 (isCompact_Disk a)
  Continuous.homeoOfEquivCompactToT2 (f := capEquiv he ha0 haπ) (by
    apply Continuous.subtype_mk
    exact continuous_expN.comp continuous_subtype_val)

theorem capHomeo_symm_apply [FiniteDimensional ℝ W] {a : ℝ} (ha0 : 0 ≤ a) (haπ : a < π)
    (ζ : Cap e a) : ((capHomeo he ha0 haπ).symm ζ : W) = diskN e ζ := rfl

omit he in
/-- The caps are invariant under linear isometries fixing `e`. -/
theorem cap_map (R : W →ₗᵢ[ℝ] W) (hR : R e = e) {a : ℝ} {ζ : W} (hζ : ζ ∈ Cap e a) :
    R ζ ∈ Cap e a :=
  ⟨by rw [R.norm_map]; exact hζ.1, by rw [polarT_map R hR]; exact hζ.2⟩

end Polar

end ExoticSpheres8And10
