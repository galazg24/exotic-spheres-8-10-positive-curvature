/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Gluing.Charts

/-! # §4: the chart transition of `X` near the gluing sphere

On the overlap `U₁ ∩ U₂` the two stereographic charts are related by the inversion and the
gauge: **`stD_κS`**: `ψ₂ = τ ∘ inv ∘ ψ₁`, with `inv(y) = 4y/|y|²`. This is [GG]'s
`τ⁻¹ ∘ ψ_S ∘ κ_S = ψ_S ∘ R`, since `R` is the inversion in stereographic coordinates
(`stereo_reflE`), and `ρ(θ(x))⁻¹` is `τ`, because `τ` only sees the direction (`θS_of_dir`).
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

section Transition

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

/-- The inversion `y ↦ 4y/|y|²` of `V`. -/
def invV (y : Vs e) : Vs e := (4 / ‖y‖ ^ 2) • y

theorem norm_sub_inner_sq (he : ‖e‖ = 1) {ζ : W} (hζ : ‖ζ‖ = 1) :
    ‖ζ - ⟪ζ, e⟫ • e‖ ^ 2 = 1 - ⟪ζ, e⟫ ^ 2 := by
  rw [@norm_sub_sq_real, hζ, norm_smul, Real.norm_eq_abs, he, real_inner_smul_right]
  rw [mul_one, sq_abs]; ring

/-- **The reflection is the inversion** in (2-scaled) stereographic coordinates. -/
theorem stereo_reflE (he : ‖e‖ = 1) {ζ : W} (hζ : ‖ζ‖ = 1) (h1 : ⟪ζ, e⟫ ≠ 1)
    (h2 : ⟪ζ, e⟫ ≠ -1) :
    (2 : ℝ) • stereo e (reflE e ζ) =
      (4 / ‖(2 : ℝ) • stereo e ζ‖ ^ 2) • ((2 : ℝ) • stereo e ζ) := by
  set t := ⟪ζ, e⟫ with ht
  have hw := norm_sub_inner_sq he hζ
  rw [← ht] at hw
  have hr : reflE e ζ - ⟪reflE e ζ, e⟫ • e = ζ - t • e := by
    rw [inner_reflE he, reflE]; module
  have hp : 0 < 1 + t := by
    have : -1 ≤ t := by
      have := abs_real_inner_le_norm ζ e; rw [hζ, he] at this; linarith [neg_abs_le t]
    rcases this.lt_or_eq with h | h
    · linarith
    · exact absurd h.symm h2
  have hm : 0 < 1 - t := by
    have : t ≤ 1 := by
      have := real_inner_le_norm ζ e; rw [hζ, he] at this; linarith
    rcases this.lt_or_eq with h | h
    · linarith
    · exact absurd h h1
  rw [stereo, stereo, hr, inner_reflE he, ← ht, norm_smul, norm_smul, mul_pow, mul_pow, hw,
    smul_smul, smul_smul, smul_smul]
  congr 1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have h1t : (1 - t ^ 2) = (1 - t) * (1 + t) := by ring
  rw [h1t]
  have hm' := hm.ne'
  have hp' := hp.ne'
  field_simp
  linear_combination 4 * inv_mul_cancel₀ hm'

theorem inner_ne_one_of_ne (he : ‖e‖ = 1) {ζ : W} (hζ : ‖ζ‖ = 1) (hz : ζ ≠ e) : ⟪ζ, e⟫ ≠ 1 := by
  intro h
  apply hz
  have : ‖ζ - e‖ ^ 2 = 0 := by
    rw [@norm_sub_sq_real, hζ, he, h]; ring
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

theorem neg_one_lt_inner (he : ‖e‖ = 1) {ζ : W} (hζ : ‖ζ‖ = 1) (hz : ⟪ζ, e⟫ ≠ -1) :
    -1 < ⟪ζ, e⟫ := by
  have := abs_real_inner_le_norm ζ e; rw [hζ, he] at this
  exact lt_of_le_of_ne (by linarith [neg_abs_le ⟪ζ, e⟫]) (fun h => hz h.symm)

theorem inner_lt_one (he : ‖e‖ = 1) {ζ : W} (hζ : ‖ζ‖ = 1) (hz : ⟪ζ, e⟫ ≠ 1) : ⟪ζ, e⟫ < 1 := by
  have := real_inner_le_norm ζ e; rw [hζ, he] at this
  exact lt_of_le_of_ne (by linarith) hz

variable (D : PolarData (m := m) e)

namespace PolarData

/-- `τ` only sees the direction: if `u` is a positive multiple of `ζ − ⟪ζ,e⟫e` then
`θ̂(u) = θ(x(ζ))`. -/
theorem θS_of_dir (z : UN e) (hz : ζ0 ((z, (1 : S3)) : M0 e) ≠ e) {u : Vs e} {c : ℝ} (hc : 0 < c)
    (hu : (u : W) = c • (ζU z - ⟪ζU z, e⟫ • e)) : D.θS u = D.gS z hz := by
  have hζ : ‖ζU z‖ = 1 := by simp [ζU]
  have ht1 := inner_ne_one_of_ne D.e_norm hζ hz
  have hlo := neg_one_lt_inner D.e_norm hζ (inner_ζU_ne D.e_norm z)
  have hhi := inner_lt_one D.e_norm hζ ht1
  have hpos : 0 < 1 - ⟪ζU z, e⟫ ^ 2 := by nlinarith
  have hu0 : u ≠ 0 := by
    intro h
    have : ((u : Vs e) : W) = 0 := by rw [h]; rfl
    rw [hu] at this
    have h2 := congrArg (fun w => ‖w‖ ^ 2) this
    simp only [norm_smul, mul_pow, norm_sub_inner_sq D.e_norm hζ, norm_zero] at h2
    have : 0 < ‖c‖ ^ 2 * (1 - ⟪ζU z, e⟫ ^ 2) := by
      have : 0 < ‖c‖ := norm_pos_iff.2 hc.ne'; positivity
    linarith
  rw [θS, dif_neg hu0]
  show D.θ _ = D.θ (D.xS (z, 1) hz)
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  show ‖u‖⁻¹ • (u : W) = pX e (ζU z)
  have hnu : ‖u‖ = c * √(1 - ⟪ζU z, e⟫ ^ 2) := by
    rw [show ‖u‖ = ‖(u : W)‖ from rfl, hu, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      ← Real.sqrt_sq (norm_nonneg (ζU z - ⟪ζU z, e⟫ • e)), norm_sub_inner_sq D.e_norm hζ]
  rw [hnu, hu, pX, smul_smul]
  congr 1
  have : 0 < √(1 - ⟪ζU z, e⟫ ^ 2) := Real.sqrt_pos.2 hpos
  field_simp

/-- **The chart transition**: `ψ₂(κ_Σ z) = τ(inv(ψ₁ z))`. -/
theorem stD_κS (z : UN e) (hz : ζ0 ((z, (1 : S3)) : M0 e) ≠ e) :
    stD (m := m) D.e_norm (D.κS z) = D.τ (invV (stD (m := m) D.e_norm z)) := by
  have hζ : ‖ζU z‖ = 1 := by simp [ζU]
  have h1 : ⟪ζU z, e⟫ ≠ 1 := inner_ne_one_of_ne D.e_norm hζ hz
  have h2 := inner_ζU_ne D.e_norm z
  set g := D.gS z hz
  set y := stD (m := m) D.e_norm z
  have hy : (y : W) = (2 : ℝ) • stereo e (ζU z) := rfl
  -- `θ̂(inv y) = g`
  have hθ : D.θS (invV y) = g := by
    have hp : 0 < 1 + ⟪ζU z, e⟫ := by linarith [neg_one_lt_inner D.e_norm hζ h2]
    have hy0 : 0 < ‖y‖ := by
      rw [norm_pos_iff]
      intro h0
      have : ((y : Vs e) : W) = 0 := by rw [h0]; rfl
      rw [hy, stereo, smul_smul] at this
      rcases smul_eq_zero.1 this with h | h
      · have : (1 + ⟪ζU z, e⟫)⁻¹ ≠ 0 := inv_ne_zero hp.ne'; simp_all
      · exact h1 (by
          have hh := norm_sub_inner_sq D.e_norm hζ
          rw [h, norm_zero] at hh
          nlinarith [sq_nonneg ⟪ζU z, e⟫])
    refine D.θS_of_dir z hz (c := 4 / ‖y‖ ^ 2 * (2 * (1 + ⟪ζU z, e⟫)⁻¹)) (by positivity) ?_
    show (4 / ‖y‖ ^ 2) • (y : W) = _
    rw [hy, stereo, smul_smul, smul_smul, mul_assoc]
  refine Subtype.ext ?_
  show ((stD (m := m) D.e_norm (D.κS z) : Vs e) : W) = D.ρ (D.θS (invV y))⁻¹ ((invV y : Vs e) : W)
  rw [hθ]
  show (2 : ℝ) • stereo e (ζU (D.κS z)) = D.ρ g⁻¹ ((invV y : Vs e) : W)
  have hκ : ζU (D.κS z) = D.ρ g⁻¹ (reflE e (ζU z)) := by
    rw [D.κS_eq z hz]; rfl
  rw [hκ, show D.ρ g⁻¹ (reflE e (ζU z)) = (D.ρ g⁻¹).toLinearIsometry (reflE e (ζU z)) from rfl,
    stereo_map e _ (D.ρ_e _), ← map_smul, stereo_reflE D.e_norm hζ h1 h2]
  show (D.ρ g⁻¹).toLinearIsometry _ = D.ρ g⁻¹ ((4 / ‖y‖ ^ 2) • (y : W))
  rw [show ‖y‖ = ‖(y : W)‖ from rfl, hy]
  rfl

end PolarData

end Transition

end

end ExoticSpheres8And10
