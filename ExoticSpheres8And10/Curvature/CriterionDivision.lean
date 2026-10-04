/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # A5/A6: dividing the curvature numerator by the area

[GG] §4.3: a two-plane is positively curved iff `𝒦(P, Q) > 0`, where the sectional curvature is
`𝒦(P,Q) / (g(P,P) g(Q,Q) − g(P,Q)²)`. A6 proves `𝒦 > 0` for every independent horizontal pair;
this file supplies the division step: for a symmetric positive-definite bilinear form `g`
(the metric on the tangent space), the squared area of an independent pair is positive, so the
sectional curvature has the sign of `𝒦`.
-/

namespace ExoticSpheres8And10

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- **The squared area of an independent pair is positive** (strict Cauchy–Schwarz for a
positive-definite symmetric bilinear form). -/
theorem area_pos (g : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ u v, g u v = g v u)
    (hpos : ∀ u, u ≠ 0 → 0 < g u u) {P Q : W} (hind : LinearIndependent ℝ ![P, Q]) :
    0 < g P P * g Q Q - g P Q ^ 2 := by
  have hQ : Q ≠ 0 := hind.ne_zero 1
  have hc : 0 < g Q Q := hpos Q hQ
  set t := -(g P Q / g Q Q)
  have hne : P + t • Q ≠ 0 := by
    intro h
    have := (LinearIndependent.pair_iff.1 hind) 1 t (by simpa using h)
    exact one_ne_zero this.1
  have h := hpos _ hne
  have hexp : g (P + t • Q) (P + t • Q) = g P P + 2 * t * g P Q + t ^ 2 * g Q Q := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm Q P]
    ring
  rw [hexp] at h
  have ht : t * g Q Q = -g P Q := by
    simp only [t]; field_simp
  have : 0 < (g P P + 2 * t * g P Q + t ^ 2 * g Q Q) * g Q Q := mul_pos h hc
  nlinarith [this, ht]

/-- **The sectional curvature has the sign of the numerator:** for an independent pair,
`𝒦 / area > 0 ↔ 𝒦 > 0`. -/
theorem sectional_pos_iff (g : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ u v, g u v = g v u)
    (hpos : ∀ u, u ≠ 0 → 0 < g u u) {P Q : W} (hind : LinearIndependent ℝ ![P, Q]) (𝒦 : ℝ) :
    0 < 𝒦 / (g P P * g Q Q - g P Q ^ 2) ↔ 0 < 𝒦 :=
  div_pos_iff_of_pos_right (area_pos g hsymm hpos hind)

/-- The dot product on `ℝ²`. -/
noncomputable def dotR2 : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => u.1 * v.1 + u.2 * v.2) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- Non-vacuity: the hypotheses of `area_pos` hold for the dot product on `ℝ²` and the
standard basis. -/
theorem area_pos_model :
    0 < dotR2 (1, 0) (1, 0) * dotR2 (0, 1) (0, 1) - dotR2 (1, 0) (0, 1) ^ 2 :=
  area_pos dotR2 (fun u v => by simp only [dotR2, LinearMap.mk₂_apply]; ring)
    (fun u hu => by
      simp only [dotR2, LinearMap.mk₂_apply]
      rcases u with ⟨a, b⟩
      have : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h; push_neg at h; exact hu (by simp [h.1, h.2])
      rcases this with h | h
      · nlinarith [mul_self_pos.2 h, mul_self_nonneg b]
      · nlinarith [mul_self_pos.2 h, mul_self_nonneg a])
    (LinearIndependent.pair_iff.2 fun s t h => by simpa [Prod.ext_iff] using h)

end ExoticSpheres8And10
