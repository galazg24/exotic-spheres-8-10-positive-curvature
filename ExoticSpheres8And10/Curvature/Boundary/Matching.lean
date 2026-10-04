/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.GaugeProduct

/-! # §4.4: matching two warped star quotients along a sphere

Two warped products `GW β₁ w₁` and `GW β₂ w₂` on `V × S³`, with the same star action, compared
at `Y` and at `λY` (`λ > 0`), where:
- `β₂(λY)(λa, λb) = β₁(Y)(a, b)` for `a, b ⊥ Y`;
- `w₂(λY) = w₁(Y)`.

* `KY_smul`: `K_{λY} = λK_Y`;
* **`hlift_match`**: for `c ⊥ Y`, `hlift₂(λc) = (λ·ĉ₁, ĉ₂)` with `ĉ = hlift₁(c)`;
* **`gB_match`**: `g₂(λY)(λc, λc') = g₁(Y)(c, c')` for `c, c' ⊥ Y`.

This is [GG]'s "the source boundary metrics agree and the star actions are identical, so the
quotient boundary metrics agree", and "`X + U` is the common star-horizontal lift".
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Match

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))

omit [FiniteDimensional ℝ V] in
theorem KY_smul_apply (l : ℝ) (Y : V) (b : E3) : KY ρV (l • Y) b = l • KY ρV Y b := by
  rw [KY_smul, ContinuousLinearMap.smul_apply]

variable {β₁ β₂ : V → V →L[ℝ] V →L[ℝ] ℝ} {w₁ w₂ : V → ℝ}

include hρ in
/-- **The common horizontal lift.** -/
theorem hlift_match (hβ₁p : ∀ Y a, a ≠ 0 → 0 < β₁ Y a a) (hβ₁n : ∀ Y a, 0 ≤ β₁ Y a a)
    (hw₁ : ∀ Y, w₁ Y ≠ 0) (hβ₂p : ∀ Y a, a ≠ 0 → 0 < β₂ Y a a) (hβ₂n : ∀ Y a, 0 ≤ β₂ Y a a)
    (hw₂ : ∀ Y, w₂ Y ≠ 0) {Y : V} {l : ℝ}
    (hβ : ∀ a b, ⟪Y, a⟫ = 0 → ⟪Y, b⟫ = 0 → β₂ (l • Y) (l • a) (l • b) = β₁ Y a b)
    (hw : w₂ (l • Y) = w₁ Y) {c : V} (hc : ⟪Y, c⟫ = 0) :
    SQ.hlift ρV (GsW β₂ w₂) (l • Y) (l • c) =
      (l • (SQ.hlift ρV (GsW β₁ w₁) Y c).1, (SQ.hlift ρV (GsW β₁ w₁) Y c).2) := by
  set ĉ := SQ.hlift ρV (GsW β₁ w₁) Y c
  have hG₁ := GsW_pos (w := w₁) hβ₁p hβ₁n hw₁
  have hG₂ := GsW_pos (w := w₂) hβ₂p hβ₂n hw₂
  have hdπ : ĉ.1 - KY ρV Y ĉ.2 = c := SQ.dπl_hlift ρV hG₁ Y c
  have hĉ1 : ⟪Y, ĉ.1⟫ = 0 := by
    have : ĉ.1 = c + KY ρV Y ĉ.2 := by rw [← hdπ]; abel
    rw [this, inner_add_right, hc, inner_Y_KY hρ, add_zero]
  symm
  refine SQ.eq_hlift ρV hG₂ (l • Y) (fun b => ?_) |>.trans ?_
  · rw [ιv_apply, GsW_apply]
    dsimp only
    rw [KY_smul_apply, hβ _ _ hĉ1 (inner_Y_KY hρ Y b), hw]
    have h0 := SQ.hlift_horizontal ρV hG₁ Y c b
    rw [ιv_apply, GsW_apply] at h0
    exact h0
  · congr 1
    rw [dπl_apply]
    dsimp only
    rw [KY_smul_apply, ← smul_sub, hdπ]

include hρ in
/-- **The quotient boundary metrics agree.** -/
theorem gB_match (hβ₁p : ∀ Y a, a ≠ 0 → 0 < β₁ Y a a) (hβ₁n : ∀ Y a, 0 ≤ β₁ Y a a)
    (hw₁ : ∀ Y, w₁ Y ≠ 0) (hβ₂p : ∀ Y a, a ≠ 0 → 0 < β₂ Y a a) (hβ₂n : ∀ Y a, 0 ≤ β₂ Y a a)
    (hw₂ : ∀ Y, w₂ Y ≠ 0) {Y : V} {l : ℝ}
    (hβ : ∀ a b, ⟪Y, a⟫ = 0 → ⟪Y, b⟫ = 0 → β₂ (l • Y) (l • a) (l • b) = β₁ Y a b)
    (hw : w₂ (l • Y) = w₁ Y) {c c' : V} (hc : ⟪Y, c⟫ = 0) (hc' : ⟪Y, c'⟫ = 0) :
    SQ.gB ρV (GsW β₂ w₂) (l • Y) (l • c) (l • c') = SQ.gB ρV (GsW β₁ w₁) Y c c' := by
  have hG₁ := GsW_pos (w := w₁) hβ₁p hβ₁n hw₁
  show GsW β₂ w₂ (l • Y) (SQ.hlift ρV (GsW β₂ w₂) (l • Y) (l • c))
      (SQ.hlift ρV (GsW β₂ w₂) (l • Y) (l • c')) =
    GsW β₁ w₁ Y (SQ.hlift ρV (GsW β₁ w₁) Y c) (SQ.hlift ρV (GsW β₁ w₁) Y c')
  rw [hlift_match hρ hβ₁p hβ₁n hw₁ hβ₂p hβ₂n hw₂ hβ hw hc,
    hlift_match hρ hβ₁p hβ₁n hw₁ hβ₂p hβ₂n hw₂ hβ hw hc', GsW_apply, GsW_apply, hw]
  dsimp only
  have t : ∀ c₁ : V, ⟪Y, c₁⟫ = 0 → ⟪Y, (SQ.hlift ρV (GsW β₁ w₁) Y c₁).1⟫ = 0 := fun c₁ hc₁ => by
    have hdπ : (SQ.hlift ρV (GsW β₁ w₁) Y c₁).1 - KY ρV Y (SQ.hlift ρV (GsW β₁ w₁) Y c₁).2 = c₁ :=
      SQ.dπl_hlift ρV hG₁ Y c₁
    have : (SQ.hlift ρV (GsW β₁ w₁) Y c₁).1 = c₁ + KY ρV Y (SQ.hlift ρV (GsW β₁ w₁) Y c₁).2 :=
      sub_eq_iff_eq_add.1 hdπ
    rw [this, inner_add_right, hc₁, inner_Y_KY hρ, add_zero]
  rw [hβ _ _ (t c hc) (t c' hc')]

end Match

end

end ExoticSpheres8And10
