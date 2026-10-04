/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # A5. The area inequalities ([GG] §4.3, "Horizontal graph")

[GG]: "`|λV−μU|² ≤ (4F²/r²)|λY−μX|²`, `|X⊗V − Y⊗U|² ≤ (8F²/r²)|X∧Y|²`. For the second area
inequality, replace independent `X,Y` by a determinant-one change of the pair making them
orthogonal. Both alternating expressions are unchanged, and the squared tensor norm becomes
`|X|²|TY|² + |Y|²|TX|²`. If `X,Y` are dependent, both expressions vanish."

Here `T : H → Vv` is linear with `‖T‖ ≤ τ` (in [GG], `τ = 2F/r`), `U = TX`, `V = TY`.

Encoding: `tensorSq X Y U V := ‖X‖²‖V‖² + ‖Y‖²‖U‖² − 2⟨X,Y⟩⟨V,U⟩` and
`wedgeSq X Y := ‖X‖²‖Y‖² − ⟨X,Y⟩²`. We prove that `tensorSq X Y U V` **is** the squared
norm of `X ⊗ V − Y ⊗ U` in Mathlib's inner-product tensor product `H ⊗[ℝ] Vv`, and that
`wedgeSq X Y = ½‖X ⊗ Y − Y ⊗ X‖²`.
-/

namespace ExoticSpheres8And10

open scoped TensorProduct RealInnerProductSpace

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv]

/-- `|X ⊗ V − Y ⊗ U|²`, written through inner products. -/
noncomputable def tensorSq (X Y : H) (U V : Vv) : ℝ :=
  ‖X‖ ^ 2 * ‖V‖ ^ 2 + ‖Y‖ ^ 2 * ‖U‖ ^ 2 - 2 * ⟪X, Y⟫ * ⟪V, U⟫

/-- `|X ∧ Y|²`, the Gram determinant. -/
noncomputable def wedgeSq (X Y : H) : ℝ := ‖X‖ ^ 2 * ‖Y‖ ^ 2 - ⟪X, Y⟫ ^ 2

/-- **Encoding, tensor.** `tensorSq` is the squared norm of `X ⊗ V − Y ⊗ U` in `H ⊗[ℝ] Vv`. -/
theorem norm_tmul_sub_tmul_sq (X Y : H) (U V : Vv) :
    ‖X ⊗ₜ[ℝ] V - Y ⊗ₜ[ℝ] U‖ ^ 2 = tensorSq X Y U V := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, TensorProduct.inner_tmul,
    real_inner_self_eq_norm_sq]
  rw [tensorSq, real_inner_comm X Y, real_inner_comm V U]
  ring

/-- **Encoding, wedge.** `wedgeSq X Y = ½‖X ⊗ Y − Y ⊗ X‖²`, i.e. the Gram determinant is the
squared norm of `X ∧ Y ↦ (X ⊗ Y − Y ⊗ X)/√2` (so `|e₁ ∧ e₂| = 1` for orthonormal `e₁, e₂`). -/
theorem wedgeSq_eq_half_norm_sq (X Y : H) :
    wedgeSq X Y = ‖X ⊗ₜ[ℝ] Y - Y ⊗ₜ[ℝ] X‖ ^ 2 / 2 := by
  rw [norm_tmul_sub_tmul_sq, tensorSq, wedgeSq, real_inner_comm X Y]
  ring

theorem wedgeSq_nonneg (X Y : H) : 0 ≤ wedgeSq X Y := by
  rw [wedgeSq_eq_half_norm_sq]
  positivity

/-! ### Invariance under the determinant-one shear `(X, Y) ↦ (X, Y − cX)` -/

theorem norm_sub_smul_sq (X Y : H) (c : ℝ) :
    ‖Y - c • X‖ ^ 2 = ‖Y‖ ^ 2 - 2 * c * ⟪X, Y⟫ + c ^ 2 * ‖X‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_comm X Y]
  ring

theorem inner_sub_smul_self (X Y : H) (c : ℝ) :
    ⟪X, Y - c • X⟫ = ⟪X, Y⟫ - c * ‖X‖ ^ 2 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem tensorSq_shear (X Y : H) (U V : Vv) (c : ℝ) :
    tensorSq X (Y - c • X) U (V - c • U) = tensorSq X Y U V := by
  have e4 : ⟪V - c • U, U⟫ = ⟪U, V⟫ - c * ‖U‖ ^ 2 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm U V]
  rw [tensorSq, tensorSq, norm_sub_smul_sq, norm_sub_smul_sq, inner_sub_smul_self, e4,
    real_inner_comm U V]
  ring

theorem wedgeSq_shear (X Y : H) (c : ℝ) : wedgeSq X (Y - c • X) = wedgeSq X Y := by
  rw [wedgeSq, wedgeSq, norm_sub_smul_sq, inner_sub_smul_self]
  ring

/-- If `Y = cX` both alternating expressions vanish ([GG], dependent case). -/
theorem tensorSq_wedgeSq_of_dependent (T : H →L[ℝ] Vv) (X : H) (c : ℝ) :
    tensorSq X (c • X) (T X) (T (c • X)) = 0 ∧ wedgeSq X (c • X) = 0 := by
  constructor
  · rw [map_smul, ← tensorSq_shear X (c • X) (T X) (c • T X) c]
    simp [tensorSq]
  · rw [← wedgeSq_shear X (c • X) c]
    simp [wedgeSq]

/-! ### The inequalities -/

variable (T : H →L[ℝ] Vv) {τ : ℝ}

theorem sq_norm_apply_le (hT : ‖T‖ ≤ τ) (z : H) : ‖T z‖ ^ 2 ≤ τ ^ 2 * ‖z‖ ^ 2 := by
  have h : ‖T z‖ ≤ τ * ‖z‖ :=
    (T.le_opNorm z).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **A5(a).** `‖λV − μU‖² ≤ τ²‖λY − μX‖²` with `U = TX`, `V = TY`. -/
theorem area_ineq_a (hT : ‖T‖ ≤ τ) (X Y : H) (lam mu : ℝ) :
    ‖lam • T Y - mu • T X‖ ^ 2 ≤ τ ^ 2 * ‖lam • Y - mu • X‖ ^ 2 := by
  have : lam • T Y - mu • T X = T (lam • Y - mu • X) := by
    rw [map_sub, map_smul, map_smul]
  rw [this]
  exact sq_norm_apply_le T hT _

/-- The orthogonal case: if `⟨X, Y⟩ = 0` then the tensor norm is `|X|²|TY|² + |Y|²|TX|²`. -/
theorem tensorSq_of_orthogonal (X Y : H) (U V : Vv) (h : ⟪X, Y⟫ = 0) :
    tensorSq X Y U V = ‖X‖ ^ 2 * ‖V‖ ^ 2 + ‖Y‖ ^ 2 * ‖U‖ ^ 2 := by
  rw [tensorSq, h]
  ring

/-- **A5(b).** `|X⊗V − Y⊗U|² ≤ 2τ²|X∧Y|²` with `U = TX`, `V = TY`. No independence hypothesis:
the dependent case is included. The proof is [GG]'s: shear `Y` to `Y' = Y − cX ⊥ X`. -/
theorem area_ineq_b (hT : ‖T‖ ≤ τ) (X Y : H) :
    tensorSq X Y (T X) (T Y) ≤ 2 * τ ^ 2 * wedgeSq X Y := by
  by_cases hX : X = 0
  · subst hX
    simp [tensorSq, wedgeSq]
  have hx : 0 < ‖X‖ ^ 2 := by positivity
  set c := ⟪X, Y⟫ / ‖X‖ ^ 2 with hc
  have horth : ⟪X, Y - c • X⟫ = 0 := by
    rw [inner_sub_smul_self, hc]
    field_simp
    ring
  have hTY : T Y - c • T X = T (Y - c • X) := by rw [map_sub, map_smul]
  rw [← tensorSq_shear X Y (T X) (T Y) c, ← wedgeSq_shear X Y c, hTY,
    tensorSq_of_orthogonal _ _ _ _ horth, wedgeSq, horth]
  have h1 := mul_le_mul_of_nonneg_left (sq_norm_apply_le T hT (Y - c • X)) (sq_nonneg ‖X‖)
  have h2 := mul_le_mul_of_nonneg_left (sq_norm_apply_le T hT X) (sq_nonneg ‖Y - c • X‖)
  nlinarith [h1, h2]

/-- [GG]'s displayed form, with `τ = 2F/r`: `|λV−μU|² ≤ (4F²/r²)|λY−μX|²` and
`|X⊗V − Y⊗U|² ≤ (8F²/r²)|X∧Y|²`. -/
theorem area_ineqs_graph (F r : ℝ) (hT : ‖T‖ ≤ 2 * F / r) (X Y : H) (lam mu : ℝ) :
    ‖lam • T Y - mu • T X‖ ^ 2 ≤ 4 * F ^ 2 / r ^ 2 * ‖lam • Y - mu • X‖ ^ 2 ∧
      tensorSq X Y (T X) (T Y) ≤ 8 * F ^ 2 / r ^ 2 * wedgeSq X Y := by
  have e1 : (2 * F / r) ^ 2 = 4 * F ^ 2 / r ^ 2 := by ring
  have e2 : 2 * (2 * F / r) ^ 2 = 8 * F ^ 2 / r ^ 2 := by ring
  refine ⟨?_, ?_⟩
  · rw [← e1]; exact area_ineq_a T hT X Y lam mu
  · rw [← e2]; exact area_ineq_b T hT X Y

/-! ### Non-vacuity

`T = 2 • id` on `ℝ²` (`EuclideanSpace ℝ (Fin 2)`) has `‖T‖ ≤ 2`, and at `X = e₀`, `Y = e₁`
inequality (b) is an equality `8 = 8`. -/

example :
    let e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
    let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
    tensorSq e0 e1 ((2 : ℝ) • e0) ((2 : ℝ) • e1) = 2 * 2 ^ 2 * wedgeSq e0 e1 := by
  intro e0 e1
  have h0 : ‖e0‖ = 1 := by simp [e0]
  have h1 : ‖e1‖ = 1 := by simp [e1]
  have h01 : ⟪e0, e1⟫ = 0 := by simp [e0, e1, EuclideanSpace.inner_single_left]
  have h10 : ⟪(2 : ℝ) • e1, (2 : ℝ) • e0⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm, h01]; ring
  rw [tensorSq, wedgeSq, norm_smul, norm_smul, h0, h1, h01, h10, Real.norm_two]
  norm_num

theorem norm_two_smul_id_le : ‖(2 : ℝ) • ContinuousLinearMap.id ℝ H‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => by
    show ‖(2 : ℝ) • x‖ ≤ 2 * ‖x‖
    rw [norm_smul, Real.norm_two]

example (X Y : H) : tensorSq X Y (((2 : ℝ) • ContinuousLinearMap.id ℝ H) X)
    (((2 : ℝ) • ContinuousLinearMap.id ℝ H) Y) ≤ 2 * 2 ^ 2 * wedgeSq X Y :=
  area_ineq_b _ norm_two_smul_id_le X Y

end ExoticSpheres8And10
