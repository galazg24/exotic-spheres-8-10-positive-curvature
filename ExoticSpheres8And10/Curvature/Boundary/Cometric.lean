/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.ShapeSum

/-! # A8, completed: the boundary cometric ([GG] §4.4)

[GG]: "At `u = 1`, the boundary quotient differential in scaled components is
`L(X,U) = F_a⁻¹X − r_a⁻¹K_yU`, hence its cometric is
`h⁻¹ = LL^* = F_a⁻²h_{S^{n−1}}^{-1} + r_a⁻²K_yK_y^*`."

* `L_adjoint`: `L^* y = (F_a⁻¹ y, −r_a⁻¹ K^* y)` is the adjoint of `L` for the product inner
  product;
* `LLstar_eq`: `L L^* = F_a⁻² Id + r_a⁻² K K^*`;
* `cometric_lift`: for the horizontal lift `(X, TX)`, `T = −(F_a/r_a)K^*`, of `Y = L(X, TX)`,
  `L L^*(F_a X) = Y` and `⟨Y, F_a X⟩ = ‖X‖² + ‖TX‖²`, i.e. `⟨Y, (LL^*)⁻¹ Y⟩ = |X|² + |U|²`.
  This is the lifted form of `h` used in target A8 (`docs/targets.md`).
-/

namespace ExoticSpheres8And10

open scoped RealInnerProductSpace

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [CompleteSpace Vv]

/-- `L(X,U) = F_a⁻¹X − r_a⁻¹ K U`. -/
noncomputable def bdryL (K : Vv →L[ℝ] H) (Fa ra : ℝ) (X : H) (U : Vv) : H :=
  Fa⁻¹ • X - ra⁻¹ • K U

/-- `L^* y = (F_a⁻¹ y, −r_a⁻¹ K^* y)`. -/
noncomputable def bdryLstar (K : Vv →L[ℝ] H) (Fa ra : ℝ) (y : H) : H × Vv :=
  (Fa⁻¹ • y, -(ra⁻¹ • ContinuousLinearMap.adjoint K y))

omit [CompleteSpace H] [CompleteSpace Vv] in
theorem bdryL_add (K : Vv →L[ℝ] H) (Fa ra : ℝ) (X X' : H) (U U' : Vv) :
    bdryL K Fa ra (X + X') (U + U') = bdryL K Fa ra X U + bdryL K Fa ra X' U' := by
  simp only [bdryL, smul_add, map_add]; abel

/-- `L^*` is the adjoint of `L` for the product inner product `⟨(X,U),(X',U')⟩ = ⟨X,X'⟩ + ⟨U,U'⟩`. -/
theorem L_adjoint (K : Vv →L[ℝ] H) (Fa ra : ℝ) (X : H) (U : Vv) (y : H) :
    ⟪bdryL K Fa ra X U, y⟫ = ⟪X, (bdryLstar K Fa ra y).1⟫ + ⟪U, (bdryLstar K Fa ra y).2⟫ := by
  simp only [bdryL, bdryLstar, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    inner_neg_right, ContinuousLinearMap.adjoint_inner_right]
  ring

/-- **The cometric.** `L L^* = F_a⁻² Id + r_a⁻² K K^*`. -/
theorem LLstar_eq (K : Vv →L[ℝ] H) (Fa ra : ℝ) (y : H) :
    bdryL K Fa ra (bdryLstar K Fa ra y).1 (bdryLstar K Fa ra y).2 =
      (Fa ^ 2)⁻¹ • y + (ra ^ 2)⁻¹ • K (ContinuousLinearMap.adjoint K y) := by
  simp only [bdryL, bdryLstar, map_neg, map_smul]
  module

/-- **Consistency with the lifted metric.** For `Y = L(X, TX)`, `T = −(F_a/r_a)K^*`:
`LL^*(F_a X) = Y` and `⟨Y, F_a X⟩ = ‖X‖² + ‖TX‖²`. -/
theorem cometric_lift (K : Vv →L[ℝ] H) (Fa ra : ℝ) (hFa : Fa ≠ 0) (hra : ra ≠ 0) (X : H) :
    bdryL K Fa ra (bdryLstar K Fa ra (Fa • X)).1 (bdryLstar K Fa ra (Fa • X)).2 =
        bdryL K Fa ra X ((-(Fa / ra) • ContinuousLinearMap.adjoint K) X) ∧
      ⟪bdryL K Fa ra X ((-(Fa / ra) • ContinuousLinearMap.adjoint K) X), Fa • X⟫ =
        ‖X‖ ^ 2 + ‖(-(Fa / ra) • ContinuousLinearMap.adjoint K) X‖ ^ 2 := by
  constructor
  · rw [LLstar_eq]
    simp only [bdryL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, map_neg,
      map_smul, smul_smul]
    match_scalars <;> field_simp
  · have e1 : bdryL K Fa ra X ((-(Fa / ra) • ContinuousLinearMap.adjoint K) X) =
        Fa⁻¹ • X + (Fa / ra ^ 2) • K (ContinuousLinearMap.adjoint K X) := by
      simp only [bdryL, ContinuousLinearMap.smul_apply, map_smul]
      module
    have e2 : ⟪K (ContinuousLinearMap.adjoint K X), X⟫ = ‖ContinuousLinearMap.adjoint K X‖ ^ 2 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    rw [e1, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, e2, real_inner_self_eq_norm_sq, ContinuousLinearMap.smul_apply,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp

/-! ### Non-vacuity: `H = Vv = ℝ`, `K = 2·id`, `F_a = r_a = 1`. -/

example (y : ℝ) : bdryL ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 1
      (bdryLstar ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 1 y).1
      (bdryLstar ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 1 y).2 =
    ((1 : ℝ) ^ 2)⁻¹ • y + ((1 : ℝ) ^ 2)⁻¹ • ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (ContinuousLinearMap.adjoint ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) y) :=
  LLstar_eq _ 1 1 y

end ExoticSpheres8And10
