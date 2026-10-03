/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Curvature of a covariant derivative

Mathlib provides covariant derivatives (Koszul connections) on vector bundles as
`CovariantDerivative` / `IsCovariantDerivativeOn`, together with metric compatibility and torsion.
It does **not** provide curvature: at Mathlib `v4.33.1` the string `curvature` occurs exactly once
in the whole library, in a comment. This file supplies the curvature operator and its structural
properties that hold with no differentiability hypotheses.

## Main definitions

## Main results

* `curvature_swap_apply`, `curvature_swap`: antisymmetry in the two vector-field arguments.
* `curvature_self_apply`, `curvature_self`: `R(X, X) = 0`.
* `curvature_zero_section`: `R(X, Y)0 = 0`, for a genuine covariant derivative on a vector bundle.
* `curvature_eq_zero_iff`: flatness in the two given directions, as an equation between the
  iterated derivative and the bracket derivative.

## Conventions

Two sign/argument conventions are fixed here, and both are inherited rather than invented.

**Application order.** For `cov` a covariant derivative, `cov σ x v` is `(∇_v σ) x`: `cov σ x` is a
continuous linear map `TangentSpace I x →L[𝕜] V x`, so the *direction* is the last argument. This is
Mathlib's convention, visible in Mathlib's `CovariantDerivative.Torsion`,
where the torsion is `cov Y x (X x) - cov X x (Y x) - [X, Y] x`, i.e. `∇_X Y - ∇_Y X - [X, Y]`.
Consequently `∇_Y σ` as a *section* is `fun y ↦ cov σ y (Y y)`, which is how the iterated
derivative below is formed.

**Curvature sign.** We use the modern convention

  `R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z`.

## Design notes

The definition and the antisymmetry results need **no bundle structure and no differentiability**:
only that each fibre `V x` is a topological `𝕜`-module, so that `TangentSpace I x →L[𝕜] V x` makes
sense and subtraction is available. They are therefore stated in the first section under minimal
hypotheses. Only `curvature_zero_section`, which needs `∇0 = 0`, requires a vector bundle and a
genuine `IsCovariantDerivativeOn`.

-/

noncomputable section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

section Defn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]

variable (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))

/-- The curvature operator of a covariant derivative `cov`, in the convention
`R(X, Y)σ = ∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_{[X,Y]} σ`.

Here `∇_Y σ` is the section `fun y ↦ cov σ y (Y y)`, so the iterated term is
`cov (fun y ↦ cov σ y (Y y)) x (X x)`. No differentiability is assumed; where `X`, `Y` or `σ`
fail to be differentiable this inherits the junk values of `cov` and of
`VectorField.mlieBracket`. -/
def curvature (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) : V x :=
  cov (fun y ↦ cov σ y (Y y)) x (X x)
    - cov (fun y ↦ cov σ y (X y)) x (Y x)
    - cov σ x (VectorField.mlieBracket I X Y x)

variable {cov} {X Y : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}

/-- `curvature` unfolded. -/
theorem curvature_apply :
    curvature cov X Y σ x =
      cov (fun y ↦ cov σ y (Y y)) x (X x)
        - cov (fun y ↦ cov σ y (X y)) x (Y x)
        - cov σ x (VectorField.mlieBracket I X Y x) :=
  rfl

/-- The curvature operator is antisymmetric in its two vector-field arguments, pointwise.

This needs no hypotheses: the two iterated terms exchange, and the bracket term
changes sign because `VectorField.mlieBracket_swap_apply` is unconditional. -/
theorem curvature_swap_apply : curvature cov X Y σ x = - curvature cov Y X σ x := by
  simp only [curvature_apply]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Y) (W := X), map_neg]
  abel

/-- The curvature operator is antisymmetric in its two vector-field arguments. -/
theorem curvature_swap : curvature cov X Y σ = - curvature cov Y X σ := by
  funext x; exact curvature_swap_apply

/-- `R(X, X)σ = 0`, pointwise. -/
@[simp] theorem curvature_self_apply : curvature cov X X σ x = 0 := by
  simp only [curvature_apply, VectorField.mlieBracket_self, Pi.zero_apply, map_zero]
  abel

/-- `R(X, X)σ = 0`. -/
@[simp] theorem curvature_self : curvature cov X X σ = 0 := by
  funext x; exact curvature_self_apply

/-- `R(X, Y)σ` vanishes identically exactly when the iterated derivative in the directions `X`, `Y`
agrees with the derivative along `[X, Y]`. -/
theorem curvature_eq_zero_iff :
    curvature cov X Y σ = 0 ↔
      ∀ x : M, cov (fun y ↦ cov σ y (Y y)) x (X x) - cov (fun y ↦ cov σ y (X y)) x (Y x)
        = cov σ x (VectorField.mlieBracket I X Y x) := by
  simp [funext_iff, curvature_apply, sub_eq_zero]

end Defn

section Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X Y : Π x : M, TangentSpace I x} {x : M}

/-- The curvature operator kills the zero section. Unlike the results above this uses `∇0 = 0`, so
it needs a genuine covariant derivative on a vector bundle. -/
theorem curvature_zero_section (hcov : IsCovariantDerivativeOn F cov Set.univ) :
    curvature cov X Y (0 : Π x : M, V x) x = 0 := by
  have h0 : ∀ y : M, cov (0 : Π x : M, V x) y = 0 := fun _ ↦ hcov.zero
  have h1 : (fun y ↦ cov (0 : Π x : M, V x) y (Y y)) = (0 : Π x : M, V x) := by
    funext y; rw [h0 y]; simp
  have h2 : (fun y ↦ cov (0 : Π x : M, V x) y (X y)) = (0 : Π x : M, V x) := by
    funext y; rw [h0 y]; simp
  rw [curvature_apply, h1, h2, h0 x]
  simp

/-- Compatibility check: the operator applies to Mathlib's bundled `CovariantDerivative` through its
coercion to a function, so no separate bundled definition is needed. -/
example (cov : CovariantDerivative I F V) (X σ : _) (x : M) :
    curvature (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)) X X σ x = 0 :=
  curvature_self_apply

end Bundle

end RiemannianGeometry
