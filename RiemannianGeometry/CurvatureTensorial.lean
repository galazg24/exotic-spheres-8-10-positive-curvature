/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.Curvature
import RiemannianGeometry.CovariantDerivativeSmooth

/-!
# Tensoriality of the curvature operator in its vector-field arguments

## Main results

* `curvature_smul_left`, `curvature_add_left`: tensoriality in `X`.
* `curvature_smul_right`, `curvature_add_right`: tensoriality in `Y`, derived from the left-hand
  versions using antisymmetry rather than reproved.

## Why this is the mathematical content

Each of the three terms of `R(X, Y)σ` fails individually to depend on `X` only through `X x`: the
middle term `∇_Y ∇_X σ` sees `X` as a *field* through the section `∇_X σ`, and the bracket term
sees the derivative of `X`. What makes curvature tensorial is that the two failures **cancel**.
Concretely, for `X ↦ f • X`:

* the iterated term contributes a Leibniz correction `(df(Y)) • (∇_X σ)(x)`, via
  `IsCovariantDerivativeOn.leibniz`;
* the bracket term contributes `-(df(Y)) • (∇_X σ)(x)`, via
  `VectorField.mlieBracket_smul_left`, since `[f • X, Y] = f • [X, Y] - (df(Y)) • X`.

These are equal and opposite, and `module` closes the resulting linear identity. That cancellation
is the classical proof, and it is why `curvature_smul_left` is the load-bearing result here while
the `Y`-slot versions are corollaries of antisymmetry.

## The differentiability hypothesis

Forming `∇_Y ∇_X σ` means differentiating the intermediate section `∇_X σ`, and
`IsCovariantDerivativeOn` states `add` and `leibniz` only for sections already known to be
differentiable at the point. So some hypothesis of that kind is unavoidable; the question is which.

These results carry

  `hcovσ : MDiffAtCovSection F cov σ x`

i.e. `∇σ` is differentiable at `x` as a section of `Hom(TM, V)`, and obtain the differentiability of
`∇_X σ` from it via `mdiffAt_cov_apply`. Two things make this the right hypothesis rather than the
`X`-dependent `MDiffAt (T% (fun y ↦ cov σ y (X y))) x` these results originally assumed:

* it does not mention `X`, so a single hypothesis on `σ` serves *every* differentiable vector field
  — visible in `curvature_add_left`, which needed two such hypotheses and now needs one;
* being `X`-free, it can be hoisted outside a `TensorialAt` structure, whose `smul` and `add` fields
  quantify over `X` and admit only `MDiffAt f x` and `MDiffAt (T% σ) x`. The old hypothesis could
  not be, which is what blocked the bundled form.

It is a hypothesis and not an instance argument deliberately: `mdiffAt_covSection_of_contMDiff`
discharges it from `ContMDiffCovariantDerivativeOn`, so a caller working with a `C^k` connection
never states it, while a caller with only pointwise regularity is not shut out. The price is the
ambient `[VectorBundle 𝕜 F V]`, needed to speak of `Hom(TM, V)` at all — `IsCovariantDerivativeOn`
itself asks only for `FiberBundle F V`.

## What is still missing: the third slot

Curvature is tensorial in **three** slots — `X`, `Y` and `σ`. Only the first two are proved here.
Tensoriality in `σ` is genuinely harder: substituting `f • σ` makes `leibniz` fire *inside* the
iterated term, producing terms in the second derivative of `f`, and the cancellation then needs the
bracket term to absorb a Hessian-symmetry contribution. It is not a variation on the proofs below.

The bundled 2-tensor form is therefore **still absent**, but for one reason now instead of two.
`TensorialAt.mkHom₂` needs a `TensorialAt` structure in each slot; the results below supply the `X`
and `Y` slots with a hypothesis that can be fixed outside the structure, so what remains is the `σ`
slot. That is recorded as the next target; it is not asserted here.
-/

noncomputable section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

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
  [IsManifold I 2 M] [CompleteSpace E]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X X' Y Y' : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {f : M → 𝕜} {x : M}

/-- The curvature operator is homogeneous in its first vector-field argument with respect to
multiplication by a differentiable function: `R(f • X, Y)σ = f • R(X, Y)σ`.

This is the Leibniz cancellation described in the module docstring, and the load-bearing result of
this file. -/
theorem curvature_smul_left
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x)
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) :
    curvature cov (f • X) Y σ x = f x • curvature cov X Y σ x := by
  have key : (fun y ↦ cov σ y ((f • X) y)) = f • (fun y ↦ cov σ y (X y)) := by
    funext y; simp
  rw [curvature_apply, curvature_apply, key, hcov.leibniz (mdiffAt_cov_apply hcovσ hX) hf,
    VectorField.mlieBracket_smul_left hf hX]
  simp
  module

/-- The curvature operator is additive in its first vector-field argument. -/
theorem curvature_add_left
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) :
    curvature cov (X + X') Y σ x = curvature cov X Y σ x + curvature cov X' Y σ x := by
  have key : (fun y ↦ cov σ y ((X + X') y))
      = (fun y ↦ cov σ y (X y)) + (fun y ↦ cov σ y (X' y)) := by
    funext y; simp
  rw [curvature_apply, curvature_apply, curvature_apply, key,
    hcov.add (mdiffAt_cov_apply hcovσ hX) (mdiffAt_cov_apply hcovσ hX'),
    VectorField.mlieBracket_add_left hX hX']
  simp
  module

/-- The curvature operator is homogeneous in its second vector-field argument.

Derived from `curvature_smul_left` by antisymmetry (`curvature_swap_apply`) rather than reproved. -/
theorem curvature_smul_right
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x)
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) :
    curvature cov X (f • Y) σ x = f x • curvature cov X Y σ x := by
  rw [curvature_swap_apply, curvature_smul_left hcov hcovσ hf hY,
    curvature_swap_apply (X := X), smul_neg]

/-- The curvature operator is additive in its second vector-field argument.

Derived from `curvature_add_left` by antisymmetry rather than reproved. -/
theorem curvature_add_right
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (hcovσ : MDiffAtCovSection F cov σ x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    curvature cov X (Y + Y') σ x = curvature cov X Y σ x + curvature cov X Y' σ x := by
  rw [curvature_swap_apply, curvature_add_left hcov hcovσ hY hY',
    curvature_swap_apply (X := X) (Y := Y), curvature_swap_apply (X := X) (Y := Y')]
  abel

end RiemannianGeometry
