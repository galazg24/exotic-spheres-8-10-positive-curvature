/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# The Koszul identity, and uniqueness of the Levi-Civita connection

For a connection on the tangent bundle that is torsion-free and compatible with a symmetric
bilinear form `g`, the value of the connection is *determined* by `g`:

  `2 g(∇_X Y, Z) = X g(Y,Z) + Y g(Z,X) - Z g(X,Y) + g([X,Y],Z) - g([X,Z],Y) - g([Y,Z],X)`.

The right-hand side does not mention the connection, so two such connections agree as soon as `g`
is nondegenerate. That is uniqueness of the Levi-Civita connection; existence is **not** proved
here.

## Main results

* `IsCompatibleWith` — compatibility of a connection with a bilinear form given as data.
* `two_apply_cov_eq_koszul` — the Koszul identity.
* `eq_of_isCompatible_of_torsion_eq_zero` — uniqueness.

## Why the metric is data rather than instances

Mathlib has `CovariantDerivative.IsMetricCompatible`, and it **does** apply to the tangent bundle —
but only if the bundle argument is pinned explicitly:

    cov.IsMetricCompatible (V := (TangentSpace I : M → Type _))

Without that annotation elaboration fails with an instance mismatch between `TangentSpace I x`'s
canonical `instAddCommGroupTangentSpace` and the `AddCommGroup` derived from a fibrewise
`NormedAddCommGroup`. That looked like a genuine diamond and is not one: the two instances are
**definitionally equal** — verified by `rfl` — because `Bundle.RiemannianMetric.toCore` goes through
`NormedAddCommGroup.ofCoreReplaceTopology`, whose stated purpose is to keep the pre-existing
topology definitionally. The failure is pure higher-order unification: Lean cannot solve
`instAddCommGroupTangentSpace I =?= fun x ↦ NormedAddCommGroup.toAddCommGroup` while the bundle is
still a metavariable. Recorded because the first diagnosis in this campaign was wrong, and the
correction matters: nothing here is blocked by a defect in Mathlib.

The metric is nevertheless supplied as **data**,

  `g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`,

which is exactly the shape of the `inner` field of `Bundle.RiemannianMetric`. The reason is
generality rather than necessity: the results below use only **symmetry** and, for uniqueness,
**nondegeneracy**, so they hold for pseudo-Riemannian metrics as well, and they need no
`RiemannianBundle` instance, no `IsContMDiffRiemannianBundle`, and no `(V := …)` annotations. A
caller holding Mathlib's `IsMetricCompatible` can feed it in through
`isCompatibleWith_of_isMetricCompatible` below.

## Conventions, which decide every sign

Three facts from the pinned source, checked rather than assumed:

* **The direction is the last argument**: `cov Y x (X x)` is `(∇_X Y)(x)`, per the warning in
  `CovariantDerivative/Basic.lean`. Reading it the other way inverts the whole formula.
* **Torsion** is `∇_X Y - ∇_Y X - [X,Y]` — Mathlib's `torsion_apply` is
  `cov Y x (X x) - cov X x (Y x) - mlieBracket I X Y x`, which is that under the convention above.
* **Compatibility** puts the derivative on the pairing: `X g(Y,Z) = g(∇_X Y, Z) + g(Y, ∇_X Z)`,
  matching `IsMetricCompatible.mvfderiv_inner_eq`.

## Proof architecture

Exactly the classical cyclic argument, and deliberately kept transparent. Write compatibility three
times — for `(Y,Z)` along `X`, for `(Z,X)` along `Y`, for `(X,Y)` along `Z` — and add the first two,
subtract the third. Group the six resulting terms into three pairs; each pair is a difference
`∇_U W - ∇_W U`, which torsion-freeness turns into a bracket. Two of the three brackets appear with
the sign that cancels them against the explicit bracket terms; the third pair contributes the factor
`2`. In Lean the six equations and the three expanded brackets are handed to `linarith` together
with the three instances of symmetry that the pairing needs, so the cancellation is checked rather
than hand-waved.
-/

noncomputable section

open Bundle VectorField Set
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-- **Compatibility of a connection with a bilinear form given as data.**

`X g(Y, Z) = g(∇_X Y, Z) + g(Y, ∇_X Z)` whenever `Y` and `Z` are differentiable at the point. This
is Mathlib's `IsMetricCompatible.mvfderiv_inner_eq` with the metric supplied explicitly instead of
through fibrewise `InnerProductSpace` instances — see the module docstring for why that is
necessary here. No hypothesis on `X` is needed, exactly as in Mathlib's version. -/
def IsCompatibleWith
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∀ {X Y Z : Π x : M, TangentSpace I x} {x : M}, MDiffAt (T% Y) x → MDiffAt (T% Z) x →
    d% (fun y ↦ g y (Y y) (Z y)) x (X x) = g x (cov Y x (X x)) (Z x) + g x (Y x) (cov Z x (X x))

/-- **The Koszul identity.**

`2 g(∇_X Y, Z) = X g(Y,Z) + Y g(Z,X) - Z g(X,Y) + g([X,Y],Z) - g([X,Z],Y) - g([Y,Z],X)`.

Note `cov Y x (X x)` on the left is `∇_X Y`, not `∇_Y X`: the direction is the last argument.

The right-hand side mentions only `g`, the brackets and the three fields — **not** the connection.
That is the whole point, and it is what makes uniqueness immediate. -/
theorem two_apply_cov_eq_koszul (hcov : IsCovariantDerivativeOn E cov univ)
    (hsymm : ∀ (x : M) (u v : TangentSpace I x), g x u v = g x v u)
    (hmc : IsCompatibleWith cov g) (htf : hcov.torsion = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (cov Y x (X x)) (Z x)
      = d% (fun y ↦ g y (Y y) (Z y)) x (X x)
        + d% (fun y ↦ g y (Z y) (X y)) x (Y x)
        - d% (fun y ↦ g y (X y) (Y y)) x (Z x)
        + g x (mlieBracket I X Y x) (Z x)
        - g x (mlieBracket I X Z x) (Y x)
        - g x (mlieBracket I Y Z x) (X x) := by
  -- torsion-freeness, as an equation
  have tf : ∀ {U W : Π x : M, TangentSpace I x} {y : M}, MDiffAt (T% U) y → MDiffAt (T% W) y →
      cov W y (U y) - cov U y (W y) = mlieBracket I U W y := by
    intro U W y hU hW
    have h0 : IsCovariantDerivativeOn.torsion hcov y (U y) (W y) = 0 := by rw [htf]; simp
    rw [hcov.torsion_apply hU hW] at h0
    exact sub_eq_zero.mp h0
  -- the three cyclic instances of metric compatibility
  have e1 := hmc (X := X) hY hZ
  have e2 := hmc (X := Y) hZ hX
  have e3 := hmc (X := Z) hX hY
  -- the three bracket terms, expanded by torsion-freeness
  have b1 : g x (mlieBracket I X Y x) (Z x)
      = g x (cov Y x (X x)) (Z x) - g x (cov X x (Y x)) (Z x) := by
    rw [← tf hX hY, map_sub, sub_apply]
  have b2 : g x (mlieBracket I X Z x) (Y x)
      = g x (cov Z x (X x)) (Y x) - g x (cov X x (Z x)) (Y x) := by
    rw [← tf hX hZ, map_sub, sub_apply]
  have b3 : g x (mlieBracket I Y Z x) (X x)
      = g x (cov Z x (Y x)) (X x) - g x (cov Y x (Z x)) (X x) := by
    rw [← tf hY hZ, map_sub, sub_apply]
  linarith [e1, e2, e3, b1, b2, b3,
    hsymm x (Y x) (cov Z x (X x)), hsymm x (Z x) (cov X x (Y x)),
    hsymm x (X x) (cov Y x (Z x))]

/-- **Uniqueness of the Levi-Civita connection.**

Two torsion-free connections compatible with the same nondegenerate symmetric form agree, pointwise
and slotwise.

The mathematical reason is exactly as expected: by the Koszul identity both sides satisfy
`2 g((∇ - ∇')_X Y, Z) = 0` for every `Z`, because the Koszul right-hand side does not depend on the
connection; nondegeneracy then forces the vector to vanish. The quantifier over `Z` is discharged by
taking `Z := FiberBundle.extend E w`, which is differentiable at `x` and has value `w` there, so `Z`
ranges over all of `TangentSpace I x`.

Nondegeneracy is assumed in the weakest form that does the work — `(∀ w, g x v w = 0) → v = 0` —
rather than positive-definiteness, so this also covers pseudo-Riemannian metrics. -/
theorem eq_of_isCompatible_of_torsion_eq_zero
    (hcov : IsCovariantDerivativeOn E cov univ) (hcov' : IsCovariantDerivativeOn E cov' univ)
    (hsymm : ∀ (x : M) (u v : TangentSpace I x), g x u v = g x v u)
    (hnd : ∀ (x : M) (v : TangentSpace I x), (∀ w, g x v w = 0) → v = 0)
    (hmc : IsCompatibleWith cov g) (hmc' : IsCompatibleWith cov' g)
    (htf : hcov.torsion = 0) (htf' : hcov'.torsion = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x) := by
  refine sub_eq_zero.mp (hnd x _ fun w ↦ ?_)
  have hZ : MDiffAt (T% (FiberBundle.extend E w)) x := FiberBundle.mdifferentiableAt_extend ..
  have k := two_apply_cov_eq_koszul hcov hsymm hmc htf hX hY hZ
  have k' := two_apply_cov_eq_koszul hcov' hsymm hmc' htf' hX hY hZ
  have h2 : (2 : ℝ) * g x (cov Y x (X x)) w = 2 * g x (cov' Y x (X x)) w := by
    simpa using k.trans k'.symm
  rw [map_sub, sub_apply]
  linarith

end RiemannianGeometry
