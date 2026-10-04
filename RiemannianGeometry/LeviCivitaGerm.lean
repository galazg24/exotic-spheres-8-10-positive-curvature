/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.LeviCivita
import RiemannianGeometry.CurvatureMetric

/-!
# Germ locality of the Levi-Civita connection

`leviCivita g Y x` depends only on the **germ** of the differentiated field `Y` at `x`: if
`Y = Y'` on a neighbourhood of `x`, then `leviCivita g Y x = leviCivita g Y' x`.

This is a general fact about the connection of `RiemannianGeometry.LeviCivita` and it needs **no
hypothesis at all** — not symmetry of `g`, not nondegeneracy, not regularity of `g` or of the
fields, and no differentiability of `Y`. That is a consequence of the design of `leviCivita`: it is
*total*, built as `½ (g x)⁻¹ ∘ koszulSection g Y x`, and both factors are germ-local for structural
reasons.

## Main results

* `koszulRHS_congr_of_eventuallyEq` — the six-term Koszul right-hand side is germ-local in its
  differentiated slot.
* `isKoszulTensorialAt_congr_of_eventuallyEq` — **the tensoriality predicate is germ-local.**
* `koszulSection_congr_of_eventuallyEq` — the bundled Koszul form is germ-local.
* `leviCivita_congr_of_eventuallyEq` — **the connection is germ-local.**

## Why the route runs through `koszulRHS`

`leviCivita g Y x` is `(2⁻¹ : ℝ) • ((g x)⁻¹ ∘L koszulSection g Y x)`. The inverse metric does not
mention `Y`, so everything reduces to `koszulSection`, and — because `koszulSection` is defined by
`dite` on `IsKoszulTensorialAt g Y x` — to two separate obligations:

1. `koszulRHS g X Y x Z` is germ-local in `Y`. Four of its six terms need an argument; two need
   only `Y x = Y' x`. The two derivative terms in which `Y` sits inside the differentiated function
   go through `Filter.EventuallyEq.mvfderiv_eq`, this project's germ-locality lemma for `mvfderiv`
   (`RiemannianGeometry.CurvatureMetric`), and the two bracket terms through Mathlib's
   `Filter.EventuallyEq.mlieBracket_vectorField_eq`. Nothing is reproved.
2. `IsKoszulTensorialAt g Y x` is germ-local **as a predicate**. This is the obligation the `dite`
   creates and it is discharged, not circumvented: the predicate quantifies over test fields but
   its body mentions `Y` only through the values `koszulRHS g U Y x Z`, so (1) makes the two
   `TensorialAt` statements literally the same statement for `Y` and for `Y'` — the operations
   involved are *equal functions*, by `funext`. Hence no case split on the predicate is needed
   inside the germ argument, and the `dite` collapses uniformly: where the predicate holds for `Y`
   it holds for `Y'`, and where it fails for `Y` it fails for `Y'`, so both sides take the junk
   value `0`.

Both directions of (2) are used, which is why `isKoszulTensorialAt_congr_of_eventuallyEq` is stated
as an implication and applied twice, once to `h` and once to its symmetrisation, rather than as
an `Iff`.

## Relation to `RiemannianGeometry.CurvatureSection.curvature_congr_of_eventuallyEq`

That lemma is the same kind of statement one layer up — germ locality of the curvature operator in
its section slot — but its proof is genuinely different: it must move the germ hypothesis through
two nested covariant derivatives, and so consumes `IsCovariantDerivativeOn` together with
differentiability of both sections near `x`. Here nothing is differentiated a second time and the
connection is a concrete formula, so the argument is a rewrite and the hypothesis list is empty.
-/

noncomputable section

open Bundle VectorField Set Filter
open scoped RiemannianGeometry.ManifoldOrder
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {X Y Y' Z : Π x : M, TangentSpace I x} {x : M}

/-! ## Germ locality of the Koszul right-hand side -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The Koszul right-hand side is germ-local in its differentiated slot.**

`κ(X, Y, x, Z) = X g(Y,Z) + Y g(Z,X) - Z g(X,Y) + g([X,Y],Z) - g([X,Z],Y) - g([Y,Z],X)` mentions
`Y` in five of its six terms, and in each of them only through data determined by the germ of `Y`
at `x`:

* the first and the third differentiate a function in which `Y` appears as a factor, so they are
  handled by `Filter.EventuallyEq.mvfderiv_eq`;
* the second and the fifth use the single value `Y x`;
* the fourth and the sixth are Lie brackets, handled by Mathlib's
  `Filter.EventuallyEq.mlieBracket_vectorField_eq`.

No hypothesis on `g`, on `X`, on `Z` or on `Y` is used. -/
theorem koszulRHS_congr_of_eventuallyEq (h : ∀ᶠ y in 𝓝 x, Y y = Y' y) :
    koszulRHS g X Y x Z = koszulRHS g X Y' x Z := by
  have hY : Y x = Y' x := h.self_of_nhds
  have e1 : d% (fun y ↦ g y (Y y) (Z y)) x = d% (fun y ↦ g y (Y' y) (Z y)) x :=
    Filter.EventuallyEq.mvfderiv_eq (h.mono fun y hy ↦ by simp only [hy])
  have e3 : d% (fun y ↦ g y (X y) (Y y)) x = d% (fun y ↦ g y (X y) (Y' y)) x :=
    Filter.EventuallyEq.mvfderiv_eq (h.mono fun y hy ↦ by simp only [hy])
  have e4 : mlieBracket I X Y x = mlieBracket I X Y' x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq Filter.EventuallyEq.rfl h
  have e6 : mlieBracket I Y Z x = mlieBracket I Y' Z x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq h Filter.EventuallyEq.rfl
  simp only [koszulRHS, e1, e3, e4, e6, hY]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The Koszul right-hand side as an *operation on the test field*, for `Y` and for `Y'`, is one and
the same operation. Stated because `TensorialAt` is a predicate on such an operation, so
transporting it needs an equality of functions and not merely of values. -/
theorem koszulRHS_funext_of_eventuallyEq (h : ∀ᶠ y in 𝓝 x, Y y = Y' y) :
    koszulRHS g X Y x = koszulRHS g X Y' x :=
  funext fun _ ↦ koszulRHS_congr_of_eventuallyEq h

/-! ## Germ locality of the tensoriality predicate -/

omit [FiniteDimensional ℝ E] in
/-- **The tensoriality predicate of the bundled Koszul form is germ-local.**

This is the obligation created by the `dite` in `koszulSection`, and it is the step on which the
whole route depends: had `IsKoszulTensorialAt` failed to be germ-local, germ locality of
`koszulSection` would have needed a case split with genuinely different content in the two
branches, and germ locality of `leviCivita` would not have followed from germ locality of
`koszulRHS` at all.

It is germ-local, and for a structural reason: both conjuncts are `TensorialAt` statements about
operations whose values are `koszulRHS g U Y x Z`, and `koszulRHS_congr_of_eventuallyEq` makes
those operations *equal as functions*. So the transport is `funext` followed by a rewrite. -/
theorem isKoszulTensorialAt_congr_of_eventuallyEq (h : ∀ᶠ y in 𝓝 x, Y y = Y' y)
    (hten : IsKoszulTensorialAt g Y x) : IsKoszulTensorialAt g Y' x := by
  constructor
  · intro Z hZ
    have e : (fun U : Π z : M, TangentSpace I z ↦ koszulRHS g U Y' x Z)
        = fun U : Π z : M, TangentSpace I z ↦ koszulRHS g U Y x Z :=
      funext fun _ ↦ (koszulRHS_congr_of_eventuallyEq h).symm
    rw [e]
    exact hten.1 Z hZ
  · intro U hU
    rw [← koszulRHS_funext_of_eventuallyEq h]
    exact hten.2 U hU

/-! ## Germ locality of the bundled Koszul form and of the connection -/

/-- **The bundled Koszul form is germ-local in its differentiated slot.**

Both branches of the `dite` are covered: where the tensoriality predicate holds, the two sides are
compared on arbitrary tangent vectors through `koszulSection_apply_extend` and
`koszulRHS_congr_of_eventuallyEq`; where it fails for `Y` it fails for `Y'` as well, by
`isKoszulTensorialAt_congr_of_eventuallyEq` applied to the symmetrised germ, and both sides are
the junk value `0`. -/
theorem koszulSection_congr_of_eventuallyEq (h : ∀ᶠ y in 𝓝 x, Y y = Y' y) :
    koszulSection g Y x = koszulSection g Y' x := by
  by_cases hten : IsKoszulTensorialAt g Y x
  · have hten' : IsKoszulTensorialAt g Y' x := isKoszulTensorialAt_congr_of_eventuallyEq h hten
    refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
    rw [koszulSection_apply_extend hten, koszulSection_apply_extend hten',
      koszulRHS_congr_of_eventuallyEq h]
  · have hten' : ¬ IsKoszulTensorialAt g Y' x := fun hc ↦
      hten (isKoszulTensorialAt_congr_of_eventuallyEq (h.mono fun y hy ↦ hy.symm) hc)
    simp only [koszulSection, dif_neg hten, dif_neg hten']

/-- **`leviCivita` depends only on the germ of the differentiated field.**

    Y = Y' near x  →  leviCivita g Y x = leviCivita g Y' x

No hypothesis: neither symmetry nor nondegeneracy nor regularity of `g`, and no differentiability
of `Y` or `Y'`. The inverse metric factor of `leviCivita` does not mention the field, so the
statement is `koszulSection_congr_of_eventuallyEq` composed with one rewrite.

This is the fact that lets the *field* forms of the submersion identities be stated with base
fields that are only `C^n` on a **neighbourhood**: a field constructed near a point can be
substituted into `leviCivita` at that point without being globally regular. -/
theorem leviCivita_congr_of_eventuallyEq (h : ∀ᶠ y in 𝓝 x, Y y = Y' y) :
    leviCivita g Y x = leviCivita g Y' x := by
  simp only [leviCivita, koszulSection_congr_of_eventuallyEq h]

/-- The germ form of `leviCivita_congr_of_eventuallyEq`: two fields agreeing near `x` have
`leviCivita`'s agreeing near `x`, not merely at `x`. The form that can be fed to a further
differentiation. -/
theorem leviCivita_eventuallyEq_of_eventuallyEq (h : ∀ᶠ y in 𝓝 x, Y y = Y' y) :
    ∀ᶠ y in 𝓝 x, leviCivita g Y y = leviCivita g Y' y := by
  filter_upwards [h.eventually_nhds] with y hy using leviCivita_congr_of_eventuallyEq hy

end RiemannianGeometry
