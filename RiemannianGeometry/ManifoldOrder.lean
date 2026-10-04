/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Two smoothness-exponent facts Mathlib's instance search cannot reach

## Main results

* `ENat.LEInfty.coe_add_one` — **global instance.** `(↑a + 1 : ℕ∞ω) ≤ ∞` for `a : ℕ∞`.
* `IsManifold.of_minSmoothness` — **plain theorem.** Over `ℝ` or `ℂ`, a `C^n` manifold is
  `C^(minSmoothness 𝕜 n)`.

## Why `IsManifold.of_le` is a theorem and not an instance

This has to be understood before adding anything nearby, because it is the constraint that shapes
both decisions. As an instance, `IsManifold.of_le : m ≤ n → [IsManifold I n M] → IsManifold I m M`
would turn a goal `IsManifold I m M` into a premise `IsManifold I ?n M` with `?n` **unconstrained**,
plus `m ≤ ?n`. That is the classic non-terminating instance shape, and Mathlib's way around it is to
introduce the class `ENat.LEInfty` and register `of_le` only where the *source* order is the fixed
`∞` (or `ω`):

    instance {a : ℕ∞ω} [IsManifold I ∞ M] [LEInfty a] : IsManifold I a M

So the mechanism Mathlib chose pins the order that would otherwise be a metavariable, and the
supported way to extend it is to add `LEInfty` instances for further *closed* shapes — not to
register new `of_le` consequences.

## `ENat.LEInfty.coe_add_one`: a global instance, and why that is safe

Mathlib registers `LEInfty` for `(n : ℕ∞)` and `(n : ℕ)` cast into `ℕ∞ω`, for numerals, and for `0`
and `1`. It does **not** register `↑a + 1`, which is the shape that appears the instant a statement
differentiates once: a lemma of the form "`C^(n+1)` data gives a `C^n` result" instantiated at
`n := m + 1` asks its manifold hypothesis at `↑(m + 1) + 1`. Instance search matches syntactically
and `↑a + 1` is not a coercion, so the search fails on a trivial inequality.

Mathlib never has to synthesize it because its own lemmas *state* `[IsManifold I (n + 1) M]` as a
hypothesis; the obligation falls on the caller, and Mathlib has no such caller in-tree.

This is one more closed shape in the mechanism Mathlib already designed, so it is registered
globally: `ENat.LEInfty` is a `Prop` class (proof irrelevance, hence no diamond), the instance has
**no** instance premise at all (so it cannot recurse, let alone loop), and its conclusion determines
`a` syntactically. Upstream candidate: beside the other `LEInfty` instances in
`Mathlib/Geometry/Manifold/IsManifold/Basic.lean`.

## `minSmoothness`: a theorem, and only a scoped instance

`minSmoothness 𝕜 n` is `n` over `ℝ` and `ℂ` and `ω` otherwise, and is an `irreducible_def`, so
`IsManifold I (minSmoothness ℝ 2) M` neither *is* nor follows from `IsManifold I 2 M` by search.
This matters because `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` carries
`[IsManifold I (minSmoothness 𝕜 2) M]` as a section variable, so every caller of its bracket lemmas
owes exactly this. Mathlib's `VectorField/Pullback.lean` registers four instances going the *other*
way — from `minSmoothness` levels to plain ones, and between `minSmoothness` levels — because those
are the directions its own proofs consumed.

The fact is stated as a plain theorem, and as an instance **only inside a scoped namespace**, for
two reasons:

1. it is **not field-generic**: it needs `IsRCLikeNormedField 𝕜`, and over a field where
   `minSmoothness 𝕜 n = ω` it is false. A global instance would silently impose an `ℝ`/`ℂ`-shaped
   convenience on a general-purpose file;
2. its premise is `IsManifold I n M` at a *variable* order. When the inner order is concrete this
   recurses on a strictly smaller term and terminates; but it re-introduces, in narrow form, the
   very shape `of_le` was kept out of instance search to avoid, and a goal written with the inner
   order left as a metavariable would hand search an unconstrained `IsManifold I ?n M`.

-/

open scoped Manifold ContDiff

/-- `↑a + 1 ≤ ∞` for `a : ℕ∞`.

A global instance: `ENat.LEInfty` is a `Prop` class, this instance has no instance premise so it
cannot recurse, and its conclusion determines `a` syntactically. It is one further closed shape in
the mechanism Mathlib already uses to keep `IsManifold.of_le` out of instance search — see the
module docstring. -/
instance ENat.LEInfty.coe_add_one {a : ℕ∞} : ENat.LEInfty ((a : ℕ∞ω) + 1) :=
  ⟨by exact_mod_cast (le_top : (a + 1 : ℕ∞) ≤ ⊤)⟩

/-- Over `ℝ` or `ℂ`, a `C^n` manifold is `C^(minSmoothness 𝕜 n)`, since `minSmoothness 𝕜 n = n`
there. `minSmoothness` is an `irreducible_def`, so this does not hold by unfolding.
-/
theorem IsManifold.of_minSmoothness {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} [h : IsManifold I n M] :
    IsManifold I (minSmoothness 𝕜 n) M := by
  simpa using h

namespace RiemannianGeometry.ManifoldOrder

/--See the module docstring for why it is not global.-/
scoped instance isManifold_minSmoothness {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I n M] :
    IsManifold I (minSmoothness 𝕜 n) M :=
  IsManifold.of_minSmoothness

end RiemannianGeometry.ManifoldOrder
