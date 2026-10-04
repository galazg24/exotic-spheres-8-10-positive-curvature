/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.HorizontalSpace
import RiemannianGeometry.MfderivAdjoint
import RiemannianGeometry.AdjointProjection

/-!
# The horizontal projection of a Riemannian submersion is `Aᵃ ∘ A`

`RiemannianGeometry.HorizontalSpace` builds the horizontal space of a submersion as an orthogonal
complement and its horizontal lift as the inverse of a restricted linear isomorphism. Both are
correct pointwise, and both are opaque: an inverse produced by `ContinuousLinearEquiv.ofBijective`
carries no route to smoothness in the base point. `RiemannianGeometry.MfderivAdjoint` builds a second,
manifestly smooth object — the fibrewise metric adjoint `Aᵃ` of `A = dπ_p` — and
`RiemannianGeometry.AdjointProjection` supplies the purely algebraic fact that an adjoint which is also a
section of `A` computes the orthogonal projection onto `(ker A)ᗮ`.

This file joins the three. Its payoff is the pair

* `horizontalProjection_eq` — `𝓗_p = Aᵃ_p ∘ A_p`, and
* `horizontalLift_eq_mfderivAdjoint` — the horizontal lift **is** `Aᵃ_p`,

which replace every occurrence of orthogonal-projection machinery by an expression built from
`mfderiv` and the inverse fibre metric, whose regularity is already known
(`contMDiffAt_mfderivAdjoint_apply`, `contMDiffAt_mfderivAdjoint_inCoordinates`).

## Main definitions

* `tangentMetric I M` — the metric-as-data underlying a `Bundle.RiemannianBundle` structure on the
  tangent bundle, i.e. the field `Bundle.RiemannianBundle.g … |>.inner`.

## Main results

* `inner_eq_tangentMetric` — the registered `inner ℝ` on a tangent space **is** `tangentMetric`,
  by `rfl`.
* `tangentMetric_nondegenerate` — nondegeneracy at every point, from positive definiteness. This
  is the hypothesis `mfderivAdjoint_spec` takes.
* `isAdjointPair_mfderivAdjoint` — `Aᵃ` is an adjoint of `A` in the sense of
  `ContinuousLinearMap.IsAdjointPair`, with no hypothesis at all.
* `isMetricSection_of_isRiemannianSubmersionAtPoint` and its applied form
  `mfderiv_mfderivAdjoint` — for a Riemannian submersion, `A ∘ Aᵃ = id`.
* `mfderivAdjoint_mem_horizontalSpace`, `range_mfderivAdjoint_eq_horizontalSpace` — `Aᵃ` lands in,
  and onto, the horizontal space.
* `horizontalProjection_eq`, `verticalProjection_eq` — the projection formulas.
* `horizontalLift_eq_mfderivAdjoint` — the reconciliation of the two horizontal lifts.
* `isRiemannianSubmersionAtPoint_of_isMetricSection` and
  `isRiemannianSubmersionAtPoint_iff_isMetricSection` — the converse, so that the Riemannian
  condition becomes an algebraic identity between `A` and `Aᵃ`.

## Implementation notes

Two instance rules of `RiemannianGeometry.RiemannianBundleBridge` are respected throughout: the fibrewise
`InnerProductSpace` is never bound to a name, and `FiniteDimensional ℝ (TangentSpace I p)` is
introduced by `inferInstanceAs` wherever `Submodule.starProjection` or completeness of the fibre is
needed. `CompleteSpace (TangentSpace I p)`, which every `AdjointProjection` lemma mentioning
`starProjection` requires, is then found by instance search from
`FiniteDimensional.complete`; no `[CompleteSpace E]` hypothesis is added.

`tangentMetric` is deliberately **not** `private`: the statements of `mfderiv_mfderivAdjoint` and
`horizontalLift_eq_mfderivAdjoint` mention it, so downstream files must be able to name it.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

/-! ## The metric of a `RiemannianBundle` as data -/

section Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]

variable (I M) in
/-- **The tangent metric as data.** Mathlib's `Bundle.RiemannianBundle E` is a one-field class
holding a `Bundle.RiemannianMetric E`, whose own `inner` field is precisely this development's
metric-as-data `Π p, T_pM →L[ℝ] T_pM →L[ℝ] ℝ`. Naming it lets the fibrewise adjoint of
`RiemannianGeometry.MfderivAdjoint`, which is stated in metric-as-data terms, be applied to a bundle
carrying only the class. -/
def tangentMetric : Π p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  (Bundle.RiemannianBundle.g (E := (TangentSpace I : M → Type _))).inner

/-- **The bridge, and it is `rfl`.** The `InnerProductSpace` instance that
`Bundle.RiemannianBundle` registers on the fibres has `tangentMetric` as its inner product, on
the nose.-/
theorem inner_eq_tangentMetric {p : M} (u v : TangentSpace I p) :
    inner ℝ u v = tangentMetric I M p u v := rfl

variable (I M) in
/-- **The tangent metric is nondegenerate at every point.** Immediate from the positive
definiteness field of `Bundle.RiemannianMetric`: a vector pairing to zero with everything pairs to
zero with itself.

This is exactly the hypothesis `mfderivAdjoint_spec` requires, and the only reason the adjoint of
`RiemannianGeometry.MfderivAdjoint` — which is defined without hypotheses, using the junk value of
`ContinuousLinearMap.inverse` — has its characterising property here. -/
theorem tangentMetric_nondegenerate (p : M) :
    ∀ v : TangentSpace I p, (∀ w, tangentMetric I M p v w = 0) → v = 0 := by
  intro v hv
  by_contra hv0
  have hpos : 0 < tangentMetric I M p v v :=
    (Bundle.RiemannianBundle.g (E := (TangentSpace I : M → Type _))).pos p v hv0
  rw [hv v] at hpos
  exact lt_irrefl 0 hpos

end Metric

/-! ## The differential and its adjoint as an adjoint pair -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]
  {f : M → B} {p : M}

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`Aᵃ` is an adjoint of `A`.** Unwound: `⟪Aᵃ w, u⟫ = ⟪w, A u⟫`, which is
`mfderivAdjoint_spec` read through `inner_eq_tangentMetric` on both sides. No submersion,
Riemannian or symmetry hypothesis is used; only nondegeneracy of the fibre metric, which
`tangentMetric_nondegenerate` supplies unconditionally.

Note the argument order: `ContinuousLinearMap.IsAdjointPair A B` is `⟪B v, x⟫ = ⟪v, A x⟫`, which
matches `mfderivAdjoint_spec` slot for slot, so the symmetry of the metric never enters. -/
theorem isAdjointPair_mfderivAdjoint :
    ContinuousLinearMap.IsAdjointPair (mfderiv I J f p)
      (mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p) := by
  intro w u
  rw [inner_eq_tangentMetric, inner_eq_tangentMetric,
    mfderivAdjoint_spec (tangentMetric_nondegenerate I M p) w u]

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- Every value of the adjoint is horizontal. This needs no hypothesis beyond the ambient metrics:
it is `mfderivAdjoint_mem_verticalSpace_orthogonal` phrased through `horizontalSpace`. -/
theorem mfderivAdjoint_mem_horizontalSpace (w : TangentSpace J (f p)) :
    mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p w ∈ horizontalSpace I J f p :=
  isAdjointPair_mfderivAdjoint.apply_mem_orthogonal_ker w

/-! ## The Riemannian condition gives the section property -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **From the Riemannian-submersion condition to the section property.** If `dπ_p` is surjective
and restricts to a linear isometry on the horizontal space, then the adjoint is a right inverse of
it: `A ∘ Aᵃ = id`.

This is `ContinuousLinearMap.IsAdjointPair.isMetricSection_of_surjective_of_inner_map_map`; the
hypothesis it wants, `A` preserving inner products on `(ker A)ᗮ`, is literally
`IsRiemannianSubmersionAtPoint`, since `horizontalSpace = (verticalSpace)ᗮ = (ker A)ᗮ` by
definition. -/
theorem isMetricSection_of_isRiemannianSubmersionAtPoint (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) :
    ContinuousLinearMap.IsMetricSection (mfderiv I J f p)
      (mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact isAdjointPair_mfderivAdjoint.isMetricSection_of_surjective_of_inner_map_map hsub hriem

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The section property in applied form**: `dπ_p (Aᵃ_p w) = w`. Together with
`mfderivAdjoint_mem_horizontalSpace` this says `Aᵃ_p w` *is* the horizontal lift of `w`; see
`horizontalLift_eq_mfderivAdjoint`. -/
theorem mfderiv_mfderivAdjoint (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) (w : TangentSpace J (f p)) :
    mfderiv I J f p (mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p w) = w :=
  isMetricSection_of_isRiemannianSubmersionAtPoint hsub hriem w

/-! ## The projection formulas -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- The adjoint maps **onto** the horizontal space. -/
theorem range_mfderivAdjoint_eq_horizontalSpace (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) :
    LinearMap.range (mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p).toLinearMap
      = horizontalSpace I J f p :=
  isAdjointPair_mfderivAdjoint.range_eq_orthogonal_ker
    (isMetricSection_of_isRiemannianSubmersionAtPoint hsub hriem)

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The projection formula, `𝓗 = Aᵃ ∘ A`.**

The right-hand side mentions no orthogonal projection, no orthogonal complement and no restricted
isomorphism: it is built from `mfderiv` and the fibrewise inverse of the metric, both of whose
regularity is established in `RiemannianGeometry.MfderivAdjoint`. This is what makes the smoothness of
the horizontal projection in `p` reachable at all. -/
theorem horizontalProjection_eq (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) (u : TangentSpace I p) :
    horizontalProjection I J f p u
      = mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p (mfderiv I J f p u) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact (isAdjointPair_mfderivAdjoint.apply_apply_eq_starProjection
    (isMetricSection_of_isRiemannianSubmersionAtPoint hsub hriem) u).symm

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The complementary formula, `𝓥 = id - Aᵃ ∘ A`.** -/
theorem verticalProjection_eq (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) (u : TangentSpace I p) :
    verticalProjection I J f p u
      = u - mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p (mfderiv I J f p u) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact isAdjointPair_mfderivAdjoint.starProjection_ker_eq_sub
    (isMetricSection_of_isRiemannianSubmersionAtPoint hsub hriem) u

/-! ## Reconciling the two horizontal lifts -/

omit [IsManifold J ∞ B] in
/-- **The horizontal lift is the metric adjoint.**

`horizontalLift` is defined through `horizontalEquiv.symm`, the inverse of a restricted linear
isomorphism: correct pointwise, but with no handle on its dependence on `p`. `mfderivAdjoint` is
built from `mfderiv` and the inverse fibre metric and is known to be `C^m`. This lemma says they
agree, and it is the reason the adjoint layer exists.

The proof is uniqueness: `existsUnique_horizontalLift` characterises the lift as the unique
horizontal vector over `v`, and `mfderivAdjoint_mem_horizontalSpace` together with
`mfderiv_mfderivAdjoint` says `Aᵃ v` is such a vector. -/
theorem horizontalLift_eq_mfderivAdjoint (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) (v : TangentSpace J (f p)) :
    (horizontalLift hsub v : TangentSpace I p)
      = mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p v := by
  obtain ⟨w, -, huniq⟩ := existsUnique_horizontalLift hsub v
  rw [huniq _ ⟨horizontalLift_mem hsub v, horizontalLift_spec hsub v⟩,
    huniq _ ⟨mfderivAdjoint_mem_horizontalSpace v, mfderiv_mfderivAdjoint hsub hriem v⟩]

/-! ## The converse -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The converse of `isMetricSection_of_isRiemannianSubmersionAtPoint`.** If the adjoint is a
right inverse of `dπ_p`, then `dπ_p` restricts to a linear isometry on the horizontal space.

No submersion hypothesis is needed: surjectivity of `dπ_p` already follows from the section
property, by `ContinuousLinearMap.IsMetricSection.surjective`. -/
theorem isRiemannianSubmersionAtPoint_of_isMetricSection
    (hsec : ContinuousLinearMap.IsMetricSection (mfderiv I J f p)
      (mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p)) :
    IsRiemannianSubmersionAtPoint I J f p :=
  fun _ hu _ hv ↦ isAdjointPair_mfderivAdjoint.inner_map_map_of_mem_orthogonal_ker hsec hu hv

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The Riemannian-submersion condition is an algebraic identity.** At a point where `dπ_p` is
surjective, being a Riemannian submersion is equivalent to `dπ_p ∘ Aᵃ_p = id`. -/
theorem isRiemannianSubmersionAtPoint_iff_isMetricSection (hsub : IsSubmersionAtPoint I J f p) :
    IsRiemannianSubmersionAtPoint I J f p ↔
      ContinuousLinearMap.IsMetricSection (mfderiv I J f p)
        (mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p) :=
  ⟨isMetricSection_of_isRiemannianSubmersionAtPoint hsub,
    isRiemannianSubmersionAtPoint_of_isMetricSection⟩

end RiemannianGeometry
