/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The vertical space of a smooth map, and the pointwise submersion condition

The first layer of the Riemannian-submersion development: the vertical tangent space of a map
`f : M → B` at a point, defined **intrinsically** as the kernel of its differential, and the
submersion condition as surjectivity of that differential.

## Main definitions

* `verticalSpace I J f p` — `ker (mfderiv I J f p)`, a submodule of `T_pM`.
* `IsSubmersionAtPoint I J f p` — `Function.Surjective (mfderiv I J f p)`.

## Main results

* `mem_verticalSpace_iff`, `isClosed_verticalSpace`.
* `finrank_verticalSpace_add` — rank–nullity: at a point where `f` is a submersion,
  `dim V_p + dim T_{f p}B = dim T_pM`.

## Why not Mathlib's `IsSubmersionAt`

`Mathlib/Geometry/Manifold/Submersion.lean` defines a submersion by **local normal form**: charts in
which `f` looks like `(u,v) ↦ u`, plus a chosen linear isomorphism `E ≃L[𝕜] E'' × F`. That is the
right definition in infinite dimensions, and it gives locality, openness and products. But it is
**not connected to the differential**: the module's own docstring says "Future work will prove that
our definition implies the latter [surjectivity of `mfderiv`], and that both are equivalent for
finite-dimensional manifolds", and its TODO list contains, unproved, both directions of that bridge
and the statement that the complement is isomorphic to `ker (mfderiv I J f x)`.

## Instance transports

`TangentSpace I p` is a type synonym for the model space `E`, and neither `T1Space` nor
`FiniteDimensional` crosses it automatically; both are supplied by `inferInstanceAs`, as elsewhere
in this development. Nothing here needs a metric, an orthogonal complement, or positive
definiteness — those enter only with the horizontal space.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  {f : M → B} {p : M}

variable (I J f p) in
/-- **The vertical tangent space** of `f` at `p`: the kernel of the differential.

Intrinsic — no chart, no trivialisation, no metric. For a submersion this is the tangent space to
the fibre through `p`, but nothing here needs the fibre to be a manifold. -/
def verticalSpace : Submodule ℝ (TangentSpace I p) :=
  LinearMap.ker (mfderiv I J f p).toLinearMap

variable (I J f p) in
/-- **The pointwise submersion condition**: the differential at `p` is surjective.

This is the classical finite-dimensional definition, taken in preference to Mathlib's chart-based
`IsSubmersionAt` because only this form gives access to `ker (mfderiv …)`. See the module
docstring. 

-/
def IsSubmersionAtPoint : Prop := Function.Surjective (mfderiv I J f p)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ B] in
theorem mem_verticalSpace_iff {u : TangentSpace I p} :
    u ∈ verticalSpace I J f p ↔ mfderiv I J f p u = 0 := LinearMap.mem_ker

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ B] in
/-- The vertical space is closed. (It is the kernel of a continuous linear map into a Hausdorff
space; the `T1Space` instance has to be transported across the `TangentSpace` synonym.) -/
theorem isClosed_verticalSpace :
    IsClosed ((verticalSpace I J f p : Submodule ℝ (TangentSpace I p)) : Set (TangentSpace I p)) :=
  have : T1Space (TangentSpace J (f p)) := inferInstanceAs (T1Space E')
  (mfderiv I J f p).isClosed_ker

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **Rank–nullity at a submersion point.** `dim V_p + dim T_{f p}B = dim T_pM`. -/
theorem finrank_verticalSpace_add (hsurj : IsSubmersionAtPoint I J f p) :
    Module.finrank ℝ (verticalSpace I J f p) + Module.finrank ℝ (TangentSpace J (f p))
      = Module.finrank ℝ (TangentSpace I p) := by
  have hfd : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have hr : LinearMap.range (mfderiv I J f p).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker (mfderiv I J f p).toLinearMap
  rw [hr, finrank_top] at h
  have h2 : Module.finrank ℝ (TangentSpace J (f p))
      + Module.finrank ℝ (verticalSpace I J f p) = Module.finrank ℝ (TangentSpace I p) := h
  omega

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ B] in
/-- **A smooth right inverse makes `f` a submersion along its image.**

If `f ∘ s = id` with both maps differentiable, then `df_{s b} ∘ ds_b = id` by the chain rule, so
`df_{s b}` is surjective with `ds_b` an explicit preimage-producing map. No chart, no slice, and no
metric: this is the cheapest source of `IsSubmersionAtPoint` there is, and it is exactly what a
fibration with a section supplies.

Note what it does **not** give: surjectivity away from the image of `s`. A map with a *global*
section is a submersion only along that section unless something else moves the base point — for a
quotient map by a group action, the action itself does, which is how a single section propagates to
every point. -/
theorem isSubmersionAtPoint_of_rightInverse {s : B → M} {b : B}
    (hf : MDifferentiableAt I J f (s b)) (hs : MDifferentiableAt J I s b)
    (hfs : f ∘ s = id) : IsSubmersionAtPoint I J f (s b) := by
  have h := mfderiv_comp b hf hs
  rw [hfs, mfderiv_id] at h
  intro v
  refine ⟨mfderiv J I s b v, ?_⟩
  have hv := congrArg
    (fun L : TangentSpace J b →L[ℝ] TangentSpace J b => L v) h
  exact hv.symm

end RiemannianGeometry
