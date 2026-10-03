/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import RiemannianGeometry.Submersion
import RiemannianGeometry.RiemannianBundleBridge

/-!
# The horizontal space of a Riemannian submersion — the pointwise layer

`Foundations.Submersion` defines the vertical space `V_p = ker (dπ_p)` with no metric. This file
adds the metric: the horizontal space is its orthogonal complement, the tangent space splits, and a
tangent vector downstairs has a unique horizontal lift upstairs.

## Main definitions

* `horizontalSpace I J f p` — `(verticalSpace I J f p)ᗮ`.
* `verticalProjection`, `horizontalProjection` — `𝓥_p`, `𝓗_p : T_pM →L[ℝ] T_pM`, as
  `Submodule.starProjection`, i.e. already endomorphisms of the fibre.
* `IsRiemannianSubmersionAtPoint` — `dπ_p` restricted to `H_p` preserves inner products.
* `IsRiemannianSubmersion` — the global notion, with **three separate fields**: smoothness of `f`,
  surjectivity of every `dπ_p`, and the isometry condition on horizontals. They are kept apart
  deliberately: the first two are metric-free and the third is the only Riemannian input.
* `horizontalEquiv`, `horizontalLift`, `horizontalIsometryEquiv` — the lift, as a continuous linear
  equivalence and (under the Riemannian condition) a linear isometry.

## Main results

`isCompl_verticalSpace_horizontalSpace` (the splitting), the projection calculus — idempotence,
`𝓗 u = u − 𝓥 u`, `𝓗 u + 𝓥 u = u`, membership of the images, `u ∈ V ↔ 𝓥 u = u` and its horizontal
twin, and orthogonality `⟪𝓗 u, 𝓥 w⟫ = 0` — and `existsUnique_horizontalLift`.

## Where the metric comes from

`[Bundle.RiemannianBundle (TangentSpace I : M → Type _)]`. A caller holding this project's
metric-as-data supplies it through `Foundations.RiemannianBundleBridge`, and the registered
`inner ℝ` is then *definitionally* that data. Taking the class rather than the derived instances is
deliberate — see below.

## Four instance rules, each of which cost a compile round to find

1. **Never bind the fibrewise `InnerProductSpace` or `NormedAddCommGroup` on `TangentSpace I p` to
   a name.** A named local becomes the preferred instance, its `toModule` stops unfolding to
   `instModuleTangentSpace`, and `Kᗮ` then fails to elaborate. Take the `RiemannianBundle` *class*
   as a hypothesis and let search re-find the scoped instances.
2. **But that rule is about the fibre where `ᗮ` is taken.** `horizontalEquiv` must name
   `NormedAddCommGroup (TangentSpace J (f p))` and `NormedSpace ℝ (TangentSpace J (f p))` — with
   `letI`, since they are data — because `ContinuousLinearEquiv.ofBijective` needs them. That is
   safe precisely because no orthogonal complement is ever taken on the *base* fibre. Rule 1 is not
   universal; it applies to the fibre carrying the complement.
3. `FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)` is needed in
   both projection bodies and ten proofs: it is what discharges
   `Submodule.HasOrthogonalProjection`, without which `starProjection` and `isCompl_orthogonal` are
   unavailable.
4. `ContinuousLinearEquiv.ofBijective` needs `CompleteSpace` of the **target** as well as the
   source, contrary to its docstring's "from a Banach space to a normed space" — the open-mapping
   theorem is used. So this construction is unavailable with a merely-normed base fibre, which
   matters for any later infinite-dimensional generalisation.

`horizontalSpace` is a `def`, so `rw` cannot see through it; `horizontalSpace_def` is provided. The
projection bodies contain a `haveI`, so the way in is `change`, not `simp [verticalProjection]` —
sound because `FiniteDimensional` and `HasOrthogonalProjection` are both `Prop`, so the instance
chosen in the body and the one chosen in a proof are defeq by proof irrelevance.

One orientation trap: Mathlib's `Submodule.starProjection_add_starProjection_orthogonal` gives
`𝓥 u + 𝓗 u = u`. The useful primitive for the other orientation is
`Submodule.starProjection_orthogonal_val : Kᗮ.starProjection u = u − K.starProjection u`, which is
literally `𝓗 u = u − 𝓥 u`.
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
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  {f : M → B} {p : M}

/-! ## §4 Horizontal space, decomposition, projections -/

variable (I J f p) in
/-- The horizontal tangent space: the orthogonal complement of the vertical space. -/
def horizontalSpace : Submodule ℝ (TangentSpace I p) := (verticalSpace I J f p)ᗮ

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem horizontalSpace_def : horizontalSpace I J f p = (verticalSpace I J f p)ᗮ := rfl

variable (I J f p) in
/-- The vertical projection `𝓥`. -/
def verticalProjection : TangentSpace I p →L[ℝ] TangentSpace I p :=
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  (verticalSpace I J f p).starProjection

variable (I J f p) in
/-- The horizontal projection `𝓗`. -/
def horizontalProjection : TangentSpace I p →L[ℝ] TangentSpace I p :=
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  (horizontalSpace I J f p).starProjection

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `T_pM = V_p ⊕ H_p`. -/
theorem isCompl_verticalSpace_horizontalSpace :
    IsCompl (verticalSpace I J f p) (horizontalSpace I J f p) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact (verticalSpace I J f p).isCompl_orthogonal

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem verticalProjection_mem (u : TangentSpace I p) :
    verticalProjection I J f p u ∈ verticalSpace I J f p := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact (verticalSpace I J f p).starProjection_apply_mem u

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem horizontalProjection_mem (u : TangentSpace I p) :
    horizontalProjection I J f p u ∈ horizontalSpace I J f p := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact (horizontalSpace I J f p).starProjection_apply_mem u

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓗 u = u - 𝓥 u`. -/
theorem horizontalProjection_eq_sub (u : TangentSpace I p) :
    horizontalProjection I J f p u = u - verticalProjection I J f p u := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  change (horizontalSpace I J f p).starProjection u = u - (verticalSpace I J f p).starProjection u
  rw [horizontalSpace_def]
  exact Submodule.starProjection_orthogonal_val u

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓗 u + 𝓥 u = u`. -/
theorem horizontalProjection_add_verticalProjection (u : TangentSpace I p) :
    horizontalProjection I J f p u + verticalProjection I J f p u = u := by
  rw [horizontalProjection_eq_sub, sub_add_cancel]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem verticalProjection_verticalProjection (u : TangentSpace I p) :
    verticalProjection I J f p (verticalProjection I J f p u) = verticalProjection I J f p u := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  change (verticalSpace I J f p).starProjection ((verticalSpace I J f p).starProjection u)
    = (verticalSpace I J f p).starProjection u
  exact Submodule.starProjection_eq_self_iff.mpr
    ((verticalSpace I J f p).starProjection_apply_mem u)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem horizontalProjection_horizontalProjection (u : TangentSpace I p) :
    horizontalProjection I J f p (horizontalProjection I J f p u)
      = horizontalProjection I J f p u := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  change (horizontalSpace I J f p).starProjection ((horizontalSpace I J f p).starProjection u)
    = (horizontalSpace I J f p).starProjection u
  exact Submodule.starProjection_eq_self_iff.mpr
    ((horizontalSpace I J f p).starProjection_apply_mem u)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem mem_verticalSpace_iff_verticalProjection_eq_self {u : TangentSpace I p} :
    u ∈ verticalSpace I J f p ↔ verticalProjection I J f p u = u := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact Submodule.starProjection_eq_self_iff.symm

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem mem_horizontalSpace_iff_horizontalProjection_eq_self {u : TangentSpace I p} :
    u ∈ horizontalSpace I J f p ↔ horizontalProjection I J f p u = u := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact Submodule.starProjection_eq_self_iff.symm

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- Horizontal and vertical parts are orthogonal. -/
theorem inner_horizontalProjection_verticalProjection (u w : TangentSpace I p) :
    inner ℝ (horizontalProjection I J f p u) (verticalProjection I J f p w) = 0 :=
  Submodule.inner_left_of_mem_orthogonal (K := verticalSpace I J f p)
    (verticalProjection_mem w) (horizontalProjection_mem u)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- Membership in the horizontal space is orthogonality to everything vertical. -/
theorem mem_horizontalSpace_iff {u : TangentSpace I p} :
    u ∈ horizontalSpace I J f p ↔ ∀ w ∈ verticalSpace I J f p, inner ℝ w u = 0 :=
  Submodule.mem_orthogonal _ u

/-! ## §5 The pointwise Riemannian-submersion condition -/

section Base

variable [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]

variable (I J f p) in
/-- `dπ_p` restricted to the horizontal space is a linear isometry, pointwise form. -/
def IsRiemannianSubmersionAtPoint : Prop :=
  ∀ u ∈ horizontalSpace I J f p, ∀ v ∈ horizontalSpace I J f p,
    inner ℝ (mfderiv I J f p u) (mfderiv I J f p v) = inner ℝ u v

variable (I J f) in
/-- A Riemannian submersion: smooth, a submersion at every point, and a pointwise isometry on
horizontal spaces. The three conditions are kept as separate fields. -/
structure IsRiemannianSubmersion : Prop where
  contMDiff : ContMDiff I J ∞ f
  submersion : ∀ p, IsSubmersionAtPoint I J f p
  isometry : ∀ p, IsRiemannianSubmersionAtPoint I J f p

end Base

/-! ## §6 The pointwise horizontal lift -/

variable (I J f p) in
/-- `dπ_p` restricted to the horizontal space. -/
def restrictHorizontal : horizontalSpace I J f p →L[ℝ] TangentSpace J (f p) :=
  (mfderiv I J f p).comp (horizontalSpace I J f p).subtypeL

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem restrictHorizontal_apply (u : horizontalSpace I J f p) :
    restrictHorizontal I J f p u = mfderiv I J f p (u : TangentSpace I p) := rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem restrictHorizontal_injective :
    Function.Injective (restrictHorizontal I J f p) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  intro u v huv
  have h0 : mfderiv I J f p ((u : TangentSpace I p) - (v : TangentSpace I p)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr huv
  have hV : (u : TangentSpace I p) - (v : TangentSpace I p) ∈ verticalSpace I J f p :=
    mem_verticalSpace_iff.mpr h0
  have hH : (u : TangentSpace I p) - (v : TangentSpace I p) ∈ horizontalSpace I J f p :=
    (horizontalSpace I J f p).sub_mem u.2 v.2
  have hz : (u : TangentSpace I p) - (v : TangentSpace I p) = 0 :=
    Submodule.disjoint_def.mp
      (isCompl_verticalSpace_horizontalSpace (I := I) (J := J) (f := f) (p := p)).disjoint _ hV hH
  exact Subtype.ext (sub_eq_zero.mp hz)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
theorem restrictHorizontal_surjective (hsub : IsSubmersionAtPoint I J f p) :
    Function.Surjective (restrictHorizontal I J f p) := by
  intro v
  obtain ⟨u, hu⟩ := hsub v
  have hvert : mfderiv I J f p (verticalProjection I J f p u) = 0 :=
    mem_verticalSpace_iff.mp (verticalProjection_mem u)
  refine ⟨⟨horizontalProjection I J f p u, horizontalProjection_mem u⟩, ?_⟩
  change mfderiv I J f p (horizontalProjection I J f p u) = v
  rw [horizontalProjection_eq_sub, map_sub, hvert, sub_zero, hu]

/-- `dπ_p : H_p ≃ T_{f p}B`. -/
def horizontalEquiv (hsub : IsSubmersionAtPoint I J f p) :
    horizontalSpace I J f p ≃L[ℝ] TangentSpace J (f p) :=
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : NormedAddCommGroup (TangentSpace J (f p)) := inferInstanceAs (NormedAddCommGroup E')
  letI : NormedSpace ℝ (TangentSpace J (f p)) := inferInstanceAs (NormedSpace ℝ E')
  haveI : FiniteDimensional ℝ (TangentSpace J (f p)) := inferInstanceAs (FiniteDimensional ℝ E')
  ContinuousLinearEquiv.ofBijective (restrictHorizontal I J f p)
    (LinearMap.ker_eq_bot.mpr restrictHorizontal_injective)
    (LinearMap.range_eq_top.mpr (restrictHorizontal_surjective hsub))

/-- The horizontal lift of a tangent vector on the base. -/
def horizontalLift (hsub : IsSubmersionAtPoint I J f p) (v : TangentSpace J (f p)) :
    TangentSpace I p := (((horizontalEquiv hsub).symm v : horizontalSpace I J f p) :
      TangentSpace I p)

omit [IsManifold I ∞ M] [IsManifold J ∞ B] in
theorem horizontalLift_mem (hsub : IsSubmersionAtPoint I J f p) (v : TangentSpace J (f p)) :
    horizontalLift hsub v ∈ horizontalSpace I J f p := ((horizontalEquiv hsub).symm v).2

omit [IsManifold I ∞ M] [IsManifold J ∞ B] in
theorem horizontalLift_spec (hsub : IsSubmersionAtPoint I J f p) (v : TangentSpace J (f p)) :
    mfderiv I J f p (horizontalLift hsub v) = v :=
  (horizontalEquiv hsub).apply_symm_apply v

omit [IsManifold I ∞ M] [IsManifold J ∞ B] in
theorem existsUnique_horizontalLift (hsub : IsSubmersionAtPoint I J f p)
    (v : TangentSpace J (f p)) :
    ∃! w : TangentSpace I p, w ∈ horizontalSpace I J f p ∧ mfderiv I J f p w = v := by
  refine ⟨horizontalLift hsub v, ⟨horizontalLift_mem hsub v, horizontalLift_spec hsub v⟩, ?_⟩
  intro w hw
  have hinj : (⟨w, hw.1⟩ : horizontalSpace I J f p)
      = ⟨horizontalLift hsub v, horizontalLift_mem hsub v⟩ := by
    apply restrictHorizontal_injective
    change mfderiv I J f p w = mfderiv I J f p (horizontalLift hsub v)
    rw [hw.2, horizontalLift_spec]
  exact congrArg Subtype.val hinj

/-! ## Bonus: the isometry upgrade -/

section Isometry

variable [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]

/-- Under the pointwise Riemannian-submersion condition, `dπ_p|_{H_p}` is a linear isometry. -/
def horizontalIsometryEquiv (hsub : IsSubmersionAtPoint I J f p)
    (hriem : IsRiemannianSubmersionAtPoint I J f p) :
    horizontalSpace I J f p ≃ₗᵢ[ℝ] TangentSpace J (f p) :=
  LinearEquiv.isometryOfInner (horizontalEquiv hsub).toLinearEquiv fun x y => by
    change inner ℝ (mfderiv I J f p (x : TangentSpace I p))
      (mfderiv I J f p (y : TangentSpace I p)) = inner ℝ (x : TangentSpace I p) y
    exact hriem x x.2 y y.2

end Isometry

end RiemannianGeometry
