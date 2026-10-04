/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.HorizontalAdjoint
import RiemannianGeometry.RelatedVectorFields

/-!
# Horizontal and vertical vector fields, and the horizontal lift of a field on the base

`RiemannianGeometry.HorizontalSpace` splits each tangent space of a submersion `f : M → B` into its
vertical and horizontal parts, and `RiemannianGeometry.HorizontalAdjoint` identifies the horizontal
projection and the horizontal lift with the fibrewise metric adjoint `dπ*` of
`RiemannianGeometry.MfderivAdjoint`. This file promotes all of that from a single point to a vector
field, and draws the first consequence for Lie brackets.

## Main definitions

* `horizontalPart I J f X`, `verticalPart I J f X` — the fields `𝓗X` and `𝓥X` obtained by applying
  the pointwise projections to a field `X` on `M`.
* `IsHorizontalField I J f X`, `IsVerticalField I J f X` — `X z` lies in the horizontal
  (resp. vertical) space at every `z`.
* `horizontalLiftField I J f Y` — the **horizontal lift** `Yᴴ` of a field `Y` on the base,
  defined as `z ↦ dπ*_z (Y (f z))`.

## Main results

* `horizontalPart_add_verticalPart`, `horizontalPart_horizontalPart`,
  `verticalPart_verticalPart`, `horizontalPart_mem`, `verticalPart_mem` — the pointwise projection
  calculus, transported to fields.
* `isHorizontalField_iff`, `isVerticalField_iff` — `IsHorizontalField X ↔ 𝓗X = X` and its twin.
* `contMDiffAt_horizontalPart`, `contMDiffAt_verticalPart` — **the payoff**: the two projections
  of a `C^m` field are `C^m`, with no subbundle theory whatever. The route is
  `horizontalProjection_eq`, which rewrites `𝓗X` as `dπ*(dπ X)`, followed by the two regularity
  theorems of `RiemannianGeometry.MfderivAdjoint`.
* `horizontalLiftField_mem`, `isHorizontalField_horizontalLiftField` — `Yᴴ` is horizontal, with
  **no hypothesis at all** (`mfderivAdjoint_mem_horizontalSpace`).
* `mfderiv_horizontalLiftField` — `Yᴴ` is `f`-related to `Y`.
* `horizontalLiftField_eq_horizontalLift` — it agrees with the pointwise lift of
  `RiemannianGeometry.HorizontalSpace`.
* `contMDiffAt_horizontalLiftField` — `Yᴴ` is `C^m` when `Y` is.
* `eq_horizontalLiftField_of_mem_of_mfderiv_eq`, `eq_horizontalLiftField` — uniqueness: a
  horizontal field `f`-related to `Y` *is* `Yᴴ`.
* `mfderiv_mlieBracket_horizontalLiftField` — `dπ [Xᴴ, Yᴴ] = [X, Y]`, from
  `mfderiv_mlieBracket_of_related`.
* `horizontalProjection_mlieBracket_horizontalLiftField` — **O'Neill's Lemma 1(2)**:
  `𝓗 [Xᴴ, Yᴴ] = [X, Y]ᴴ`.
* `verticalProjection_mlieBracket_horizontalLiftField` — the complementary vertical part,
  `𝓥 [Xᴴ, Yᴴ] = [Xᴴ, Yᴴ] − [X, Y]ᴴ`.

## Regularity accounting

Exactly one derivative of `f` is spent, and it is spent in
`contMDiffAt_mfderiv_inCoordinates` (through `ContMDiffWithinAt.mfderivWithin_const`, which needs
`m + 1 ≤ n`). Nothing else in this file differentiates anything. So:

* `f` of class `C^(m+1)` on an open set, both fibre metrics of class `C^m`, and `X` a `C^m` field
  give `𝓗X` and `𝓥X` of class `C^m`; likewise `Y` of class `C^m` gives `Yᴴ` of class `C^m`.
* The bracket statements are at order `n` with `minSmoothness ℝ 2 ≤ n` and `(n : ℕ∞ω) ≠ ∞`, the
  hypotheses of `mfderiv_mlieBracket_of_related`. They are *not* specialised to `n = 2`: `n` stays
  a variable, and the two `IsManifold` premises `mfderiv_mlieBracket_of_related` carries at orders
  `1` and `n + 1` are discharged from the ambient `[IsManifold I ∞ M]` by instance search, using
  the `ENat.LEInfty.coe_add_one` instance of `RiemannianGeometry.ManifoldOrder`.

`(n : ℕ∞ω) ≠ ∞` is a genuine restriction inherited from `mfderiv_mlieBracket_of_related`; the
finite-order statement is what is available, and it is what is stated.

## The submersion hypotheses, and the form they are taken in

`horizontalProjection_eq` needs `IsSubmersionAtPoint` and `IsRiemannianSubmersionAtPoint` at the
point where it is applied, and the smoothness proofs apply it at every point of a neighbourhood of
`p`. The hypotheses are therefore taken in the **eventual** form `∀ᶠ z in 𝓝 p, …`, which is the
weakest form the proofs consume: `ContMDiffAt` and `mlieBracket` are germ notions, so nothing
stronger is ever needed. A caller holding the bundled `IsRiemannianSubmersion I J f` supplies both
by `Filter.Eventually.of_forall (h.submersion)` and `Filter.Eventually.of_forall (h.isometry)`.

## Instance notes

* `CompleteSpace E` is **not** an added hypothesis: `FiniteDimensional ℝ E` is in the ambient block
  and Mathlib's `FiniteDimensional.complete` is an instance, so the `[CompleteSpace E]` premise of
  `contMDiffAt_mfderivAdjoint_apply` and the `[CompleteSpace E]`, `[CompleteSpace E']` premises of
  `mfderiv_mlieBracket_of_related` are found by search. Similarly `SeparatingDual ℝ E'` is a global
  instance over `ℝ`. **No typeclass assumption beyond the stated ambient block is added anywhere in
  this file.**
* The `RiemannianBundle` instance on `TangentSpace J` is not needed for `horizontalPart`,
  `verticalPart` or the two field predicates, so it is introduced only after them; the metric on
  the base enters first with the adjoint.
* Rule 1 of `RiemannianGeometry.HorizontalSpace` is respected: no fibrewise `InnerProductSpace` or
  `NormedAddCommGroup` on a tangent space is ever bound to a local name.
-/

noncomputable section

open Bundle VectorField
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
  {f : M → B}

/-! ## Horizontal and vertical parts of a vector field

Only the metric upstairs is used in this section. -/

variable (I J f) in
/-- **The horizontal part `𝓗X` of a vector field**: the pointwise horizontal projection of `X`. -/
def horizontalPart (X : Π z : M, TangentSpace I z) : Π z : M, TangentSpace I z :=
  fun z ↦ horizontalProjection I J f z (X z)

variable (I J f) in
/-- **The vertical part `𝓥X` of a vector field**: the pointwise vertical projection of `X`. -/
def verticalPart (X : Π z : M, TangentSpace I z) : Π z : M, TangentSpace I z :=
  fun z ↦ verticalProjection I J f z (X z)

variable {X : Π z : M, TangentSpace I z}

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓗X z` is horizontal. -/
theorem horizontalPart_mem (z : M) : horizontalPart I J f X z ∈ horizontalSpace I J f z :=
  horizontalProjection_mem _

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓥X z` is vertical. -/
theorem verticalPart_mem (z : M) : verticalPart I J f X z ∈ verticalSpace I J f z :=
  verticalProjection_mem _

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`X = 𝓗X + 𝓥X`**, as sections of the tangent bundle. -/
theorem horizontalPart_add_verticalPart :
    horizontalPart I J f X + verticalPart I J f X = X :=
  funext fun z ↦ horizontalProjection_add_verticalProjection (X z)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓥X = X − 𝓗X`, as sections. This is the form in which the regularity of `𝓥X` is deduced from
that of `𝓗X`. -/
theorem verticalPart_eq_sub : verticalPart I J f X = X - horizontalPart I J f X := by
  funext z
  change verticalProjection I J f z (X z) = X z - horizontalProjection I J f z (X z)
  rw [eq_sub_iff_add_eq, add_comm]
  exact horizontalProjection_add_verticalProjection (X z)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`𝓗` is idempotent on fields**: `𝓗(𝓗X) = 𝓗X`. -/
theorem horizontalPart_horizontalPart :
    horizontalPart I J f (horizontalPart I J f X) = horizontalPart I J f X :=
  funext fun z ↦ horizontalProjection_horizontalProjection (X z)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`𝓥` is idempotent on fields**: `𝓥(𝓥X) = 𝓥X`. -/
theorem verticalPart_verticalPart :
    verticalPart I J f (verticalPart I J f X) = verticalPart I J f X :=
  funext fun z ↦ verticalProjection_verticalProjection (X z)

variable (I J f) in
/-- **A horizontal vector field**: every value is horizontal. -/
def IsHorizontalField (X : Π z : M, TangentSpace I z) : Prop :=
  ∀ z, X z ∈ horizontalSpace I J f z

variable (I J f) in
/-- **A vertical vector field**: every value is vertical. -/
def IsVerticalField (X : Π z : M, TangentSpace I z) : Prop :=
  ∀ z, X z ∈ verticalSpace I J f z

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`X` is horizontal iff `𝓗X = X`.** -/
theorem isHorizontalField_iff : IsHorizontalField I J f X ↔ horizontalPart I J f X = X :=
  ⟨fun h ↦ funext fun z ↦ mem_horizontalSpace_iff_horizontalProjection_eq_self.mp (h z),
    fun h z ↦ mem_horizontalSpace_iff_horizontalProjection_eq_self.mpr (congrFun h z)⟩

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`X` is vertical iff `𝓥X = X`.** -/
theorem isVerticalField_iff : IsVerticalField I J f X ↔ verticalPart I J f X = X :=
  ⟨fun h ↦ funext fun z ↦ mem_verticalSpace_iff_verticalProjection_eq_self.mp (h z),
    fun h z ↦ mem_verticalSpace_iff_verticalProjection_eq_self.mpr (congrFun h z)⟩

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓗X` is a horizontal field. -/
theorem isHorizontalField_horizontalPart : IsHorizontalField I J f (horizontalPart I J f X) :=
  fun z ↦ horizontalPart_mem z

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `𝓥X` is a vertical field. -/
theorem isVerticalField_verticalPart : IsVerticalField I J f (verticalPart I J f X) :=
  fun z ↦ verticalPart_mem z

/-! ## Regularity of the projections

The metric on the base enters from here on. -/

section Base

variable [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]

omit [FiniteDimensional ℝ E'] in
/-- **The horizontal part of a `C^m` field is `C^m`.**

This is the payoff of the adjoint layer, and it needs no subbundle theory: `horizontalProjection_eq`
rewrites `𝓗X` as `dπ*(dπ X)`, `contMDiffAt_mfderiv_apply` gives the regularity of `dπ X` as a field
along `f`, and `contMDiffAt_mfderivAdjoint_apply` gives that of its image under the adjoint. One
derivative of `f` is spent, in `contMDiffAt_mfderiv_inCoordinates`; the metrics are used at order
`m`. -/
theorem contMDiffAt_horizontalPart {m : ℕ∞} {u : Set M} {p : M}
    (hu : IsOpen u) (hpu : p ∈ u) (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hgM : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z
        (tangentMetric I M z)) p)
    (hgB : ContMDiffAt J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q
        (tangentMetric J B q)) (f p))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ContMDiffAt I I.tangent ((m : ℕ∞ω)) (T% X) p) :
    ContMDiffAt I I.tangent ((m : ℕ∞ω)) (T% (horizontalPart I J f X)) p := by
  have key : ContMDiffAt I I.tangent ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' E z
        (mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f z
          (mfderiv I J f z (X z)))) p :=
    contMDiffAt_mfderivAdjoint_apply hu hpu hf hgM hgB (tangentMetric_nondegenerate I M p)
      (contMDiffAt_mfderiv_apply hu hpu hf hX)
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hsub, hriem] with z hz hz'
  simp only [horizontalPart, horizontalProjection_eq hz hz']

omit [FiniteDimensional ℝ E'] in
/-- **The vertical part of a `C^m` field is `C^m`.** Immediate from
`contMDiffAt_horizontalPart` and `verticalPart_eq_sub`, using Mathlib's
`ContMDiffAt.sub_section`. -/
theorem contMDiffAt_verticalPart {m : ℕ∞} {u : Set M} {p : M}
    (hu : IsOpen u) (hpu : p ∈ u) (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hgM : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z
        (tangentMetric I M z)) p)
    (hgB : ContMDiffAt J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q
        (tangentMetric J B q)) (f p))
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hX : ContMDiffAt I I.tangent ((m : ℕ∞ω)) (T% X) p) :
    ContMDiffAt I I.tangent ((m : ℕ∞ω)) (T% (verticalPart I J f X)) p := by
  rw [verticalPart_eq_sub]
  exact hX.sub_section (contMDiffAt_horizontalPart hu hpu hf hgM hgB hsub hriem hX)

/-! ## The horizontal lift of a vector field on the base -/

variable (I J f) in
/-- **The horizontal lift `Yᴴ` of a vector field on the base**: `Yᴴ z = dπ*_z (Y (f z))`.

Defined through the fibrewise metric adjoint rather than through `horizontalLift`, precisely so
that its regularity is available (`contMDiffAt_horizontalLiftField`); the two agree, by
`horizontalLiftField_eq_horizontalLift`. -/
def horizontalLiftField (Y : Π q : B, TangentSpace J q) : Π z : M, TangentSpace I z :=
  fun z ↦ mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f z (Y (f z))

variable {Y : Π q : B, TangentSpace J q}

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`Yᴴ z` is horizontal, with no hypothesis whatever** — not even that `f` is a submersion at
`z`. This is `mfderivAdjoint_mem_horizontalSpace`. -/
theorem horizontalLiftField_mem (z : M) :
    horizontalLiftField I J f Y z ∈ horizontalSpace I J f z :=
  mfderivAdjoint_mem_horizontalSpace _

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- `Yᴴ` is a horizontal field. -/
theorem isHorizontalField_horizontalLiftField :
    IsHorizontalField I J f (horizontalLiftField I J f Y) :=
  fun z ↦ horizontalLiftField_mem z

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`Yᴴ` is `f`-related to `Y`**: `dπ_z (Yᴴ z) = Y (f z)`. This is `mfderiv_mfderivAdjoint`, and
is the hypothesis `mfderiv_mlieBracket_of_related` consumes. -/
theorem mfderiv_horizontalLiftField {z : M} (hsub : IsSubmersionAtPoint I J f z)
    (hriem : IsRiemannianSubmersionAtPoint I J f z) :
    mfderiv I J f z (horizontalLiftField I J f Y z) = Y (f z) :=
  mfderiv_mfderivAdjoint hsub hriem _

omit [IsManifold J ∞ B] in
/-- **The lift of a field is the pointwise lift of its values.** -/
theorem horizontalLiftField_eq_horizontalLift {z : M} (hsub : IsSubmersionAtPoint I J f z)
    (hriem : IsRiemannianSubmersionAtPoint I J f z) :
    horizontalLiftField I J f Y z = horizontalLift hsub (Y (f z)) :=
  (horizontalLift_eq_mfderivAdjoint hsub hriem _).symm

omit [FiniteDimensional ℝ E'] in
/-- **The lift of a `C^m` field is a `C^m` field.**

`z ↦ (Y (f z) : TB)` is `(T% Y) ∘ f`, a composition, so `ContMDiffAt.comp` supplies the field
along `f` that `contMDiffAt_mfderivAdjoint_apply` wants. As with the projections, the single
derivative of `f` is the one spent in `contMDiffAt_mfderiv_inCoordinates`. -/
theorem contMDiffAt_horizontalLiftField {m : ℕ∞} {u : Set M} {p : M}
    (hu : IsOpen u) (hpu : p ∈ u) (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hgM : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z
        (tangentMetric I M z)) p)
    (hgB : ContMDiffAt J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q
        (tangentMetric J B q)) (f p))
    (hY : ContMDiffAt J J.tangent ((m : ℕ∞ω)) (T% Y) (f p)) :
    ContMDiffAt I I.tangent ((m : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) p := by
  have hml : ((m : ℕ∞ω)) ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((m : ℕ∞ω)) f p :=
    ((hf p hpu).contMDiffAt (hu.mem_nhds hpu)).of_le hml
  exact contMDiffAt_mfderivAdjoint_apply hu hpu hf hgM hgB
    (tangentMetric_nondegenerate I M p) (hY.comp p hfp)

omit [IsManifold J ∞ B] in
/-- **Uniqueness of the horizontal lift, pointwise.** A horizontal vector over `Y (f z)` is
`Yᴴ z`. -/
theorem eq_horizontalLiftField_of_mem_of_mfderiv_eq {z : M} (hsub : IsSubmersionAtPoint I J f z)
    (hriem : IsRiemannianSubmersionAtPoint I J f z) {v : TangentSpace I z}
    (hv : v ∈ horizontalSpace I J f z) (hrel : mfderiv I J f z v = Y (f z)) :
    v = horizontalLiftField I J f Y z := by
  obtain ⟨w, -, huniq⟩ := existsUnique_horizontalLift hsub (Y (f z))
  rw [huniq _ ⟨hv, hrel⟩,
    huniq _ ⟨horizontalLiftField_mem z, mfderiv_horizontalLiftField hsub hriem⟩]

omit [IsManifold J ∞ B] in
/-- **Uniqueness of the horizontal lift, as fields.** A horizontal field `f`-related to `Y` is
`Yᴴ`. -/
theorem eq_horizontalLiftField (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z) (hX : IsHorizontalField I J f X)
    (hrel : ∀ z, mfderiv I J f z (X z) = Y (f z)) : X = horizontalLiftField I J f Y :=
  funext fun z ↦
    eq_horizontalLiftField_of_mem_of_mfderiv_eq (hsub z) (hriem z) (hX z) (hrel z)

/-! ## The bracket of horizontal lifts -/

/-- **The bracket of the lifts is `f`-related to the bracket**:
`dπ_p [Xᴴ, Yᴴ]_p = [X, Y]_{f p}`.

This is `mfderiv_mlieBracket_of_related` fed with `mfderiv_horizontalLiftField`. The order `n` is
kept variable: the two `IsManifold` premises at orders `1` and `n + 1` are found by instance search
from the ambient `[IsManifold I ∞ M]` and `[IsManifold J ∞ B]`, and `CompleteSpace E`,
`CompleteSpace E'` and `SeparatingDual ℝ E'` from finite-dimensionality over `ℝ`. -/
theorem mfderiv_mlieBracket_horizontalLiftField {n : ℕ∞} {p : M}
    {X Y : Π q : B, TangentSpace J q} (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hXH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f X)) z)
    (hYH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    mfderiv I J f p
        (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
      = mlieBracket J X Y (f p) := by
  have hXrel : ∀ᶠ z in 𝓝 p,
      mfderiv I J f z (horizontalLiftField I J f X z) = X (f z) := by
    filter_upwards [hsub, hriem] with z hz hz' using mfderiv_horizontalLiftField hz hz'
  have hYrel : ∀ᶠ z in 𝓝 p,
      mfderiv I J f z (horizontalLiftField I J f Y z) = Y (f z) := by
    filter_upwards [hsub, hriem] with z hz hz' using mfderiv_horizontalLiftField hz hz'
  exact mfderiv_mlieBracket_of_related hn hn' hf hXrel hYrel hXH hYH hX hY

/-- **O'Neill's Lemma 1(2): the horizontal part of `[Xᴴ, Yᴴ]` is the lift of `[X, Y]`.**

`𝓗_p [Xᴴ, Yᴴ]_p = ([X, Y])ᴴ p`. Proved by `horizontalProjection_eq`, which turns the left side
into `dπ*_p (dπ_p [Xᴴ, Yᴴ]_p)`, followed by
`mfderiv_mlieBracket_horizontalLiftField`; the resulting `dπ*_p ([X, Y]_{f p})` is `([X, Y])ᴴ p`
by definition. 

-/
theorem horizontalProjection_mlieBracket_horizontalLiftField {n : ℕ∞} {p : M}
    {X Y : Π q : B, TangentSpace J q} (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hXH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f X)) z)
    (hYH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    horizontalProjection I J f p
        (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
      = horizontalLiftField I J f (mlieBracket J X Y) p := by
  rw [horizontalProjection_eq hsub.self_of_nhds hriem.self_of_nhds,
    mfderiv_mlieBracket_horizontalLiftField hn hn' hf hsub hriem hXH hYH hX hY]
  rfl

/-- **The vertical part of `[Xᴴ, Yᴴ]`.**

`𝓥_p [Xᴴ, Yᴴ]_p = [Xᴴ, Yᴴ]_p − ([X, Y])ᴴ p`. This is the object O'Neill's Lemma 2 identifies
with `2 A_X Y`. That identification is **not** made here, and no `A`-tensor is defined in this
file: the statement below is exactly the difference of the bracket and the lift of the bracket,
and nothing more. -/
theorem verticalProjection_mlieBracket_horizontalLiftField {n : ℕ∞} {p : M}
    {X Y : Π q : B, TangentSpace J q} (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiffAt I J ((n : ℕ∞ω)) f p)
    (hsub : ∀ᶠ z in 𝓝 p, IsSubmersionAtPoint I J f z)
    (hriem : ∀ᶠ z in 𝓝 p, IsRiemannianSubmersionAtPoint I J f z)
    (hXH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f X)) z)
    (hYH : ∀ᶠ z in 𝓝 p,
      ContMDiffAt I I.tangent ((n : ℕ∞ω)) (T% (horizontalLiftField I J f Y)) z)
    (hX : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% X) q)
    (hY : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y) q) :
    verticalProjection I J f p
        (mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p)
      = mlieBracket I (horizontalLiftField I J f X) (horizontalLiftField I J f Y) p
        - horizontalLiftField I J f (mlieBracket J X Y) p := by
  rw [verticalProjection_eq hsub.self_of_nhds hriem.self_of_nhds,
    mfderiv_mlieBracket_horizontalLiftField hn hn' hf hsub hriem hXH hYH hX hY]
  rfl

/-! ## O'Neill's Lemma 1(1)

Placed here, upstream of everything that uses it, because both `ONeillLemmaTwo` and
`ONeillLemmaOne` consume it: keeping the diagonal case in the former and the general case in the
latter would have made "delete the special case and re-derive it" circular. It needs nothing beyond
this file. -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **O'Neill's Lemma 1(1), pointwise**: `⟨Y₁ᴴ, Y₂ᴴ⟩ z = ⟨Y₁, Y₂⟩ (f z)`.

`IsRiemannianSubmersionAtPoint` is *already* stated for two
independent horizontal vectors, `horizontalLiftField_mem` places both lifts in `H_z` with no
hypothesis, and `mfderiv_horizontalLiftField` identifies `dπ_z (Yᵢᴴ z)` with `Yᵢ (f z)`. **No
differentiability and no metric smoothness are used**, and the submersion and isometry conditions
are consumed only at `z`. -/
theorem tangentMetric_horizontalLiftField_apply
    {Y₁ Y₂ : Π q : B, TangentSpace J q} {z : M} (hsub : IsSubmersionAtPoint I J f z)
    (hriem : IsRiemannianSubmersionAtPoint I J f z) :
    tangentMetric I M z (horizontalLiftField I J f Y₁ z) (horizontalLiftField I J f Y₂ z)
      = tangentMetric J B (f z) (Y₁ (f z)) (Y₂ (f z)) := by
  have h := hriem _ (horizontalLiftField_mem (Y := Y₁) z) _ (horizontalLiftField_mem (Y := Y₂) z)
  rw [mfderiv_horizontalLiftField (Y := Y₁) hsub hriem,
    mfderiv_horizontalLiftField (Y := Y₂) hsub hriem] at h
  rw [← inner_eq_tangentMetric, ← inner_eq_tangentMetric]
  exact h.symm

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **O'Neill's Lemma 1(1)**: `⟨Y₁ᴴ, Y₂ᴴ⟩ = ⟨Y₁, Y₂⟩ ∘ f`, as functions on `M`.

The statement in the form O'Neill writes it. The pointwise form
`tangentMetric_horizontalLiftField_apply` is what the Koszul terms actually consume, and
`ONeillLemmaOne.tangentMetric_horizontalLiftField_eventuallyEq` is what the derivative terms
consume. 

-/
theorem tangentMetric_horizontalLiftField {Y₁ Y₂ : Π q : B, TangentSpace J q}
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z) :
    (fun z ↦ tangentMetric I M z (horizontalLiftField I J f Y₁ z)
        (horizontalLiftField I J f Y₂ z))
      = (fun q ↦ tangentMetric J B q (Y₁ q) (Y₂ q)) ∘ f :=
  funext fun z ↦ tangentMetric_horizontalLiftField_apply (hsub z) (hriem z)

/-! ## Every horizontal vector is the value of a basic field

O'Neill's arguments repeatedly quantify over *basic fields* and conclude something about a *vector*.
Closing that gap needs the converse: a horizontal vector at `p` must be exhibited as the value at
`p` of a basic field regular enough for the machinery being applied.

This is the base-side analogue of `ONeillLemmaTwo.verticalExtend`, and it is stated here as a
reusable lemma rather than being inlined into whichever nondegeneracy argument happens to need it.
The construction is exactly what the name suggests: extend the base tangent vector `dπ_p u` to a
local field on `B` with `FiberBundle.extend`, then lift it. Nothing about `u` is used except
`dπ_p u`, which is why the statement is about `𝓗_p u` rather than about `u`.

Regularity is available at **every** finite order, because `FiberBundle.exists_contMDiffOn_extend`
supplies a `C^∞` extension on a neighbourhood — note the neighbourhood: `contMDiffAt_extend` gives
smoothness only at the fibre's own base point, which is not enough for anything that differentiates
the field. -/

omit [FiniteDimensional ℝ E'] in
/-- **The horizontal projection of any tangent vector is the value of a basic field**, of class
`C^m` on a neighbourhood of `f p`, for any finite `m`. -/
theorem exists_basic_eq_horizontalProjection {m : ℕ∞}
    (hsub : IsSubmersionAtPoint I J f p) (hriem : IsRiemannianSubmersionAtPoint I J f p)
    (u : TangentSpace I p) :
    ∃ W : Π q : B, TangentSpace J q,
      (∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((m : ℕ∞ω)) (T% W) q) ∧
        horizontalLiftField I J f W p = horizontalProjection I J f p u := by
  refine ⟨FiberBundle.extend E' (mfderiv I J f p u), ?_, ?_⟩
  · obtain ⟨s, hs, hsσ⟩ :=
      FiberBundle.exists_contMDiffOn_extend (k := (∞ : ℕ∞ω)) J E' (mfderiv I J f p u)
    have hle : ((m : ℕ∞ω)) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
    filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs)] with q hq
    exact (hsσ.of_le hle).contMDiffAt (mem_interior_iff_mem_nhds.mp hq)
  · rw [horizontalProjection_eq hsub hriem u]
    change mfderivAdjoint (tangentMetric I M) (tangentMetric J B) f p
      (FiberBundle.extend E' (mfderiv I J f p u) (f p)) = _
    rw [FiberBundle.extend_apply_self]

omit [FiniteDimensional ℝ E'] in
/-- **Every horizontal vector at `p` is the value at `p` of a basic field**, of class `C^m` on a
neighbourhood of `f p`, for any finite `m`.

The form O'Neill's arguments consume: it is what lets "for all basic fields" be turned into "for all
horizontal vectors". -/
theorem exists_basic_eq_of_mem_horizontalSpace {m : ℕ∞}
    (hsub : IsSubmersionAtPoint I J f p) (hriem : IsRiemannianSubmersionAtPoint I J f p)
    {v : TangentSpace I p} (hv : v ∈ horizontalSpace I J f p) :
    ∃ W : Π q : B, TangentSpace J q,
      (∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((m : ℕ∞ω)) (T% W) q) ∧
        horizontalLiftField I J f W p = v := by
  obtain ⟨W, hW, hWv⟩ := exists_basic_eq_horizontalProjection (m := m) hsub hriem v
  refine ⟨W, hW, ?_⟩
  rwa [mem_horizontalSpace_iff_horizontalProjection_eq_self.mp hv] at hWv

end Base

end RiemannianGeometry
