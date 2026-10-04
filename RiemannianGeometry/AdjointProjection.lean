/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Adjoint pairs and metric sections of continuous linear maps

Let `A : E₁ →L[ℝ] E₂` be a continuous linear map between real inner-product spaces, and let
`K := LinearMap.ker A.toLinearMap`. This file studies a second map `B : E₂ →L[ℝ] E₁` which is an
adjoint of `A` and, in the main case of interest, a right inverse of it. The conclusion is that
`B ∘ A` is the orthogonal projection onto `Kᗮ`.

This is the algebraic core of the pointwise theory of Riemannian submersions: at a point `p` of a
submersion `f`, take `E₁` to be the tangent space at `p`, `E₂` the tangent space at `f p`, `A` the
differential, and `B` the horizontal lift. Nothing here mentions manifolds, bundles or tangent
spaces; the geometric layer instantiates these statements fibrewise.

## Main definitions

* `ContinuousLinearMap.IsAdjointPair A B` — the relation `⟪B v, x⟫_ℝ = ⟪v, A x⟫_ℝ`.
* `ContinuousLinearMap.IsMetricSection A B` — the relation `A (B v) = v`.

## Main results

Assuming only `hB : IsAdjointPair A B`:

* `ContinuousLinearMap.IsAdjointPair.unique` — `B` is determined by `A`.
* `ContinuousLinearMap.IsAdjointPair.symm` — the relation is symmetric in `A` and `B`.
* `ContinuousLinearMap.IsAdjointPair.range_le_orthogonal_ker` — `range B ≤ Kᗮ`.
* `ContinuousLinearMap.IsAdjointPair.ker_eq_orthogonal_range` — `ker B = (range A)ᗮ`, and its
  mirror image `ContinuousLinearMap.IsAdjointPair.ker_eq_orthogonal_range'` — `K = (range B)ᗮ`.

Assuming in addition `hAB : IsMetricSection A B`:

* `ContinuousLinearMap.IsAdjointPair.inner_map_map` — `B` preserves inner products.
* `ContinuousLinearMap.IsAdjointPair.range_eq_orthogonal_ker` — `range B = Kᗮ`.
* `ContinuousLinearMap.IsAdjointPair.apply_apply_eq_starProjection` —
  `B (A x) = Kᗮ.starProjection x`.
* `ContinuousLinearMap.IsAdjointPair.starProjection_ker_eq_sub` —
  `K.starProjection x = x - B (A x)`.
* `ContinuousLinearMap.IsAdjointPair.inner_map_map_of_mem_orthogonal_ker` — `A` preserves inner
  products on `Kᗮ`.

Conversely, `ContinuousLinearMap.IsAdjointPair.isMetricSection_of_surjective_of_inner_map_map`
recovers `IsMetricSection A B` from surjectivity of `A` together with the statement that `A`
preserves inner products on `Kᗮ`. This is the direction the geometric layer needs, since there the
submersion hypothesis is what is given and the section is what must be produced.

## Implementation notes

The adjoint relation is taken as a *hypothesis*, not as `ContinuousLinearMap.adjoint A`. The
intended application builds its adjoint from a fibre metric supplied as data, and mentioning
Mathlib's `adjoint` would force an instance path that construction deliberately avoids.
`ContinuousLinearMap.isAdjointPair_adjoint` reconciles the two views by checking that Mathlib's
adjoint is an adjoint pair in the present sense; `ContinuousLinearMap.IsAdjointPair.unique` shows
there is nothing else it could be.

Completeness is used sparingly and is recorded per declaration. `CompleteSpace E₂` is needed only
for `ContinuousLinearMap.isAdjointPair_adjoint`, where Mathlib's `adjoint` demands it.
`CompleteSpace E₁` is needed only where `Submodule.starProjection` appears, to know that `K` has an
orthogonal projection at all; `ContinuousLinearMap.IsAdjointPair.range_eq_orthogonal_ker`, in
particular, needs no completeness of either space. Finite-dimensionality is never used.

## Tags

adjoint, orthogonal projection, Riemannian submersion, horizontal lift
-/

open scoped InnerProductSpace

namespace RiemannianGeometry.AdjointProjection

/-- The kernel of a continuous linear map out of a complete inner-product space is closed, hence
complete, hence has an orthogonal projection.

Instance search does not find this unaided. Mathlib has all three ingredients —
`ContinuousLinearMap.isClosed_ker`, `IsClosed.completeSpace_coe` and
`Submodule.HasOrthogonalProjection.ofCompleteSpace` — but no instance chaining them, because the
middle one is a theorem taking an `IsClosed` hypothesis, which instance search cannot supply.

**Deliberately `scoped`, not global.** Mathlib's omission is treated here as a design decision to
be respected rather than an oversight to be patched: a project should not claim global synthesis
territory for a Mathlib namespace merely because it is convenient. The class is a `Prop`
(`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:49`), so a diamond would be harmless by
proof irrelevance and the instance has no recursive premise, so it cannot loop — the reason for
scoping is not safety but ownership. It is not needed in the finite-dimensional setting the
manifold layer works in, where `HasOrthogonalProjection` is already free.
-/
scoped instance instHasOrthogonalProjectionKer
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] (A : E₁ →L[ℝ] E₂) :
    (LinearMap.ker A.toLinearMap).HasOrthogonalProjection :=
  have : CompleteSpace (LinearMap.ker A.toLinearMap) := A.isClosed_ker.completeSpace_coe
  inferInstance

end RiemannianGeometry.AdjointProjection

open scoped RiemannianGeometry.AdjointProjection

namespace ContinuousLinearMap

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- `B` is a metric adjoint of `A`: the defining identity `⟪B v, x⟫_ℝ = ⟪v, A x⟫_ℝ`, taken as a
hypothesis rather than read off `ContinuousLinearMap.adjoint`. The argument order matches Mathlib's
`ContinuousLinearMap.adjoint_inner_left`. -/
def IsAdjointPair (A : E₁ →L[ℝ] E₂) (B : E₂ →L[ℝ] E₁) : Prop :=
  ∀ (v : E₂) (x : E₁), ⟪B v, x⟫_ℝ = ⟪v, A x⟫_ℝ

/-- `B` is a section of `A`: `A ∘ B = id`. Combined with `ContinuousLinearMap.IsAdjointPair` this
says that `A` restricts to a surjective isometry from the orthogonal complement of its kernel onto
`E₂`; see `ContinuousLinearMap.IsAdjointPair.inner_map_map_of_mem_orthogonal_ker` and
`ContinuousLinearMap.IsAdjointPair.isMetricSection_of_surjective_of_inner_map_map`. -/
def IsMetricSection (A : E₁ →L[ℝ] E₂) (B : E₂ →L[ℝ] E₁) : Prop :=
  ∀ v : E₂, A (B v) = v

variable {A : E₁ →L[ℝ] E₂} {B : E₂ →L[ℝ] E₁}

/-! ### Reconciliation with `ContinuousLinearMap.adjoint` -/

/-- Mathlib's adjoint is an adjoint pair in the sense of `ContinuousLinearMap.IsAdjointPair`. With
`ContinuousLinearMap.IsAdjointPair.unique`, this identifies the two notions completely. -/
theorem isAdjointPair_adjoint [CompleteSpace E₁] [CompleteSpace E₂] (A : E₁ →L[ℝ] E₂) :
    IsAdjointPair A (adjoint A) :=
  fun v x ↦ adjoint_inner_left A x v

/-- An adjoint of `A` is unique. -/
theorem IsAdjointPair.unique {B' : E₂ →L[ℝ] E₁} (hB : IsAdjointPair A B)
    (hB' : IsAdjointPair A B') : B = B' :=
  ContinuousLinearMap.ext fun v ↦ ext_inner_right ℝ fun x ↦ by rw [hB v x, hB' v x]

/-- The adjoint relation is symmetric: because the real inner product is symmetric, `B` is an
adjoint of `A` exactly when `A` is an adjoint of `B`. -/
theorem IsAdjointPair.symm (hB : IsAdjointPair A B) : IsAdjointPair B A := fun x v ↦ by
  rw [real_inner_comm v (A x), ← hB v x, real_inner_comm x (B v)]

/-- On complete spaces, an adjoint pair consists of `A` and Mathlib's adjoint of `A`. -/
theorem IsAdjointPair.eq_adjoint [CompleteSpace E₁] [CompleteSpace E₂] (hB : IsAdjointPair A B) :
    B = adjoint A :=
  hB.unique (isAdjointPair_adjoint A)

/-! ### Consequences of the adjoint relation alone -/

/-- The range of an adjoint of `A` is orthogonal to the kernel of `A`. No section hypothesis is
needed: this is just `⟪B v, x⟫_ℝ = ⟪v, A x⟫_ℝ = 0` for `x` in the kernel. -/
theorem IsAdjointPair.range_le_orthogonal_ker (hB : IsAdjointPair A B) :
    LinearMap.range B.toLinearMap ≤ (LinearMap.ker A.toLinearMap)ᗮ := by
  rintro _ ⟨v, rfl⟩
  refine (Submodule.mem_orthogonal' _ _).2 fun x hx ↦ ?_
  have hAx : A x = 0 := hx
  change ⟪B v, x⟫_ℝ = 0
  rw [hB v x, hAx, inner_zero_right]

/-- Every value of an adjoint of `A` is orthogonal to the kernel of `A`. -/
theorem IsAdjointPair.apply_mem_orthogonal_ker (hB : IsAdjointPair A B) (v : E₂) :
    B v ∈ (LinearMap.ker A.toLinearMap)ᗮ :=
  hB.range_le_orthogonal_ker ⟨v, rfl⟩

/-- The kernel of an adjoint of `A` is the orthogonal complement of the range of `A`. No section
hypothesis is needed. -/
theorem IsAdjointPair.ker_eq_orthogonal_range (hB : IsAdjointPair A B) :
    LinearMap.ker B.toLinearMap = (LinearMap.range A.toLinearMap)ᗮ := by
  ext v
  constructor
  · intro hv
    have hv0 : B v = 0 := hv
    refine (Submodule.mem_orthogonal' _ _).2 ?_
    rintro _ ⟨x, rfl⟩
    change ⟪v, A x⟫_ℝ = 0
    rw [← hB v x, hv0, inner_zero_left]
  · intro hv
    have h : ∀ x : E₁, ⟪B v, x⟫_ℝ = 0 := fun x ↦ by
      rw [hB v x]
      exact (Submodule.mem_orthogonal' _ _).1 hv _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.2 (inner_self_eq_zero (𝕜 := ℝ).1 (h (B v)))

/-- The kernel of `A` is the orthogonal complement of the range of any adjoint of `A`: the mirror
image of `ContinuousLinearMap.IsAdjointPair.ker_eq_orthogonal_range` under
`ContinuousLinearMap.IsAdjointPair.symm`. No section hypothesis is needed. -/
theorem IsAdjointPair.ker_eq_orthogonal_range' (hB : IsAdjointPair A B) :
    LinearMap.ker A.toLinearMap = (LinearMap.range B.toLinearMap)ᗮ :=
  hB.symm.ker_eq_orthogonal_range

/-! ### Consequences of the adjoint relation together with the section property -/

/-- A section of `A` is injective. -/
theorem IsMetricSection.injective (hAB : IsMetricSection A B) : Function.Injective B :=
  fun u v h ↦ by rw [← hAB u, ← hAB v, h]

/-- `A` is surjective as soon as it has a section. -/
theorem IsMetricSection.surjective (hAB : IsMetricSection A B) : Function.Surjective A :=
  fun v ↦ ⟨B v, hAB v⟩

/-- An adjoint which is also a section preserves inner products. -/
theorem IsAdjointPair.inner_map_map (hB : IsAdjointPair A B) (hAB : IsMetricSection A B)
    (u v : E₂) : ⟪B u, B v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [hB u (B v), hAB v]

/-- An adjoint which is also a section preserves norms. -/
theorem IsAdjointPair.norm_map (hB : IsAdjointPair A B) (hAB : IsMetricSection A B) (v : E₂) :
    ‖B v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hB.inner_map_map hAB v v]

/-- On the orthogonal complement of `ker A`, the composite `B ∘ A` is the identity. This is the
step with content: `x - B (A x)` lies in `ker A` because `A (B (A x)) = A x`, and it lies in
`(ker A)ᗮ` because both `x` and `B (A x)` do, so it is orthogonal to itself. -/
theorem IsAdjointPair.apply_apply_of_mem_orthogonal_ker (hB : IsAdjointPair A B)
    (hAB : IsMetricSection A B) {x : E₁} (hx : x ∈ (LinearMap.ker A.toLinearMap)ᗮ) :
    B (A x) = x := by
  have hker : x - B (A x) ∈ LinearMap.ker A.toLinearMap := by
    change A (x - B (A x)) = 0
    rw [map_sub, hAB (A x), sub_self]
  have horth : x - B (A x) ∈ (LinearMap.ker A.toLinearMap)ᗮ :=
    Submodule.sub_mem _ hx (hB.apply_mem_orthogonal_ker (A x))
  have hzero : ⟪x - B (A x), x - B (A x)⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 horth _ hker
  exact (sub_eq_zero.1 (inner_self_eq_zero (𝕜 := ℝ).1 hzero)).symm

/-- The range of an adjoint which is also a section is exactly the orthogonal complement of the
kernel of `A`. Note that no completeness hypothesis is needed: the inclusion `Kᗮ ≤ range B` is
witnessed directly by `x = B (A x)`, so neither closedness of `range B` nor the identity
`Kᗮᗮ = K` is invoked. -/
theorem IsAdjointPair.range_eq_orthogonal_ker (hB : IsAdjointPair A B)
    (hAB : IsMetricSection A B) :
    LinearMap.range B.toLinearMap = (LinearMap.ker A.toLinearMap)ᗮ :=
  le_antisymm hB.range_le_orthogonal_ker fun _ hx ↦
    ⟨A _, hB.apply_apply_of_mem_orthogonal_ker hAB hx⟩

/-- **The projection formula.** `B ∘ A` is the orthogonal projection onto `(ker A)ᗮ`. -/
theorem IsAdjointPair.apply_apply_eq_starProjection [CompleteSpace E₁] (hB : IsAdjointPair A B)
    (hAB : IsMetricSection A B) (x : E₁) :
    B (A x) = (LinearMap.ker A.toLinearMap)ᗮ.starProjection x := by
  have hker : x - B (A x) ∈ LinearMap.ker A.toLinearMap := by
    change A (x - B (A x)) = 0
    rw [map_sub, hAB (A x), sub_self]
  exact (Submodule.eq_starProjection_of_mem_orthogonal' (hB.apply_mem_orthogonal_ker (A x))
    (Submodule.le_orthogonal_orthogonal _ hker) (by abel)).symm

/-- The vertical projection, as a formula with no orthogonal-projection machinery on the right. -/
theorem IsAdjointPair.starProjection_ker_eq_sub [CompleteSpace E₁] (hB : IsAdjointPair A B)
    (hAB : IsMetricSection A B) (x : E₁) :
    (LinearMap.ker A.toLinearMap).starProjection x = x - B (A x) := by
  rw [hB.apply_apply_eq_starProjection hAB x, Submodule.starProjection_orthogonal_val]
  abel

/-- `A` preserves inner products on the orthogonal complement of its kernel. -/
theorem IsAdjointPair.inner_map_map_of_mem_orthogonal_ker (hB : IsAdjointPair A B)
    (hAB : IsMetricSection A B) {x y : E₁} (hx : x ∈ (LinearMap.ker A.toLinearMap)ᗮ)
    (hy : y ∈ (LinearMap.ker A.toLinearMap)ᗮ) : ⟪A x, A y⟫_ℝ = ⟪x, y⟫_ℝ :=
  calc ⟪A x, A y⟫_ℝ = ⟪B (A x), B (A y)⟫_ℝ := (hB.inner_map_map hAB _ _).symm
    _ = ⟪x, y⟫_ℝ := by
        rw [hB.apply_apply_of_mem_orthogonal_ker hAB hx,
          hB.apply_apply_of_mem_orthogonal_ker hAB hy]

/-! ### Idempotence -/

/-- `B` is unchanged by reinserting it into the section relation. -/
theorem IsMetricSection.apply_apply_apply (hAB : IsMetricSection A B) (v : E₂) :
    B (A (B v)) = B v := by rw [hAB v]

/-- Values of `B` are fixed by the orthogonal projection onto `(ker A)ᗮ`. Only the adjoint
relation is used. -/
theorem IsAdjointPair.starProjection_orthogonal_ker_apply [CompleteSpace E₁]
    (hB : IsAdjointPair A B) (v : E₂) :
    (LinearMap.ker A.toLinearMap)ᗮ.starProjection (B v) = B v :=
  Submodule.starProjection_eq_self_iff.2 (hB.apply_mem_orthogonal_ker v)

/-- Values of `B` are annihilated by the orthogonal projection onto `ker A`. -/
theorem IsAdjointPair.starProjection_ker_apply [CompleteSpace E₁] (hB : IsAdjointPair A B)
    (hAB : IsMetricSection A B) (v : E₂) :
    (LinearMap.ker A.toLinearMap).starProjection (B v) = 0 := by
  rw [hB.starProjection_ker_eq_sub hAB, hAB.apply_apply_apply, sub_self]

/-- `B ∘L A` is idempotent. -/
theorem IsMetricSection.isIdempotentElem_comp (hAB : IsMetricSection A B) :
    IsIdempotentElem (B ∘L A) := by
  ext x
  simpa using hAB.apply_apply_apply (A x)

/-! ### The converse -/

/-- **The converse.** If `B` is an adjoint of `A`, if `A` is surjective, and if `A` preserves inner
products on the orthogonal complement of its kernel, then `B` is a section of `A`.

This is the form the geometric layer consumes: for a Riemannian submersion the differential is
surjective and restricts to a linear isometry on the horizontal space, and the horizontal lift is
then automatically a section. Completeness of `E₁` is used only to split an arbitrary preimage into
its vertical and horizontal parts. -/
theorem IsAdjointPair.isMetricSection_of_surjective_of_inner_map_map [CompleteSpace E₁]
    (hB : IsAdjointPair A B) (hA : Function.Surjective A)
    (hiso : ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ, ∀ y ∈ (LinearMap.ker A.toLinearMap)ᗮ,
      ⟪A x, A y⟫_ℝ = ⟪x, y⟫_ℝ) :
    IsMetricSection A B := by
  have key : ∀ p ∈ (LinearMap.ker A.toLinearMap)ᗮ, B (A p) = p := by
    intro p hp
    have hd : B (A p) - p ∈ (LinearMap.ker A.toLinearMap)ᗮ :=
      Submodule.sub_mem _ (hB.apply_mem_orthogonal_ker (A p)) hp
    have hzero : ⟪B (A p) - p, B (A p) - p⟫_ℝ = 0 := by
      rw [inner_sub_left, hB (A p) (B (A p) - p), hiso p hp _ hd, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero (𝕜 := ℝ).1 hzero)
  intro v
  obtain ⟨x, rfl⟩ := hA v
  have hp : (LinearMap.ker A.toLinearMap)ᗮ.starProjection x ∈ (LinearMap.ker A.toLinearMap)ᗮ :=
    Submodule.starProjection_apply_mem _ _
  have hAp : A ((LinearMap.ker A.toLinearMap)ᗮ.starProjection x) = A x := by
    have hmem : (LinearMap.ker A.toLinearMap).starProjection x ∈ LinearMap.ker A.toLinearMap :=
      Submodule.starProjection_apply_mem _ _
    have hzero : A ((LinearMap.ker A.toLinearMap).starProjection x) = 0 := hmem
    rw [Submodule.starProjection_orthogonal_val, map_sub, hzero, sub_zero]
  calc A (B (A x)) = A (B (A ((LinearMap.ker A.toLinearMap)ᗮ.starProjection x))) := by rw [hAp]
    _ = A ((LinearMap.ker A.toLinearMap)ᗮ.starProjection x) := by rw [key _ hp]
    _ = A x := hAp

end ContinuousLinearMap
