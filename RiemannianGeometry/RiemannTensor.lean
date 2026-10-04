/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.RiemannCurvature

/-!
# The `(0,4)` Riemann curvature tensor

`RiemannianGeometry.RiemannCurvature` builds the curvature *operator*
`riemannCurvatureAt g x : T_xM →L[ℝ] T_xM →L[ℝ] End(T_xM)` of a metric. This file lowers the
remaining index with the metric, giving the fully covariant curvature tensor, and records the two
symmetries that are immediate from the operator.

## The convention, spelled out because every sign downstream depends on it

  `Rm(u, v, w, z) = g (R(u,v) w) z`

with `R(u,v) = riemannCurvatureAt g x u v`, i.e. **the metric contracts the output of the
endomorphism against the last argument**, and the first two arguments are the ones the operator is
antisymmetric in. Written out through the field-level operator, and with the project's convention
that the direction of a covariant derivative is its last argument:

  `Rm(X, Y, Z, W) = g (∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z) W`.

Two consequences worth stating now, since they are what a reader will check against a textbook:

* the antisymmetric pair is the **first** one, `Rm(u,v,w,z) = −Rm(v,u,w,z)`;
* sectional curvature will therefore be `Rm(u,v,v,u)` over the area term, **not** `Rm(u,v,u,v)`.
  With the opposite index convention the sign of every sectional curvature flips, which is why the
  convention is fixed here and referred to rather than re-derived.

## Main results

* `riemannTensorAt` — the bundled `T_xM →L[ℝ] T_xM →L[ℝ] T_xM →L[ℝ] T_xM →L[ℝ] ℝ`.
* `riemannTensorAt_apply` — `Rm(u,v,w,z) = g x (R_x u v w) z`, by `rfl`.
* `riemannTensorAt_apply_fields` — the canonical evaluation against the field-level curvature.
* `riemannTensorAt_swap_left`, `riemannTensorAt_self_left` — first-pair antisymmetry, free from
  `riemannCurvatureAt_swap` and `_self`.

## Why an iterated continuous linear map rather than a `ContinuousMultilinearMap`

The iterated form is what the rest of this development uses (`curvatureAt`, and Mathlib's own
`derivMetricTensor`), it needs no norm on the fibre, and it is what the algebraic symmetry proofs
consume. A `ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ T_xM) ℝ` would need the fibre to carry a
`NormedAddCommGroup` instance, which `TangentSpace I x` does not have — the transport from `E` is
definitional but not syntactic, and introducing it risks a topology mismatch against the bundle's
own instance. Recorded as a deliberate choice, not an oversight.

**One practical note, because it cost time.** The four-fold tower
`T_xM →L T_xM →L T_xM →L T_xM →L ℝ` needs `maxSynthPendingDepth ≥ 3` for its `TopologicalSpace`
instance to be found. The project's `lakefile.toml` sets that, so library builds are fine; a bare
`lake env lean` on a scratch file is not, and reports a missing `TopologicalSpace` instance that
looks like a genuine gap and is not one.

## Regularity

-/

noncomputable section

open Bundle FiberBundle Set VectorField Filter
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {X Y Z W : Π x : M, TangentSpace I x} {x : M}

section Tensor

variable (hsymm : IsSymm g) (hnd : IsNondegenerate g)
  (hg : IsContMDiffMetricSection E ((2 : ℕ∞)) g)

include hsymm hnd hg

/-- Inner layer of `riemannTensorAt`: for fixed `u`, the map `v ↦ (w, z) ↦ g x (R_x u v w) z`.

`(g x) ∘L (R_x u v)` is already continuous linear in `w` and `z`; only the outer two slots need
bundling, and they are bundled by `LinearMap.toContinuousLinearMap` since the fibre is
finite-dimensional. The `T2Space` and `FiniteDimensional` instances must be transported across the
`TangentSpace I x` synonym by hand, exactly as in `curvatureAt`. -/
def riemannTensorAtAux (x : M) (u : TangentSpace I x) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  have : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ (g x) ∘L (riemannCurvatureAt hsymm hnd hg x u v)
      map_add' := fun v v' ↦ by ext w; simp
      map_smul' := fun c v ↦ by ext w; simp }

theorem riemannTensorAtAux_apply (x : M) (u v w z : TangentSpace I x) :
    riemannTensorAtAux hsymm hnd hg x u v w z
      = g x (riemannCurvatureAt hsymm hnd hg x u v w) z := rfl

/-- **The `(0,4)` Riemann curvature tensor at a point**, `Rm(u,v,w,z) = g (R(u,v) w) z`.

See the module docstring for the convention, on which every downstream sign depends. -/
def riemannTensorAt (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] ℝ :=
  have : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ riemannTensorAtAux hsymm hnd hg x u
      map_add' := fun u u' ↦ by
        refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦
          ContinuousLinearMap.ext fun z ↦ ?_
        simp [riemannTensorAtAux_apply, map_add]
      map_smul' := fun c u ↦ by
        refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦
          ContinuousLinearMap.ext fun z ↦ ?_
        simp [riemannTensorAtAux_apply, map_smul] }

/-- **The defining identity of the tensor**, by `rfl`. -/
theorem riemannTensorAt_apply (x : M) (u v w z : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x u v w z
      = g x (riemannCurvatureAt hsymm hnd hg x u v w) z := rfl

/-- **The canonical evaluation theorem.** The tensor, evaluated on the values of vector fields,
is the metric contraction of the field-level curvature of the Levi-Civita connection.

No extension, trivialisation or frame appears, so this certifies the object against `curvature`
rather than against the construction. -/
theorem riemannTensorAt_apply_fields
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% Y) y)
    (hZ : CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% Z) x) :
    riemannTensorAt hsymm hnd hg x (X x) (Y x) (Z x) (W x)
      = g x (curvature (leviCivita g) X Y Z x) (W x) := by
  rw [riemannTensorAt_apply, riemannCurvatureAt_apply hsymm hnd hg hX hY hZ]

/-! ## First-pair antisymmetry
-/

/-- **Antisymmetry in the first pair.** `Rm(u,v,w,z) = −Rm(v,u,w,z)`. -/
theorem riemannTensorAt_swap_left (u v w z : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x u v w z = - riemannTensorAt hsymm hnd hg x v u w z := by
  rw [riemannTensorAt_apply, riemannTensorAt_apply, riemannCurvatureAt_swap hsymm hnd hg u v]
  simp

/-- The diagonal case of `riemannTensorAt_swap_left`. -/
theorem riemannTensorAt_self_left (u w z : TangentSpace I x) :
    riemannTensorAt hsymm hnd hg x u u w z = 0 := by
  rw [riemannTensorAt_apply, riemannCurvatureAt_self hsymm hnd hg u]
  simp

end Tensor

end RiemannianGeometry
