/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.LeviCivita
import RiemannianGeometry.CurvatureBundled

/-!
# The Riemann curvature operator of a metric

The general curvature layer (`RiemannianGeometry.Curvature*`) builds
`R_x : T_xM →L[𝕜] T_xM →L[𝕜] End(V x)` for an arbitrary connection on an arbitrary vector bundle,
under a local-regularity hypothesis on the connection. `RiemannianGeometry.LeviCivita` constructs the
Levi-Civita connection of a metric supplied as data. This file joins them: it **discharges** that
hypothesis for the Levi-Civita connection, and specialises the bundled operator to
`V := TangentSpace I`, `cov := leviCivita g`, giving an operator that depends on the metric alone.

## Main results

* `riemannCurvatureAt` — `R_x : T_xM →L[ℝ] T_xM →L[ℝ] End(T_xM)`, from the metric alone.
* `riemannCurvatureAt_apply` — the canonical evaluation theorem.
* `riemannCurvatureAt_swap`, `riemannCurvatureAt_self` — antisymmetry and vanishing on the diagonal.

## Hypotheses, and generality

Only three properties of `g` are used: **symmetry**, **weak nondegeneracy**
(`(∀ w, g x v w = 0) → v = 0`), and being a `C²` section of `Hom(TM, Hom(TM, ℝ))`. Positive
definiteness appears nowhere, so `riemannCurvatureAt` is the **pseudo-Riemannian** curvature
operator; the Riemannian case is the special case where `g` happens to be positive definite. A later
sectional-curvature layer may specialise, but nothing here should.

`C²` is also the exact order: the connection costs one derivative and its curvature costs another,
so a `C²` metric gives a curvature operator at each point but no smoothness of `x ↦ R_x`. That is
why the smoothness order is fixed at `n := 2` here rather than carried as a parameter — a `C^(k+2)`
metric would give a `C^k` curvature *field*, which is a separate statement and not needed yet.
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
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-! ## The Levi-Civita connection discharges the repaired regularity hypothesis -/

/-- **The Levi-Civita connection satisfies `CovC2LocalMDiffAt`.**

A theorem, not an assumption. It is derived from the stronger and more reusable
`contMDiffAt_leviCivita` (`C^(m+1)` data on an open set gives a `C^m` section) at `m := 1`, packaged
as `mdiffAtCovSection_leviCivita`.
-/
theorem covC2LocalMDiffAt_leviCivita (hsymm : IsSymm g) (hnd : IsNondegenerate g)
    (hg : IsContMDiffMetricSection E ((2 : ℕ∞)) g) (x : M) :
    CovC2LocalMDiffAt E (leviCivita g) x := by
  intro s hs
  obtain ⟨u, hu_sub, hu_open, hxu⟩ := mem_nhds_iff.1 hs
  exact mdiffAtCovSection_leviCivita hu_open hxu hsymm hnd (ContMDiff.contMDiffOn hg)
    (fun y hy ↦ (hu_sub hy).contMDiffWithinAt)

/-! ## The Riemann curvature operator -/

section Riemann

variable (hsymm : IsSymm g) (hnd : IsNondegenerate g)
  (hg : IsContMDiffMetricSection E ((2 : ℕ∞)) g)

include hsymm hnd hg

/-- **The Riemann curvature operator of a metric, at a point.**

  `R_x : T_xM →L[ℝ] T_xM →L[ℝ] (T_xM →L[ℝ] T_xM)`

`curvatureAt` of the general layer, specialised to `V := TangentSpace I` and
`cov := leviCivita g`, with every hypothesis of that layer discharged from `g`:
`isCovariantDerivativeOn_leviCivita` for the connection axioms and
`covC2LocalMDiffAt_leviCivita` for the local regularity. **No auxiliary hypothesis remains**: the
object is constructible from a symmetric, nondegenerate, `C²` metric and nothing else. -/
def riemannCurvatureAt (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  curvatureAt (F := E) (V := fun y : M ↦ TangentSpace I y) (n := (2 : ℕ∞))
    (isCovariantDerivativeOn_leviCivita hsymm hnd fun y ↦ (hg y).mdifferentiableAt (by simp))
    (covC2LocalMDiffAt_leviCivita hsymm hnd hg x) (by simp) (by simp)

/-- **The canonical evaluation theorem.** `R_x (X x) (Y x) (Z x) = R(X, Y)Z x`.

No extension, trivialisation or frame appears, so this certifies that `riemannCurvatureAt`
represents the field-level curvature of `leviCivita g` and is not an artefact of the construction.
Every later result about `riemannCurvatureAt` should be derived from this. -/
theorem riemannCurvatureAt_apply
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% Y) y)
    (hZ : CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% Z) x) :
    riemannCurvatureAt hsymm hnd hg x (X x) (Y x) (Z x) = curvature (leviCivita g) X Y Z x :=
  curvatureAt_apply (F := E) (V := fun y : M ↦ TangentSpace I y) (n := (2 : ℕ∞)) _ _ _ _ hX hY hZ

/-- **Antisymmetry.** -/
theorem riemannCurvatureAt_swap (u w : TangentSpace I x) :
    riemannCurvatureAt hsymm hnd hg x u w = - riemannCurvatureAt hsymm hnd hg x w u :=
  curvatureAt_swap (F := E) (V := fun y : M ↦ TangentSpace I y) (n := (2 : ℕ∞)) _ _ _ _ u w

/-- **Vanishing on the diagonal.** -/
theorem riemannCurvatureAt_self (u : TangentSpace I x) :
    riemannCurvatureAt hsymm hnd hg x u u = 0 :=
  curvatureAt_self (F := E) (V := fun y : M ↦ TangentSpace I y) (n := (2 : ℕ∞)) _ _ _ _ u

end Riemann

end RiemannianGeometry
