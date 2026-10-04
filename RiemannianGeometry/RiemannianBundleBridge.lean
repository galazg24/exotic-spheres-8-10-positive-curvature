/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import RiemannianGeometry.SectionalCurvature
import RiemannianGeometry.KoszulRegularity

/-!
# From metric-as-data to Mathlib's `RiemannianBundle`

This development represents a metric as **data**, `g : Π x, T_xM →L[ℝ] T_xM →L[ℝ] ℝ`, deliberately:
that is what makes the connection and curvature layers pseudo-Riemannian. Mathlib's
orthogonal-complement and orthogonal-projection API, by contrast, needs an `InnerProductSpace`
instance on the fibre.

This file is the bridge, and it is the sanctioned one rather than an ad hoc instance.
`Bundle.ContMDiffRiemannianMetric` (`Geometry/Manifold/VectorBundle/Riemannian.lean`) has *exactly*
the fields this project's data provides — `inner`, `symm`, `pos`, `contMDiff` are literally `g`,
`IsSymm g`, `IsPosDef g`, `IsContMDiffMetricSection E n g` — plus one analytic condition,
`isVonNBounded`. Feeding it to `Bundle.RiemannianBundle` registers **scoped, priority-80**
`NormedAddCommGroup` and `InnerProductSpace` instances on the fibres, which Mathlib documents as
"compatible in a defeq way with the initial topology" and built "without creating diamonds", naming
the tangent bundle as the motivating case.

## Main results

* `isVonNBounded_sublevel_of_posDef` — the one genuine obligation, stated about an abstract
  finite-dimensional normed space so that no `TangentSpace` transport occurs inside its proof.
* `toContMDiffRiemannianMetric` — the bridge.
* `innerProductSpace_demo` — the payoff, *checked* rather than asserted: inside the resulting
  `RiemannianBundle` instance, `Kᗮ`, `Submodule.starProjection` and `Submodule.isCompl_orthogonal`
  all elaborate on submodules of the fibre, and the registered `inner ℝ` **is** the supplied `g`,
  by `rfl`.

## Two operational rules, both found by measurement

**Never bind the fibrewise `InnerProductSpace` (or `NormedAddCommGroup`) to a name.** Writing
`have h : InnerProductSpace ℝ (TangentSpace I p) := inferInstance` — or taking it as a named
instance hypothesis — makes the *opaque local* the preferred instance, and `Kᗮ` then fails with
`InnerProductSpace.toNormedSpace.toModule` against `instModuleTangentSpace`, because the former no
longer unfolds. Let instance search re-find the scoped instance at each use site. Take
`[Bundle.RiemannianBundle (TangentSpace I : M → Type _)]` as the hypothesis instead; that is a
class, not the derived structure, and it is safe.

**State analytic lemmas about the model space, not the fibre.** `isVonNBounded_sublevel_of_posDef`
is about an abstract `V`; applied at `V := E` its `Set E`-typed conclusion is accepted against the
`Set (TangentSpace I b)`-typed goal by plain defeq. This is strictly better than transporting
`FiniteDimensional`, `T2Space`, `NormedAddCommGroup` and `NormedSpace` across the synonym, and it
is the pattern the rest of the submersion layer should follow.

Measured, so it is not folklore: with the `RiemannianBundle` instance in scope, genuine
applications of `riemannTensorAt` and `sectionalCurvatureAt` still elaborate, and `inner ℝ u v` and
`g p u v` coexist in one expression. (`#check @f` on a constant is *not* a diamond test — it runs no
instance search — so the check was done on applications.) `set_option
backward.isDefEq.respectTransparency false`, which Mathlib's own analogous construction uses, turns
out **not** to be needed here.
-/

noncomputable section

open Bundle Bornology Metric Set
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

/-! ## The analytic core

The only real obligation in `ContMDiffRiemannianMetric` is `isVonNBounded`. It is stated here
purely about a finite-dimensional normed space, so that no `TangentSpace` type-synonym transport
is needed anywhere inside the proof. -/

/-- **Unit sublevel sets of a positive-definite continuous quadratic form are bounded.**

In a finite-dimensional real normed space, `{v | q v v < 1}` is von Neumann bounded: `q` attains a
strictly positive minimum `c` on the (compact) unit sphere, whence `q v ≥ c * ‖v‖ ^ 2`, so
`q v < 1` forces `‖v‖ ≤ √(1 / c)`. If the space is a subsingleton the sphere is empty and the
minimum argument fails, but then every set is bounded (`IsVonNBounded.of_subsingleton`). -/
theorem isVonNBounded_sublevel_of_posDef
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (q : V →L[ℝ] V →L[ℝ] ℝ) (hq : ∀ v : V, v ≠ 0 → 0 < q v v) :
    IsVonNBounded ℝ {v : V | q v v < 1} := by
  obtain hV | hV := subsingleton_or_nontrivial V
  · exact IsVonNBounded.of_subsingleton
  · have hcont : Continuous fun v : V ↦ q v v := q.continuous₂.comp₂ continuous_id continuous_id
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
    rw [mem_sphere_zero_iff_norm] at hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu
      exact zero_ne_one hu
    have hc : 0 < q u u := hq u hu0
    refine (NormedSpace.isVonNBounded_iff' ℝ).2 ⟨Real.sqrt (1 / q u u), fun v hv ↦ ?_⟩
    simp only [Set.mem_ofPred_eq] at hv
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv0
    have hsph : ‖v‖⁻¹ • v ∈ sphere (0 : V) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
    have hscale : q (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = (‖v‖ ^ 2)⁻¹ * q v v := by
      simp only [map_smul, smul_apply, smul_eq_mul, ← inv_pow]
      ring
    have hge : q u u ≤ (‖v‖ ^ 2)⁻¹ * q v v := by
      have h := isMinOn_iff.1 hmin _ hsph
      rwa [hscale] at h
    have h2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    have key : ‖v‖ ^ 2 * q u u ≤ q v v :=
      calc ‖v‖ ^ 2 * q u u ≤ ‖v‖ ^ 2 * ((‖v‖ ^ 2)⁻¹ * q v v) :=
            mul_le_mul_of_nonneg_left hge h2.le
        _ = q v v := by field_simp
    have hle : ‖v‖ ^ 2 ≤ 1 / q u u := by
      rw [le_div_iff₀ hc]
      linarith
    calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
      _ ≤ Real.sqrt (1 / q u u) := Real.sqrt_le_sqrt hle

/-! ## The bridge -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {n : ℕ∞ω}

/-- A symmetric, positive-definite, `C^n` metric-as-data is a `ContMDiffRiemannianMetric`. -/
noncomputable def toContMDiffRiemannianMetric
    (hsymm : IsSymm g) (hpos : IsPosDef g) (hg : IsContMDiffMetricSection E n g) :
    Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _) where
  inner := g
  symm := hsymm
  pos := hpos
  isVonNBounded b := isVonNBounded_sublevel_of_posDef (V := E) (g b) fun v hv ↦ hpos b v hv
  contMDiff := hg

/-! ## The payoff

Everything the orthogonal-complement layer needs, demonstrated by elaboration. -/

set_option linter.style.haveILetI false in
set_option linter.unusedSectionVars false in
/-- With the scoped instances open, each tangent space is an inner product space.

Briefed as an anonymous `example`; named so that `#print axioms` can be reported for it. -/
theorem innerProductSpace_demo
    (hsymm : IsSymm g) (hpos : IsPosDef g) (hg : IsContMDiffMetricSection E n g) (p : M) :
    True := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(toContMDiffRiemannianMetric hsymm hpos hg).toRiemannianMetric⟩
  -- (0) the registered inner product on the fibre *is* the given metric-as-data, by `rfl`
  have h₀ : ∀ v w : TangentSpace I p, inner ℝ v w = g p v w := fun _ _ ↦ rfl
  -- (1) the `InnerProductSpace ℝ (TangentSpace I p)` instance is found by instance search
  have h₁ : ∀ v w : TangentSpace I p, inner ℝ v w = inner ℝ w v := fun v w ↦ real_inner_comm w v
  have h₁' : ∀ v : TangentSpace I p, inner ℝ v v = ‖v‖ ^ 2 := fun v ↦ real_inner_self_eq_norm_sq v
  -- (2) `Submodule.orthogonal` on submodules of the fibre
  have h₂ : Submodule ℝ (TangentSpace I p) → Submodule ℝ (TangentSpace I p) := fun K ↦ Kᗮ
  -- (3) `Submodule.starProjection`, for *every* submodule of the fibre
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have h₃ : ∀ K : Submodule ℝ (TangentSpace I p),
      TangentSpace I p →L[ℝ] TangentSpace I p := fun K ↦ K.starProjection
  -- (4) and the two layers compose: `K` and `Kᗮ` are complementary
  have h₄ : ∀ K : Submodule ℝ (TangentSpace I p), IsCompl K Kᗮ :=
    fun K ↦ K.isCompl_orthogonal
  trivial

/-! ## Diamond check

Does having a `RiemannianBundle` instance on the tangent bundle break what previously
elaborated? -/

section DiamondCheck

variable [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]


/-- Both curvature constructions still elaborate *and apply* with a `RiemannianBundle` instance
active on the tangent bundle. -/
noncomputable def diamondCheck_curvature
    (hsymm : IsSymm g) (hpos : IsPosDef g) (hg2 : IsContMDiffMetricSection E ((2 : ℕ∞)) g)
    (p : M) (u v w z : TangentSpace I p) : ℝ × ℝ :=
  (riemannTensorAt hsymm (IsPosDef.isNondegenerate hpos) hg2 p u v w z,
    sectionalCurvatureAt hsymm hpos hg2 p u v)

/-- The scoped inner product and the metric-as-data coexist in one statement. -/
noncomputable def diamondCheck_coexist (p : M) (u v : TangentSpace I p) : ℝ :=
  inner ℝ u v + g p u v

end DiamondCheck


end RiemannianGeometry
