/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.RiemannTensor
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Sectional curvature

This is the one place in the development that specialises to **positive-definite** metrics. The
curvature operator, the `(0,4)` tensor and all of the algebraic symmetries hold for a symmetric
weakly nondegenerate metric — pseudo-Riemannian generality — and are proved there. Sectional
curvature is a quotient, and it is only the Riemannian case in which the denominator is guaranteed
nonzero, so positivity enters here and nowhere earlier.

## Main results

* `IsPosDef` — positive definiteness of a metric-as-data.
* `gramDet` — `g(u,u) g(v,v) − g(u,v)²`, the squared area of the parallelogram spanned by `u`, `v`.
* `gramDet_pos` — it is **positive** for linearly independent `u`, `v` when `g` is positive
  definite. This is the strict Cauchy–Schwarz inequality, proved directly rather than through an
  `InnerProductSpace` instance, which a metric supplied as data does not carry.
* `sectionalCurvatureAt` — `Rm(u,v,v,u) / gramDet g x u v`.

## The sign convention

With `Rm(u,v,w,z) = g (R(u,v) w) z` (see `RiemannianGeometry.RiemannTensor`), the numerator is

  `Rm(u, v, v, u) = g (R(u,v) v) u`

and **not** `Rm(u,v,u,v)`. Getting this backwards flips the sign of every sectional curvature, so it
is worth stating the check: for the round sphere with the standard connection this convention gives
positive sectional curvature, because `R(u,v)v` points along `u`. The two conventions differ by the
last-pair antisymmetry `Rm(u,v,v,u) = −Rm(u,v,u,v)` of `RiemannianGeometry.CurvatureMetric`.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {x : M}

/-- **Positive definiteness** of a metric supplied as data. Assumed *only* from here on; every
earlier result in this development uses at most symmetry and weak nondegeneracy. -/
def IsPosDef (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∀ (y : M) (v : TangentSpace I y), v ≠ 0 → 0 < g y v v

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Positive definiteness implies weak nondegeneracy, so the Riemannian case really is a special
case of everything proved earlier. -/
theorem IsPosDef.isNondegenerate (hpos : IsPosDef g) : IsNondegenerate g := by
  intro y v hv
  by_contra h
  exact absurd (hv v) (ne_of_gt (hpos y v h))

/-- The **Gram determinant** of a pair of tangent vectors: the squared area of the parallelogram
they span, and the denominator of sectional curvature. -/
def gramDet (g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M)
    (u v : TangentSpace I x) : ℝ := g x u u * g x v v - (g x u v) ^ 2

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The quadratic expansion behind the Cauchy–Schwarz argument. -/
theorem gram_expand (hsymm : IsSymm g) (u v : TangentSpace I x) (t : ℝ) :
    g x (u + t • v) (u + t • v) = g x u u + 2 * t * g x u v + t ^ 2 * g x v v := by
  simp only [map_add, map_smul]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hsymm x v u]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **The denominator of sectional curvature is positive.**
-/
theorem gramDet_pos (hsymm : IsSymm g) (hpos : IsPosDef g) {u v : TangentSpace I x}
    (hli : LinearIndependent ℝ ![u, v]) : 0 < gramDet g x u v := by
  have hpair := LinearIndependent.pair_iff.mp hli
  have hv : v ≠ 0 := by
    intro h
    have := (hpair 0 1 (by simp [h])).2
    norm_num at this
  have ha : 0 < g x v v := hpos x v hv
  set t : ℝ := -(g x u v) / (g x v v) with ht
  have hne : u + t • v ≠ 0 := by
    intro h
    have := (hpair 1 t (by simpa using h)).1
    norm_num at this
  have hq := hpos x (u + t • v) hne
  rw [gram_expand hsymm u v t, ht] at hq
  have hane : g x v v ≠ 0 := ne_of_gt ha
  rw [gramDet]
  field_simp at hq
  nlinarith [hq, ha, sq_nonneg (g x u v)]

/-- **A vector is never independent of itself.** Pure linear algebra, stated because the degenerate
branch of `sectionalCurvatureAt` is reached through it.
-/
theorem not_linearIndependent_self {R N : Type*} [DivisionRing R] [AddCommGroup N] [Module R N]
    (v : N) : ¬ LinearIndependent R ![v, v] := by
  rw [LinearIndependent.pair_iff]
  intro h
  have h1 := (h 1 (-1) (by simp)).1
  exact one_ne_zero h1

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **A dependent pair has vanishing Gram determinant.**

The converse of `gramDet_pos`, and the fact that turns `sectionalCurvatureAt`'s junk value on a
degenerate pair into an honest `0`: on such a pair the denominator is `0`, so the quotient is
Lean's `r / 0 = 0`. A `0 ≤ K` statement quantified over *all* pairs is therefore true at the
degenerate ones for a stated reason rather than by accident.

Neither symmetry nor positive-definiteness is used: it is bilinearity alone. -/
theorem gramDet_eq_zero_of_not_linearIndependent {u v : TangentSpace I x}
    (h : ¬ LinearIndependent ℝ ![u, v]) : gramDet g x u v = 0 := by
  rw [LinearIndependent.pair_iff] at h
  simp only [not_forall, not_and_or] at h
  obtain ⟨s, t, hst, hne⟩ := h
  rcases eq_or_ne t 0 with rfl | ht
  · have hs : s ≠ 0 := by rcases hne with h' | h'; exacts [h', absurd rfl h']
    have hu : u = 0 := by
      have h0 : s • u = 0 := by simpa using hst
      exact (smul_eq_zero.1 h0).resolve_left hs
    simp [gramDet, hu]
  · have h2 : (t⁻¹ * s) • u + v = 0 := by
      have := congrArg (fun w : TangentSpace I x ↦ (t⁻¹ : ℝ) • w) hst
      simpa only [smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_zero] using this
    have hv : v = -((t⁻¹ * s) • u) := eq_neg_of_add_eq_zero_right h2
    subst hv
    simp only [gramDet, map_neg, map_smul, neg_apply, smul_apply, smul_eq_mul, neg_neg, mul_neg]
    ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The Gram determinant vanishes on the diagonal.** The special case of
`gramDet_eq_zero_of_not_linearIndependent` that the degenerate branch of every `0 ≤ K` statement
actually reaches. -/
theorem gramDet_self_eq_zero (v : TangentSpace I x) : gramDet g x v v = 0 :=
  gramDet_eq_zero_of_not_linearIndependent (not_linearIndependent_self v)

section Sectional

variable (hsymm : IsSymm g) (hpos : IsPosDef g)
  (hg : IsContMDiffMetricSection E ((2 : ℕ∞)) g)

include hsymm hpos hg

/-- **Sectional curvature of the plane spanned by `u` and `v`.**

  `sec(u,v) = Rm(u,v,v,u) / (g(u,u) g(v,v) − g(u,v)²)`

See the module docstring for the sign convention: the numerator is `Rm(u,v,v,u)`, i.e.
`g (R(u,v) v) u`. For linearly independent `u`, `v` the denominator is positive by `gramDet_pos`;
for dependent `u`, `v` it is zero and the value is Lean's junk `0`, which is why every theorem below
carries a linear-independence hypothesis. -/
def sectionalCurvatureAt (x : M) (u v : TangentSpace I x) : ℝ :=
  riemannTensorAt hsymm (IsPosDef.isNondegenerate hpos) hg x u v v u / gramDet g x u v

theorem sectionalCurvatureAt_def (x : M) (u v : TangentSpace I x) :
    sectionalCurvatureAt hsymm hpos hg x u v
      = riemannTensorAt hsymm (IsPosDef.isNondegenerate hpos) hg x u v v u / gramDet g x u v := rfl

end Sectional

end RiemannianGeometry
