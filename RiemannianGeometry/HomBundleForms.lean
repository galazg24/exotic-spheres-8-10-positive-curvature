/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.KoszulBundled

/-!
# The double frame test for fields of bilinear forms

`contMDiffAt_hom_hom_of_contMDiffAt_frame` reduces smoothness of a section of
`Hom(TM, Hom(TM, ℝ))` — a field of bilinear forms, i.e. a metric-shaped object — to smoothness of
its scalars on a local frame.

-/

open Bundle Module Set
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
/-- **The double frame test, with the scalars as a hypothesis.**

A field `K` of bilinear forms on the tangent spaces is a `C^m` section of `Hom(TM, Hom(TM, ℝ))` at
`x` as soon as `y ↦ K y (s_i y) (s_j y)` is `C^m` at `x` for the local frame `s` induced by an atlas
trivialisation `e` whose base set contains `x` and a basis `b` of the model fibre.

`RiemannianGeometry.contMDiffAt_hom_hom_of_eq_koszulRHS_frame` is this argument specialised to the Koszul
right-hand side; the two frame tests and the trivial-line-bundle step are the same, and only the
supply of the scalars differs. -/
theorem contMDiffAt_hom_hom_of_contMDiffAt_frame {m : ℕ∞} {x : M}
    {κ : Type*} [Finite κ] (b : Basis κ ℝ E)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (hxe : x ∈ e.baseSet)
    (K : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hscal : ∀ i j, ContMDiffAt I 𝓘(ℝ) ((m : ℕ∞ω))
      (fun y ↦ K y (e.localFrame b i y) (e.localFrame b j y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (K y)) x := by
  have hinner : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)) y
        (K y (e.localFrame b i y))) x := fun i ↦
    contMDiffAt_hom_bundle_of_contMDiffAt_localFrame (IB := I) (n := (m : ℕ∞ω))
      (E₂ := Bundle.Trivial M ℝ) (F₂ := ℝ) b e hxe
      (fun y ↦ (K y (e.localFrame b i y) : TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y))
      (fun j ↦ contMDiffAt_trivial_section (hscal i j))
  exact contMDiffAt_hom_bundle_of_contMDiffAt_localFrame (IB := I) (n := (m : ℕ∞ω))
    (E₂ := fun y : M ↦ (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)) (F₂ := E →L[ℝ] ℝ)
    b e hxe
    (fun y ↦ (K y : TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)))
    hinner

end RiemannianGeometry
