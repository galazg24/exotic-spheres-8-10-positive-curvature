/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.HorizontalSpace

/-!
# Equivariant isometries and compositions of Riemannian submersions

Four pointwise facts about the project's `RiemannianGeometry.HorizontalSpace` layer, all standard and all
metric-generic.

Let `f : M → B`, and let `φ : M → M`, `ψ : B → B` satisfy `f ∘ φ = ψ ∘ f`, with `dφ_p` preserving
the metric of `M` and `dψ_{f p}` injective.

* `mfderiv_mem_horizontalSpace_of_isometry` — `dφ_p` carries `f`-horizontal vectors at `p` to
  `f`-horizontal vectors at `φ p`. The only input beyond the chain rule is that an isometry of a
  finite-dimensional inner product space onto itself is surjective.
* `isRiemannianSubmersionAtPoint_of_isometry` — if moreover `dψ_{f p}` preserves the metric of `B`,
  the Riemannian-submersion condition at `φ p` gives it at `p`. With `ψ = id` this is how the
  condition spreads along the fibres of a submersion with a transitive fibrewise isometry group.
* `inner_mfderiv_of_isometry` — conversely, if `f` is a Riemannian submersion at `p` and at `φ p`
  and a submersion at `p`, then `dψ_{f p}` **is** an isometry of the metric of `B`. This is how a
  quotient metric inherits the symmetries of the metric it descends from.
* `isRiemannianSubmersionAtPoint_comp` — a composite of Riemannian submersions is one.

No hypothesis is imposed on the global behaviour of `φ` or `ψ`: everything is at the point.
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
  {f : M → B} {φ : M → M} {ψ : B → B} {p : M}

omit [IsManifold I ∞ M] in
/-- **An isometric endomorphism of a tangent space is onto.** Injective because the metric is
positive definite, hence surjective by finite-dimensionality. -/
theorem surjective_mfderiv_of_isometry
    (hiso : ∀ u v : TangentSpace I p,
      inner ℝ (mfderiv I I φ p u) (mfderiv I I φ p v) = inner ℝ u v) :
    Function.Surjective (mfderiv I I φ p) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have : FiniteDimensional ℝ (TangentSpace I (φ p)) := inferInstanceAs (FiniteDimensional ℝ E)
  have hinj : Function.Injective (mfderiv I I φ p) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
    have h0 := hiso u u
    rw [hu, inner_zero_left] at h0
    exact inner_self_eq_zero.1 h0.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv I I φ p).toLinearMap) rfl).1 hinj

omit [IsManifold I ∞ M] [IsManifold J ∞ B] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The chain rule for `f ∘ φ = ψ ∘ f`, applied to a vector. -/
theorem mfderiv_comm_apply (hfφ : f ∘ φ = ψ ∘ f) (hf : MDifferentiableAt I J f p)
    (hf' : MDifferentiableAt I J f (φ p)) (hφ : MDifferentiableAt I I φ p)
    (hψ : MDifferentiableAt J J ψ (f p)) (u : TangentSpace I p) :
    mfderiv J J ψ (f p) (mfderiv I J f p u) = mfderiv I J f (φ p) (mfderiv I I φ p u) := by
  have h1 := mfderiv_comp p hf' hφ
  have h2 := mfderiv_comp p hψ hf
  rw [hfφ] at h1
  rw [h1] at h2
  exact (congrArg (fun T ↦ T u) h2).symm

omit [IsManifold I ∞ M] [IsManifold J ∞ B] [FiniteDimensional ℝ E'] in
/-- **An isometry commuting with `f` preserves horizontality.** `dφ_p` sends the `f`-horizontal
space at `p` into the `f`-horizontal space at `φ p`, whenever `f ∘ φ = ψ ∘ f` with `dψ_{f p}`
injective. -/
theorem mfderiv_mem_horizontalSpace_of_isometry (hfφ : f ∘ φ = ψ ∘ f)
    (hf : MDifferentiableAt I J f p) (hf' : MDifferentiableAt I J f (φ p))
    (hφ : MDifferentiableAt I I φ p) (hψ : MDifferentiableAt J J ψ (f p))
    (hψinj : Function.Injective (mfderiv J J ψ (f p)))
    (hiso : ∀ u v : TangentSpace I p,
      inner ℝ (mfderiv I I φ p u) (mfderiv I I φ p v) = inner ℝ u v)
    {u : TangentSpace I p} (hu : u ∈ horizontalSpace I J f p) :
    mfderiv I I φ p u ∈ horizontalSpace I J f (φ p) := by
  refine mem_horizontalSpace_iff.2 fun w hw ↦ ?_
  obtain ⟨w', rfl⟩ := surjective_mfderiv_of_isometry hiso w
  rw [hiso]
  refine mem_horizontalSpace_iff.1 hu w' (mem_verticalSpace_iff.2 (hψinj ?_))
  rw [mfderiv_comm_apply hfφ hf hf' hφ hψ, map_zero]
  exact mem_verticalSpace_iff.1 hw

section Base

variable [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]

omit [IsManifold I ∞ M] [IsManifold J ∞ B] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The chain rule for `f ∘ φ = ψ ∘ f`, read through the metric of `B`. The two sides are pairings
at the base points `ψ (f p)` and `f (φ p)`, which are equal but not definitionally so; the
transport is done once, here, by rewriting the function `f ∘ φ`. -/
theorem inner_mfderiv_comm (hfφ : f ∘ φ = ψ ∘ f) (hf : MDifferentiableAt I J f p)
    (hf' : MDifferentiableAt I J f (φ p)) (hφ : MDifferentiableAt I I φ p)
    (hψ : MDifferentiableAt J J ψ (f p)) (u v : TangentSpace I p) :
    inner ℝ (mfderiv J J ψ (f p) (mfderiv I J f p u)) (mfderiv J J ψ (f p) (mfderiv I J f p v))
      = inner ℝ (mfderiv I J f (φ p) (mfderiv I I φ p u))
          (mfderiv I J f (φ p) (mfderiv I I φ p v)) := by
  have key : inner ℝ (mfderiv I J (ψ ∘ f) p u) (mfderiv I J (ψ ∘ f) p v)
      = inner ℝ (mfderiv I J (f ∘ φ) p u) (mfderiv I J (f ∘ φ) p v) := by
    rw [hfφ]
  rw [mfderiv_comp p hψ hf, mfderiv_comp p hf' hφ] at key
  exact key

omit [IsManifold I ∞ M] [IsManifold J ∞ B] [FiniteDimensional ℝ E'] in
/-- **Transport of the Riemannian-submersion condition along an equivariant isometry.** If
`f ∘ φ = ψ ∘ f`, `dφ_p` and `dψ_{f p}` are isometries, and `f` is a Riemannian submersion at
`φ p`, then it is one at `p`. -/
theorem isRiemannianSubmersionAtPoint_of_isometry (hfφ : f ∘ φ = ψ ∘ f)
    (hf : MDifferentiableAt I J f p) (hf' : MDifferentiableAt I J f (φ p))
    (hφ : MDifferentiableAt I I φ p) (hψ : MDifferentiableAt J J ψ (f p))
    (hiso : ∀ u v : TangentSpace I p,
      inner ℝ (mfderiv I I φ p u) (mfderiv I I φ p v) = inner ℝ u v)
    (hψiso : ∀ a b : TangentSpace J (f p),
      inner ℝ (mfderiv J J ψ (f p) a) (mfderiv J J ψ (f p) b) = inner ℝ a b)
    (hR : IsRiemannianSubmersionAtPoint I J f (φ p)) :
    IsRiemannianSubmersionAtPoint I J f p := by
  have hψinj : Function.Injective (mfderiv J J ψ (f p)) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
    have h0 := hψiso a a
    rw [ha, inner_zero_left] at h0
    exact inner_self_eq_zero.1 h0.symm
  intro u hu v hv
  rw [← hψiso, inner_mfderiv_comm hfφ hf hf' hφ hψ,
    hR _ (mfderiv_mem_horizontalSpace_of_isometry hfφ hf hf' hφ hψ hψinj hiso hu)
      _ (mfderiv_mem_horizontalSpace_of_isometry hfφ hf hf' hφ hψ hψinj hiso hv), hiso]

omit [IsManifold I ∞ M] [IsManifold J ∞ B] in
/-- **A source isometry commuting with a Riemannian submersion induces a base isometry.**

If `f` is a submersion at `p`, a Riemannian submersion at `p` and at `φ p`, `f ∘ φ = ψ ∘ f`,
`dφ_p` is an isometry and `dψ_{f p}` is injective, then `dψ_{f p}` preserves the metric of `B`.
Every base vector is `dπ` of a horizontal one; `dφ` keeps it horizontal; and the metric of `B` is
read off horizontal vectors at both ends. -/
theorem inner_mfderiv_of_isometry (hfφ : f ∘ φ = ψ ∘ f)
    (hf : MDifferentiableAt I J f p) (hf' : MDifferentiableAt I J f (φ p))
    (hφ : MDifferentiableAt I I φ p) (hψ : MDifferentiableAt J J ψ (f p))
    (hψinj : Function.Injective (mfderiv J J ψ (f p)))
    (hiso : ∀ u v : TangentSpace I p,
      inner ℝ (mfderiv I I φ p u) (mfderiv I I φ p v) = inner ℝ u v)
    (hsub : IsSubmersionAtPoint I J f p) (hRp : IsRiemannianSubmersionAtPoint I J f p)
    (hRφ : IsRiemannianSubmersionAtPoint I J f (φ p)) (a b : TangentSpace J (f p)) :
    inner ℝ (mfderiv J J ψ (f p) a) (mfderiv J J ψ (f p) b) = inner ℝ a b := by
  rw [← horizontalLift_spec hsub a, ← horizontalLift_spec hsub b,
    inner_mfderiv_comm hfφ hf hf' hφ hψ,
    hRφ _ (mfderiv_mem_horizontalSpace_of_isometry hfφ hf hf' hφ hψ hψinj hiso
        (horizontalLift_mem hsub a))
      _ (mfderiv_mem_horizontalSpace_of_isometry hfφ hf hf' hφ hψ hψinj hiso
        (horizontalLift_mem hsub b)),
    hiso, hRp _ (horizontalLift_mem hsub a) _ (horizontalLift_mem hsub b)]

end Base

/-! ## Composition -/

section Comp

variable
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
  {C : Type*} [TopologicalSpace C] [ChartedSpace H'' C] [IsManifold K ∞ C]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]
  [Bundle.RiemannianBundle (TangentSpace K : C → Type _)]
  {g : B → C}

omit [IsManifold I ∞ M] [IsManifold J ∞ B] [IsManifold K ∞ C] [FiniteDimensional ℝ E''] in
/-- **A composite of Riemannian submersions is a Riemannian submersion**, pointwise.

The vertical space of `g ∘ f` contains that of `f`, so a `g ∘ f`-horizontal vector is
`f`-horizontal; and `df` carries it to a `g`-horizontal vector, because every `g`-vertical vector
is `df` of an `f`-horizontal vector that is `g ∘ f`-vertical. -/
theorem isRiemannianSubmersionAtPoint_comp (hg : MDifferentiableAt J K g (f p))
    (hf : MDifferentiableAt I J f p) (hsub : IsSubmersionAtPoint I J f p)
    (hRf : IsRiemannianSubmersionAtPoint I J f p)
    (hRg : IsRiemannianSubmersionAtPoint J K g (f p)) :
    IsRiemannianSubmersionAtPoint I K (g ∘ f) p := by
  have hcomp : ∀ u : TangentSpace I p,
      mfderiv I K (g ∘ f) p u = mfderiv J K g (f p) (mfderiv I J f p u) := fun u ↦ by
    rw [mfderiv_comp p hg hf]; rfl
  -- a `g ∘ f`-horizontal vector is `f`-horizontal
  have hHf : ∀ {u : TangentSpace I p}, u ∈ horizontalSpace I K (g ∘ f) p →
      u ∈ horizontalSpace I J f p := fun {u} hu ↦ by
    refine mem_horizontalSpace_iff.2 fun w hw ↦ mem_horizontalSpace_iff.1 hu w ?_
    rw [mem_verticalSpace_iff, hcomp, mem_verticalSpace_iff.1 hw, map_zero]
  -- and `df` of it is `g`-horizontal
  have hHg : ∀ {u : TangentSpace I p}, u ∈ horizontalSpace I K (g ∘ f) p →
      mfderiv I J f p u ∈ horizontalSpace J K g (f p) := fun {u} hu ↦ by
    refine mem_horizontalSpace_iff.2 fun w hw ↦ ?_
    rw [← horizontalLift_spec hsub w,
      hRf _ (horizontalLift_mem hsub w) _ (hHf hu)]
    refine mem_horizontalSpace_iff.1 hu _ ?_
    rw [mem_verticalSpace_iff, hcomp, horizontalLift_spec hsub w]
    exact mem_verticalSpace_iff.1 hw
  intro u hu v hv
  rw [hcomp, hcomp, hRg _ (hHg hu) _ (hHg hv), hRf _ (hHf hu) _ (hHf hv)]

end Comp

end RiemannianGeometry
