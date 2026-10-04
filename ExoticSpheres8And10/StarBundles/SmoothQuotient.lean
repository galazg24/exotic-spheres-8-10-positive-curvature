/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.Equivariant

/-! # The smooth manifold `E/S³_⋆`

A **smooth star quotient** of a star bundle `E` (`IsSmoothStarQuotient`) is a smooth manifold `Q`
with a map `p : E → Q` such that
* `p` is smooth and surjective;
* the fibres of `p` are exactly the star orbits;
* smoothness descends along `p`: a map `f : Q → N` to a smooth manifold is smooth iff `f ∘ p` is.

The quotient manifold `E/S³_⋆` of the free smooth action of `S³_⋆` (the manifold in Sperança's
Theorem 1) is a smooth star quotient: its projection is a surjective submersion (the quotient
manifold theorem, e.g. J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Thm 21.10), and
smoothness descends along surjective submersions (ibid., Thm 4.29).

* **`isSmoothStarQuotient_starQuotMap`**: the polar model `QuotSpace D` of `prop:polar`, with
  `starQuotMap : E → QuotSpace D`, is a smooth star quotient.
* **`IsSmoothStarQuotient.diffeomorph`**: any two smooth star quotients are diffeomorphic, by a
  diffeomorphism commuting with the projections (`IsSmoothStarQuotient.diffeomorph_comp`). So
  the notion determines the smooth manifold `E/S³_⋆` up to diffeomorphism, and the polar model
  is that manifold.

A homeomorphism `E/S³_⋆ ≃ₜ QuotSpace D` alone would not identify the smooth structures: exotic
spheres are homeomorphic to the standard sphere.
-/

namespace ExoticSpheres8And10

open Set Function Module

open scoped Manifold ContDiff

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

section SmoothQuotient

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} {R : StarRep e} {E : Type} [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

namespace StarBundle

/-- **A smooth quotient of `E` by the star action**: a smooth surjection `p : E → Q` onto an
`(m + 1)`-manifold whose fibres are the star orbits and along which smoothness descends. The
quotient manifold `E/S³_⋆` is one; any two are diffeomorphic (`IsSmoothStarQuotient.diffeomorph`). -/
structure IsSmoothStarQuotient {Q : Type} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) Q] (p : E → Q) : Prop where
  smooth : ContMDiff (IP m) (𝓡 (m + 1)) ∞ p
  surjective : Surjective p
  fibres : ∀ x x' : E, p x = p x' ↔ ∃ q : S3, x' = B.star q x
  descends : ∀ (N : Type) [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
    [IsManifold (𝓡 (m + 1)) ∞ N] (f : Q → N),
    ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ f ↔ ContMDiff (IP m) (𝓡 (m + 1)) ∞ (f ∘ p)

/-- **The polar model is a smooth star quotient**: `starQuotMap : E → QuotSpace D` is smooth and
surjective, its fibres are the star orbits, and smoothness descends along it. -/
theorem isSmoothStarQuotient_starQuotMap [FiniteDimensional ℝ W] [T2Space E]
    [Fact (finrank ℝ (Vs e) = m + 1)] : B.IsSmoothStarQuotient B.starQuotMap where
  smooth := B.contMDiff_starQuotMap
  surjective := B.starQuotMap_surjective
  fibres := B.starQuotMap_eq_iff
  descends _ _ _ _ f := B.contMDiff_iff_comp_starQuotMap f

variable {B}

variable {Q Q' : Type} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) Q]
  [TopologicalSpace Q'] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) Q'] {p : E → Q}
  {p' : E → Q'}

/-- The map `Q → Q'` induced by two smooth star quotients, `p x ↦ p' x`. -/
def IsSmoothStarQuotient.lift (hp : B.IsSmoothStarQuotient p) (p' : E → Q') : Q → Q' :=
  fun y => p' (surjInv hp.surjective y)

theorem IsSmoothStarQuotient.lift_comp (hp : B.IsSmoothStarQuotient p)
    (hp' : B.IsSmoothStarQuotient p') (x : E) : hp.lift p' (p x) = p' x := by
  obtain ⟨q, hq⟩ := (hp.fibres _ _).1 (surjInv_eq hp.surjective (p x))
  exact (hp'.fibres _ _).2 ⟨q, hq⟩

/-- **Any two smooth star quotients are diffeomorphic**: `p x ↦ p' x` is a `C^∞` diffeomorphism
`Q → Q'`. -/
def IsSmoothStarQuotient.diffeomorph [IsManifold (𝓡 (m + 1)) ∞ Q] [IsManifold (𝓡 (m + 1)) ∞ Q']
    (hp : B.IsSmoothStarQuotient p) (hp' : B.IsSmoothStarQuotient p') :
    Q ≃ₘ^∞⟮𝓡 (m + 1), 𝓡 (m + 1)⟯ Q' where
  toFun := hp.lift p'
  invFun := hp'.lift p
  left_inv y := by
    obtain ⟨x, rfl⟩ := hp.surjective y
    rw [hp.lift_comp hp', hp'.lift_comp hp]
  right_inv y := by
    obtain ⟨x, rfl⟩ := hp'.surjective y
    rw [hp'.lift_comp hp, hp.lift_comp hp']
  contMDiff_toFun := by
    show ContMDiff _ _ _ (hp.lift p')
    rw [hp.descends Q' (hp.lift p'), show hp.lift p' ∘ p = p' from funext (hp.lift_comp hp')]
    exact hp'.smooth
  contMDiff_invFun := by
    show ContMDiff _ _ _ (hp'.lift p)
    rw [hp'.descends Q (hp'.lift p), show hp'.lift p ∘ p' = p from funext (hp'.lift_comp hp)]
    exact hp.smooth

theorem IsSmoothStarQuotient.diffeomorph_comp [IsManifold (𝓡 (m + 1)) ∞ Q]
    [IsManifold (𝓡 (m + 1)) ∞ Q'] (hp : B.IsSmoothStarQuotient p)
    (hp' : B.IsSmoothStarQuotient p') (x : E) : hp.diffeomorph hp' (p x) = p' x :=
  hp.lift_comp hp' x

end StarBundle

end SmoothQuotient

end

end ExoticSpheres8And10
