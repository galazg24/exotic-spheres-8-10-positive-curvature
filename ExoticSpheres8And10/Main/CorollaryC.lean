/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Main.CorollaryCLogic
import ExoticSpheres8And10.Main.RoundSphere

/-! # [GG] Corollary C with geometric `SEC` and `PSC`

`S5_CorollaryC` states the deduction for two abstract predicates `SEC`, `PSC` on `Θ`. Here they
are **defined geometrically**, from a representation relation `Rep : RepRel n Θ`. `Rep M x`
reads "the closed smooth `n`-manifold `M`, with some orientation, represents `x ∈ Θ_n`"; it is
the Kervaire–Milnor input, since Mathlib has no `Θ_n`:
* `SECc Rep x`: some `M` with `Rep M x` carries a smooth metric of positive sectional curvature;
* `PSCc Rep x`: some `M` with `Rep M x` carries a smooth metric of positive scalar curvature.

Two former hypotheses of `corollaryC_dim10` are now **theorems**:
* `SECc → PSCc` (`SECc_PSCc`), from `sec > 0 ⇒ scal > 0` (`S5_Scalar`);
* `SECc 0` (`SECc_zero`), from the positive curvature of the round sphere
  (`hasPosCurvMetric_sphere`). The only input here is that the standard sphere represents `0`,
  i.e. that `0 ∈ Θ_n` is the class of `Sⁿ`.

Inputs that remain, all as named hypotheses:
- Kervaire–Milnor: `Θ ≃+ ℤ/6` (resp. `ℤ/2`), `Rep`, and `Rep Sⁿ 0`;
- Hitchin: `PSCc x → α x = 0`, with `α ≠ 0`;
- orientation reversal is negation: `Rep M x → Rep M (−x)` (an imported input);
- Sperança's Theorem 1: the quotient manifold `E/S³_⋆` of the special bundle represents `g`. In
  `SECc_of_theoremA` and `SECc_of_theoremB` this is the hypothesis that **some smooth star
  quotient** `p : E → Q` (`IsSmoothStarQuotient`) has `Rep Q g`. All smooth star quotients are
  diffeomorphic to `E/S³_⋆` (`IsSmoothStarQuotient.diffeomorph`), so the hypothesis says no more
  than Sperança's diffeomorphism. `theoremA`/`theoremB` then put a metric of positive sectional
  curvature on that `Q` itself, so no transfer of `Rep` between manifolds is needed.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Module

open scoped Manifold ContDiff

noncomputable section

section Geom

/-- The Kervaire–Milnor **representation relation**: `Rep M x` means that the closed smooth
`n`-manifold `M` (with some orientation) represents `x ∈ Θ_n`. -/
abbrev RepRel (n : ℕ) (Θ : Type) : Type 1 :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M], Θ → Prop

variable {n : ℕ} {Θ : Type}

/-- `x` is represented by a manifold with a metric of **positive sectional curvature**. -/
def SECc (Rep : RepRel n Θ) (x : Θ) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
    (_ : IsManifold (𝓡 n) ∞ M), Rep M x ∧ HasPosCurvMetric (𝓡 n) M

/-- `x` is represented by a manifold with a metric of **positive scalar curvature**. -/
def PSCc (Rep : RepRel n Θ) (x : Θ) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
    (_ : IsManifold (𝓡 n) ∞ M), Rep M x ∧ HasPosScalMetric (𝓡 n) M

/-- **`SEC ⇒ PSC`** (`n ≥ 2`), now a theorem: `sec > 0 ⇒ scal > 0`. -/
theorem SECc_PSCc (hn : 2 ≤ n) (Rep : RepRel n Θ) (x : Θ) : SECc Rep x → PSCc Rep x := by
  rintro ⟨M, i1, i2, i3, hR, hM⟩
  exact ⟨M, i1, i2, i3, hR, HasPosCurvMetric.hasPosScalMetric (𝓡 n) M
    (by rw [finrank_euclideanSpace_fin]; exact hn) hM⟩

/-- **`SEC 0`**, now a theorem: the round sphere has positive sectional curvature. The input is
only that the standard sphere represents `0`. -/
theorem SECc_zero [Zero Θ] (Rep : RepRel n Θ) (hround : Rep (Sph n) 0) : SECc Rep 0 :=
  ⟨Sph n, inferInstance, inferInstance, inferInstance, hround, hasPosCurvMetric_sphere n⟩

/-- Orientation reversal (the imported input `Rep M x → Rep M (−x)`) preserves `SEC`. -/
theorem SECc_neg [Neg Θ] (Rep : RepRel n Θ)
    (hneg : ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M] (x : Θ), Rep M x → Rep M (-x)) (x : Θ) :
    SECc Rep x → SECc Rep (-x) := by
  rintro ⟨M, i1, i2, i3, hR, hM⟩
  exact ⟨M, i1, i2, i3, hneg M x hR, hM⟩

/-- **[GG] Corollary C, dimension 10, with geometric `SEC`, `PSC`.** -/
theorem corollaryC_dim10_geom [AddCommGroup Θ] (Rep : RepRel (9 + 1) Θ) (eΘ : Θ ≃+ ZMod 6)
    (α : Θ →+ ZMod 2) (hα : α ≠ 0) (hHitchin : ∀ x, PSCc Rep x → α x = 0)
    (hround : Rep (Sph (9 + 1)) 0)
    (hneg : ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (9 + 1))) M]
      [IsManifold (𝓡 (9 + 1)) ∞ M] (x : Θ), Rep M x → Rep M (-x))
    (g : Θ) (hg : eΘ g ∈ zmod6Order3) (hg0 : g ≠ 0) (hSg : SECc Rep g) :
    ∀ x, SECc Rep x ↔ PSCc Rep x :=
  corollaryC_dim10 eΘ α hα (PSCc Rep) (SECc Rep) (SECc_PSCc (by norm_num) Rep) hHitchin
    (SECc_zero Rep hround) g hg hg0 hSg (SECc_neg Rep hneg)

/-- **[GG] Corollary C, dimension 8, with geometric `SEC`.** -/
theorem corollaryC_dim8_geom [AddCommGroup Θ] (Rep : RepRel (7 + 1) Θ) (eΘ : Θ ≃+ ZMod 2)
    (hround : Rep (Sph (7 + 1)) 0) (g : Θ) (hg0 : g ≠ 0) (hSg : SECc Rep g) :
    ∀ x, SECc Rep x :=
  corollaryC_dim8 eΘ (SECc Rep) (SECc_zero Rep hround) g hg0 hSg

section FromTheorems

variable {E : Type} [TopologicalSpace E]

/-- **`SEC g` from Theorem B**, given RW and Sperança's Theorem 1 in the form: some smooth quotient
`p : E → Q` of `E¹³` by the star action (the quotient manifold `E¹³/S³_⋆`) represents `g`. -/
theorem SECc_of_theoremB
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (9 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 9) ∞ E] [T2Space E] (B : StarBundle (m := 9) rep10 E)
    (Rep : RepRel (9 + 1) Θ) (g : Θ) :
    letI := rep10.factVs 9
    (∀ D : PolarData (m := 9) e10, D.ρ = rep10.ρ → RWGluing (𝓡 (9 + 1)) (QuotSpace D)) →
    (∃ (Q : Type) (_ : TopologicalSpace Q) (_ : ChartedSpace (EuclideanSpace ℝ (Fin (9 + 1))) Q)
      (_ : IsManifold (𝓡 (9 + 1)) ∞ Q) (p : E → Q), B.IsSmoothStarQuotient (m := 9) p ∧ Rep Q g) →
    SECc Rep g := by
  letI := rep10.factVs 9
  rintro hRW ⟨Q, i1, i2, i3, p, hp, hR⟩
  exact ⟨Q, i1, i2, i3, hR, theoremB B p hp hRW⟩

/-- **`SEC g` from Theorem A**, given RW and Sperança's Theorem 1 in the form: some smooth quotient
`p : E → Q` of `E¹¹` by the star action (the quotient manifold `E¹¹/S³_⋆`) represents `g`. -/
theorem SECc_of_theoremA
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (7 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 7) ∞ E] [T2Space E] (B : StarBundle (m := 7) rep8 E)
    (Rep : RepRel (7 + 1) Θ) (g : Θ) :
    letI := rep8.factVs 7
    (∀ D : PolarData (m := 7) e8, D.ρ = rep8.ρ → RWGluing (𝓡 (7 + 1)) (QuotSpace D)) →
    (∃ (Q : Type) (_ : TopologicalSpace Q) (_ : ChartedSpace (EuclideanSpace ℝ (Fin (7 + 1))) Q)
      (_ : IsManifold (𝓡 (7 + 1)) ∞ Q) (p : E → Q), B.IsSmoothStarQuotient (m := 7) p ∧ Rep Q g) →
    SECc Rep g := by
  letI := rep8.factVs 7
  rintro hRW ⟨Q, i1, i2, i3, p, hp, hR⟩
  exact ⟨Q, i1, i2, i3, hR, theoremA B p hp hRW⟩

end FromTheorems

/-- **Non-vacuity** of `corollaryC_dim10_geom`: every hypothesis holds for `Θ = ℤ/6`,
`Rep M x := x ∈ ⟨2⟩`, `α` the reduction mod 2, and `g = 2`. `SECc Rep 2` is witnessed by the round
`S¹⁰`, so the round-sphere theorem is used. -/
theorem corollaryC_dim10_geom_satisfiable :
    ∃ (Rep : RepRel (9 + 1) (ZMod 6)) (α : ZMod 6 →+ ZMod 2), α ≠ 0 ∧
      (∀ x, PSCc Rep x → α x = 0) ∧ Rep (Sph (9 + 1)) 0 ∧
      (∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (9 + 1))) M]
        [IsManifold (𝓡 (9 + 1)) ∞ M] (x : ZMod 6), Rep M x → Rep M (-x)) ∧
      SECc Rep 2 := by
  have hpsc : ∀ x : ZMod 6, x ∈ zmod6Order3 →
      (ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2)).toAddMonoidHom x = 0 := by
    intro x hx
    rw [mem_zmod6Order3_iff] at hx
    have key : ∀ y : ZMod 6, y ∈ ({0, 2, 4} : Finset (ZMod 6)) →
        (ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2)) y = 0 := by decide
    exact key x hx
  refine ⟨fun _ _ _ _ x => x ∈ zmod6Order3,
    (ZMod.castHom (by norm_num : 2 ∣ 6) (ZMod 2)).toAddMonoidHom, castHom_ne_zero,
    fun x ⟨_, _, _, _, hx, _⟩ => hpsc x hx,
    zmod6Order3.zero_mem, fun _ _ _ _ x hx => zmod6Order3.neg_mem hx,
    ⟨Sph (9 + 1), inferInstance, inferInstance, inferInstance, ?_, hasPosCurvMetric_sphere _⟩⟩
  show (2 : ZMod 6) ∈ zmod6Order3
  rw [mem_zmod6Order3_iff]; decide

end Geom

end

end ExoticSpheres8And10
