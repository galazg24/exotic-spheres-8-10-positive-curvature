/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.ActionField.Bridge
import ExoticSpheres8And10.StarBundles.SmoothQuotient
import ExoticSpheres8And10.Geometry.DiffeoTransport

/-! # [GG] Theorems A and B, modulo the imported inputs

Let `E → S⁸` be a star bundle for `ρ₈` (by Sperança, `E¹¹` is one), and let `Q` be the smooth
manifold `E/S³_⋆`: a smooth quotient of `E` by the star action (`IsSmoothStarQuotient`; any two
are diffeomorphic, `IsSmoothStarQuotient.diffeomorph`).

**`theoremA`**: if the Reiser–Wraith gluing theorem holds for the polar models, `Q` carries a
smooth metric of positive sectional curvature. **`theoremB`** is the same for `n = 10`, `ρ₁₀`.

The proof has two steps.
* **`polarModelA`** (resp. `polarModelB`): the polar model `X = QuotSpace D` of `prop:polar` is
  itself a smooth star quotient of `E`, and carries `sec > 0` given RW. The chain is
  `prop:polar` (`prop_polar`, `starQuotMap`) → `lem:K` (`lem_K`, through `norm_KY_le`) →
  `thm:HLYgeneral` (`hly_general`).
* The smooth star quotients `Q` and `X` are diffeomorphic, and the metric is pulled back along the
  diffeomorphism (`HasPosCurvMetric.of_diffeomorph`).

Imported, as named hypotheses or outside Lean:
- Reiser–Wraith (`RWGluing`);
- Sperança's Theorem 1: `E¹¹ → S⁸` and `E¹³ → S¹⁰` are such star bundles, and their quotient
  manifolds `E/S³_⋆` are diffeomorphic to the exotic 8-sphere and to a generator of the order-3
  subgroup of `Θ₁₀` (used in `SECc_of_theoremA`, `SECc_of_theoremB`).
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

variable {E : Type} [TopologicalSpace E]

/-- **The polar model of `E/S³_⋆` for `ρ₈`.** The quotient manifold `X = QuotSpace D` of the polar
datum `D` of `prop:polar` is a smooth star quotient of `E` (through `starQuotMap`), and carries a
smooth metric of positive sectional curvature if RW holds for it. -/
theorem polarModelA
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (7 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 7) ∞ E] [T2Space E] (B : StarBundle (m := 7) rep8 E) :
    letI := rep8.factVs 7
    ∃ D : PolarData (m := 7) e8, D.ρ = rep8.ρ ∧
      (∃ p : E → QuotSpace D, B.IsSmoothStarQuotient p) ∧
      (RWGluing (𝓡 (7 + 1)) (QuotSpace D) → HasPosCurvMetric (𝓡 (7 + 1)) (QuotSpace D)) := by
  letI := rep8.factVs 7
  have hD : B.equivSections.polarData.ρ = rep8.ρ := rfl
  refine ⟨B.equivSections.polarData, hD, ⟨B.starQuotMap, B.isSmoothStarQuotient_starQuotMap⟩,
    fun hRW => hly_general _ ?_ hRW⟩
  refine norm_KY_le _ (Kf := Kf ℝ) (fun ξ hξ y => ?_) (fun y hy ξ => lem_K ℝ y hy ξ)
  rw [hD]; exact hasDerivAt_actionField ℝ hξ y

/-- **The polar model of `E/S³_⋆` for `ρ₁₀`**; see `polarModelA`. -/
theorem polarModelB
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (9 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 9) ∞ E] [T2Space E] (B : StarBundle (m := 9) rep10 E) :
    letI := rep10.factVs 9
    ∃ D : PolarData (m := 9) e10, D.ρ = rep10.ρ ∧
      (∃ p : E → QuotSpace D, B.IsSmoothStarQuotient p) ∧
      (RWGluing (𝓡 (9 + 1)) (QuotSpace D) → HasPosCurvMetric (𝓡 (9 + 1)) (QuotSpace D)) := by
  letI := rep10.factVs 9
  have hD : B.equivSections.polarData.ρ = rep10.ρ := rfl
  refine ⟨B.equivSections.polarData, hD, ⟨B.starQuotMap, B.isSmoothStarQuotient_starQuotMap⟩,
    fun hRW => hly_general _ ?_ hRW⟩
  refine norm_KY_le _ (Kf := Kf (EuclideanSpace ℝ (Fin 3))) (fun ξ hξ y => ?_)
    (fun y hy ξ => lem_K (EuclideanSpace ℝ (Fin 3)) y hy ξ)
  rw [hD]; exact hasDerivAt_actionField (EuclideanSpace ℝ (Fin 3)) hξ y

/-- **[GG] Theorem A, Lean form.** For a star bundle `E` for `ρ₈`, every smooth quotient
`p : E → Q` of `E` by the star action (the smooth manifold `E/S³_⋆`) carries a smooth metric of
positive sectional curvature, given RW for the polar models. -/
theorem theoremA
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (7 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 7) ∞ E] [T2Space E] (B : StarBundle (m := 7) rep8 E)
    {Q : Type} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin (7 + 1))) Q]
    [IsManifold (𝓡 (7 + 1)) ∞ Q] (p : E → Q) (hp : B.IsSmoothStarQuotient (m := 7) p) :
    letI := rep8.factVs 7
    (∀ D : PolarData (m := 7) e8, D.ρ = rep8.ρ → RWGluing (𝓡 (7 + 1)) (QuotSpace D)) →
      HasPosCurvMetric (𝓡 (7 + 1)) Q := by
  letI := rep8.factVs 7
  intro hRW
  obtain ⟨D, hD, ⟨p₀, hp₀⟩, hpos⟩ := polarModelA B
  exact (hpos (hRW D hD)).of_diffeomorph (hp.diffeomorph hp₀)

/-- **[GG] Theorem B, Lean form** (`n = 10`, `ρ₁₀`); see `theoremA`. -/
theorem theoremB
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (9 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 9) ∞ E] [T2Space E] (B : StarBundle (m := 9) rep10 E)
    {Q : Type} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin (9 + 1))) Q]
    [IsManifold (𝓡 (9 + 1)) ∞ Q] (p : E → Q) (hp : B.IsSmoothStarQuotient (m := 9) p) :
    letI := rep10.factVs 9
    (∀ D : PolarData (m := 9) e10, D.ρ = rep10.ρ → RWGluing (𝓡 (9 + 1)) (QuotSpace D)) →
      HasPosCurvMetric (𝓡 (9 + 1)) Q := by
  letI := rep10.factVs 9
  intro hRW
  obtain ⟨D, hD, ⟨p₀, hp₀⟩, hpos⟩ := polarModelB B
  exact (hpos (hRW D hD)).of_diffeomorph (hp.diffeomorph hp₀)

/-- **Non-vacuity**: `theoremA` applies to the star bundle for `ρ₈` given by the product bundle,
with its polar model as the smooth star quotient. -/
example : letI := rep8.factVs 7
    (∀ D : PolarData (m := 7) e8, D.ρ = rep8.ρ → RWGluing (𝓡 (7 + 1)) (QuotSpace D)) →
      HasPosCurvMetric (𝓡 (7 + 1)) (QuotSpace (prodBundle (m := 7) rep8).equivSections.polarData) := by
  letI := rep8.factVs 7
  exact theoremA (prodBundle (m := 7) rep8) _ (prodBundle (m := 7) rep8).isSmoothStarQuotient_starQuotMap

/-- **Non-vacuity**: `theoremB` applies to the product star bundle for `ρ₁₀`. -/
example : letI := rep10.factVs 9
    (∀ D : PolarData (m := 9) e10, D.ρ = rep10.ρ → RWGluing (𝓡 (9 + 1)) (QuotSpace D)) →
      HasPosCurvMetric (𝓡 (9 + 1)) (QuotSpace (prodBundle (m := 9) rep10).equivSections.polarData) := by
  letI := rep10.factVs 9
  exact theoremB (prodBundle (m := 9) rep10) _ (prodBundle (m := 9) rep10).isSmoothStarQuotient_starQuotMap

end

end ExoticSpheres8And10
