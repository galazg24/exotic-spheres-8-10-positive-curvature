/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.ActionField.Bridge

/-! # [GG] Theorems A and B, modulo the imported inputs

**`theoremA`** (`n = 8`, `ρ₈`). Let `E → S⁸` be a star bundle for `ρ₈`; by Sperança, `E¹¹`
is one. Then there is a polar datum `D` with:
- `D.ρ = ρ₈`;
- `E/S³_⋆ ≃ₜ X = QuotSpace D`, the quotient manifold;
- `RWGluing X → X` carries a smooth metric with `sec > 0`.

**`theoremB`** is the same for `n = 10` and `ρ₁₀`.

The chain is `prop:polar` (`prop_polar`) → `lem:K` (`lem_K`, through `norm_KY_le`) →
`thm:HLYgeneral` (`hly_general`).

Imported, as named hypotheses or outside Lean:
- Reiser–Wraith (`RWGluing`);
- Sperança's theorem that `E¹¹ → S⁸` and `E¹³ → S¹⁰` are such star bundles, and that their
  quotients are the exotic 8-sphere and a generator of the order-3 subgroup of `Θ₁₀`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

variable {E : Type} [TopologicalSpace E]

/-- **[GG] Theorem A, Lean form.** -/
theorem theoremA
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (7 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 7) ∞ E] [T2Space E] (B : StarBundle (m := 7) rep8 E) :
    letI := rep8.factVs 7
    ∃ D : PolarData (m := 7) e8, D.ρ = rep8.ρ ∧
      Nonempty (Quotient (EquivSections.starSetoid B) ≃ₜ QuotSpace D) ∧
      (RWGluing (𝓡 (7 + 1)) (QuotSpace D) → HasPosCurvMetric (𝓡 (7 + 1)) (QuotSpace D)) := by
  letI := rep8.factVs 7
  obtain ⟨D, hD, -, -, -, -, ⟨hq⟩⟩ := B.prop_polar
  refine ⟨D, hD, ⟨hq.trans D.orbitSpaceHomeo⟩, fun hRW => hly_general D ?_ hRW⟩
  refine norm_KY_le D (Kf := Kf ℝ) (fun ξ hξ y => ?_) (fun y hy ξ => lem_K ℝ y hy ξ)
  rw [hD]; exact hasDerivAt_actionField ℝ hξ y

/-- **[GG] Theorem B, Lean form** (`n = 10`, `ρ₁₀`). -/
theorem theoremB
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (9 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 9) ∞ E] [T2Space E] (B : StarBundle (m := 9) rep10 E) :
    letI := rep10.factVs 9
    ∃ D : PolarData (m := 9) e10, D.ρ = rep10.ρ ∧
      Nonempty (Quotient (EquivSections.starSetoid B) ≃ₜ QuotSpace D) ∧
      (RWGluing (𝓡 (9 + 1)) (QuotSpace D) → HasPosCurvMetric (𝓡 (9 + 1)) (QuotSpace D)) := by
  letI := rep10.factVs 9
  obtain ⟨D, hD, -, -, -, -, ⟨hq⟩⟩ := B.prop_polar
  refine ⟨D, hD, ⟨hq.trans D.orbitSpaceHomeo⟩, fun hRW => hly_general D ?_ hRW⟩
  refine norm_KY_le D (Kf := Kf (EuclideanSpace ℝ (Fin 3))) (fun ξ hξ y => ?_)
    (fun y hy ξ => lem_K (EuclideanSpace ℝ (Fin 3)) y hy ξ)
  rw [hD]; exact hasDerivAt_actionField (EuclideanSpace ℝ (Fin 3)) hξ y

/-- **Non-vacuity**: `theoremA` applies to a star bundle for `ρ₈` (the product bundle). -/
example := theoremA (prodBundle rep8)

/-- **Non-vacuity**: `theoremB` applies to a star bundle for `ρ₁₀`. -/
example := theoremB (prodBundle rep10)

end

end ExoticSpheres8And10
