/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.RemarkGeneralBound

/-! # [DHZ] Proposition 5.1 (`prop:geometric`), and `rem:general_bound` from RW alone

[DHZ] Prop. 5.1: "Let `ρ : S³ → O(V)` be an orthogonal representation on an `n`-dimensional
real vector space, `n ≥ 3`, and let `β : S(V) → S³` satisfy `β(ρ(q)z) = qβ(z)q⁻¹`. The disks in
`Dⁿ ∪_{J_β} Dⁿ` admit positively curved metrics whose boundary metrics agree under `J_β` and
whose outward second fundamental forms have positive definite sum. Consequently the glued
manifold admits a smooth metric of positive sectional curvature."

[DHZ]'s proof is [HLY]'s two-disk construction with the bound `‖K_z‖ ≤ L` for *some* `L`, which
exists by compactness. Here:
* `norm_KY_le_dρ`: `‖K_y‖ ≤ ‖dρ₁‖‖y‖`, so `L = max 1 ‖dρ₁‖` bounds `K` on `S(V)`. This needs no
  compactness argument.
* **`dhz_prop51`**: for every star representation `R` and every smooth conjugation-equivariant
  `β`, the clutched manifold `X = QuotSpace (R.polarOf β)` has:
  - attaching map `σ = J_β`;
  - an `RWData`: two caps of positive sectional curvature, equal boundary metrics,
    `B_N + B_S ≥ 0`;
  - given RW, a smooth metric of positive sectional curvature.
* `dhzGluing_of_RW`: the hypothesis `DHZGluing` of `S4_RemarkGeneral` follows from RW.
* **`remark_general_bound_RW`**: [D] `rem:general_bound` with **RW as the only input**.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

theorem norm_KY_le_dρ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (y : V) : ‖KY ρV y‖ ≤ ‖dρ ρV‖ * ‖y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
  show ‖dρ ρV b y‖ ≤ _
  calc ‖dρ ρV b y‖ ≤ ‖dρ ρV b‖ * ‖y‖ := (dρ ρV b).le_opNorm y
    _ ≤ ‖dρ ρV‖ * ‖b‖ * ‖y‖ := mul_le_mul_of_nonneg_right ((dρ ρV).le_opNorm b) (norm_nonneg _)
    _ = ‖dρ ρV‖ * ‖y‖ * ‖b‖ := by ring

section DHZ

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W}
  [Fact (finrank ℝ (Vs e) = m + 1)]

local notation "SV" => Metric.sphere (0 : Vs e) 1

/-- Every polar datum has a bound `‖K_y‖ ≤ L` on `S(V)`. -/
theorem exists_K_bound (D : PolarData (m := m) e) :
    ∃ L : ℝ, 0 < L ∧ ∀ y : Vs e, ‖y‖ = 1 → ‖KY D.ρVs y‖ ≤ L :=
  ⟨max 1 ‖dρ D.ρVs‖, lt_max_of_lt_left one_pos, fun y hy =>
    (norm_KY_le_dρ D.ρVs y).trans (by rw [hy, mul_one]; exact le_max_right _ _)⟩

/-- **[DHZ] Proposition 5.1.** -/
theorem dhz_prop51 (R : StarRep e) (β : SV → S3) (hβs : ContMDiff (𝓡 m) (𝓡 3) ∞ β)
    (hβe : ∀ (q : S3) (y y' : SV), ((y' : Vs e) : W) = R.ρ q ((y : Vs e) : W) →
      β y' = q * β y * q⁻¹) :
    (∀ y : SV, (((R.polarOf (m := m) β hβs hβe).sigmaV y : Vs e) : W) =
        R.ρ (β y) ((y : Vs e) : W)) ∧
      Nonempty (RWData (𝓡 (m + 1)) (QuotSpace (R.polarOf (m := m) β hβs hβe))) ∧
      (RWGluing (𝓡 (m + 1)) (QuotSpace (R.polarOf (m := m) β hβs hβe)) →
        HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace (R.polarOf (m := m) β hβs hβe))) := by
  obtain ⟨L, hL, hK⟩ := exists_K_bound (R.polarOf (m := m) β hβs hβe)
  exact ⟨sigmaV_eq_J R β hβs hβe, exists_rwData_L _ L hL hK,
    fun hRW => hly_general_L _ L hL hK hRW⟩

/-- `DHZGluing` follows from the Reiser–Wraith gluing theorem. -/
theorem dhzGluing_of_RW (R : StarRep e)
    (hRW : ∀ (β : SV → S3) (hβs : ContMDiff (𝓡 m) (𝓡 3) ∞ β)
      (hβe : ∀ (q : S3) (y y' : SV), ((y' : Vs e) : W) = R.ρ q ((y : Vs e) : W) →
        β y' = q * β y * q⁻¹),
      RWGluing (𝓡 (m + 1)) (QuotSpace (R.polarOf (m := m) β hβs hβe))) :
    DHZGluing (m := m) R :=
  fun β hβs hβe => (dhz_prop51 R β hβs hβe).2.2 (hRW β hβs hβe)

end DHZ

section RemarkRW

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] [T2Space E]

/-- **[D] `rem:general_bound`, with Reiser–Wraith as the only input.** For every star bundle,
with any representation and no bound on `K`, `E/S³_⋆ ≃ₜ QuotSpace D`, and `QuotSpace D`
carries a smooth metric of positive sectional curvature, given RW. -/
theorem remark_general_bound_RW (B : StarBundle (m := m) R E) :
    letI := R.factVs m
    ∃ D : PolarData (m := m) e, D.ρ = R.ρ ∧
      Nonempty (Quotient (EquivSections.starSetoid B) ≃ₜ QuotSpace D) ∧
      Nonempty (RWData (𝓡 (m + 1)) (QuotSpace D)) ∧
      (RWGluing (𝓡 (m + 1)) (QuotSpace D) → HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace D)) := by
  letI := R.factVs m
  obtain ⟨D, hD, -, -, -, -, ⟨hq⟩⟩ := B.prop_polar
  obtain ⟨L, hL, hK⟩ := exists_K_bound D
  exact ⟨D, hD, ⟨hq.trans D.orbitSpaceHomeo⟩, exists_rwData_L D L hL hK,
    fun hRW => hly_general_L D L hL hK hRW⟩

/-- **Non-vacuity**: the remark applies to a star bundle for `ρ₈`. -/
example := remark_general_bound_RW (m := 7) (prodBundle rep8)

end RemarkRW

end

end ExoticSpheres8And10
