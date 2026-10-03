/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Main.TheoremsAB

/-! # [D] Remark `rem:general_bound`: the representation bound can be removed

[D]: "let `E → S(ℝe ⊕ V)` be any star bundle … By `prop:polar`, `E` is equivariantly isomorphic
to a polar bundle `P_θ` … By `lem:attaching`, `E/S³_⋆ ≅ D(V)_N ∪_{σ_{ρ,θ}} D(V)_S` with
`σ_{ρ,θ}(x) = ρ(θ(x))⁻¹x`. Set `β = θ⁻¹`. Then `β` is again conjugation-equivariant and
`σ_{ρ,θ}(x) = ρ(β(x))x = J_β(x)`. Deng–Hu–Zhang [Proposition 5.1], together with Reiser–Wraith,
therefore implies that `E/S³_⋆` admits a smooth metric of positive sectional curvature."

The remark's own content is kernel-checked:
* `StarRep.polarOf`: the polar datum with clutching `θ = β⁻¹`, for a smooth
  conjugation-equivariant `β`;
* `inv_θ_equiv`: `β = θ⁻¹` is smooth and conjugation-equivariant;
* `sigmaV_eq_J`: `σ_{ρ,θ}(x) = ρ(β(x))x = J_β(x)`, with `σ` the attaching map of
  `lem:attaching` (`polarX_κS`);
* **`remark_general_bound`**: for every star bundle and every representation, with no bound on
  `K`, `E/S³_⋆ ≃ₜ QuotSpace D` for a polar datum `D = polarOf β`. Given the cited input,
  `QuotSpace D` carries a smooth metric of positive sectional curvature.

The cited input is **[DHZ] Prop. 5.1 combined with RW**. It enters as the named hypothesis
`DHZGluing R`: for every smooth conjugation-equivariant `β`, the manifold glued along `J_β`
carries a smooth metric with `sec > 0`. That manifold is realised as `QuotSpace (R.polarOf β)`,
whose attaching map is `σ = J_β` by `lem:attaching` and `sigmaV_eq_J`. The hypothesis is
discharged in `Curvature.DHZ`, where [DHZ] Prop. 5.1 is proved (`remark_general_bound_RW`), so
that only RW remains.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

section Remark

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W}

local notation "SV" => Metric.sphere (0 : Vs e) 1

/-- `β = θ⁻¹` is conjugation-equivariant whenever `θ` is. -/
theorem inv_θ_equiv {ρ : S3 →* (W ≃ₗᵢ[ℝ] W)} {θ : SV → S3}
    (hθ : ∀ (q : S3) (y y' : SV), ((y' : Vs e) : W) = ρ q ((y : Vs e) : W) →
      θ y' = q * θ y * q⁻¹) :
    ∀ (q : S3) (y y' : SV), ((y' : Vs e) : W) = ρ q ((y : Vs e) : W) →
      (θ y')⁻¹ = q * (θ y)⁻¹ * q⁻¹ := by
  intro q y y' h
  rw [hθ q y y' h]; group

variable [Fact (finrank ℝ (Vs e) = m + 1)]

/-- The polar datum with clutching `θ = β⁻¹`, i.e. attaching map `J_β`. -/
def StarRep.polarOf (R : StarRep e) (β : SV → S3) (hβs : ContMDiff (𝓡 m) (𝓡 3) ∞ β)
    (hβe : ∀ (q : S3) (y y' : SV), ((y' : Vs e) : W) = R.ρ q ((y : Vs e) : W) →
      β y' = q * β y * q⁻¹) : PolarData (m := m) e where
  e_norm := R.e_norm
  ρ := R.ρ
  ρ_e := R.ρ_e
  ρ_smooth := R.ρ_smooth
  θ := fun y => (β y)⁻¹
  θ_smooth := contMDiff_invS3.comp hβs
  θ_equiv := inv_θ_equiv hβe

/-- **`σ_{ρ,θ} = J_β`**: the attaching map of `lem:attaching` is `x ↦ ρ(β(x))x`. -/
theorem sigmaV_eq_J (R : StarRep e) (β : SV → S3) (hβs) (hβe) (y : SV) :
    (((R.polarOf (m := m) β hβs hβe).sigmaV y : Vs e) : W) = R.ρ (β y) ((y : Vs e) : W) := by
  show R.ρ ((β y)⁻¹)⁻¹ ((y : Vs e) : W) = _
  rw [inv_inv]

/-- **[DHZ] Prop. 5.1 + RW, as a named hypothesis.** For every smooth conjugation-equivariant
`β : S(V) → S³`, the disk gluing along `J_β` carries a smooth metric of positive sectional
curvature. -/
def DHZGluing (R : StarRep e) : Prop :=
  ∀ (β : SV → S3) (hβs : ContMDiff (𝓡 m) (𝓡 3) ∞ β)
    (hβe : ∀ (q : S3) (y y' : SV), ((y' : Vs e) : W) = R.ρ q ((y : Vs e) : W) →
      β y' = q * β y * q⁻¹),
    HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace (R.polarOf (m := m) β hβs hβe))

/-- Every polar datum with representation `R.ρ` is `R.polarOf θ⁻¹`. -/
theorem polarOf_inv (R : StarRep e) (D : PolarData (m := m) e) (hD : D.ρ = R.ρ) :
    ∃ (hβs : ContMDiff (𝓡 m) (𝓡 3) ∞ fun y => (D.θ y)⁻¹)
      (hβe : ∀ (q : S3) (y y' : SV), ((y' : Vs e) : W) = R.ρ q ((y : Vs e) : W) →
        (D.θ y')⁻¹ = q * (D.θ y)⁻¹ * q⁻¹),
      R.polarOf (m := m) (fun y => (D.θ y)⁻¹) hβs hβe = D := by
  refine ⟨contMDiff_invS3.comp D.θ_smooth, inv_θ_equiv (hD ▸ D.θ_equiv), ?_⟩
  obtain ⟨e_norm, ρ, ρ_e, ρ_smooth, θ, θ_smooth, θ_equiv⟩ := D
  obtain ⟨Re_norm, Rρ, Rρ_e, Rρ_smooth⟩ := R
  simp only at hD
  subst hD
  simp only [StarRep.polarOf, inv_inv]

end Remark

section RemarkMain

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] [T2Space E]

/-- **[D] Remark `rem:general_bound`.** For every star bundle `E`, with an arbitrary
representation and no bound on `K`:
- `E/S³_⋆ ≃ₜ QuotSpace D` for a polar datum `D` whose attaching map is `J_β`, `β = θ⁻¹`
  smooth and conjugation-equivariant;
- given [DHZ] Prop. 5.1 + RW (`DHZGluing`), `QuotSpace D` carries a smooth metric with
  `sec > 0`. -/
theorem remark_general_bound (B : StarBundle (m := m) R E) :
    letI := R.factVs m
    ∃ D : PolarData (m := m) e, D.ρ = R.ρ ∧
      Nonempty (Quotient (EquivSections.starSetoid B) ≃ₜ QuotSpace D) ∧
      (∃ (β : Metric.sphere (0 : Vs e) 1 → S3) (hβs : ContMDiff (𝓡 m) (𝓡 3) ∞ β)
        (hβe : ∀ (q : S3) (y y' : Metric.sphere (0 : Vs e) 1),
          ((y' : Vs e) : W) = R.ρ q ((y : Vs e) : W) → β y' = q * β y * q⁻¹),
        R.polarOf (m := m) β hβs hβe = D ∧
        ∀ y, ((D.sigmaV y : Vs e) : W) = R.ρ (β y) ((y : Vs e) : W)) ∧
      (DHZGluing (m := m) R → HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace D)) := by
  letI := R.factVs m
  obtain ⟨D, hD, -, -, -, -, ⟨hq⟩⟩ := B.prop_polar
  obtain ⟨hβs, hβe, hpol⟩ := polarOf_inv R D hD
  refine ⟨D, hD, ⟨hq.trans D.orbitSpaceHomeo⟩,
    ⟨fun y => (D.θ y)⁻¹, hβs, hβe, hpol, fun y => ?_⟩, fun hDHZ => ?_⟩
  · rw [← sigmaV_eq_J R _ hβs hβe y, hpol]
  · have h := hDHZ (fun y => (D.θ y)⁻¹) hβs hβe
    have key : ∀ D₁ D₂ : PolarData (m := m) e, D₁ = D₂ →
        HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace D₁) →
          HasPosCurvMetric (𝓡 (m + 1)) (QuotSpace D₂) := by
      rintro _ _ rfl h; exact h
    exact key _ _ hpol h

/-- **Non-vacuity**: the remark applies to the product star bundles for `ρ₈` and `ρ₁₀`, which
are not covered by any bound-free statement in `theoremA`. -/
example := remark_general_bound (m := 7) (prodBundle rep8)

end RemarkMain

end

end ExoticSpheres8And10
