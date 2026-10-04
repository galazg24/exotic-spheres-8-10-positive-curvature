/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.NormalForm
import ExoticSpheres8And10.StarBundles.InnerEndomorphisms

/-! # §3, Step 2: normalising the star action over the poles

[GG] `prop:polar`, Step 2: over a fixed point `ζ₀` of `ρ` (the poles `o_N = e`, `o_S = −e`) there
is `s₀ ∈ E_{ζ₀}` with `q ⋆ s₀ = s₀ q` (`eq:model`).

Proof as in [GG]: `φ(q) = p₀⁻¹(q ⋆ p₀)` is a continuous injective homomorphism `S³ → S³`, hence
inner (`injContEndoInner_S3`, B1, proved without Lie theory), `φ(q) = cqc⁻¹`, and `s₀ = p₀c`.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Step2

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} {R : StarRep e} {E : Type*} [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

namespace StarBundle

/-- `φ(q) = p₀⁻¹ (q ⋆ p₀)` for `p₀` over a `ρ`-fixed point. -/
def phiHomE (p₀ : E) (hfix : ∀ q, B.proj (B.star q p₀) = B.proj p₀) : S3 →* S3 where
  toFun q := B.divE p₀ (B.star q p₀)
  map_one' := by
    apply B.divE_unique; rw [B.ract_one, B.star_one]
  map_mul' q q' := by
    apply B.divE_unique
    rw [← B.ract_mul, B.ract_divE _ _ (hfix q), ← B.star_ract, B.ract_divE _ _ (hfix q'),
      B.star_mul]

theorem phiHomE_spec (p₀ : E) (hfix) (q : S3) :
    B.star q p₀ = B.ract p₀ (B.phiHomE p₀ hfix q) :=
  (B.ract_divE _ _ (hfix q)).symm

theorem phiHomE_injective (p₀ : E) (hfix) : Injective (B.phiHomE p₀ hfix) := by
  intro q q' h
  have h1 : B.star q p₀ = B.star q' p₀ := by
    rw [B.phiHomE_spec p₀ hfix q, B.phiHomE_spec p₀ hfix q', h]
  have h2 : B.star (q'⁻¹ * q) p₀ = p₀ := by
    rw [B.star_mul, h1, ← B.star_mul, inv_mul_cancel, B.star_one]
  have := B.star_free _ _ h2
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem phiHomE_continuous (p₀ : E) (hfix) : Continuous (B.phiHomE p₀ hfix) := by
  have hs : ContMDiff (𝓡 3) (IP m) ∞ fun q : S3 => B.star q p₀ :=
    B.star_smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have := B.contMDiffOn_divE (f := fun _ : S3 => p₀) (f' := fun q => B.star q p₀) isOpen_univ
    contMDiffOn_const hs.contMDiffOn fun q _ => hfix q
  exact (contMDiffOn_univ.1 this).continuous

/-- **[GG] `prop:polar`, Step 2** (`eq:model`): over a `ρ`-fixed point there is `s₀` with
`q ⋆ s₀ = s₀ q` for all `q`. -/
theorem exists_model_point (ζ₀ : Sn) (hfix : ∀ q, R.ρS q ζ₀ = ζ₀) :
    ∃ s₀ : E, B.proj s₀ = ζ₀ ∧ ∀ q, B.star q s₀ = B.ract s₀ q := by
  set p₀ := B.sec ζ₀ ζ₀
  have hp : B.proj p₀ = ζ₀ := B.proj_sec ζ₀ ζ₀ (B.mem_nbhd ζ₀)
  have hfix' : ∀ q, B.proj (B.star q p₀) = B.proj p₀ := fun q => by
    rw [B.proj_star, hp, hfix]
  obtain ⟨c, hc⟩ := injContEndoInner_S3 (B.phiHomE p₀ hfix') (B.phiHomE_injective p₀ hfix')
    (B.phiHomE_continuous p₀ hfix')
  refine ⟨B.ract p₀ c, by rw [B.proj_ract, hp], fun q => ?_⟩
  rw [B.star_ract, B.phiHomE_spec p₀ hfix' q, hc, B.ract_mul, B.ract_mul, mul_assoc,
    inv_mul_cancel, mul_one]

end StarBundle

end Step2

end

end ExoticSpheres8And10
