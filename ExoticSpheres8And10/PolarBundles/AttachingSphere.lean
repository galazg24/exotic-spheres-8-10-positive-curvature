/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.PolarBundles.OrientationSphere
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # A2 for `ρ₈`: `σ` and `σ̂` are smooth maps of the manifold `S⁷`

[GG] `lem:attaching`: "The map `σ(y) = ρ(θ(y)⁻¹) y` is a diffeomorphism of `S^{n−1}` with
inverse `σ̂(y) = ρ(θ(y)) y`." `A3_Sphere` proves ambient smoothness and `σ(S⁷) ⊆ S⁷`. Here the
statement is upgraded to Mathlib's manifold structure on the unit sphere of `ℝ⁸ = ℍ ⊕ ℍ`
(`EuclideanSpace.instChartedSpaceSphere`, model `𝓡 7`): for any smooth unit-valued
`θ : S⁷ → ℍ`, the maps `y ↦ ρ₈(θ(y)⁻¹) y` and `y ↦ ρ₈(θ(y)) y` are `C^∞` maps `S⁷ → S⁷`.

Under the equivariance `eq:equiv`, `θ(ρ(q)y) = qθ(y)q⁻¹`, they are mutually inverse
(`sigmaHat_sigma`, `sigma_sigmaHat`), so `σ` is a diffeomorphism of `S⁷` (`sigmaDiffeo`).
-/

namespace ExoticSpheres8And10

open Quaternion Metric Module

open scoped Manifold ContDiff RealInnerProductSpace

/-- `ℍ ⊕ ℍ` with the Euclidean (`L²`) norm: `ℝ⁸`. -/
abbrev V8 := WithLp 2 (ℍ[ℝ] × ℍ[ℝ])

/-- The identification `V8 ≃ ℍ × ℍ`. -/
noncomputable abbrev eV8 : V8 ≃L[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℍ[ℝ] ℍ[ℝ]

instance fact_finrank_V8 : Fact (finrank ℝ V8 = 7 + 1) :=
  ⟨by rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (ℍ[ℝ] × ℍ[ℝ])), Module.finrank_prod,
    Quaternion.finrank_eq_four]⟩

local notation "S7" => sphere (0 : V8) 1

theorem norm_sq_V8 (w : V8) : ‖w‖ ^ 2 = dot2 (eV8 w) (eV8 w) := by
  rw [WithLp.prod_norm_sq_eq_of_L2, dot2, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  rfl

theorem norm_rho8V {q : ℍ[ℝ]} (hq : ‖q‖ = 1) (z : V8) : ‖eV8.symm (rho8 q (eV8 z))‖ = ‖z‖ := by
  have h : ‖eV8.symm (rho8 q (eV8 z))‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_V8, norm_sq_V8, ContinuousLinearEquiv.apply_symm_apply, rho8_dot q hq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem contDiffAt_rho8V {n : ℕ∞} {q₀ : ℍ[ℝ]} (hq : q₀ ≠ 0) (z₀ : V8) :
    ContDiffAt ℝ n (fun p : ℍ[ℝ] × V8 => eV8.symm (rho8 p.1 (eV8 p.2))) (q₀, z₀) := by
  have hz : ContDiffAt ℝ n (fun p : ℍ[ℝ] × V8 => eV8 p.2) (q₀, z₀) :=
    (eV8.contDiff.comp contDiff_snd).contDiffAt
  have hinv : ContDiffAt ℝ n (fun p : ℍ[ℝ] × V8 => p.1⁻¹) (q₀, z₀) :=
    (contDiffAt_quat_inv hq).comp _ contDiffAt_fst
  exact eV8.symm.contDiff.contDiffAt.comp _
    ((contDiffAt_fst.mul hz.fst).prodMk ((contDiffAt_fst.mul hz.snd).mul hinv))

theorem rho8V_mem {τ : S7 → ℍ[ℝ]} (hτn : ∀ y, ‖τ y‖ = 1) (y : S7) :
    eV8.symm (rho8 (τ y) (eV8 y)) ∈ S7 := by
  rw [mem_sphere_zero_iff_norm, norm_rho8V (hτn y)]
  exact mem_sphere_zero_iff_norm.1 y.2

/-- **`y ↦ ρ₈(τ(y)) y` is a smooth self-map of the manifold `S⁷`** for smooth unit-valued `τ`. -/
theorem contMDiff_rho8_sphere (τ : S7 → ℍ[ℝ]) (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℍ[ℝ]) ∞ τ)
    (hτn : ∀ y, ‖τ y‖ = 1) :
    ContMDiff (𝓡 7) (𝓡 7) ∞
      (Set.codRestrict (fun y : S7 => eV8.symm (rho8 (τ y) (eV8 y))) S7 (rho8V_mem hτn)) := by
  refine ContMDiff.codRestrict_sphere (fun y => ?_) _
  have hp : ContMDiffAt (𝓡 7) 𝓘(ℝ, ℍ[ℝ] × V8) ∞ (fun y : S7 => (τ y, (y : V8))) y :=
    (hτ y).prodMk_space (contMDiff_coe_sphere y)
  have hne : τ y ≠ 0 := fun h => by simpa [h] using hτn y
  exact ContDiffAt.comp_contMDiffAt (g := fun p : ℍ[ℝ] × V8 => eV8.symm (rho8 p.1 (eV8 p.2)))
    (f := fun y : S7 => (τ y, (y : V8))) (contDiffAt_rho8V (n := ⊤) hne (y : V8)) hp

/-- **[GG] `lem:attaching`, smoothness of `σ` on `S⁷`:** `σ(y) = ρ₈(θ(y)⁻¹) y`. -/
theorem contMDiff_sigma8_sphere (θ : S7 → ℍ[ℝ]) (hθ : ContMDiff (𝓡 7) 𝓘(ℝ, ℍ[ℝ]) ∞ θ)
    (hθn : ∀ y, ‖θ y‖ = 1) :
    ContMDiff (𝓡 7) (𝓡 7) ∞ (Set.codRestrict (fun y : S7 => eV8.symm (rho8 (θ y)⁻¹ (eV8 y))) S7
      (rho8V_mem (τ := fun y => (θ y)⁻¹) fun y => by rw [norm_inv, hθn, inv_one])) := by
  refine contMDiff_rho8_sphere (fun y => (θ y)⁻¹) (fun y => ?_)
    (fun y => by rw [norm_inv, hθn, inv_one])
  have hne : θ y ≠ 0 := fun h => by simpa [h] using hθn y
  exact ContDiffAt.comp_contMDiffAt (g := fun q : ℍ[ℝ] => q⁻¹) (f := θ)
    (contDiffAt_quat_inv (n := ⊤) hne) (hθ y)

/-- **Smoothness of `σ̂` on `S⁷`:** `σ̂(y) = ρ₈(θ(y)) y`. -/
theorem contMDiff_sigmaHat8_sphere (θ : S7 → ℍ[ℝ]) (hθ : ContMDiff (𝓡 7) 𝓘(ℝ, ℍ[ℝ]) ∞ θ)
    (hθn : ∀ y, ‖θ y‖ = 1) :
    ContMDiff (𝓡 7) (𝓡 7) ∞
      (Set.codRestrict (fun y : S7 => eV8.symm (rho8 (θ y) (eV8 y))) S7 (rho8V_mem hθn)) :=
  contMDiff_rho8_sphere θ hθ hθn

theorem norm_qj' : ‖qmk 0 0 1 0‖ = 1 := by
  have h : Quaternion.normSq (qmk 0 0 1 0) = 1 := by simp [Quaternion.normSq_def']
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg (qmk 0 0 1 0)]

/-- Non-vacuity: the constant `θ ≡ j` (giving `σ(x, w) = (−jx, jwj⁻¹)`, not the identity). -/
theorem sigma8_sphere_model :
    ContMDiff (𝓡 7) (𝓡 7) ∞ (Set.codRestrict
      (fun y : S7 => eV8.symm (rho8 (qmk 0 0 1 0)⁻¹ (eV8 y))) S7
      (rho8V_mem (τ := fun _ => (qmk 0 0 1 0)⁻¹) fun _ => by rw [norm_inv, norm_qj', inv_one])) :=
  contMDiff_sigma8_sphere (fun _ => qmk 0 0 1 0) contMDiff_const (fun _ => norm_qj')

/-! ## `σ̂ = σ⁻¹` under `eq:equiv`; `σ` is a diffeomorphism -/

theorem rho8_rho8_inv {q : ℍ[ℝ]} (hq : q ≠ 0) (z : ℍ[ℝ] × ℍ[ℝ]) : rho8 q (rho8 q⁻¹ z) = z := by
  simp [rho8, mul_assoc, hq]

theorem rho8_inv_rho8 {q : ℍ[ℝ]} (hq : q ≠ 0) (z : ℍ[ℝ] × ℍ[ℝ]) : rho8 q⁻¹ (rho8 q z) = z := by
  simp [rho8, mul_assoc, hq]

/-- The action `ρ₈(q)` of a unit quaternion on `S⁷`. -/
noncomputable def rho8S (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (y : S7) : S7 :=
  ⟨eV8.symm (rho8 q (eV8 y)), rho8V_mem (τ := fun _ => q) (fun _ => hq) y⟩

/-- `σ : S⁷ → S⁷`, `σ(y) = ρ₈(θ(y))⁻¹ y` ([GG] `eq:sigma`). -/
noncomputable def sigmaS (θ : S7 → ℍ[ℝ]) (hθn : ∀ y, ‖θ y‖ = 1) (y : S7) : S7 :=
  rho8S (θ y)⁻¹ (by rw [norm_inv, hθn, inv_one]) y

/-- `σ̂ : S⁷ → S⁷`, `σ̂(y) = ρ₈(θ(y)) y`. -/
noncomputable def sigmaHatS (θ : S7 → ℍ[ℝ]) (hθn : ∀ y, ‖θ y‖ = 1) (y : S7) : S7 :=
  rho8S (θ y) (hθn y) y

/-- `eq:equiv` on `S⁷`. -/
def IsEquivariant8 (θ : S7 → ℍ[ℝ]) : Prop :=
  ∀ (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (y : S7), θ (rho8S q hq y) = q * θ y * q⁻¹

theorem ne_zero_of_norm_one' {q : ℍ[ℝ]} (h : ‖q‖ = 1) : q ≠ 0 := fun h0 => by simp [h0] at h

/-- **[GG] `lem:attaching`(2): `σ̂ ∘ σ = id`.** -/
theorem sigmaHat_sigma (θ : S7 → ℍ[ℝ]) (hθn : ∀ y, ‖θ y‖ = 1) (hequiv : IsEquivariant8 θ)
    (y : S7) : sigmaHatS θ hθn (sigmaS θ hθn y) = y := by
  have hne := ne_zero_of_norm_one' (hθn y)
  have hθσ : θ (sigmaS θ hθn y) = θ y := by
    rw [sigmaS, hequiv, inv_inv, inv_mul_cancel₀ hne, one_mul]
  apply Subtype.ext
  show eV8.symm (rho8 (θ (sigmaS θ hθn y)) (eV8 (eV8.symm (rho8 (θ y)⁻¹ (eV8 y))))) = (y : V8)
  rw [hθσ, ContinuousLinearEquiv.apply_symm_apply, rho8_rho8_inv hne,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **`σ ∘ σ̂ = id`.** -/
theorem sigma_sigmaHat (θ : S7 → ℍ[ℝ]) (hθn : ∀ y, ‖θ y‖ = 1) (hequiv : IsEquivariant8 θ)
    (y : S7) : sigmaS θ hθn (sigmaHatS θ hθn y) = y := by
  have hne := ne_zero_of_norm_one' (hθn y)
  have hθσ : θ (sigmaHatS θ hθn y) = θ y := by
    rw [sigmaHatS, hequiv, mul_inv_cancel_right₀ hne]
  apply Subtype.ext
  show eV8.symm (rho8 (θ (sigmaHatS θ hθn y))⁻¹ (eV8 (eV8.symm (rho8 (θ y) (eV8 y))))) = (y : V8)
  rw [hθσ, ContinuousLinearEquiv.apply_symm_apply, rho8_inv_rho8 hne,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **[GG] `lem:attaching`(2) for `ρ₈`: `σ` is a diffeomorphism of `S⁷` with inverse `σ̂`**, for
any smooth, unit-valued, `ρ₈`-equivariant `θ`. -/
noncomputable def sigmaDiffeo (θ : S7 → ℍ[ℝ]) (hθ : ContMDiff (𝓡 7) 𝓘(ℝ, ℍ[ℝ]) ∞ θ)
    (hθn : ∀ y, ‖θ y‖ = 1) (hequiv : IsEquivariant8 θ) :
    Diffeomorph (𝓡 7) (𝓡 7) S7 S7 ∞ where
  toFun := sigmaS θ hθn
  invFun := sigmaHatS θ hθn
  left_inv := sigmaHat_sigma θ hθn hequiv
  right_inv := sigma_sigmaHat θ hθn hequiv
  contMDiff_toFun := contMDiff_sigma8_sphere θ hθ hθn
  contMDiff_invFun := contMDiff_sigmaHat8_sphere θ hθ hθn

/-- Non-vacuity of `eq:equiv`: `θ ≡ 1` is equivariant (so `sigmaDiffeo` is inhabited). -/
theorem isEquivariant8_one : IsEquivariant8 (fun _ => (1 : ℍ[ℝ])) := fun q hq _ => by
  rw [mul_one, mul_inv_cancel₀ (ne_zero_of_norm_one' hq)]

noncomputable example : Diffeomorph (𝓡 7) (𝓡 7) S7 S7 ∞ :=
  sigmaDiffeo _ contMDiff_const (fun _ => norm_one) isEquivariant8_one

end ExoticSpheres8And10
