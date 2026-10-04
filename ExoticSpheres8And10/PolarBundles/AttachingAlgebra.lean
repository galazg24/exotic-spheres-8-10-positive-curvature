/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # A2. Attaching-map algebra ([GG] `lem:attaching`(2))

Abstract setting: a group `G` acting on `X` (in [GG], `G = S³` acting on `S^{n-1}` through
`ρ`), and a map `θ : X → G` that is equivariant for conjugation, `θ (g • x) = g θ(x) g⁻¹`
([GG] `eq:equiv`).

We define `σ y = θ(y)⁻¹ • y` ([GG] `eq:sigma`) and `σ̂ y = θ(y) • y`, and prove:
* `θ ∘ σ = θ` and `θ ∘ σ̂ = θ`;
* `σ̂ ∘ σ = id` and `σ ∘ σ̂ = id`, packaged as an `Equiv`;
* the boundary computation: if `u_S = θ(x) u_N` ([GG] `eq:transition`), `y_N = u_N⁻¹ • x`
  and `y_S = u_S⁻¹ • x`, then `y_S = σ y_N`.
-/

namespace ExoticSpheres8And10

section Attaching

variable {G X : Type*} [Group G] [MulAction G X]

/-- `θ` is equivariant for the conjugation action of `G` on itself ([GG] `eq:equiv`). -/
def IsConjEquivariant (θ : X → G) : Prop :=
  ∀ (g : G) (x : X), θ (g • x) = g * θ x * g⁻¹

/-- The attaching map `σ(y) = ρ(θ(y))⁻¹ y` of [GG] `eq:sigma`. -/
def attachSigma (θ : X → G) (y : X) : X := (θ y)⁻¹ • y

/-- The claimed inverse `σ̂(y) = ρ(θ(y)) y`. -/
def attachSigmaHat (θ : X → G) (y : X) : X := θ y • y

variable {θ : X → G}

theorem theta_attachSigma (hθ : IsConjEquivariant θ) (y : X) :
    θ (attachSigma θ y) = θ y := by
  unfold attachSigma
  rw [hθ, inv_inv]
  group

theorem theta_attachSigmaHat (hθ : IsConjEquivariant θ) (y : X) :
    θ (attachSigmaHat θ y) = θ y := by
  unfold attachSigmaHat
  rw [hθ]
  group

theorem attachSigmaHat_attachSigma (hθ : IsConjEquivariant θ) (y : X) :
    attachSigmaHat θ (attachSigma θ y) = y := by
  rw [attachSigmaHat, theta_attachSigma hθ, attachSigma, smul_inv_smul]

theorem attachSigma_attachSigmaHat (hθ : IsConjEquivariant θ) (y : X) :
    attachSigma θ (attachSigmaHat θ y) = y := by
  rw [attachSigma, theta_attachSigmaHat hθ, attachSigmaHat, inv_smul_smul]

/-- `σ` as a bijection of `X`, with inverse `σ̂` ([GG] `lem:attaching`(2), last sentence,
bijectivity part; smoothness is not formalised). -/
def attachSigmaEquiv (hθ : IsConjEquivariant θ) : X ≃ X where
  toFun := attachSigma θ
  invFun := attachSigmaHat θ
  left_inv := attachSigmaHat_attachSigma hθ
  right_inv := attachSigma_attachSigmaHat hθ

@[simp] theorem attachSigmaEquiv_apply (hθ : IsConjEquivariant θ) (y : X) :
    attachSigmaEquiv hθ y = attachSigma θ y := rfl

@[simp] theorem attachSigmaEquiv_symm_apply (hθ : IsConjEquivariant θ) (y : X) :
    (attachSigmaEquiv hθ).symm y = attachSigmaHat θ y := rfl

/-- **Boundary computation** ([GG] `lem:attaching`(2), proof). On the common boundary the
transition is `u_S = θ(x) u_N`; the boundary markings are `y_N = u_N⁻¹ • x` and
`y_S = u_S⁻¹ • x`. Then `y_S = σ(y_N)`. -/
theorem attaching_boundary (hθ : IsConjEquivariant θ) (x yN yS : X) (uN uS : G)
    (hS : uS = θ x * uN) (hyN : yN = uN⁻¹ • x) (hyS : yS = uS⁻¹ • x) :
    yS = attachSigma θ yN := by
  have hx : θ yN = uN⁻¹ * θ x * uN := by
    rw [hyN, hθ, inv_inv]
  rw [hyS, attachSigma, hx, hS, hyN, smul_smul]
  congr 1
  group

/-! ### Non-vacuity

The hypothesis `IsConjEquivariant` is satisfiable, non-trivially: `G` acting on itself by
conjugation (`ConjAct G`), with `θ` the identity. For `G = S³` this is the conjugation
action of `S³` on itself. -/

theorem isConjEquivariant_conjAct (G : Type*) [Group G] :
    IsConjEquivariant (G := ConjAct G) (X := G) ConjAct.toConjAct := by
  intro g x
  rw [ConjAct.smul_def]
  rfl

/-- The boundary theorem fires in the conjugation model: with `u_N = 1` and `u_S = θ(x)`,
`y_S = σ(y_N)` is the non-trivial statement `θ(x)⁻¹ • x = σ x`. -/
example (G : Type*) [Group G] (x : G) :
    ((ConjAct.toConjAct x)⁻¹ • x : G) =
      attachSigma (ConjAct.toConjAct (G := G)) ((1 : ConjAct G)⁻¹ • x) :=
  attaching_boundary (isConjEquivariant_conjAct G) x _ _ 1 _
    (by rw [mul_one]) rfl rfl

end Attaching

end ExoticSpheres8And10
