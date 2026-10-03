/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Southern.Gauge

/-! # A1, completed: `K_y ξ` is the derivative of the orbit ([D] §5.2, `lem:K`)

[D]: "For `y ∈ S^{n-1}` let `K_y : Im ℍ → T_yS^{n−1}` be the infinitesimal action,
`K_y ξ = d/dτ|₀ ρ(e^{τξ})y`." and, in the proof of `lem:K`, "At `y = (x,w)`,
`K_yξ = (ξx, 2ξ × Im w)`" for `ρ₈(q)(λ,x,w) = (λ, qx, qwq⁻¹)`, and "At `y = (p,w,x)`,
`K_yξ = (0, ξw, 2ξ × x)`" for `ρ₁₀(q)(p,w,x) = (p, qw, qxq⁻¹)`.

A1 proved the bound for the displayed components. Here the components are **derived**:
along any differentiable curve of units `q(τ)` with `q(0) = 1`, `q'(0) = ξ` (in particular
`q(τ) = e^{τξ}`, instantiated below), the orbit has velocity `(ξx, ξw − wξ)`, resp.
`(0, ξw, ξx − xξ)`, and `ξw − wξ = 2ξ × Im w` is A1's `commutator_eq_two_qcross`.
-/

namespace ExoticSpheres8And10

open Quaternion NormedSpace

/-- Velocity of `τ ↦ q(τ) w q(τ)⁻¹` at `0`. -/
theorem hasDerivAt_conj_orbit (q : ℝ → ℍ[ℝ]) (ξ w : ℍ[ℝ]) (hq0 : q 0 = 1)
    (hq : HasDerivAt q ξ 0) :
    HasDerivAt (fun τ => q τ * w * (q τ)⁻¹) (ξ * w - w * ξ) 0 := by
  have hinv := hasDerivAt_quat_inv q ξ 0 hq (by rw [hq0]; exact one_ne_zero)
  exact ((hq.mul_const w).mul hinv).congr_deriv (by rw [hq0]; simp [sub_eq_add_neg])

/-- **`ρ₈`.** The orbit `τ ↦ (λ, q(τ)x, q(τ)wq(τ)⁻¹)` has velocity `(0, ξx, ξw − wξ)`. -/
theorem orbit8_velocity (q : ℝ → ℍ[ℝ]) (ξ : ℍ[ℝ]) (hq0 : q 0 = 1) (hq : HasDerivAt q ξ 0)
    (lam : ℝ) (x w : ℍ[ℝ]) :
    HasDerivAt (fun τ => (lam, q τ * x, q τ * w * (q τ)⁻¹)) ((0 : ℝ), ξ * x, ξ * w - w * ξ) 0 :=
  (hasDerivAt_const 0 lam).prodMk ((hq.mul_const x).prodMk (hasDerivAt_conj_orbit q ξ w hq0 hq))

/-- **`ρ₁₀`.** The orbit `τ ↦ (p, q(τ)w, q(τ)xq(τ)⁻¹)` has velocity `(0, ξw, ξx − xξ)`. -/
theorem orbit10_velocity (q : ℝ → ℍ[ℝ]) (ξ : ℍ[ℝ]) (hq0 : q 0 = 1) (hq : HasDerivAt q ξ 0)
    (p w x : ℍ[ℝ]) :
    HasDerivAt (fun τ => (p, q τ * w, q τ * x * (q τ)⁻¹)) ((0 : ℍ[ℝ]), ξ * w, ξ * x - x * ξ) 0 :=
  (hasDerivAt_const 0 p).prodMk ((hq.mul_const w).prodMk (hasDerivAt_conj_orbit q ξ x hq0 hq))

/-- The exponential curve `τ ↦ e^{τξ}` is an admissible curve: `q(0) = 1`, `q'(0) = ξ`, and
`q(τ)` is a unit for every `τ`. -/
theorem exp_curve (ξ : ℍ[ℝ]) :
    exp ((0 : ℝ) • ξ) = 1 ∧ HasDerivAt (fun τ : ℝ => exp (τ • ξ)) ξ 0 ∧
      ∀ τ : ℝ, exp (τ • ξ) ≠ 0 := by
  refine ⟨by simp, (hasDerivAt_exp_smul_const ξ (0 : ℝ)).congr_deriv (by simp), fun τ => ?_⟩
  have h : exp (τ • ξ) * exp ((-τ) • ξ) = 1 := by
    -- `exp_add_of_commute` needs a `ℚ`-algebra structure, obtained by restricting scalars
    let _ : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
    rw [← exp_add_of_commute (((Commute.refl ξ).smul_left τ).smul_right (-τ)), ← add_smul,
      add_neg_cancel, zero_smul, exp_zero]
  exact left_ne_zero_of_mul_eq_one h

/-- **[D]'s `K_yξ` for `ρ₈`, literally.** `d/dτ|₀ ρ₈(e^{τξ})(λ,x,w) = (0, ξx, ξw − wξ)`. -/
theorem K8_eq (ξ : ℍ[ℝ]) (lam : ℝ) (x w : ℍ[ℝ]) :
    HasDerivAt (fun τ : ℝ => (lam, exp (τ • ξ) * x, exp (τ • ξ) * w * (exp (τ • ξ))⁻¹))
      ((0 : ℝ), ξ * x, ξ * w - w * ξ) 0 := by
  obtain ⟨-, hd, -⟩ := exp_curve ξ
  exact orbit8_velocity _ ξ (by simp) hd lam x w

/-- **[D]'s `K_yξ` for `ρ₁₀`, literally.** `d/dτ|₀ ρ₁₀(e^{τξ})(p,w,x) = (0, ξw, ξx − xξ)`. -/
theorem K10_eq (ξ p w x : ℍ[ℝ]) :
    HasDerivAt (fun τ : ℝ => (p, exp (τ • ξ) * w, exp (τ • ξ) * x * (exp (τ • ξ))⁻¹))
      ((0 : ℍ[ℝ]), ξ * w, ξ * x - x * ξ) 0 := by
  obtain ⟨-, hd, -⟩ := exp_curve ξ
  exact orbit10_velocity _ ξ (by simp) hd p w x

/-- **`lem:K` for `ρ₈`, end to end.** On `S⁷` (`‖x‖² + ‖w‖² = 1`), the derivative of the
exponential orbit has squared (Euclidean) norm at most `4‖ξ‖²`. -/
theorem lemK_rho8 (ξ : ℍ[ℝ]) (lam : ℝ) (x w : ℍ[ℝ]) (hy : ‖x‖ ^ 2 + ‖w‖ ^ 2 = 1) :
    HasDerivAt (fun τ : ℝ => (lam, exp (τ • ξ) * x, exp (τ • ξ) * w * (exp (τ • ξ))⁻¹))
      ((0 : ℝ), ξ * x, ξ * w - w * ξ) 0 ∧
    ‖(0 : ℝ)‖ ^ 2 + ‖ξ * x‖ ^ 2 + ‖ξ * w - w * ξ‖ ^ 2 ≤ 4 * ‖ξ‖ ^ 2 :=
  ⟨K8_eq ξ lam x w, by simpa using actionField_bound_dim8 ξ x w hy⟩

/-- **`lem:K` for `ρ₁₀`, end to end.** On `S⁹` (`‖p‖² + ‖w‖² + ‖x‖² = 1`). -/
theorem lemK_rho10 (ξ p w x : ℍ[ℝ]) (hy : ‖p‖ ^ 2 + ‖w‖ ^ 2 + ‖x‖ ^ 2 = 1) :
    HasDerivAt (fun τ : ℝ => (p, exp (τ • ξ) * w, exp (τ • ξ) * x * (exp (τ • ξ))⁻¹))
      ((0 : ℍ[ℝ]), ξ * w, ξ * x - x * ξ) 0 ∧
    ‖(0 : ℍ[ℝ])‖ ^ 2 + ‖ξ * w‖ ^ 2 + ‖ξ * x - x * ξ‖ ^ 2 ≤ 4 * ‖ξ‖ ^ 2 :=
  ⟨K10_eq ξ p w x, by simpa using actionField_bound_dim10 ξ p w x hy⟩

end ExoticSpheres8And10
