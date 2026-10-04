/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.ActionField.Bound

/-! # A4. Gauge algebra ([GG] §4.2, "The southern filling", items 1 and 3)

At the level of values of derivatives at a point, in `ℍ[ℝ]`. Here `θ`, `u` are the values of
the (unit-quaternion-valued) maps at a point and `dθ`, `du` the values of their derivatives on
a tangent vector; `χ` is the value of the cutoff.

[GG] item 1 (*Gauge compatibility*): "From `u_S = θ u_N`: `u_S⁻¹du_S = u_N⁻¹θ⁻¹dθ u_N + u_N⁻¹du_N`
and `u_S⁻¹A_Su_S = u_N⁻¹θ⁻¹A_Sθu_N`. So compatibility is `A_N = θ⁻¹A_Sθ + θ⁻¹dθ`, which holds:
`(χ−1)θ⁻¹dθ + θ⁻¹dθ = χθ⁻¹dθ`." Here `A_N = χ θ⁻¹dθ`, `A_S = (χ−1) dθ θ⁻¹`
(`eq:potentials`), `ω = u⁻¹Au + u⁻¹du`.

[GG] item 3 (*Star invariance*): "By `eq:equiv`, `θ(ρ(q)x)⁻¹dθ(ρ(q)x) = q(θ⁻¹dθ)q⁻¹` [...].
With `u ↦ qu`, `(qu)⁻¹qAq⁻¹(qu) + (qu)⁻¹d(qu) = u⁻¹Au + u⁻¹du`."
-/

namespace ExoticSpheres8And10

open Quaternion

section Values

variable (θ dθ uN duN : ℍ[ℝ]) (χ : ℝ)

/-- **A4(a), potentials.** `A_N = θ⁻¹ A_S θ + θ⁻¹ dθ` for `A_N = χ θ⁻¹dθ`,
`A_S = (χ−1) dθθ⁻¹`. -/
theorem gauge_potentials (hθ : θ ≠ 0) :
    χ • (θ⁻¹ * dθ) = θ⁻¹ * ((χ - 1) • (dθ * θ⁻¹)) * θ + θ⁻¹ * dθ := by
  have key : θ⁻¹ * ((χ - 1) • (dθ * θ⁻¹)) * θ = (χ - 1) • (θ⁻¹ * dθ) := by
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc, inv_mul_cancel₀ hθ, mul_one]
  rw [key, sub_smul, one_smul]
  abel

/-- **A4(a), connection forms.** With `u_S = θ u_N` and `du_S = dθ u_N + θ du_N` (Leibniz),
the two gauges define the same connection form:
`u_S⁻¹ A_S u_S + u_S⁻¹ du_S = u_N⁻¹ A_N u_N + u_N⁻¹ du_N`. -/
theorem gauge_compatible (hθ : θ ≠ 0) :
    (θ * uN)⁻¹ * ((χ - 1) • (dθ * θ⁻¹)) * (θ * uN) + (θ * uN)⁻¹ * (dθ * uN + θ * duN) =
      uN⁻¹ * (χ • (θ⁻¹ * dθ)) * uN + uN⁻¹ * duN := by
  rw [gauge_potentials θ dθ χ hθ, mul_inv_rev]
  simp only [mul_add, add_mul, mul_assoc, inv_mul_cancel_left₀ hθ]
  abel

/-- `d(θ⁻¹) = −θ⁻¹ dθ θ⁻¹`, at the level of values: if `dι` is the derivative of `θ⁻¹`, the
Leibniz rule for `θ θ⁻¹ = 1` gives `dθ θ⁻¹ + θ dι = 0`, hence `dι = −θ⁻¹ dθ θ⁻¹`. -/
theorem dinv_of_leibniz (dι : ℍ[ℝ]) (hθ : θ ≠ 0) (h : dθ * θ⁻¹ + θ * dι = 0) :
    dι = -(θ⁻¹ * dθ * θ⁻¹) := by
  have : θ * dι = -(dθ * θ⁻¹) := eq_neg_of_add_eq_zero_right h
  calc dι = θ⁻¹ * (θ * dι) := (inv_mul_cancel_left₀ hθ dι).symm
    _ = -(θ⁻¹ * dθ * θ⁻¹) := by rw [this, mul_neg, mul_assoc]

/-- ... and the genuine derivative: along a curve `θ(t)` of nonzero quaternions,
`d/dt θ⁻¹ = −θ⁻¹ θ' θ⁻¹`. -/
theorem hasDerivAt_quat_inv (θc : ℝ → ℍ[ℝ]) (θ' : ℍ[ℝ]) (t : ℝ) (h : HasDerivAt θc θ' t)
    (hne : θc t ≠ 0) :
    HasDerivAt (fun s => (θc s)⁻¹) (-((θc t)⁻¹ * θ' * (θc t)⁻¹)) t :=
  ((hasFDerivAt_inv' (𝕜 := ℝ) hne).comp_hasDerivAt t h).congr_deriv (by simp)

end Values

/-- **A4(b), star invariance of the connection form.** For a constant `q ≠ 0` and `u ≠ 0`,
`(qu)⁻¹ (qAq⁻¹) (qu) + (qu)⁻¹ d(qu) = u⁻¹Au + u⁻¹du`, where `d(qu) = q du`. -/
theorem star_invariance_form (q u A du : ℍ[ℝ]) (hq : q ≠ 0) :
    (q * u)⁻¹ * (q * A * q⁻¹) * (q * u) + (q * u)⁻¹ * (q * du) = u⁻¹ * A * u + u⁻¹ * du := by
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hq]

/-- **A4(b), star invariance of `θ⁻¹dθ`.** If `θ' = qθq⁻¹` and `dθ' = q dθ q⁻¹` (the values
of `θ ∘ ρ(q)` and its derivative, by `eq:equiv` with `q` constant), then
`θ'⁻¹ dθ' = q (θ⁻¹dθ) q⁻¹`. -/
theorem star_invariance_mc (q θ dθ : ℍ[ℝ]) (hq : q ≠ 0) :
    (q * θ * q⁻¹)⁻¹ * (q * dθ * q⁻¹) = q * (θ⁻¹ * dθ) * q⁻¹ := by
  simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left₀ hq]

/-! ### Non-vacuity

The only hypotheses are `θ ≠ 0` and `q ≠ 0`, which hold for the unit quaternions of [GG]
(e.g. `θ = q = 1`, or `θ = i`). Instance with non-commuting values: -/

example : (qmk 0 1 0 0 * qmk 0 0 1 0)⁻¹ * ((2 - 1 : ℝ) • (qmk 0 0 0 1 * (qmk 0 1 0 0)⁻¹)) *
      (qmk 0 1 0 0 * qmk 0 0 1 0) +
    (qmk 0 1 0 0 * qmk 0 0 1 0)⁻¹ * (qmk 0 0 0 1 * qmk 0 0 1 0 + qmk 0 1 0 0 * qmk 1 0 0 0) =
    (qmk 0 0 1 0)⁻¹ * ((2 : ℝ) • ((qmk 0 1 0 0)⁻¹ * qmk 0 0 0 1)) * qmk 0 0 1 0 +
      (qmk 0 0 1 0)⁻¹ * qmk 1 0 0 0 :=
  gauge_compatible _ _ _ _ 2 (fun h => by simpa using congrArg (fun q : ℍ[ℝ] => q.imI) h)

end ExoticSpheres8And10
