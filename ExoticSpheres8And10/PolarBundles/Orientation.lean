/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.ActionField.Bound

/-! # A3. Orientation bookkeeping ([D] `lem:attaching`(3), second paragraph)

[D]: "For orientation bookkeeping put `β = dθ θ⁻¹`. Differentiating equivariance and the
definition of `σ` gives `β_y K_y = Id − Ad_{θ(y)}`, `Dσ_y = ρ(θ(y)⁻¹)(Id − K_y β_y)`, where
`K_y ξ = d/dτ|₀ ρ(e^{τξ}) y`. The determinant identity `det(Id − AB) = det(Id − BA)` gives
`det(Id − K_y β_y) = det Ad_{θ(y)} = 1`."

* (a) Sylvester for linear maps between finite-dimensional real spaces.
* (b) The matrix of `v ↦ q v q⁻¹` on `Im ℍ` (basis `i, j, k`) has determinant `1`, `q ≠ 0`.
* (c) Differentiated equivariance at a point, along an abstract curve `q(τ)` with `q 0 = 1`,
  `q' 0 = ξ`: `dθ_y(K_y ξ) = ξθ − θξ`, hence `β_y K_y ξ = ξ − θ ξ θ⁻¹`.
* (d) `det(Id − K_y β_y) = 1`.
-/

namespace ExoticSpheres8And10

open Quaternion

/-! ### (a) Sylvester's determinant identity for linear maps -/

theorem det_id_sub_comp_comm {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] E) :
    LinearMap.det (LinearMap.id - A ∘ₗ B) = LinearMap.det (LinearMap.id - B ∘ₗ A) := by
  classical
  let bE := Module.finBasis ℝ E
  let bF := Module.finBasis ℝ F
  rw [← LinearMap.det_toMatrix bF (LinearMap.id - A ∘ₗ B),
    ← LinearMap.det_toMatrix bE (LinearMap.id - B ∘ₗ A), map_sub, map_sub,
    LinearMap.toMatrix_id, LinearMap.toMatrix_id, LinearMap.toMatrix_comp bF bE bF,
    LinearMap.toMatrix_comp bE bF bE]
  exact Matrix.det_one_sub_mul_comm _ _

/-! ### (b) `det Ad_q = 1` on `Im ℍ` -/

/-- `normSq q` in components. -/
noncomputable def nsq (q : ℍ[ℝ]) : ℝ := q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

/-- The matrix of `v ↦ q v q⁻¹` on `Im ℍ` in the basis `i, j, k`. -/
noncomputable def adMatrix (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2) / nsq q,
      2 * (q.imI * q.imJ - q.re * q.imK) / nsq q,
      2 * (q.imI * q.imK + q.re * q.imJ) / nsq q;
    2 * (q.imI * q.imJ + q.re * q.imK) / nsq q,
      (q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2) / nsq q,
      2 * (q.imJ * q.imK - q.re * q.imI) / nsq q;
    2 * (q.imI * q.imK - q.re * q.imJ) / nsq q,
      2 * (q.imJ * q.imK + q.re * q.imI) / nsq q,
      (q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2) / nsq q]

theorem nsq_ne_zero {q : ℍ[ℝ]} (hq : q ≠ 0) : nsq q ≠ 0 := by
  have h : Quaternion.normSq q ≠ 0 := fun h => hq (Quaternion.normSq_eq_zero.1 h)
  rwa [Quaternion.normSq_def'] at h

/-- Embedding of coordinates `(v₀, v₁, v₂)` as the imaginary quaternion `v₀i + v₁j + v₂k`. -/
def imEmb (v : Fin 3 → ℝ) : ℍ[ℝ] := qmk 0 (v 0) (v 1) (v 2)

theorem imEmb_sub (v w : Fin 3 → ℝ) : imEmb (v - w) = imEmb v - imEmb w := by
  ext <;> simp [imEmb]

theorem imEmb_injective : Function.Injective imEmb := by
  intro v w h
  have h1 := congrArg (fun q : ℍ[ℝ] => q.imI) h
  have h2 := congrArg (fun q : ℍ[ℝ] => q.imJ) h
  have h3 := congrArg (fun q : ℍ[ℝ] => q.imK) h
  simp only [imEmb, qmk_imI, qmk_imJ, qmk_imK] at h1 h2 h3
  funext i
  fin_cases i <;> assumption

/-- `adMatrix q` represents `v ↦ q v q⁻¹` on `Im ℍ`. -/
theorem conj_imEmb (q : ℍ[ℝ]) (hq : q ≠ 0) (v : Fin 3 → ℝ) :
    q * imEmb v * q⁻¹ = imEmb ((adMatrix q).mulVec v) := by
  have hN : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 ≠ 0 := nsq_ne_zero hq
  rw [Quaternion.inv_def, mul_smul_comm]
  ext <;>
    simp only [imEmb, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, qmk_re, qmk_imI, qmk_imJ, qmk_imK,
      Quaternion.normSq_def', Matrix.mulVec, dotProduct, Fin.sum_univ_three, adMatrix,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const, nsq] <;>
    field_simp <;>
    ring

/-- **A3(b).** `det Ad_q = 1` for `q ≠ 0`: the determinant of the (unnormalised) rotation
matrix is `‖q‖⁶`, divided by `‖q‖⁶`. -/
theorem det_adMatrix (q : ℍ[ℝ]) (hq : q ≠ 0) : (adMatrix q).det = 1 := by
  have hN : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 ≠ 0 := nsq_ne_zero hq
  rw [Matrix.det_fin_three]
  simp only [adMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const, nsq]
  field_simp
  ring

theorem det_toLin'_adMatrix (q : ℍ[ℝ]) (hq : q ≠ 0) :
    LinearMap.det (Matrix.toLin' (adMatrix q)) = 1 := by
  rw [LinearMap.det_toLin', det_adMatrix q hq]

/-! ### (c) Differentiated equivariance at a point -/

/-- **A3(c).** Let `θ : Y → ℍ` be differentiable at `y`, `γ` a curve through `y` with
`γ'(0) = K_y ξ` (the orbit `τ ↦ ρ(q(τ)) y`), and `q` a curve of units with `q 0 = 1`,
`q' 0 = ξ`. If `θ(γ τ) = q(τ) θ(y) q(τ)⁻¹` for all `τ` (equivariance along the orbit),
then `dθ_y(K_y ξ) = ξ θ(y) − θ(y) ξ`. -/
theorem dtheta_K {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (θ : Y → ℍ[ℝ]) (Dθ : Y →L[ℝ] ℍ[ℝ]) (y : Y) (hθ : HasFDerivAt θ Dθ y)
    (γ : ℝ → Y) (Kξ : Y) (hγ0 : γ 0 = y) (hγ : HasDerivAt γ Kξ 0)
    (q : ℝ → ℍ[ℝ]) (ξ : ℍ[ℝ]) (hq0 : q 0 = 1) (hq : HasDerivAt q ξ 0)
    (hqne : ∀ τ, q τ ≠ 0) (hequiv : ∀ τ, θ (γ τ) = q τ * θ y * (q τ)⁻¹) :
    Dθ Kξ = ξ * θ y - θ y * ξ := by
  have h1 : (fun τ => θ (γ τ) * q τ) = fun τ => q τ * θ y := by
    funext τ
    rw [hequiv τ, mul_assoc, inv_mul_cancel₀ (hqne τ), mul_one]
  have hθγ : HasDerivAt (fun τ => θ (γ τ)) (Dθ Kξ) 0 := by
    rw [← hγ0] at hθ
    exact hθ.comp_hasDerivAt (x := 0) hγ
  have hL : HasDerivAt (fun τ => θ (γ τ) * q τ) (Dθ Kξ * q 0 + θ (γ 0) * ξ) 0 :=
    hθγ.mul hq
  have hR : HasDerivAt (fun τ => q τ * θ y) (ξ * θ y) 0 := hq.mul_const (θ y)
  rw [h1] at hL
  have := hL.unique hR
  rw [hq0, hγ0, mul_one] at this
  rw [← this]
  abel

/-- **A3(c), consequence.** `β_y(K_y ξ) = dθ_y(K_y ξ) θ(y)⁻¹ = ξ − θ(y) ξ θ(y)⁻¹`, i.e.
`β_y K_y = Id − Ad_{θ(y)}`. -/
theorem beta_K {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (θ : Y → ℍ[ℝ]) (Dθ : Y →L[ℝ] ℍ[ℝ]) (y : Y) (hθ : HasFDerivAt θ Dθ y) (hθy : θ y ≠ 0)
    (γ : ℝ → Y) (Kξ : Y) (hγ0 : γ 0 = y) (hγ : HasDerivAt γ Kξ 0)
    (q : ℝ → ℍ[ℝ]) (ξ : ℍ[ℝ]) (hq0 : q 0 = 1) (hq : HasDerivAt q ξ 0)
    (hqne : ∀ τ, q τ ≠ 0) (hequiv : ∀ τ, θ (γ τ) = q τ * θ y * (q τ)⁻¹) :
    Dθ Kξ * (θ y)⁻¹ = ξ - θ y * ξ * (θ y)⁻¹ := by
  rw [dtheta_K θ Dθ y hθ γ Kξ hγ0 hγ q ξ hq0 hq hqne hequiv, sub_mul, mul_assoc ξ,
    mul_inv_cancel₀ hθy, mul_one]

/-! ### (d) `det(Id − K_y β_y) = 1` -/

/-- **A3(d).** Let `T` be finite-dimensional (in [D], `T = T_y S^{n−1}`), `K : Im ℍ → T` and
`β : T → Im ℍ` linear (with `Im ℍ` in coordinates `i, j, k`), and suppose
`β(K v) = v − θ v θ⁻¹` for all `v` (the conclusion of (c)). Then `det(Id − Kβ) = 1`. -/
theorem det_id_sub_K_beta {T : Type*} [AddCommGroup T] [Module ℝ T] [FiniteDimensional ℝ T]
    (K : (Fin 3 → ℝ) →ₗ[ℝ] T) (β : T →ₗ[ℝ] (Fin 3 → ℝ)) (θy : ℍ[ℝ]) (hθy : θy ≠ 0)
    (hβK : ∀ v, imEmb (β (K v)) = imEmb v - θy * imEmb v * θy⁻¹) :
    LinearMap.det (LinearMap.id - K ∘ₗ β) = 1 := by
  rw [det_id_sub_comp_comm]
  have : LinearMap.id - β ∘ₗ K = Matrix.toLin' (adMatrix θy) := by
    apply LinearMap.ext
    intro v
    have h := hβK v
    rw [conj_imEmb θy hθy v, ← imEmb_sub] at h
    have h' := imEmb_injective h
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      Matrix.toLin'_apply, h']
    abel
  rw [this, det_toLin'_adMatrix θy hθy]

/-! ### Non-vacuity

* (c): a non-degenerate model. `Y = ℍ`, `θ = id`, `q(τ) = 1 + τξ` for imaginary `ξ`
  (a curve of nonzero quaternions with `q 0 = 1`, `q' 0 = ξ`), and `γ(τ) = q(τ) y q(τ)⁻¹`, the
  conjugation orbit, whose velocity is computed from Mathlib's derivative of inversion. Every
  hypothesis of `dtheta_K` is discharged; at `ξ = i`, `y = j` the conclusion is `2k = 2k`.
* (d): `T = Im ℍ`, `K = id`, `β = id − Ad_θ` for any `θ ≠ 0`. -/

theorem curve_one_add_smul (ξ : ℍ[ℝ]) (hξ : ξ.re = 0) :
    HasDerivAt (fun τ : ℝ => 1 + τ • ξ) ξ 0 ∧ ∀ τ : ℝ, (1 + τ • ξ) ≠ 0 := by
  refine ⟨(((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add 1).congr_deriv (by simp), ?_⟩
  intro τ h
  have := congrArg (fun q : ℍ[ℝ] => q.re) h
  simp [Quaternion.re_smul, hξ] at this

theorem conj_orbit_hasDerivAt (ξ y : ℍ[ℝ]) (hξ : ξ.re = 0) :
    HasDerivAt (fun τ : ℝ => (1 + τ • ξ) * y * (1 + τ • ξ)⁻¹) (ξ * y - y * ξ) 0 := by
  have hq := (curve_one_add_smul ξ hξ).1
  have h0 : (1 + (0 : ℝ) • ξ) = 1 := by simp
  have hF := hasFDerivAt_inv' (𝕜 := ℝ) (x := (1 + (0 : ℝ) • ξ)) (by rw [h0]; exact one_ne_zero)
  have hinv : HasDerivAt (fun τ : ℝ => (1 + τ • ξ)⁻¹) (-ξ) 0 :=
    (hF.comp_hasDerivAt (x := (0 : ℝ)) hq).congr_deriv (by simp)
  exact ((hq.mul_const y).mul hinv).congr_deriv (by simp [sub_eq_add_neg])

example : ContinuousLinearMap.id ℝ ℍ[ℝ] (qmk 0 1 0 0 * qmk 0 0 1 0 - qmk 0 0 1 0 * qmk 0 1 0 0) =
    qmk 0 1 0 0 * id (qmk 0 0 1 0) - id (qmk 0 0 1 0) * qmk 0 1 0 0 :=
  dtheta_K (Y := ℍ[ℝ]) id (ContinuousLinearMap.id ℝ _) (qmk 0 0 1 0) (hasFDerivAt_id _)
    (fun τ : ℝ => (1 + τ • qmk 0 1 0 0) * qmk 0 0 1 0 * (1 + τ • qmk 0 1 0 0)⁻¹) _
    (by simp) (conj_orbit_hasDerivAt _ _ rfl) (fun τ : ℝ => 1 + τ • qmk 0 1 0 0) _ (by simp)
    (curve_one_add_smul _ rfl).1 (curve_one_add_smul _ rfl).2 (fun _ => rfl)

example (θy : ℍ[ℝ]) (hθy : θy ≠ 0) :
    LinearMap.det (LinearMap.id - (LinearMap.id : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ∘ₗ
      (LinearMap.id - Matrix.toLin' (adMatrix θy))) = 1 :=
  det_id_sub_K_beta LinearMap.id (LinearMap.id - Matrix.toLin' (adMatrix θy)) θy hθy
    (fun v => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Matrix.toLin'_apply]
      rw [imEmb_sub, conj_imEmb θy hθy])

end ExoticSpheres8And10
