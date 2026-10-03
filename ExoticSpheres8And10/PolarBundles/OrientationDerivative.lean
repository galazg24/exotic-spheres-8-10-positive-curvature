/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.ActionField.Chains
import ExoticSpheres8And10.Curvature.Southern.Gauge

/-! # A3, completed: `Dσ_y = ρ(θ(y)⁻¹)(Id − K_yβ_y)` and the orientation of `σ`

[D] `lem:attaching`, proof: "Differentiating equivariance and the definition of `σ` gives
`β_yK_y = Id − Ad_{θ(y)}`, `Dσ_y = ρ(θ(y)⁻¹)(Id − K_yβ_y)` [...] `det(Id − K_yβ_y) = det
Ad_{θ(y)} = 1`. The first factor preserves the ambient orientation and sends the normal `y` to
`σ(y)`, so `σ` preserves the standard sphere orientation."

For `ρ₈(q)(x,w) = (qx, qwq⁻¹)` and `ρ₁₀(q)(p,w,x) = (p, qw, qxq⁻¹)`, and `σ(y) = ρ(θ(y))⁻¹y`:
* `dsigma8`, `dsigma10`: along any differentiable curve through `y` with velocity `v`, the
  velocity of `σ` is `ρ(θ⁻¹)(v − K_y(dθ(v)θ⁻¹))`, i.e. `Dσ_y = ρ(θ(y)⁻¹)(Id − K_yβ_y)`;
* `det_rho8`, `det_rho10`: `det ρ(q) = 1` for `‖q‖ = 1` (the first factor preserves orientation);
* `rho8_self`, `rho10_self`: `ρ(θ(y)⁻¹) y = σ(y)` (it sends the normal `y` to `σ(y)`);
* `det_Dsigma8_ambient`: `det(ρ(θ⁻¹) ∘ (Id − Kβ)) = 1`.
-/

namespace ExoticSpheres8And10

open Quaternion

/-! ## The representations and action fields -/

/-- `ρ₈(q)(x,w) = (qx, qwq⁻¹)`. -/
noncomputable def rho8 (q : ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ]) : ℍ[ℝ] × ℍ[ℝ] := (q * y.1, q * y.2 * q⁻¹)

/-- `K_y η = (ηx, ηw − wη)` for `ρ₈` (A1, `K8_eq`). -/
noncomputable def K8 (y : ℍ[ℝ] × ℍ[ℝ]) (η : ℍ[ℝ]) : ℍ[ℝ] × ℍ[ℝ] := (η * y.1, η * y.2 - y.2 * η)

/-- `ρ₁₀(q)(p,w,x) = (p, qw, qxq⁻¹)`. -/
noncomputable def rho10 (q : ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] :=
  (y.1, q * y.2.1, q * y.2.2 * q⁻¹)

/-- `K_y η = (0, ηw, ηx − xη)` for `ρ₁₀` (A1, `K10_eq`). -/
noncomputable def K10 (y : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) (η : ℍ[ℝ]) : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] :=
  (0, η * y.2.1, η * y.2.2 - y.2.2 * η)

theorem rho8_self (θ : ℍ[ℝ] × ℍ[ℝ] → ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ]) :
    rho8 (θ y)⁻¹ y = ((θ y)⁻¹ * y.1, (θ y)⁻¹ * y.2 * θ y) := by
  simp [rho8]

theorem rho10_self (θ : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] → ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) :
    rho10 (θ y)⁻¹ y = (y.1, (θ y)⁻¹ * y.2.1, (θ y)⁻¹ * y.2.2 * θ y) := by
  simp [rho10]

/-! ## `Dσ` -/

/-- **`Dσ_y` for `ρ₈`.** Let `t ↦ (x(t), w(t))` pass through `y = (x₀, w₀)` with velocity
`(a, b)`, and `θ(t) = θ(x(t),w(t))` have derivative `θ'` (`= dθ_y(a,b)`), `θ(0) ≠ 0`. Then
`σ = (θ⁻¹x, θ⁻¹wθ)` has velocity `ρ₈(θ₀⁻¹)((a,b) − K_y(θ'θ₀⁻¹))`. -/
theorem dsigma8 (θc x w : ℝ → ℍ[ℝ]) (θ' a b : ℍ[ℝ]) (hθ : HasDerivAt θc θ' 0)
    (hx : HasDerivAt x a 0) (hw : HasDerivAt w b 0) (hne : θc 0 ≠ 0) :
    HasDerivAt (fun t => ((θc t)⁻¹ * x t, (θc t)⁻¹ * w t * θc t))
      (rho8 (θc 0)⁻¹ ((a, b) - K8 (x 0, w 0) (θ' * (θc 0)⁻¹))) 0 := by
  have hinv := hasDerivAt_quat_inv θc θ' 0 hθ hne
  refine ((hinv.mul hx).prodMk ((hinv.mul hw).mul hθ)).congr_deriv ?_
  refine Prod.ext ?_ ?_
  · simp only [rho8, K8, Prod.fst_sub, Prod.snd_sub]
    simp only [mul_sub, neg_mul, mul_assoc]
    abel
  · simp only [rho8, K8, Prod.fst_sub, Prod.snd_sub, inv_inv]
    simp only [Pi.mul_apply, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, mul_assoc,
      inv_mul_cancel₀ hne, mul_one]
    abel

/-- **`Dσ_y` for `ρ₁₀`.** Same statement for `σ = (p, θ⁻¹w, θ⁻¹xθ)`. -/
theorem dsigma10 (θc p w x : ℝ → ℍ[ℝ]) (θ' c b a : ℍ[ℝ]) (hθ : HasDerivAt θc θ' 0)
    (hp : HasDerivAt p c 0) (hw : HasDerivAt w b 0) (hx : HasDerivAt x a 0) (hne : θc 0 ≠ 0) :
    HasDerivAt (fun t => (p t, (θc t)⁻¹ * w t, (θc t)⁻¹ * x t * θc t))
      (rho10 (θc 0)⁻¹ ((c, b, a) - K10 (p 0, w 0, x 0) (θ' * (θc 0)⁻¹))) 0 := by
  have hinv := hasDerivAt_quat_inv θc θ' 0 hθ hne
  refine (hp.prodMk ((hinv.mul hw).prodMk ((hinv.mul hx).mul hθ))).congr_deriv ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [rho10, K10]
  · simp only [rho10, K10, Prod.fst_sub, Prod.snd_sub]
    simp only [mul_sub, neg_mul, mul_assoc]
    abel
  · simp only [rho10, K10, Prod.fst_sub, Prod.snd_sub, inv_inv]
    simp only [Pi.mul_apply, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, mul_assoc,
      inv_mul_cancel₀ hne, mul_one]
    abel

/-! ## `det ρ(q) = 1` for unit `q` -/

/-- Matrix of `v ↦ qv` in the basis `1, i, j, k`. -/
def lmulMatrix (q : ℍ[ℝ]) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q.re, -q.imI, -q.imJ, -q.imK;
     q.imI, q.re, -q.imK, q.imJ;
     q.imJ, q.imK, q.re, -q.imI;
     q.imK, -q.imJ, q.imI, q.re]

/-- Matrix of `v ↦ vq` in the basis `1, i, j, k`. -/
def rmulMatrix (q : ℍ[ℝ]) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q.re, -q.imI, -q.imJ, -q.imK;
     q.imI, q.re, q.imK, -q.imJ;
     q.imJ, -q.imK, q.re, q.imI;
     q.imK, q.imJ, -q.imI, q.re]

/-- Coordinates `(re, i, j, k)`. -/
noncomputable def qcoord : ℍ[ℝ] ≃ₗ[ℝ] (Fin 4 → ℝ) := QuaternionAlgebra.linearEquivTuple (-1) 0 (-1)

theorem qcoord_apply (v : ℍ[ℝ]) : qcoord v = ![v.re, v.imI, v.imJ, v.imK] := rfl

theorem det_fin_four_expand (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det = ∑ j : Fin 4, (-1) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det :=
  Matrix.det_succ_row_zero M

theorem det_lmulMatrix (q : ℍ[ℝ]) : (lmulMatrix q).det = normSq q ^ 2 := by
  rw [Matrix.det_succ_row_zero, Quaternion.normSq_def']
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, lmulMatrix, Matrix.submatrix_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Fin.succAbove, Fin.succ, Fin.castSucc]
  simp
  ring

theorem det_rmulMatrix (q : ℍ[ℝ]) : (rmulMatrix q).det = normSq q ^ 2 := by
  rw [Matrix.det_succ_row_zero, Quaternion.normSq_def']
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, rmulMatrix, Matrix.submatrix_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Fin.succAbove, Fin.succ, Fin.castSucc]
  simp
  ring

theorem lmul_conj (q : ℍ[ℝ]) :
    (qcoord.toLinearMap ∘ₗ LinearMap.mulLeft ℝ q ∘ₗ qcoord.symm.toLinearMap) =
      Matrix.toLin' (lmulMatrix q) := by
  apply LinearMap.ext; intro v
  have hv : v = qcoord (qcoord.symm v) := (qcoord.apply_symm_apply v).symm
  set u := qcoord.symm v
  rw [hv]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.mulLeft_apply, Matrix.toLin'_apply]
  funext i
  fin_cases i <;>
    simp [qcoord_apply, lmulMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem rmul_conj (q : ℍ[ℝ]) :
    (qcoord.toLinearMap ∘ₗ LinearMap.mulRight ℝ q ∘ₗ qcoord.symm.toLinearMap) =
      Matrix.toLin' (rmulMatrix q) := by
  apply LinearMap.ext; intro v
  have hv : v = qcoord (qcoord.symm v) := (qcoord.apply_symm_apply v).symm
  set u := qcoord.symm v
  rw [hv]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.mulRight_apply, Matrix.toLin'_apply]
  funext i
  fin_cases i <;>
    simp [qcoord_apply, rmulMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem det_mulLeft (q : ℍ[ℝ]) : LinearMap.det (LinearMap.mulLeft ℝ q) = normSq q ^ 2 := by
  rw [← LinearMap.det_conj (LinearMap.mulLeft ℝ q) qcoord]
  change LinearMap.det (qcoord.toLinearMap ∘ₗ LinearMap.mulLeft ℝ q ∘ₗ
    qcoord.symm.toLinearMap) = _
  rw [lmul_conj, LinearMap.det_toLin', det_lmulMatrix]

theorem det_mulRight (q : ℍ[ℝ]) : LinearMap.det (LinearMap.mulRight ℝ q) = normSq q ^ 2 := by
  rw [← LinearMap.det_conj (LinearMap.mulRight ℝ q) qcoord]
  change LinearMap.det (qcoord.toLinearMap ∘ₗ LinearMap.mulRight ℝ q ∘ₗ
    qcoord.symm.toLinearMap) = _
  rw [rmul_conj, LinearMap.det_toLin', det_rmulMatrix]

/-- `Ad_q = L_q ∘ R_{q⁻¹}` on all of `ℍ`. -/
noncomputable def adLin (q : ℍ[ℝ]) : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] :=
  LinearMap.mulLeft ℝ q ∘ₗ LinearMap.mulRight ℝ q⁻¹

theorem adLin_apply (q v : ℍ[ℝ]) : adLin q v = q * v * q⁻¹ := by
  simp [adLin, mul_assoc]

theorem det_adLin (q : ℍ[ℝ]) (hq : q ≠ 0) : LinearMap.det (adLin q) = 1 := by
  have hn : normSq q ≠ 0 := fun h => hq (normSq_eq_zero.1 h)
  rw [adLin, LinearMap.det_comp, det_mulLeft, det_mulRight, map_inv₀]
  field_simp

/-- `ρ₈(q)` as a linear map on `ℍ × ℍ`. -/
noncomputable def rho8Lin (q : ℍ[ℝ]) : (ℍ[ℝ] × ℍ[ℝ]) →ₗ[ℝ] (ℍ[ℝ] × ℍ[ℝ]) :=
  LinearMap.prodMap (LinearMap.mulLeft ℝ q) (adLin q)

theorem rho8Lin_apply (q : ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ]) : rho8Lin q y = rho8 q y := by
  simp [rho8Lin, rho8, adLin_apply]

/-- **The first factor preserves orientation (`ρ₈`).** `det ρ₈(q) = 1` for `‖q‖ = 1`. -/
theorem det_rho8 (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : LinearMap.det (rho8Lin q) = 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hn : normSq q = 1 := by rw [normSq_eq_norm_mul_self, hq, one_mul]
  rw [rho8Lin, LinearMap.det_prodMap, det_mulLeft, det_adLin q hq0, hn]
  norm_num

/-- `ρ₁₀(q)` as a linear map on `ℍ × ℍ × ℍ` (the real parts of `p` and `x` are fixed; on
`Im ℍ ⊕ ℍ ⊕ Im ℍ` the determinant is the same, block by block). -/
noncomputable def rho10Lin (q : ℍ[ℝ]) :
    (ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) →ₗ[ℝ] (ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) :=
  LinearMap.prodMap LinearMap.id (LinearMap.prodMap (LinearMap.mulLeft ℝ q) (adLin q))

theorem rho10Lin_apply (q : ℍ[ℝ]) (y : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) : rho10Lin q y = rho10 q y := by
  simp [rho10Lin, rho10, adLin_apply]

/-- **The first factor preserves orientation (`ρ₁₀`).** -/
theorem det_rho10 (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : LinearMap.det (rho10Lin q) = 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hn : normSq q = 1 := by rw [normSq_eq_norm_mul_self, hq, one_mul]
  rw [rho10Lin, LinearMap.det_prodMap, LinearMap.det_prodMap, LinearMap.det_id, det_mulLeft,
    det_adLin q hq0, hn]
  norm_num

/-! ## The orientation of `σ` -/

/-- **`σ` preserves orientation (ambient form, `ρ₈`).** Under the hypotheses of
`det_id_sub_K_beta_of_equivariance` on `Y = ℍ × ℍ`, the ambient linear map
`ρ₈(θ(y)⁻¹) ∘ (Id − Kβ)`, which is `Dσ_y` by `dsigma8`, has determinant `1`. -/
theorem det_Dsigma8_ambient (θ : ℍ[ℝ] × ℍ[ℝ] → ℍ[ℝ]) (Dθ : (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] ℍ[ℝ])
    (y : ℍ[ℝ] × ℍ[ℝ]) (hθ : HasFDerivAt θ Dθ y) (hunit : ∀ z, ‖θ z‖ = 1)
    (K : (Fin 3 → ℝ) →ₗ[ℝ] (ℍ[ℝ] × ℍ[ℝ]))
    (horbit : ∀ v, ∃ (γ : ℝ → ℍ[ℝ] × ℍ[ℝ]) (q : ℝ → ℍ[ℝ]), γ 0 = y ∧ HasDerivAt γ (K v) 0 ∧
      q 0 = 1 ∧ HasDerivAt q (imEmb v) 0 ∧ (∀ τ, q τ ≠ 0) ∧
      ∀ τ, θ (γ τ) = q τ * θ y * (q τ)⁻¹) :
    LinearMap.det (rho8Lin (θ y)⁻¹ ∘ₗ (LinearMap.id - K ∘ₗ betaCoord Dθ (θ y))) = 1 := by
  rw [LinearMap.det_comp, det_id_sub_K_beta_of_equivariance θ Dθ y hθ hunit K horbit,
    det_rho8 _ (by rw [norm_inv, hunit, inv_one]), one_mul]

/-! ### Non-vacuity -/

example : LinearMap.det (rho8Lin 1) = 1 := det_rho8 1 (by simp)
example : LinearMap.det (rho10Lin (qmk 0 1 0 0)) = 1 :=
  det_rho10 _ (norm_eq_one_of_components (by norm_num))

/-- `dsigma8` fires on constant curves with `θ ≡ i`. -/
example (x₀ w₀ : ℍ[ℝ]) :
    HasDerivAt (fun _ : ℝ => ((qmk 0 1 0 0)⁻¹ * x₀, (qmk 0 1 0 0)⁻¹ * w₀ * qmk 0 1 0 0))
      (rho8 (qmk 0 1 0 0)⁻¹ ((0, 0) - K8 (x₀, w₀) (0 * (qmk 0 1 0 0)⁻¹))) 0 :=
  dsigma8 (fun _ => qmk 0 1 0 0) (fun _ => x₀) (fun _ => w₀) 0 0 0 (hasDerivAt_const _ _)
    (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    (by intro h; have := congrArg (fun q : ℍ[ℝ] => q.imI) h; simp at this)

end ExoticSpheres8And10
