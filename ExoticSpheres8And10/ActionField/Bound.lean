/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib

/-! # A1. Action-field bound ([D] `lem:K`)

[D] `lem:K`: "For `ρ₈` and `ρ₁₀`, `‖K_y‖_op ≤ 2` for every `y ∈ S^{n-1}`."
Proof: "For `ξ, v ∈ ℍ` with `ξ` imaginary, `ξv − vξ = [ξ, Im v] = 2 ξ × Im v`.
*Dimension 8.* At `y = (x, w)`, `K_y ξ = (ξx, 2ξ × Im w)`, so
`|K_y ξ|² = |ξ|²|x|² + 4|ξ × Im w|² ≤ |ξ|²(|x|² + 4|Im w|²) ≤ 4|ξ|²`, using `|x|²+|w|² = 1`.
Equality requires `x = 0`, `Re w = 0` and `ξ ⊥ Im w`, for example at `y = (0, i)`.
*Dimension 10.* At `y = (p, w, x)`, `K_y ξ = (0, ξw, 2ξ × x)`, so
`|K_y ξ|² = |ξ|²|w|² + 4|ξ × x|² ≤ |ξ|²(|w|² + 4|x|²) ≤ 4|ξ|²`.
Equality holds for `|x| = 1` and `ξ ⊥ x`."

We formalise the pointwise inequality `‖K_y ξ‖² ≤ 4‖ξ‖²` in both dimensions, where the
components of `K_y ξ` are written as quaternion expressions (`ξx` and `ξw − wξ`, resp. `ξw`
and `ξx − xξ`), together with the key identities and the equality cases. The operator-norm
corollary is not stated separately.
-/

namespace ExoticSpheres8And10

open Quaternion

/-- A quaternion from its four components, typed in `ℍ[ℝ]` (the anonymous constructor
elaborates in `QuaternionAlgebra ℝ (-1) 0 (-1)`, which does not carry the norm). -/
def qmk (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩

@[simp] theorem qmk_re (a b c d : ℝ) : (qmk a b c d).re = a := rfl
@[simp] theorem qmk_imI (a b c d : ℝ) : (qmk a b c d).imI = b := rfl
@[simp] theorem qmk_imJ (a b c d : ℝ) : (qmk a b c d).imJ = c := rfl
@[simp] theorem qmk_imK (a b c d : ℝ) : (qmk a b c d).imK = d := rfl

/-- The cross product of the imaginary parts, as a purely imaginary quaternion. -/
def qcross (ξ u : ℍ[ℝ]) : ℍ[ℝ] :=
  qmk 0 (ξ.imJ * u.imK - ξ.imK * u.imJ) (ξ.imK * u.imI - ξ.imI * u.imK)
    (ξ.imI * u.imJ - ξ.imJ * u.imI)

@[simp] theorem qcross_re (ξ u : ℍ[ℝ]) : (qcross ξ u).re = 0 := rfl
@[simp] theorem qcross_imI (ξ u : ℍ[ℝ]) :
    (qcross ξ u).imI = ξ.imJ * u.imK - ξ.imK * u.imJ := rfl
@[simp] theorem qcross_imJ (ξ u : ℍ[ℝ]) :
    (qcross ξ u).imJ = ξ.imK * u.imI - ξ.imI * u.imK := rfl
@[simp] theorem qcross_imK (ξ u : ℍ[ℝ]) :
    (qcross ξ u).imK = ξ.imI * u.imJ - ξ.imJ * u.imI := rfl

/-- The Euclidean inner product of the imaginary parts. -/
def qdot (ξ u : ℍ[ℝ]) : ℝ := ξ.imI * u.imI + ξ.imJ * u.imJ + ξ.imK * u.imK

theorem norm_sq_eq (q : ℍ[ℝ]) :
    ‖q‖ ^ 2 = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']

/-- `qcross` agrees with Mathlib's `crossProduct` on the imaginary parts. -/
theorem qcross_eq_crossProduct (ξ u : ℍ[ℝ]) :
    ![(qcross ξ u).imI, (qcross ξ u).imJ, (qcross ξ u).imK] =
      crossProduct ![ξ.imI, ξ.imJ, ξ.imK] ![u.imI, u.imJ, u.imK] := by
  rw [cross_apply]
  rfl

/-- `qcross` depends only on the imaginary part of its second argument. -/
theorem qcross_im (ξ u : ℍ[ℝ]) : qcross ξ u.im = qcross ξ u := rfl

/-- `qdot` is the real inner product on imaginary quaternions. -/
theorem qdot_eq_inner (ξ u : ℍ[ℝ]) (hξ : ξ.re = 0) :
    qdot ξ u = inner ℝ ξ u := by
  rw [Quaternion.inner_def]
  simp only [qdot, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star, hξ]
  ring

/-- **Key identity 1.** `ξv − vξ = 2 (ξ × Im v)`. (It holds for all `ξ`; [D] states it for
imaginary `ξ`, where `ξ × Im v = Im ξ × Im v`.) -/
theorem commutator_eq_two_qcross (ξ v : ℍ[ℝ]) : ξ * v - v * ξ = (2 : ℝ) • qcross ξ v.im := by
  rw [qcross_im]
  ext <;>
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub,
      Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul, qcross_re, qcross_imI, qcross_imJ, qcross_imK] <;>
    ring

/-- Lagrange's identity for imaginary quaternions:
`‖ξ × u‖² = ‖ξ‖²‖u‖² − ⟨ξ,u⟩²`. -/
theorem norm_qcross_sq (ξ u : ℍ[ℝ]) (hξ : ξ.re = 0) (hu : u.re = 0) :
    ‖qcross ξ u‖ ^ 2 = ‖ξ‖ ^ 2 * ‖u‖ ^ 2 - qdot ξ u ^ 2 := by
  simp only [norm_sq_eq, qcross_re, qcross_imI, qcross_imJ, qcross_imK, qdot, hξ, hu]
  ring

theorem norm_qcross_sq_le (ξ u : ℍ[ℝ]) : ‖qcross ξ u‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖u‖ ^ 2 := by
  simp only [norm_sq_eq, qcross_re, qcross_imI, qcross_imJ, qcross_imK]
  nlinarith [sq_nonneg (ξ.imI * u.imI + ξ.imJ * u.imJ + ξ.imK * u.imK),
    mul_nonneg (sq_nonneg ξ.re) (sq_nonneg u.re),
    mul_nonneg (sq_nonneg ξ.re) (add_nonneg (add_nonneg (sq_nonneg u.imI) (sq_nonneg u.imJ))
      (sq_nonneg u.imK)),
    mul_nonneg (sq_nonneg u.re) (add_nonneg (add_nonneg (sq_nonneg ξ.imI) (sq_nonneg ξ.imJ))
      (sq_nonneg ξ.imK))]

/-- **Key identity 2.** `‖ξ × u‖ ≤ ‖ξ‖‖u‖`. -/
theorem norm_qcross_le (ξ u : ℍ[ℝ]) : ‖qcross ξ u‖ ≤ ‖ξ‖ * ‖u‖ := by
  have h := norm_qcross_sq_le ξ u
  rw [← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- `‖ξv − vξ‖² ≤ 4‖ξ‖²‖Im v‖²`. -/
theorem norm_commutator_sq_le (ξ v : ℍ[ℝ]) :
    ‖ξ * v - v * ξ‖ ^ 2 ≤ 4 * ‖ξ‖ ^ 2 * ‖v.im‖ ^ 2 := by
  rw [commutator_eq_two_qcross, norm_smul, mul_pow, Real.norm_two]
  have := norm_qcross_sq_le ξ v.im
  nlinarith

theorem norm_im_sq_le (v : ℍ[ℝ]) : ‖v.im‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  simp only [norm_sq_eq, Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im,
    Quaternion.imK_im]
  nlinarith [sq_nonneg v.re]

theorem norm_mul_sq (a b : ℍ[ℝ]) : ‖a * b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_mul, mul_pow]

/-- **A1(a), dimension 8.** If `‖x‖² + ‖w‖² = 1` then `‖ξx‖² + ‖ξw − wξ‖² ≤ 4‖ξ‖²`.
(The hypothesis that `ξ` is imaginary is not needed.) -/
theorem actionField_bound_dim8 (ξ x w : ℍ[ℝ]) (h : ‖x‖ ^ 2 + ‖w‖ ^ 2 = 1) :
    ‖ξ * x‖ ^ 2 + ‖ξ * w - w * ξ‖ ^ 2 ≤ 4 * ‖ξ‖ ^ 2 := by
  have h1 := norm_commutator_sq_le ξ w
  have h2 := norm_im_sq_le w
  rw [norm_mul_sq]
  have hξ := sq_nonneg ‖ξ‖
  have hx := sq_nonneg ‖x‖
  have hh : ‖ξ‖ ^ 2 * (‖x‖ ^ 2 + ‖w‖ ^ 2) = ‖ξ‖ ^ 2 * 1 := by rw [h]
  nlinarith [mul_le_mul_of_nonneg_left h2 hξ, mul_nonneg hξ hx]

/-- The refined dimension-8 bound of [D]: `‖ξx‖² + ‖ξw − wξ‖² ≤ ‖ξ‖²(‖x‖² + 4‖Im w‖²)`. -/
theorem actionField_refined_dim8 (ξ x w : ℍ[ℝ]) :
    ‖ξ * x‖ ^ 2 + ‖ξ * w - w * ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * (‖x‖ ^ 2 + 4 * ‖w.im‖ ^ 2) := by
  have h1 := norm_commutator_sq_le ξ w
  rw [norm_mul_sq]
  nlinarith

/-- **A1(a), equality.** Equality holds when `x = 0`, `w` is a unit imaginary quaternion and
`ξ` is imaginary and orthogonal to `w`. -/
theorem actionField_eq_dim8 (ξ w : ℍ[ℝ]) (hξ : ξ.re = 0) (hw : w.re = 0) (hw1 : ‖w‖ = 1)
    (horth : qdot ξ w = 0) :
    ‖ξ * 0‖ ^ 2 + ‖ξ * w - w * ξ‖ ^ 2 = 4 * ‖ξ‖ ^ 2 := by
  have hwim : w.im = w := Quaternion.ext _ _ (by rw [Quaternion.re_im, hw]) rfl rfl rfl
  rw [mul_zero, norm_zero, commutator_eq_two_qcross, norm_smul, mul_pow, Real.norm_two, hwim,
    norm_qcross_sq ξ w hξ hw, horth, hw1]
  ring

theorem norm_eq_one_of_components {q : ℍ[ℝ]}
    (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) : ‖q‖ = 1 := by
  have h2 : ‖q‖ ^ 2 = 1 ^ 2 := by rw [norm_sq_eq, h, one_pow]
  exact (pow_left_inj₀ (norm_nonneg q) zero_le_one two_ne_zero).1 h2

/-- An explicit instance: `x = 0`, `w = i`, `ξ = j`. -/
example : ‖qmk 0 0 1 0 * 0‖ ^ 2 + ‖qmk 0 0 1 0 * qmk 0 1 0 0 - qmk 0 1 0 0 * qmk 0 0 1 0‖ ^ 2 =
    4 * ‖qmk 0 0 1 0‖ ^ 2 :=
  actionField_eq_dim8 _ _ rfl rfl (norm_eq_one_of_components (by norm_num)) (by simp [qdot])

/-- **A1(b), dimension 10.** If `‖p‖² + ‖w‖² + ‖x‖² = 1` then
`‖ξw‖² + ‖ξx − xξ‖² ≤ 4‖ξ‖²`. (The hypotheses that `ξ`, `p` and `x` are imaginary are not
needed.) -/
theorem actionField_bound_dim10 (ξ p w x : ℍ[ℝ]) (h : ‖p‖ ^ 2 + ‖w‖ ^ 2 + ‖x‖ ^ 2 = 1) :
    ‖ξ * w‖ ^ 2 + ‖ξ * x - x * ξ‖ ^ 2 ≤ 4 * ‖ξ‖ ^ 2 := by
  have h1 := norm_commutator_sq_le ξ x
  have h2 := norm_im_sq_le x
  rw [norm_mul_sq]
  have hξ := sq_nonneg ‖ξ‖
  have hh : ‖ξ‖ ^ 2 * (‖p‖ ^ 2 + ‖w‖ ^ 2 + ‖x‖ ^ 2) = ‖ξ‖ ^ 2 * 1 := by rw [h]
  nlinarith [mul_le_mul_of_nonneg_left h2 hξ, mul_nonneg hξ (sq_nonneg ‖w‖),
    mul_nonneg hξ (sq_nonneg ‖p‖)]

/-- **A1(b), equality.** Equality holds for `w = 0`, `x` a unit imaginary quaternion, and `ξ`
imaginary with `ξ ⊥ x`. -/
theorem actionField_eq_dim10 (ξ x : ℍ[ℝ]) (hξ : ξ.re = 0) (hx : x.re = 0) (hx1 : ‖x‖ = 1)
    (horth : qdot ξ x = 0) :
    ‖ξ * 0‖ ^ 2 + ‖ξ * x - x * ξ‖ ^ 2 = 4 * ‖ξ‖ ^ 2 :=
  actionField_eq_dim8 ξ x hξ hx hx1 horth

end ExoticSpheres8And10
