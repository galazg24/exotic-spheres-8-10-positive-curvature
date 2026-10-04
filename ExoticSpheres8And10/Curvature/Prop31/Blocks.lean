/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # D2(b). HLY Proposition 3.1: curvature blocks ⇒ `eq:sharp-master`

Source: [HLY] §3.1–3.2 (`sec:cap`): the blocks `eq:HVHV`, `eq:HHVV`, `eq:HVVV`, `eq:HHHV`
(PDF (3.8)–(3.11)), `eq:HHHH` (3.12), `eq:VVVV` (3.13), the Plücker relation `eq:Plucker` (3.14),
the bracket contraction `eq:bracketcontraction` (3.15) and `eq:sharp-master` (3.16), with the norm
convention `eq:normconvention` (1.3).

Pointwise, in the normalised frames `X_i` (horizontal, `i : Fin n`) and `E_a` (vertical, `a : Fin 3`):
a tangent vector is a pair `(X, U) : (Fin n → ℝ) × (Fin 3 → ℝ)` of coordinate vectors. The curvature
`Rm(w₁,w₂,w₃,w₄) = ⟨R(w₁,w₂)w₃,w₄⟩` is an arbitrary function, additive in each slot, with the
Riemann symmetries; the block formulas are **hypotheses** on its values on pure horizontal /
vertical vectors (equivalent, by multilinearity, to the component formulas). The sectional
numerator of `(X+U)∧(Y+V)` is `Rm(x,y,y,x)` (HLY §1.3: `𝒦(A∧B) = ⟨R(A,B)B,A⟩`).
-/

namespace ExoticSpheres8And10.Prop31Algebra

open Finset

/-! ## Algebraic preliminaries -/

/-- The Levi-Civita symbol on `Fin 3`. -/
def lc : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- The structure constants of `Im ℍ` in a `Q`-orthonormal basis: `[e_a, e_b] = c_{ab}^c e_c`,
`c_{ab}^c = 2 ε_{abc}` since `[u,v] = 2 u × v`. -/
def cst (a b c : Fin 3) : ℝ := 2 * lc a b c

/-- The bracket `[U, V]` in components: `[U,V]^c = Σ_{a,b} c_{ab}^c U_a V_b`. -/
def brk (U V : Fin 3 → ℝ) (c : Fin 3) : ℝ := ∑ a, ∑ b, cst a b c * U a * V b

theorem brk_eq_two_cross (U V : Fin 3 → ℝ) : brk U V = (2 : ℝ) • crossProduct U V := by
  funext c
  fin_cases c <;> simp [brk, cst, lc, cross_apply, Fin.sum_univ_three] <;> ring

theorem cst_anti (a b c : Fin 3) : cst b a c = -cst a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [cst, lc]

theorem brk_anti (U V : Fin 3 → ℝ) (c : Fin 3) : brk V U c = -brk U V c := by
  unfold brk
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [cst_anti]; ring

/-- `Σ f g`. -/
def dot {ι : Type*} [Fintype ι] (f g : ι → ℝ) : ℝ := ∑ i, f i * g i

/-- The Gram determinant `|f ∧ g|² = |f|²|g|² − ⟨f,g⟩²`. -/
def gram {ι : Type*} [Fintype ι] (f g : ι → ℝ) : ℝ := dot f f * dot g g - dot f g ^ 2

/-- The wedge components `(f ∧ g)_{ij} = f_i g_j − f_j g_i`. -/
def wedge {ι : Type*} (f g : ι → ℝ) (i j : ι) : ℝ := f i * g j - f j * g i

/-- Lagrange: `Σ_{i,j} (f∧g)_{ij}² = 2 |f∧g|²`, i.e. `Σ_{i<j}(f∧g)_{ij}² = |f∧g|²`. -/
theorem sum_wedge_sq {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    ∑ i, ∑ j, wedge f g i j ^ 2 = 2 * gram f g := by
  have e : 2 * gram f g = (∑ i, f i * f i) * (∑ j, g j * g j) + (∑ i, g i * g i) * (∑ j, f j * f j)
      - 2 * ((∑ i, f i * g i) * (∑ j, f j * g j)) := by
    unfold gram dot; ring
  rw [e]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
  simp only [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  unfold wedge; ring

theorem gram_nonneg {ι : Type*} [Fintype ι] (f g : ι → ℝ) : 0 ≤ gram f g := by
  have h := sum_wedge_sq f g
  have : 0 ≤ ∑ i, ∑ j, wedge f g i j ^ 2 := by positivity
  linarith

/-- `|[U,V]|² = 4 |U∧V|²`. -/
theorem brk_sq (U V : Fin 3 → ℝ) : ∑ c, brk U V c ^ 2 = 4 * gram U V := by
  simp [brk, cst, lc, gram, dot, Fin.sum_univ_three]
  ring

/-! ### Cauchy–Schwarz on nested finite sums -/

theorem cs1 {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem cs2 {ι κ : Type*} [Fintype ι] [Fintype κ] (F G : ι → κ → ℝ) :
    (∑ i, ∑ j, F i j * G i j) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * (∑ i, ∑ j, G i j ^ 2) := by
  simpa only [Fintype.sum_prod_type] using
    cs1 (fun p : ι × κ => F p.1 p.2) (fun p => G p.1 p.2)

theorem cs4 {ι κ μ ν : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    (F G : ι → κ → μ → ν → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l * G i j k l) ^ 2 ≤
      (∑ i, ∑ j, ∑ k, ∑ l, F i j k l ^ 2) * (∑ i, ∑ j, ∑ k, ∑ l, G i j k l ^ 2) := by
  simpa only [Fintype.sum_prod_type] using
    cs1 (fun p : ι × κ × μ × ν => F p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => G p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- From a squared bound to an absolute bound: `S² ≤ A·B`, `A, B ≥ 0` ⇒ `|S| ≤ √A √B`. -/
theorem abs_le_sqrt_mul {S A B : ℝ} (hA : 0 ≤ A) (h : S ^ 2 ≤ A * B) : |S| ≤ √A * √B := by
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt h

/-- A 4-index sum of a product `f(i,j) g(k,l)` of squares factors. -/
theorem sum4_mul_sq {ι κ μ ν : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    (f : ι → κ → ℝ) (g : μ → ν → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (f i j * g k l) ^ 2 = (∑ i, ∑ j, f i j ^ 2) * (∑ k, ∑ l, g k l ^ 2) := by
  simp only [mul_pow, ← mul_sum, sum_mul]

/-! ### The Plücker relation `eq:Plucker` -/

/-- `β_{ia} = X_i V_a − Y_i U_a`, the `H ⊗ V` component of `(X+U)∧(Y+V)`. -/
def beta {n : ℕ} (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) (i : Fin n) (a : Fin 3) : ℝ :=
  X i * V a - Y i * U a

/-- **`eq:Plucker`**: `β_{ia}β_{jb} − β_{ib}β_{ja} = α_{ij} γ_{ab}` for the decomposable bivector
`(X+U)∧(Y+V)`, with `α = X∧Y`, `γ = U∧V`. -/
theorem plucker {n : ℕ} (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) (i j : Fin n) (a b : Fin 3) :
    beta X Y U V i a * beta X Y U V j b - beta X Y U V i b * beta X Y U V j a =
      wedge X Y i j * wedge U V a b := by
  unfold beta wedge; ring

end ExoticSpheres8And10.Prop31Algebra
