/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Blocks

/-! # D2(b), continued: the expansion and the six block contributions -/

namespace ExoticSpheres8And10.Prop31Algebra

open Finset

/-- Antisymmetrisation: `Σ S_{ij} x_i y_j = ½ Σ S_{ij} (x∧y)_{ij}` for antisymmetric `S`. -/
theorem sum_anti {ι : Type*} [Fintype ι] (S : ι → ι → ℝ) (hS : ∀ i j, S j i = -S i j)
    (x y : ι → ℝ) :
    ∑ i, ∑ j, S i j * x i * y j = 1 / 2 * ∑ i, ∑ j, S i j * wedge x y i j := by
  have h : ∑ i, ∑ j, S i j * x j * y i = -∑ i, ∑ j, S i j * x i * y j := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [hS a b]; ring
  have e1 : ∑ i, ∑ j, S i j * wedge x y i j =
      ∑ i, ∑ j, S i j * x i * y j - ∑ i, ∑ j, S i j * x j * y i := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    unfold wedge; ring
  rw [e1, h]; ring

theorem abs_le_of_sq_le {S B : ℝ} (h : S ^ 2 ≤ B ^ 2) (hB : 0 ≤ B) : |S| ≤ B :=
  (Real.abs_le_sqrt h).trans_eq (Real.sqrt_sq hB)

theorem sum_swap23 {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] (f : ι → κ → μ → ℝ) :
    ∑ i, ∑ j, ∑ a, f i j a = ∑ i, ∑ a, ∑ j, f i j a :=
  sum_congr rfl fun _ _ => Finset.sum_comm

/-! ## The setting: tangent vectors in the normalised frames -/

variable {n : ℕ}

/-- A tangent vector: horizontal coordinates in the frame `X_i`, vertical ones in `E_a`. -/
abbrev Tv (n : ℕ) := (Fin n → ℝ) × (Fin 3 → ℝ)

/-- A principal-horizontal vector. -/
def hv (X : Fin n → ℝ) : Tv n := (X, 0)
/-- A principal-vertical vector. -/
def vv (U : Fin 3 → ℝ) : Tv n := (0, U)

/-- Kronecker delta on `Fin 3`. -/
def kd (a b : Fin 3) : ℝ := if a = b then 1 else 0

/-- `eq:HVHV`: `⟨R(X_i,E_a)E_b,X_j⟩`. -/
noncomputable def FHVHV (N : Fin n → Fin n → ℝ) (Ω : Fin n → Fin n → Fin 3 → ℝ) (r : ℝ)
    (i j : Fin n) (a b : Fin 3) : ℝ :=
  N i j * kd a b + r ^ 2 / 4 * ∑ k, Ω i k b * Ω j k a - 1 / 4 * ∑ c, cst a b c * Ω i j c

/-- `eq:HHVV`: `⟨R(X_i,X_j)E_a,E_b⟩`. -/
noncomputable def FHHVV (Ω : Fin n → Fin n → Fin 3 → ℝ) (r : ℝ) (i j : Fin n) (a b : Fin 3) : ℝ :=
  r ^ 2 / 4 * ∑ k, (Ω i k a * Ω j k b - Ω j k a * Ω i k b) + 1 / 2 * ∑ c, cst a b c * Ω i j c

/-- `eq:HVVV`: `⟨R(X_i,E_a)E_b,E_c⟩`. -/
noncomputable def FHVVV (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) (r : ℝ) (i : Fin n)
    (a b c : Fin 3) : ℝ :=
  r / 2 * ∑ k, ϑ k * (kd a b * Ω i k c - kd a c * Ω i k b)

/-- `eq:HHHV`: `⟨R(X_i,X_j)X_k,E_a⟩`, where `DΩ i j k a = (D_iΩ)_{jk}^a`. -/
noncomputable def FHHHV (Ω : Fin n → Fin n → Fin 3 → ℝ) (DΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ)
    (ϑ : Fin n → ℝ) (r : ℝ) (i j k : Fin n) (a : Fin 3) : ℝ :=
  -(r / 2) * (DΩ i j k a - DΩ j i k a) - r / 2 * (ϑ i * Ω j k a - ϑ j * Ω i k a)
    + r * ϑ k * Ω i j a

/-- `Ω(X,Y)^c = Σ_{i,j} Ω_{ij}^c X_i Y_j`. -/
def ΩXY (Ω : Fin n → Fin n → Fin 3 → ℝ) (X Y : Fin n → ℝ) (c : Fin 3) : ℝ :=
  ∑ i, ∑ j, Ω i j c * X i * Y j

/-- `𝒥 = ⟨Ω(X,Y), [U,V]⟩`. -/
def Jt (Ω : Fin n → Fin n → Fin 3 → ℝ) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) : ℝ :=
  ∑ c, ΩXY Ω X Y c * brk U V c

/-- The ordered-array norm square `Σ_{i,j,a} (Ω_{ij}^a)²`; `eq:normconvention` makes it `2|Ω|²`. -/
def OmSq (Ω : Fin n → Fin n → Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, ∑ a, Ω i j a ^ 2

theorem OmSq_nonneg (Ω : Fin n → Fin n → Fin 3 → ℝ) : 0 ≤ OmSq Ω := by unfold OmSq; positivity

/-! ## The expansion of `𝒦((X+U)∧(Y+V))` into the six blocks -/

theorem expand (Rm : Tv n → Tv n → Tv n → Tv n → ℝ)
    (h1 : ∀ a b c d e, Rm (a + b) c d e = Rm a c d e + Rm b c d e)
    (h2 : ∀ a b c d e, Rm a (b + c) d e = Rm a b d e + Rm a c d e)
    (h3 : ∀ a b c d e, Rm a b (c + d) e = Rm a b c e + Rm a b d e)
    (h4 : ∀ a b c d e, Rm a b c (d + e) = Rm a b c d + Rm a b c e)
    (ha1 : ∀ a b c d, Rm b a c d = -Rm a b c d) (ha2 : ∀ a b c d, Rm a b d c = -Rm a b c d)
    (hp : ∀ a b c d, Rm c d a b = Rm a b c d) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    Rm (hv X + vv U) (hv Y + vv V) (hv Y + vv V) (hv X + vv U) =
      Rm (hv X) (hv Y) (hv Y) (hv X) + Rm (vv U) (vv V) (vv V) (vv U)
      + (Rm (hv X) (vv V) (vv V) (hv X) + Rm (hv Y) (vv U) (vv U) (hv Y)
          - Rm (hv X) (vv V) (vv U) (hv Y) - Rm (hv Y) (vv U) (vv V) (hv X))
      + 2 * Rm (hv X) (hv Y) (vv V) (vv U)
      + (2 * Rm (hv X) (hv Y) (hv Y) (vv U) - 2 * Rm (hv X) (hv Y) (hv X) (vv V))
      + (2 * Rm (hv X) (vv V) (vv V) (vv U) - 2 * Rm (hv Y) (vv U) (vv V) (vv U)) := by
  simp only [h1, h2, h3, h4]
  set x : Tv n := hv X
  set y : Tv n := hv Y
  set u : Tv n := vv U
  set v : Tv n := vv V
  have t3 := ha2 x y x v
  have t5 : Rm x v y x = -Rm x y x v := by rw [hp y x x v, ha1 x y x v]
  have t6 := ha2 x v u y
  have t9 : Rm u y y x = Rm x y y u := by rw [hp y x u y, ha1 x y u y, ha2 x y y u, neg_neg]
  have t10 : Rm u y y u = Rm y u u y := by rw [ha1 y u y u, ha2 y u u y, neg_neg]
  have t11 := ha1 y u v x
  have t12 := ha1 y u v u
  have t13 : Rm u v y x = Rm x y v u := by rw [hp y x u v, ha1 x y u v, ha2 x y v u, neg_neg]
  have t14 : Rm u v y u = -Rm y u v u := by rw [hp y u u v, ha2 y u v u]
  have t15 : Rm u v v x = Rm x v v u := by rw [hp v x u v, ha1 x v u v, ha2 x v v u, neg_neg]
  linarith

/-! ## Block 1: the `H⊗V` diagonal block (`eq:HVHV`) -/

/-- The four `HVVH` terms combine into `Σ β_{ia}β_{jb} ⟨R(X_i,E_a)E_b,X_j⟩`. -/
theorem BB_eq (Rm : Tv n → Tv n → Tv n → Tv n → ℝ) (F : Fin n → Fin n → Fin 3 → Fin 3 → ℝ)
    (hF : ∀ X U V Y, Rm (hv X) (vv U) (vv V) (hv Y) =
      ∑ i, ∑ j, ∑ a, ∑ b, X i * U a * V b * Y j * F i j a b)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    Rm (hv X) (vv V) (vv V) (hv X) + Rm (hv Y) (vv U) (vv U) (hv Y)
        - Rm (hv X) (vv V) (vv U) (hv Y) - Rm (hv Y) (vv U) (vv V) (hv X) =
      ∑ i, ∑ j, ∑ a, ∑ b, beta X Y U V i a * beta X Y U V j b * F i j a b := by
  rw [hF, hF, hF, hF]
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun a _ =>
    sum_congr rfl fun b _ => ?_
  unfold beta; ring

/-- The `N`-part of the `H⊗V` block is at least `λ_min(N) m²`. -/
theorem Npart (N : Fin n → Fin n → ℝ) (ν : ℝ)
    (hν : ∀ x : Fin n → ℝ, ν * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, N i j * x i * x j)
    (β : Fin n → Fin 3 → ℝ) :
    ν * ∑ i, ∑ a, β i a ^ 2 ≤ ∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * (N i j * kd a b) := by
  have e : ∀ i j a, ∑ b, β i a * β j b * (N i j * kd a b) = N i j * β i a * β j a := by
    intro i j a
    simp only [kd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [e]
  have hR : ∑ i, ∑ j, ∑ a, N i j * β i a * β j a = ∑ a, ∑ i, ∑ j, N i j * β i a * β j a :=
    (sum_swap23 _).trans Finset.sum_comm
  rw [hR]
  calc ν * ∑ i, ∑ a, β i a ^ 2 = ∑ a, ν * ∑ i, β i a ^ 2 := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ a, ∑ i, ∑ j, N i j * β i a * β j a := sum_le_sum fun a _ => hν (fun i => β i a)

/-- `Σ_{i,j,a,b} (Σ_k Ω_{ik}^b Ω_{jk}^a)² ≤ (Σ Ω²)²`. -/
theorem quad_sq_le (Ω : Fin n → Fin n → Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k b * Ω j k a) ^ 2 ≤ OmSq Ω ^ 2 := by
  calc ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k b * Ω j k a) ^ 2
      ≤ ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k b ^ 2) * (∑ k, Ω j k a ^ 2) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun a _ => sum_le_sum fun b _ =>
          cs1 _ _
    _ = (∑ i, ∑ b, ∑ k, Ω i k b ^ 2) * (∑ j, ∑ a, ∑ k, Ω j k a ^ 2) := by
        rw [Finset.sum_mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm, Finset.sum_mul_sum]
    _ = OmSq Ω ^ 2 := by
        unfold OmSq; rw [sq]; congr 1 <;> exact sum_congr rfl fun i _ => Finset.sum_comm

/-- The quadratic part of the `H⊗V` block: `|Σ ββ Σ_k Ω Ω| ≤ (Σ Ω²) m²`. -/
theorem Tpart (Ω : Fin n → Fin n → Fin 3 → ℝ) (β : Fin n → Fin 3 → ℝ) :
    |∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * (∑ k, Ω i k b * Ω j k a)| ≤
      OmSq Ω * ∑ i, ∑ a, β i a ^ 2 := by
  have hG : ∑ i, ∑ j, ∑ a, ∑ b, (β i a * β j b) ^ 2 = (∑ i, ∑ a, β i a ^ 2) ^ 2 := by
    rw [sq (∑ i, ∑ a, β i a ^ 2), Finset.sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  have e : ∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * (∑ k, Ω i k b * Ω j k a) =
      ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k b * Ω j k a) * (β i a * β j b) :=
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
      sum_congr rfl fun _ _ => mul_comm _ _
  have hS := cs4 (fun i j a b => ∑ k, Ω i k b * Ω j k a) (fun i j a b => β i a * β j b)
  rw [← e, hG] at hS
  have h2 : (∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * (∑ k, Ω i k b * Ω j k a)) ^ 2 ≤
      (OmSq Ω * ∑ i, ∑ a, β i a ^ 2) ^ 2 := by
    rw [mul_pow]
    exact hS.trans (mul_le_mul_of_nonneg_right (quad_sq_le Ω) (sq_nonneg _))
  have h0 : 0 ≤ OmSq Ω * ∑ i, ∑ a, β i a ^ 2 := mul_nonneg (OmSq_nonneg Ω) (by positivity)
  exact abs_le_of_sq_le h2 h0

end ExoticSpheres8And10.Prop31Algebra
