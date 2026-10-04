/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Contributions
import ExoticSpheres8And10.Curvature.Prop31.EpsilonBudget

/-! # D2(b), concluded: the remaining contributions and `eq:sharp-master` -/

namespace ExoticSpheres8And10.Prop31Algebra

open Finset

variable {n : ℕ}

/-! ### Reordering helpers -/

theorem sum_c_inner {γ α β δ ε : Type*} [Fintype γ] [Fintype α] [Fintype β] [Fintype δ]
    [Fintype ε] (f : γ → α → β → δ → ε → ℝ) :
    ∑ c, ∑ i, ∑ j, ∑ a, ∑ b, f c i j a b = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, f c i j a b := by
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem sqrt_two_mul_self : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem sqrt_two_sq_mul {x : ℝ} (hx : 0 ≤ x) : √(2 * x ^ 2) = √2 * x := by
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hx]

/-! ### `Ω(X,Y)` and the bracket term `𝒥` -/

theorem ΩXY_half (Ω : Fin n → Fin n → Fin 3 → ℝ) (hΩ : ∀ i j a, Ω j i a = -Ω i j a)
    (X Y : Fin n → ℝ) (c : Fin 3) :
    ΩXY Ω X Y c = 1 / 2 * ∑ i, ∑ j, Ω i j c * wedge X Y i j :=
  sum_anti (fun i j => Ω i j c) (fun i j => hΩ i j c) X Y

/-- `|Ω(X,Y)|² ≤ ½ (Σ Ω²) |X∧Y|²`, i.e. `|Ω(X,Y)| ≤ |Ω| |X∧Y|` in HLY's norm. -/
theorem ΩXY_sq_le (Ω : Fin n → Fin n → Fin 3 → ℝ) (hΩ : ∀ i j a, Ω j i a = -Ω i j a)
    (X Y : Fin n → ℝ) :
    ∑ c, ΩXY Ω X Y c ^ 2 ≤ 1 / 2 * OmSq Ω * gram X Y := by
  have hc : ∀ c, ΩXY Ω X Y c ^ 2 ≤ 1 / 2 * (∑ i, ∑ j, Ω i j c ^ 2) * gram X Y := by
    intro c
    rw [ΩXY_half Ω hΩ]
    have h := cs2 (fun i j => Ω i j c) (fun i j => wedge X Y i j)
    rw [sum_wedge_sq] at h
    have e : (1 / 2 * ∑ i, ∑ j, Ω i j c * wedge X Y i j) ^ 2 =
        1 / 4 * (∑ i, ∑ j, Ω i j c * wedge X Y i j) ^ 2 := by ring
    rw [e]
    linarith
  calc ∑ c, ΩXY Ω X Y c ^ 2 ≤ ∑ c, 1 / 2 * (∑ i, ∑ j, Ω i j c ^ 2) * gram X Y :=
        sum_le_sum fun c _ => hc c
    _ = 1 / 2 * OmSq Ω * gram X Y := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        congr 2
        unfold OmSq
        rw [Finset.sum_comm]
        exact sum_congr rfl fun i _ => Finset.sum_comm

/-- `|𝒥| ≤ |Ω(X,Y)| |[U,V]|`. -/
theorem Jt_abs_le (Ω : Fin n → Fin n → Fin 3 → ℝ) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    |Jt Ω X Y U V| ≤ √(∑ c, ΩXY Ω X Y c ^ 2) * √(∑ c, brk U V c ^ 2) :=
  abs_le_sqrt_mul (by positivity) (cs1 _ _)

/-- `Σ_{a,b} c_{ab}^c β_{ia}β_{jb} = α_{ij} [U,V]^c` (Plücker plus antisymmetry). -/
theorem cst_beta (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) (i j : Fin n) (c : Fin 3) :
    ∑ a, ∑ b, cst a b c * beta X Y U V i a * beta X Y U V j b = wedge X Y i j * brk U V c := by
  rw [sum_anti (fun a b => cst a b c) (fun a b => cst_anti a b c)]
  have e : ∀ a b, cst a b c * wedge (beta X Y U V i) (beta X Y U V j) a b =
      wedge X Y i j * (cst a b c * wedge U V a b) := by
    intro a b
    have h := plucker X Y U V i j a b
    have e2 : wedge (beta X Y U V i) (beta X Y U V j) a b =
        beta X Y U V i a * beta X Y U V j b - beta X Y U V i b * beta X Y U V j a := rfl
    rw [e2, h]; ring
  simp only [e, ← Finset.mul_sum]
  have hb : ∑ a, ∑ b, cst a b c * wedge U V a b = 2 * brk U V c := by
    have h := sum_anti (fun a b => cst a b c) (fun a b => cst_anti a b c) U V
    unfold brk; linarith
  rw [hb]; ring

/-- The bracket part of the `H⊗V` block is `2𝒥` (so `eq:HVHV` contributes `−𝒥/2`). -/
theorem bracket_BB (Ω : Fin n → Fin n → Fin 3 → ℝ) (hΩ : ∀ i j a, Ω j i a = -Ω i j a)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, beta X Y U V i a * beta X Y U V j b * ∑ c, cst a b c * Ω i j c =
      2 * Jt Ω X Y U V := by
  have e : ∀ i j, ∑ a, ∑ b, beta X Y U V i a * beta X Y U V j b * ∑ c, cst a b c * Ω i j c =
      ∑ c, Ω i j c * (wedge X Y i j * brk U V c) := by
    intro i j
    have h1 : ∀ a b, beta X Y U V i a * beta X Y U V j b * ∑ c, cst a b c * Ω i j c =
        ∑ c, Ω i j c * (cst a b c * beta X Y U V i a * beta X Y U V j b) := by
      intro a b; rw [Finset.mul_sum]; exact sum_congr rfl fun c _ => by ring
    simp only [h1]
    rw [sum_swap23, Finset.sum_comm]
    refine sum_congr rfl fun c _ => ?_
    simp only [← Finset.mul_sum]
    rw [cst_beta]
  simp only [e]
  rw [sum_swap23, Finset.sum_comm]
  unfold Jt
  rw [Finset.mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [ΩXY_half Ω hΩ]
  have h2 : ∑ i, ∑ j, Ω i j c * (wedge X Y i j * brk U V c) =
      (∑ i, ∑ j, Ω i j c * wedge X Y i j) * brk U V c := by
    rw [Finset.sum_mul]
    exact sum_congr rfl fun i _ => by
      rw [Finset.sum_mul]; exact sum_congr rfl fun j _ => by ring
  rw [h2]; ring

/-- The bracket part of `eq:HHVV`, contracted with `X,Y,V,U`, is `−𝒥`. -/
theorem bracket_HHVV (Ω : Fin n → Fin n → Fin 3 → ℝ) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * ∑ c, cst a b c * Ω i j c = -Jt Ω X Y U V := by
  have e : Jt Ω X Y U V = -∑ c, ΩXY Ω X Y c * brk V U c := by
    unfold Jt; rw [← Finset.sum_neg_distrib]
    exact sum_congr rfl fun c _ => by rw [brk_anti]; ring
  rw [e, neg_neg]
  unfold ΩXY brk
  have h : ∀ c, (∑ i, ∑ j, Ω i j c * X i * Y j) * (∑ a, ∑ b, cst a b c * V a * U b) =
      ∑ i, ∑ j, ∑ a, ∑ b, Ω i j c * X i * Y j * (cst a b c * V a * U b) := by
    intro c
    rw [Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  simp only [h]
  rw [sum_c_inner]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun a _ =>
    sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact sum_congr rfl fun c _ => by ring

/-! ### The quadratic part of `eq:HHVV` -/

/-- `Q_{ijab} = Σ_k (Ω_{ik}^a Ω_{jk}^b − Ω_{jk}^a Ω_{ik}^b)`. -/
def Qf (Ω : Fin n → Fin n → Fin 3 → ℝ) (i j : Fin n) (a b : Fin 3) : ℝ :=
  ∑ k, (Ω i k a * Ω j k b - Ω j k a * Ω i k b)

theorem Qf_anti_ab (Ω : Fin n → Fin n → Fin 3 → ℝ) (i j : Fin n) (a b : Fin 3) :
    Qf Ω i j b a = -Qf Ω i j a b := by
  unfold Qf; rw [← Finset.sum_neg_distrib]; exact sum_congr rfl fun k _ => by ring

theorem Qf_anti_ij (Ω : Fin n → Fin n → Fin 3 → ℝ) (i j : Fin n) (a b : Fin 3) :
    Qf Ω j i a b = -Qf Ω i j a b := by
  unfold Qf; rw [← Finset.sum_neg_distrib]; exact sum_congr rfl fun k _ => by ring

theorem Qf_sq_le (Ω : Fin n → Fin n → Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, Qf Ω i j a b ^ 2 ≤ 4 * OmSq Ω ^ 2 := by
  have h1 : ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k a * Ω j k b) ^ 2 ≤ OmSq Ω ^ 2 := by
    have := quad_sq_le Ω
    calc ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k a * Ω j k b) ^ 2
        = ∑ i, ∑ j, ∑ b, ∑ a, (∑ k, Ω i k a * Ω j k b) ^ 2 :=
          sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => Finset.sum_comm
      _ ≤ _ := this
  have h2 : ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω j k a * Ω i k b) ^ 2 ≤ OmSq Ω ^ 2 := by
    have := quad_sq_le Ω
    calc ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω j k a * Ω i k b) ^ 2
        = ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k b * Ω j k a) ^ 2 :=
          sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
            sum_congr rfl fun _ _ => by
              congr 1; exact sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ _ := this
  have pt : ∀ i j a b, Qf Ω i j a b ^ 2 ≤
      2 * (∑ k, Ω i k a * Ω j k b) ^ 2 + 2 * (∑ k, Ω j k a * Ω i k b) ^ 2 := by
    intro i j a b
    have e : Qf Ω i j a b = (∑ k, Ω i k a * Ω j k b) - ∑ k, Ω j k a * Ω i k b := by
      unfold Qf; rw [Finset.sum_sub_distrib]
    rw [e]
    nlinarith [sq_nonneg ((∑ k, Ω i k a * Ω j k b) + ∑ k, Ω j k a * Ω i k b)]
  calc ∑ i, ∑ j, ∑ a, ∑ b, Qf Ω i j a b ^ 2
      ≤ ∑ i, ∑ j, ∑ a, ∑ b, (2 * (∑ k, Ω i k a * Ω j k b) ^ 2
          + 2 * (∑ k, Ω j k a * Ω i k b) ^ 2) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun a _ => sum_le_sum fun b _ =>
          pt i j a b
    _ = 2 * ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω i k a * Ω j k b) ^ 2
          + 2 * ∑ i, ∑ j, ∑ a, ∑ b, (∑ k, Ω j k a * Ω i k b) ^ 2 := by
        simp only [sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 4 * OmSq Ω ^ 2 := by linarith

/-- The quadratic part of `eq:HHVV` contracted with `X,Y,V,U`: `|·| ≤ (Σ Ω²) |X∧Y| |U∧V|`. -/
theorem Qpart (Ω : Fin n → Fin n → Fin 3 → ℝ) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    |∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * Qf Ω i j a b| ≤
      OmSq Ω * √(gram X Y) * √(gram U V) := by
  set R : Fin n → Fin n → ℝ := fun i j => ∑ a, ∑ b, Qf Ω i j a b * wedge V U a b with hRdef
  have hR : ∀ i j, 1 / 2 * R j i = -(1 / 2 * R i j) := by
    intro i j
    have e : R j i = -R i j := by
      simp only [hRdef]
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun b _ => ?_
      rw [Qf_anti_ij]; ring
    rw [e]; ring
  have inner : ∀ i j, ∑ a, ∑ b, X i * Y j * V a * U b * Qf Ω i j a b =
      1 / 2 * R i j * X i * Y j := by
    intro i j
    have h := sum_anti (fun a b => Qf Ω i j a b) (fun a b => Qf_anti_ab Ω i j a b) V U
    have e : ∑ a, ∑ b, X i * Y j * V a * U b * Qf Ω i j a b =
        X i * Y j * ∑ a, ∑ b, Qf Ω i j a b * V a * U b := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun a _ => by
        rw [Finset.mul_sum]; exact sum_congr rfl fun b _ => by ring
    rw [e, h]; simp only [hRdef]; ring
  simp only [inner]
  rw [sum_anti (fun i j => 1 / 2 * R i j) hR X Y]
  have e2 : ∑ i, ∑ j, 1 / 2 * R i j * wedge X Y i j =
      1 / 2 * ∑ i, ∑ j, ∑ a, ∑ b, Qf Ω i j a b * (wedge X Y i j * wedge V U a b) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [hRdef, Finset.mul_sum, Finset.sum_mul]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [e2]
  have hcs := cs4 (fun i j a b => Qf Ω i j a b) (fun i j a b => wedge X Y i j * wedge V U a b)
  rw [sum4_mul_sq, sum_wedge_sq, sum_wedge_sq] at hcs
  have hgv : gram V U = gram U V := by unfold gram dot; simp only [mul_comm]
  rw [hgv] at hcs
  have hS := abs_le_sqrt_mul (by positivity) hcs
  have hQ : √(∑ i, ∑ j, ∑ a, ∑ b, Qf Ω i j a b ^ 2) ≤ 2 * OmSq Ω := by
    calc √(∑ i, ∑ j, ∑ a, ∑ b, Qf Ω i j a b ^ 2) ≤ √((2 * OmSq Ω) ^ 2) := by
          apply Real.sqrt_le_sqrt; have := Qf_sq_le Ω; nlinarith
      _ = 2 * OmSq Ω := Real.sqrt_sq (by have := OmSq_nonneg Ω; positivity)
  have hW : √(2 * gram X Y * (2 * gram U V)) = 2 * (√(gram X Y) * √(gram U V)) := by
    rw [show 2 * gram X Y * (2 * gram U V) = 2 ^ 2 * (gram X Y * gram U V) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (gram_nonneg X Y)]
  rw [hW] at hS
  have h0 : 0 ≤ √(gram X Y) * √(gram U V) := by positivity
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  calc 1 / 2 * (1 / 2 * |∑ i, ∑ j, ∑ a, ∑ b, Qf Ω i j a b * (wedge X Y i j * wedge V U a b)|)
      ≤ 1 / 2 * (1 / 2 * (2 * OmSq Ω * (2 * (√(gram X Y) * √(gram U V))))) := by
        gcongr
        exact hS.trans (mul_le_mul_of_nonneg_right hQ (by positivity))
    _ = OmSq Ω * √(gram X Y) * √(gram U V) := by ring

/-! ### `eq:HHHV`: the one-vertical block -/

theorem FHHHV_anti (Ω : Fin n → Fin n → Fin 3 → ℝ) (hΩ : ∀ i j a, Ω j i a = -Ω i j a)
    (DΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) (r : ℝ) (i j k : Fin n) (a : Fin 3) :
    FHHHV Ω DΩ ϑ r j i k a = -FHHHV Ω DΩ ϑ r i j k a := by
  unfold FHHHV; rw [hΩ i j a]; ring

theorem oneV_eq (Rm : Tv n → Tv n → Tv n → Tv n → ℝ) (Ω : Fin n → Fin n → Fin 3 → ℝ)
    (hΩ : ∀ i j a, Ω j i a = -Ω i j a) (DΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ)
    (ϑ : Fin n → ℝ) (r : ℝ)
    (hF : ∀ X Y Z U, Rm (hv X) (hv Y) (hv Z) (vv U) =
      ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * Z k * U a * FHHHV Ω DΩ ϑ r i j k a)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    2 * Rm (hv X) (hv Y) (hv Y) (vv U) - 2 * Rm (hv X) (hv Y) (hv X) (vv V) =
      -∑ i, ∑ j, ∑ k, ∑ a,
        FHHHV Ω DΩ ϑ r i j k a * (wedge X Y i j * beta X Y U V k a) := by
  rw [hF, hF]
  set G := FHHHV Ω DΩ ϑ r
  set H : Fin n → Fin n → ℝ := fun i j => ∑ k, ∑ a, G i j k a * beta X Y U V k a with hH
  have hHa : ∀ i j, H j i = -H i j := by
    intro i j
    simp only [hH]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [G]; rw [FHHHV_anti Ω hΩ]; ring
  have e1 : 2 * ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * Y k * U a * G i j k a
      - 2 * ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * X k * V a * G i j k a =
      -2 * ∑ i, ∑ j, H i j * X i * Y j := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hH, Finset.sum_mul, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => sum_congr rfl fun a _ => ?_
    unfold beta; ring
  rw [e1, sum_anti H hHa]
  have e2 : ∑ i, ∑ j, H i j * wedge X Y i j =
      ∑ i, ∑ j, ∑ k, ∑ a, G i j k a * (wedge X Y i j * beta X Y U V k a) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [hH, Finset.sum_mul]
    exact sum_congr rfl fun k _ => sum_congr rfl fun a _ => by ring
  rw [e2]; ring

/-- Norm of `α ⊗ β`: `Σ (α_{ij} β_{ka})² = 2|X∧Y|² m²`. -/
theorem ab_sq (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ a, (wedge X Y i j * beta X Y U V k a) ^ 2 =
      2 * gram X Y * ∑ k, ∑ a, beta X Y U V k a ^ 2 := by
  rw [sum4_mul_sq, sum_wedge_sq]

theorem sum_theta_Om_sq (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ a, (ϑ i * Ω j k a) ^ 2 = (∑ i, ϑ i ^ 2) * OmSq Ω := by
  unfold OmSq; rw [Finset.sum_mul]
  exact sum_congr rfl fun i _ => by
    simp only [mul_pow, ← Finset.mul_sum]

/-- **The `eq:HHHV` bound**: `|Σ ⟨R(X_i,X_j)X_k,E_a⟩ α_{ij} β_{ka}| ≤ 2r(M₁ + 2|ϑ|M₀) h m`. -/
theorem oneV_bound (Ω : Fin n → Fin n → Fin 3 → ℝ) (DΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ)
    (ϑ : Fin n → ℝ) (r t M0 M1 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hϑ : ∑ k, ϑ k ^ 2 = t ^ 2) (hOm : OmSq Ω ≤ 2 * M0 ^ 2)
    (hDOm : ∑ i, ∑ j, ∑ k, ∑ a, DΩ i j k a ^ 2 ≤ 2 * M1 ^ 2)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    |∑ i, ∑ j, ∑ k, ∑ a, FHHHV Ω DΩ ϑ r i j k a * (wedge X Y i j * beta X Y U V k a)| ≤
      2 * r * (M1 + 2 * t * M0) * √(gram X Y) * √(∑ k, ∑ a, beta X Y U V k a ^ 2) := by
  set P : Fin n → Fin n → Fin n → Fin 3 → ℝ := fun i j k a => wedge X Y i j * beta X Y U V k a
  set mS := ∑ k, ∑ a, beta X Y U V k a ^ 2
  have hP : √(∑ i, ∑ j, ∑ k, ∑ a, P i j k a ^ 2) = √2 * (√(gram X Y) * √mS) := by
    simp only [P]
    rw [ab_sq, Real.sqrt_mul (mul_nonneg (by norm_num) (gram_nonneg X Y)),
      Real.sqrt_mul (by norm_num)]
    ring
  -- the five pieces and their Cauchy–Schwarz bounds
  have csb : ∀ F : Fin n → Fin n → Fin n → Fin 3 → ℝ,
      |∑ i, ∑ j, ∑ k, ∑ a, F i j k a * P i j k a| ≤
        √(∑ i, ∑ j, ∑ k, ∑ a, F i j k a ^ 2) * (√2 * (√(gram X Y) * √mS)) := by
    intro F; rw [← hP]; exact abs_le_sqrt_mul (by positivity) (cs4 F P)
  have sA : √(∑ i, ∑ j, ∑ k, ∑ a, DΩ i j k a ^ 2) ≤ √2 * M1 := by
    rw [← sqrt_two_sq_mul hM1]; exact Real.sqrt_le_sqrt hDOm
  have sA' : √(∑ i, ∑ j, ∑ k, ∑ a, DΩ j i k a ^ 2) ≤ √2 * M1 := by
    rw [Finset.sum_comm]; exact sA
  have sB : √(∑ i, ∑ j, ∑ k, ∑ a, (ϑ i * Ω j k a) ^ 2) ≤ √2 * (t * M0) := by
    rw [sum_theta_Om_sq, hϑ, ← sqrt_two_sq_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hOm (sq_nonneg t); nlinarith
  have sB' : √(∑ i, ∑ j, ∑ k, ∑ a, (ϑ j * Ω i k a) ^ 2) ≤ √2 * (t * M0) := by
    rw [Finset.sum_comm]; exact sB
  have sC : √(∑ i, ∑ j, ∑ k, ∑ a, (ϑ k * Ω i j a) ^ 2) ≤ √2 * (t * M0) := by
    have e : ∑ i, ∑ j, ∑ k, ∑ a, (ϑ k * Ω i j a) ^ 2 = ∑ i, ∑ j, ∑ k, ∑ a, (ϑ i * Ω j k a) ^ 2 := by
      rw [sum_theta_Om_sq]; unfold OmSq; rw [Finset.mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      exact sum_congr rfl fun k _ => by ring
    rw [e]; exact sB
  have split : ∑ i, ∑ j, ∑ k, ∑ a, FHHHV Ω DΩ ϑ r i j k a * P i j k a =
      -(r / 2) * ∑ i, ∑ j, ∑ k, ∑ a, DΩ i j k a * P i j k a
      + r / 2 * ∑ i, ∑ j, ∑ k, ∑ a, DΩ j i k a * P i j k a
      - r / 2 * ∑ i, ∑ j, ∑ k, ∑ a, (ϑ i * Ω j k a) * P i j k a
      + r / 2 * ∑ i, ∑ j, ∑ k, ∑ a, (ϑ j * Ω i k a) * P i j k a
      + r * ∑ i, ∑ j, ∑ k, ∑ a, (ϑ k * Ω i j a) * P i j k a := by
    simp only [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
      sum_congr rfl fun a _ => ?_
    unfold FHHHV; ring
  change |∑ i, ∑ j, ∑ k, ∑ a, FHHHV Ω DΩ ϑ r i j k a * P i j k a| ≤ _
  rw [split]
  have hpos : 0 ≤ √2 * (√(gram X Y) * √mS) := by positivity
  have b1 := (csb fun i j k a => DΩ i j k a).trans (mul_le_mul_of_nonneg_right sA hpos)
  have b2 := (csb fun i j k a => DΩ j i k a).trans (mul_le_mul_of_nonneg_right sA' hpos)
  have b3 := (csb fun i j k a => ϑ i * Ω j k a).trans (mul_le_mul_of_nonneg_right sB hpos)
  have b4 := (csb fun i j k a => ϑ j * Ω i k a).trans (mul_le_mul_of_nonneg_right sB' hpos)
  have b5 := (csb fun i j k a => ϑ k * Ω i j a).trans (mul_le_mul_of_nonneg_right sC hpos)
  set S1 := ∑ i, ∑ j, ∑ k, ∑ a, DΩ i j k a * P i j k a
  set S2 := ∑ i, ∑ j, ∑ k, ∑ a, DΩ j i k a * P i j k a
  set S3 := ∑ i, ∑ j, ∑ k, ∑ a, (ϑ i * Ω j k a) * P i j k a
  set S4 := ∑ i, ∑ j, ∑ k, ∑ a, (ϑ j * Ω i k a) * P i j k a
  set S5 := ∑ i, ∑ j, ∑ k, ∑ a, (ϑ k * Ω i j a) * P i j k a
  set g := √(gram X Y) * √mS
  have hs2 := sqrt_two_mul_self
  have hr2 : 0 ≤ r / 2 := by positivity
  calc |-(r / 2) * S1 + r / 2 * S2 - r / 2 * S3 + r / 2 * S4 + r * S5|
      ≤ r / 2 * |S1| + r / 2 * |S2| + r / 2 * |S3| + r / 2 * |S4| + r * |S5| := by
        have := abs_add_le (-(r / 2) * S1 + r / 2 * S2 - r / 2 * S3 + r / 2 * S4) (r * S5)
        have := abs_add_le (-(r / 2) * S1 + r / 2 * S2 - r / 2 * S3) (r / 2 * S4)
        have := abs_sub (-(r / 2) * S1 + r / 2 * S2) (r / 2 * S3)
        have := abs_add_le (-(r / 2) * S1) (r / 2 * S2)
        simp only [abs_mul, abs_neg, abs_of_nonneg hr, abs_of_nonneg hr2] at *
        linarith
    _ ≤ r / 2 * (√2 * M1 * (√2 * g)) + r / 2 * (√2 * M1 * (√2 * g))
          + r / 2 * (√2 * (t * M0) * (√2 * g)) + r / 2 * (√2 * (t * M0) * (√2 * g))
          + r * (√2 * (t * M0) * (√2 * g)) := by gcongr
    _ = 2 * r * (M1 + 2 * t * M0) * √(gram X Y) * √mS := by
        simp only [g]
        have : √2 * M1 * (√2 * (√(gram X Y) * √mS)) = 2 * M1 * (√(gram X Y) * √mS) := by
          rw [show √2 * M1 * (√2 * (√(gram X Y) * √mS)) =
            (√2 * √2) * M1 * (√(gram X Y) * √mS) by ring, hs2]
        have h2 : √2 * (t * M0) * (√2 * (√(gram X Y) * √mS)) =
            2 * (t * M0) * (√(gram X Y) * √mS) := by
          rw [show √2 * (t * M0) * (√2 * (√(gram X Y) * √mS)) =
            (√2 * √2) * (t * M0) * (√(gram X Y) * √mS) by ring, hs2]
        rw [this, h2]; ring

end ExoticSpheres8And10.Prop31Algebra
