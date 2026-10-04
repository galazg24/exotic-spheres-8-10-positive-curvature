/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Main

/-! # D2(b), final: `eq:HVVV`, the remaining evaluations, and `eq:sharp-master` -/

namespace ExoticSpheres8And10.Prop31Algebra

open Finset

variable {n : ℕ}

/-! ### `eq:HVVV`: the three-vertical block -/

theorem FHVVV_anti (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) (r : ℝ) (i : Fin n)
    (a b c : Fin 3) : FHVVV Ω ϑ r i a c b = -FHVVV Ω ϑ r i a b c := by
  unfold FHVVV
  rw [← mul_neg, ← sum_neg_distrib]
  congr 1
  exact sum_congr rfl fun k _ => by ring

theorem threeV_eq (Rm : Tv n → Tv n → Tv n → Tv n → ℝ) (Ω : Fin n → Fin n → Fin 3 → ℝ)
    (ϑ : Fin n → ℝ) (r : ℝ)
    (hF : ∀ X U V Z, Rm (hv X) (vv U) (vv V) (vv Z) =
      ∑ i, ∑ a, ∑ b, ∑ c, X i * U a * V b * Z c * FHVVV Ω ϑ r i a b c)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    2 * Rm (hv X) (vv V) (vv V) (vv U) - 2 * Rm (hv Y) (vv U) (vv V) (vv U) =
      ∑ i, ∑ a, ∑ b, ∑ c, FHVVV Ω ϑ r i a b c * (beta X Y U V i a * wedge V U b c) := by
  rw [hF, hF]
  set Hf := FHVVV Ω ϑ r
  have inner : ∀ i a, ∑ b, ∑ c, Hf i a b c * V b * U c =
      1 / 2 * ∑ b, ∑ c, Hf i a b c * wedge V U b c := fun i a =>
    sum_anti (fun b c => Hf i a b c) (fun b c => FHVVV_anti Ω ϑ r i a b c) V U
  have e1 : 2 * ∑ i, ∑ a, ∑ b, ∑ c, X i * V a * V b * U c * Hf i a b c
      - 2 * ∑ i, ∑ a, ∑ b, ∑ c, Y i * U a * V b * U c * Hf i a b c =
      2 * ∑ i, ∑ a, beta X Y U V i a * ∑ b, ∑ c, Hf i a b c * V b * U c := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    unfold beta; ring
  rw [e1]
  simp only [inner, Finset.mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
    sum_congr rfl fun c _ => ?_
  ring

/-- `w_i^c = Σ_k ϑ_k Ω_{ik}^c`. -/
def wv (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) (i : Fin n) (c : Fin 3) : ℝ :=
  ∑ k, ϑ k * Ω i k c

theorem FHVVV_eq (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) (r : ℝ) (i : Fin n)
    (a b c : Fin 3) :
    FHVVV Ω ϑ r i a b c = r / 2 * (kd a b * wv Ω ϑ i c - kd a c * wv Ω ϑ i b) := by
  unfold FHVVV wv
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun k _ => by ring

/-- HLY: `Σ_{a,b,c} (δ_{ab} w^c − δ_{ac} w^b)² = 4|w|²` (here `dim Im ℍ = 3` enters). -/
theorem delta_sq (w : Fin 3 → ℝ) :
    ∑ a, ∑ b, ∑ c, (kd a b * w c - kd a c * w b) ^ 2 = 4 * ∑ c, w c ^ 2 := by
  simp [kd, Fin.sum_univ_three]
  ring

theorem Hf_sq (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) (r : ℝ) :
    ∑ i, ∑ a, ∑ b, ∑ c, FHVVV Ω ϑ r i a b c ^ 2 = r ^ 2 * ∑ i, ∑ c, wv Ω ϑ i c ^ 2 := by
  rw [Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [FHVVV_eq, mul_pow]
  have hd := delta_sq (wv Ω ϑ i)
  calc ∑ a, ∑ b, ∑ c, (r / 2) ^ 2 * (kd a b * wv Ω ϑ i c - kd a c * wv Ω ϑ i b) ^ 2
      = (r / 2) ^ 2 * ∑ a, ∑ b, ∑ c, (kd a b * wv Ω ϑ i c - kd a c * wv Ω ϑ i b) ^ 2 := by
        simp only [Finset.mul_sum]
    _ = r ^ 2 * ∑ c, wv Ω ϑ i c ^ 2 := by rw [hd]; ring

theorem wv_sq_le (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) :
    ∑ i, ∑ c, wv Ω ϑ i c ^ 2 ≤ (∑ k, ϑ k ^ 2) * OmSq Ω := by
  calc ∑ i, ∑ c, wv Ω ϑ i c ^ 2 ≤ ∑ i, ∑ c, (∑ k, ϑ k ^ 2) * (∑ k, Ω i k c ^ 2) :=
        sum_le_sum fun i _ => sum_le_sum fun c _ => cs1 _ _
    _ = (∑ k, ϑ k ^ 2) * OmSq Ω := by
        unfold OmSq
        rw [Finset.mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm

/-- **The `eq:HVVV` bound**: `|Σ ⟨R(X_i,E_a)E_b,E_c⟩ β_{ia} γ_{bc}| ≤ 2r|ϑ|M₀ m k`. -/
theorem threeV_bound (Ω : Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ) (r t M0 : ℝ) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (hM0 : 0 ≤ M0) (hϑ : ∑ k, ϑ k ^ 2 = t ^ 2) (hOm : OmSq Ω ≤ 2 * M0 ^ 2)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    |∑ i, ∑ a, ∑ b, ∑ c, FHVVV Ω ϑ r i a b c * (beta X Y U V i a * wedge V U b c)| ≤
      2 * r * t * M0 * √(∑ i, ∑ a, beta X Y U V i a ^ 2) * √(gram U V) := by
  have hcs := cs4 (fun i a b c => FHVVV Ω ϑ r i a b c) (fun i a b c => beta X Y U V i a * wedge V U b c)
  rw [sum4_mul_sq, sum_wedge_sq, Hf_sq] at hcs
  have hgv : gram V U = gram U V := by unfold gram dot; simp only [mul_comm]
  rw [hgv] at hcs
  have hS := abs_le_sqrt_mul (by positivity) hcs
  have h1 : √(r ^ 2 * ∑ i, ∑ c, wv Ω ϑ i c ^ 2) ≤ √2 * (r * t * M0) := by
    rw [← sqrt_two_sq_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := wv_sq_le Ω ϑ
    rw [hϑ] at this
    have h2 : t ^ 2 * OmSq Ω ≤ t ^ 2 * (2 * M0 ^ 2) := mul_le_mul_of_nonneg_left hOm (sq_nonneg t)
    have h3 := mul_le_mul_of_nonneg_left (this.trans h2) (sq_nonneg r)
    nlinarith [h3]
  have h2 : √((∑ i, ∑ a, beta X Y U V i a ^ 2) * (2 * gram U V)) =
      √2 * (√(∑ i, ∑ a, beta X Y U V i a ^ 2) * √(gram U V)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]; ring
  rw [h2] at hS
  calc _ ≤ _ := hS
    _ ≤ √2 * (r * t * M0) * (√2 * (√(∑ i, ∑ a, beta X Y U V i a ^ 2) * √(gram U V))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 * r * t * M0 * √(∑ i, ∑ a, beta X Y U V i a ^ 2) * √(gram U V) := by
        rw [show √2 * (r * t * M0) * (√2 * (√(∑ i, ∑ a, beta X Y U V i a ^ 2) * √(gram U V)))
          = (√2 * √2) * (r * t * M0) * (√(∑ i, ∑ a, beta X Y U V i a ^ 2) * √(gram U V)) by ring,
          sqrt_two_mul_self]
        ring

/-! ### The `eq:HHVV` and `eq:HVHV` evaluations -/

theorem HHVV_eq (Rm : Tv n → Tv n → Tv n → Tv n → ℝ) (Ω : Fin n → Fin n → Fin 3 → ℝ) (r : ℝ)
    (hF : ∀ X Y U V, Rm (hv X) (hv Y) (vv U) (vv V) =
      ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * U a * V b * FHHVV Ω r i j a b)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    2 * Rm (hv X) (hv Y) (vv V) (vv U) =
      r ^ 2 / 2 * ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * Qf Ω i j a b - Jt Ω X Y U V := by
  rw [hF]
  have split : ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * FHHVV Ω r i j a b =
      r ^ 2 / 4 * ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * Qf Ω i j a b
      + 1 / 2 * ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * ∑ c, cst a b c * Ω i j c := by
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    unfold FHHVV Qf
    ring
  rw [split, bracket_HHVV]
  ring

theorem BB_split (N : Fin n → Fin n → ℝ) (Ω : Fin n → Fin n → Fin 3 → ℝ) (r : ℝ)
    (β : Fin n → Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * FHVHV N Ω r i j a b =
      ∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * (N i j * kd a b)
      + r ^ 2 / 4 * ∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * (∑ k, Ω i k b * Ω j k a)
      - 1 / 4 * ∑ i, ∑ j, ∑ a, ∑ b, β i a * β j b * ∑ c, cst a b c * Ω i j c := by
  rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  unfold FHVHV
  ring

/-! ## `eq:sharp-master` -/

theorem hv_add_vv (X : Fin n → ℝ) (U : Fin 3 → ℝ) : ((X, U) : Tv n) = hv X + vv U := by
  refine Prod.ext ?_ ?_ <;> simp [hv, vv]

/-- **D2(b): the curvature blocks of HLY §3.1 imply `eq:sharp-master`.**

Hypotheses: `Rm(w₁,w₂,w₃,w₄) = ⟨R(w₁,w₂)w₃,w₄⟩` is additive in each slot with the Riemann
symmetries; its values on horizontal/vertical vectors are given by `eq:HHHH`, `eq:HVHV`,
`eq:HHVV`, `eq:HVVV`, `eq:HHHV`, `eq:VVVV`; `Ω` is a 2-form; `|ϑ| = t`; `2|Ω|² ≤ 2M₀²` and
`2|DΩ|² ≤ 2M₁²` in the ordered-array norms (`eq:normconvention`); `λ_min N ≥ ν`;
`𝒦_B(X∧Y) ≥ κ|X∧Y|²`. Conclusion: for every decomposable bivector `(X+U)∧(Y+V)`,
`𝒦 ≥ ` the right side of `eq:sharp-master` with `h = |X∧Y|`, `m = |β|`, `k = |U∧V|`. -/
theorem sharp_master (Rm : Tv n → Tv n → Tv n → Tv n → ℝ)
    (h1 : ∀ a b c d e, Rm (a + b) c d e = Rm a c d e + Rm b c d e)
    (h2 : ∀ a b c d e, Rm a (b + c) d e = Rm a b d e + Rm a c d e)
    (h3 : ∀ a b c d e, Rm a b (c + d) e = Rm a b c e + Rm a b d e)
    (h4 : ∀ a b c d e, Rm a b c (d + e) = Rm a b c d + Rm a b c e)
    (ha1 : ∀ a b c d, Rm b a c d = -Rm a b c d) (ha2 : ∀ a b c d, Rm a b d c = -Rm a b c d)
    (hp : ∀ a b c d, Rm c d a b = Rm a b c d)
    (N : Fin n → Fin n → ℝ) (Ω : Fin n → Fin n → Fin 3 → ℝ)
    (DΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ)
    (KB : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (r t ν κ M0 M1 : ℝ)
    (hr : 0 < r) (ht : 0 ≤ t) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hΩ : ∀ i j a, Ω j i a = -Ω i j a) (hϑ : ∑ k, ϑ k ^ 2 = t ^ 2)
    (hOm : OmSq Ω ≤ 2 * M0 ^ 2)
    (hDOm : ∑ i, ∑ j, ∑ k, ∑ a, DΩ i j k a ^ 2 ≤ 2 * M1 ^ 2)
    (hν : ∀ x : Fin n → ℝ, ν * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, N i j * x i * x j)
    (hKB : ∀ X Y, κ * gram X Y ≤ KB X Y)
    (hHHHH : ∀ X Y, Rm (hv X) (hv Y) (hv Y) (hv X) = KB X Y - 3 / 4 * r ^ 2 * ∑ c, ΩXY Ω X Y c ^ 2)
    (hHVHV : ∀ X U V Y, Rm (hv X) (vv U) (vv V) (hv Y) =
      ∑ i, ∑ j, ∑ a, ∑ b, X i * U a * V b * Y j * FHVHV N Ω r i j a b)
    (hHHVV : ∀ X Y U V, Rm (hv X) (hv Y) (vv U) (vv V) =
      ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * U a * V b * FHHVV Ω r i j a b)
    (hHVVV : ∀ X U V Z, Rm (hv X) (vv U) (vv V) (vv Z) =
      ∑ i, ∑ a, ∑ b, ∑ c, X i * U a * V b * Z c * FHVVV Ω ϑ r i a b c)
    (hHHHV : ∀ X Y Z U, Rm (hv X) (hv Y) (hv Z) (vv U) =
      ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * Z k * U a * FHHHV Ω DΩ ϑ r i j k a)
    (hVVVV : ∀ U V Z T, Rm (vv U) (vv V) (vv Z) (vv T) =
      (1 / r ^ 2 - t ^ 2) * (dot V Z * dot U T - dot U Z * dot V T))
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    ExoticSpheres8And10.sharpRHS κ r M0 M1 t ν (√(gram X Y)) (√(∑ i, ∑ a, beta X Y U V i a ^ 2))
        (√(gram U V)) ≤ Rm (X, U) (Y, V) (Y, V) (X, U) := by
  rw [hv_add_vv X U, hv_add_vv Y V, expand Rm h1 h2 h3 h4 ha1 ha2 hp X Y U V,
    BB_eq Rm _ hHVHV X Y U V, BB_split, bracket_BB Ω hΩ, HHVV_eq Rm Ω r hHHVV,
    oneV_eq Rm Ω hΩ DΩ ϑ r hHHHV, threeV_eq Rm Ω ϑ r hHVVV]
  have f1 := oneV_bound Ω DΩ ϑ r t M0 M1 hr.le ht hM0 hM1 hϑ hOm hDOm X Y U V
  have f3 := threeV_bound Ω ϑ r t M0 hr.le ht hM0 hϑ hOm X Y U V
  set gH := gram X Y
  set gV := gram U V
  set mS := ∑ i, ∑ a, beta X Y U V i a ^ 2
  have hgH : 0 ≤ gH := gram_nonneg X Y
  have hgV : 0 ≤ gV := gram_nonneg U V
  have hmS : 0 ≤ mS := by positivity
  have eh : √gH ^ 2 = gH := Real.sq_sqrt hgH
  have ek : √gV ^ 2 = gV := Real.sq_sqrt hgV
  have em : √mS ^ 2 = mS := Real.sq_sqrt hmS
  have hh0 : 0 ≤ √gH := Real.sqrt_nonneg _
  have hk0 : 0 ≤ √gV := Real.sqrt_nonneg _
  have hm0 : 0 ≤ √mS := Real.sqrt_nonneg _
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  -- HHHH
  have fHH : (κ - 3 / 4 * r ^ 2 * M0 ^ 2) * √gH ^ 2 ≤ Rm (hv X) (hv Y) (hv Y) (hv X) := by
    rw [hHHHH, eh]
    have hq := ΩXY_sq_le Ω hΩ X Y
    have hq2 : 1 / 2 * OmSq Ω * gH ≤ M0 ^ 2 * gH :=
      mul_le_mul_of_nonneg_right (by linarith) hgH
    have := mul_le_mul_of_nonneg_left (hq.trans hq2) (by positivity : (0:ℝ) ≤ 3 / 4 * r ^ 2)
    have := hKB X Y
    nlinarith
  -- VVVV
  have fVV : Rm (vv U) (vv V) (vv V) (vv U) = (1 / r ^ 2 - t ^ 2) * √gV ^ 2 := by
    rw [hVVVV, ek]; simp only [gV, gram, dot]
    congr 1
    rw [Finset.sum_congr rfl fun a _ => mul_comm (V a) (U a)]
    ring
  -- H⊗V block
  have fN := Npart N ν hν (beta X Y U V)
  have fT := Tpart Ω (beta X Y U V)
  have fT' : -(1 / 2 * r ^ 2 * M0 ^ 2 * √mS ^ 2) ≤
      r ^ 2 / 4 * ∑ i, ∑ j, ∑ a, ∑ b, beta X Y U V i a * beta X Y U V j b *
        (∑ k, Ω i k b * Ω j k a) := by
    rw [em]
    have h0 := neg_abs_le (∑ i, ∑ j, ∑ a, ∑ b, beta X Y U V i a * beta X Y U V j b *
        (∑ k, Ω i k b * Ω j k a))
    have h5 : OmSq Ω * mS ≤ 2 * M0 ^ 2 * mS := mul_le_mul_of_nonneg_right hOm hmS
    have := mul_le_mul_of_nonneg_left (h0.trans' (neg_le_neg (fT.trans h5)))
      (by positivity : (0:ℝ) ≤ r ^ 2 / 4)
    nlinarith
  -- HHVV quadratic part
  have fQ := Qpart Ω X Y U V
  have fQ' : -(r ^ 2 * M0 ^ 2 * √gH * √gV) ≤
      r ^ 2 / 2 * ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * Qf Ω i j a b := by
    have h0 := neg_abs_le (∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * V a * U b * Qf Ω i j a b)
    have h5 : OmSq Ω * √gH * √gV ≤ 2 * M0 ^ 2 * √gH * √gV := by
      have := mul_le_mul_of_nonneg_right hOm hh0
      exact mul_le_mul_of_nonneg_right this hk0
    have := mul_le_mul_of_nonneg_left (h0.trans' (neg_le_neg (fQ.trans h5)))
      (by positivity : (0:ℝ) ≤ r ^ 2 / 2)
    nlinarith
  -- the bracket term 𝒥
  have fJ : |Jt Ω X Y U V| ≤ M0 * √gH * (2 * √gV) := by
    have hJ := Jt_abs_le Ω X Y U V
    have ha : √(∑ c, ΩXY Ω X Y c ^ 2) ≤ M0 * √gH := by
      rw [← Real.sqrt_sq hM0, ← Real.sqrt_mul (sq_nonneg M0)]
      apply Real.sqrt_le_sqrt
      have hq := ΩXY_sq_le Ω hΩ X Y
      have hq2 : 1 / 2 * OmSq Ω * gH ≤ M0 ^ 2 * gH :=
        mul_le_mul_of_nonneg_right (by linarith) hgH
      linarith
    have hb : √(∑ c, brk U V c ^ 2) = 2 * √gV := by
      rw [brk_sq, Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [hb] at hJ
    exact hJ.trans (mul_le_mul_of_nonneg_right ha (by positivity))
  -- one- and three-vertical blocks
  have f1' := le_abs_self (∑ i, ∑ j, ∑ k, ∑ a,
    FHHHV Ω DΩ ϑ r i j k a * (wedge X Y i j * beta X Y U V k a))
  have f3' := neg_abs_le (∑ i, ∑ a, ∑ b, ∑ c,
    FHVVV Ω ϑ r i a b c * (beta X Y U V i a * wedge V U b c))
  have fJ' := neg_abs_le (Jt Ω X Y U V)
  have fJ'' := le_abs_self (Jt Ω X Y U V)
  have fNm : ν * √mS ^ 2 ≤ ∑ i, ∑ j, ∑ a, ∑ b, beta X Y U V i a * beta X Y U V j b *
      (N i j * kd a b) := by rw [em]; exact fN
  unfold ExoticSpheres8And10.sharpRHS
  have e1 : M0 * √gH * (2 * √gV) = 2 * M0 * √gH * √gV := by ring
  rw [e1] at fJ
  linarith [fHH, fVV, fNm, fT', fQ', fJ, f1, f3, f1', f3', fJ', fJ'']

/-! ## Non-vacuity: the constant-curvature-one model

`Rm(a,b,c,d) = ⟨b,c⟩⟨a,d⟩ − ⟨a,c⟩⟨b,d⟩` on `Tv n` with the product inner product, `r = 1`,
`ϑ = 0`, `Ω = 0`, `DΩ = 0`, `N = Id`, `ν = κ = 1`, `K_B = gram`, `M₀ = M₁ = 0`. Every hypothesis
of `sharp_master`, including all six block formulas, is discharged. -/

/-- The product inner product on `Tv n`. -/
def ip (p q : Tv n) : ℝ := dot p.1 q.1 + dot p.2 q.2

theorem ip_add_left (a b c : Tv n) : ip (a + b) c = ip a c + ip b c := by
  simp only [ip, dot, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, sum_add_distrib]; ring

theorem ip_comm (a b : Tv n) : ip a b = ip b a := by
  simp only [ip, dot, mul_comm]

theorem ip_add_right (a b c : Tv n) : ip a (b + c) = ip a b + ip a c := by
  rw [ip_comm, ip_add_left, ip_comm b, ip_comm c]

/-- Constant curvature one. -/
def RmCC (a b c d : Tv n) : ℝ := ip b c * ip a d - ip a c * ip b d

theorem ip_hv_vv (X : Fin n → ℝ) (U : Fin 3 → ℝ) : ip (hv X) (vv U) = 0 := by
  simp [ip, hv, vv, dot]

theorem ip_vv_hv (X : Fin n → ℝ) (U : Fin 3 → ℝ) : ip (vv U) (hv X) = 0 := by
  rw [ip_comm, ip_hv_vv]

theorem ip_hv_hv (X Y : Fin n → ℝ) : ip (hv X : Tv n) (hv Y) = dot X Y := by
  simp [ip, hv, dot]

theorem ip_vv_vv (U V : Fin 3 → ℝ) : ip (vv U : Tv n) (vv V) = dot U V := by
  simp [ip, vv, dot]

/-- Kronecker delta on `Fin n`, the identity `N`. -/
def kdn (i j : Fin n) : ℝ := if i = j then 1 else 0

/-- The zero curvature form. -/
def Ω0 (n : ℕ) : Fin n → Fin n → Fin 3 → ℝ := fun _ _ _ => 0

theorem dot_comm {ι : Type*} [Fintype ι] (f g : ι → ℝ) : dot f g = dot g f := by
  simp only [dot, mul_comm]

theorem model_HVHV (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, X i * U a * V b * Y j * FHVHV (kdn (n := n)) (Ω0 n) 1 i j a b =
      dot U V * dot X Y := by
  have hF : ∀ i j a b, FHVHV (kdn (n := n)) (Ω0 n) 1 i j a b = kdn i j * kd a b := by
    intro i j a b; simp [FHVHV, Ω0]
  simp only [hF]
  have hb : ∀ i j a, ∑ b, X i * U a * V b * Y j * (kdn i j * kd a b) =
      X i * U a * V a * Y j * kdn i j := by
    intro i j a
    simp only [kd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [hb]
  have ha : ∀ i j, ∑ a, X i * U a * V a * Y j * kdn i j = X i * Y j * kdn i j * dot U V := by
    intro i j; unfold dot; rw [Finset.mul_sum]
    exact sum_congr rfl fun a _ => by ring
  simp only [ha]
  have hj : ∀ i, ∑ j, X i * Y j * kdn i j * dot U V = X i * Y i * dot U V := by
    intro i
    simp only [kdn, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  simp only [hj]
  unfold dot; rw [Finset.mul_sum]
  exact sum_congr rfl fun i _ => by ring

theorem model_sharp_master (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    ExoticSpheres8And10.sharpRHS 1 1 0 0 0 1 (√(gram X Y)) (√(∑ i, ∑ a, beta X Y U V i a ^ 2))
        (√(gram U V)) ≤ RmCC (X, U) (Y, V) (Y, V) (X, U) := by
  have h1 : ∀ a b c d e : Tv n, RmCC (a + b) c d e = RmCC a c d e + RmCC b c d e := by
    intro a b c d e; simp only [RmCC, ip_add_left]; ring
  have h2 : ∀ a b c d e : Tv n, RmCC a (b + c) d e = RmCC a b d e + RmCC a c d e := by
    intro a b c d e; simp only [RmCC, ip_add_left]; ring
  have h3 : ∀ a b c d e : Tv n, RmCC a b (c + d) e = RmCC a b c e + RmCC a b d e := by
    intro a b c d e; simp only [RmCC, ip_add_right]; ring
  have h4 : ∀ a b c d e : Tv n, RmCC a b c (d + e) = RmCC a b c d + RmCC a b c e := by
    intro a b c d e; simp only [RmCC, ip_add_right]; ring
  have ha1 : ∀ a b c d : Tv n, RmCC b a c d = -RmCC a b c d := by
    intro a b c d; simp only [RmCC]; ring
  have ha2 : ∀ a b c d : Tv n, RmCC a b d c = -RmCC a b c d := by
    intro a b c d; simp only [RmCC]; ring
  have hp : ∀ a b c d : Tv n, RmCC c d a b = RmCC a b c d := by
    intro a b c d; simp only [RmCC]
    rw [ip_comm d a, ip_comm c b, ip_comm c a, ip_comm d b]; ring
  have hν : ∀ x : Fin n → ℝ, 1 * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, kdn i j * x i * x j := by
    intro x
    have : ∀ i, ∑ j, kdn i j * x i * x j = x i ^ 2 := by
      intro i
      simp only [kdn, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    simp only [this, one_mul]; exact le_rfl
  have hHHHH : ∀ X Y : Fin n → ℝ, RmCC (hv X) (hv Y) (hv Y) (hv X) =
      gram X Y - 3 / 4 * 1 ^ 2 * ∑ c, ΩXY (Ω0 n) X Y c ^ 2 := by
    intro X Y
    simp only [RmCC, ip_hv_hv, gram, ΩXY, Ω0, zero_mul, Finset.sum_const_zero]
    rw [dot_comm Y X]; ring
  have hHVHV : ∀ (X : Fin n → ℝ) (U V : Fin 3 → ℝ) (Y : Fin n → ℝ),
      RmCC (hv X) (vv U) (vv V) (hv Y) =
        ∑ i, ∑ j, ∑ a, ∑ b, X i * U a * V b * Y j * FHVHV kdn (Ω0 n) 1 i j a b := by
    intro X U V Y
    rw [model_HVHV]
    simp only [RmCC, ip_vv_vv, ip_hv_hv, ip_hv_vv, ip_vv_hv]
    ring
  have hHHVV : ∀ (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ), RmCC (hv X) (hv Y) (vv U) (vv V) =
      ∑ i, ∑ j, ∑ a, ∑ b, X i * Y j * U a * V b * FHHVV (Ω0 n) 1 i j a b := by
    intro X Y U V; simp [RmCC, ip_hv_vv, FHHVV, Ω0]
  have hHVVV : ∀ (X : Fin n → ℝ) (U V Z : Fin 3 → ℝ), RmCC (hv X) (vv U) (vv V) (vv Z) =
      ∑ i, ∑ a, ∑ b, ∑ c, X i * U a * V b * Z c * FHVVV (Ω0 n) (fun _ => 0) 1 i a b c := by
    intro X U V Z; simp [RmCC, ip_hv_vv, FHVVV]
  have hHHHV : ∀ (X Y Z : Fin n → ℝ) (U : Fin 3 → ℝ), RmCC (hv X) (hv Y) (hv Z) (vv U) =
      ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * Z k * U a *
        FHHHV (Ω0 n) (fun _ _ _ _ => 0) (fun _ => 0) 1 i j k a := by
    intro X Y Z U; simp [RmCC, ip_hv_vv, FHHHV, Ω0]
  have hVVVV : ∀ U V Z T : Fin 3 → ℝ, RmCC (vv U : Tv n) (vv V) (vv Z) (vv T) =
      (1 / 1 ^ 2 - 0 ^ 2) * (dot V Z * dot U T - dot U Z * dot V T) := by
    intro U V Z T; simp [RmCC, ip_vv_vv]
  exact sharp_master RmCC h1 h2 h3 h4 ha1 ha2 hp kdn (Ω0 n) (fun _ _ _ _ => 0) (fun _ => 0)
    gram 1 0 1 1 0 0 one_pos le_rfl le_rfl le_rfl (fun _ _ _ => by simp [Ω0]) (by simp)
    (by simp [OmSq, Ω0]) (by simp) hν (fun X Y => by simp) hHHHH hHVHV hHHVV hHVVV hHHHV
    hVVVV X Y U V
