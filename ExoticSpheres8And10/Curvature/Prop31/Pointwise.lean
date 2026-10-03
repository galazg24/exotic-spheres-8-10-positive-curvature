/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Final

/-! # D2, composite: HLY Proposition 3.1 at a point, from the blocks and the ε-budget

Chains `sharp_master` (D2(b)) → `sharp_to_master` → `master_to_reserve` → the homogeneous form of
`eq:southlowerbound`, and identifies `h² + m² + k²` with the squared area `|ξ|²` of the bivector
`ξ = (X+U)∧(Y+V)` in the orthonormal frame (HLY: "`|ξ|² = h² + m² + k²`"). So the conclusion is
`𝒦(ξ) ≥ c_S |ξ|²`, i.e. `sec(ξ) ≥ c_S`, pointwise, *given* HLY's curvature blocks. -/

namespace ExoticSpheres8And10.Prop31Algebra

open Finset

variable {n : ℕ}

/-- `|ξ|²` for `ξ = (X+U)∧(Y+V)` in the orthonormal frame. -/
def totalGram (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) : ℝ :=
  (dot X X + dot U U) * (dot Y Y + dot V V) - (dot X Y + dot U V) ^ 2

/-- HLY: `|ξ|² = h² + m² + k²` with `h = |X∧Y|`, `m = |β|`, `k = |U∧V|`. -/
theorem totalGram_eq (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    totalGram X Y U V = gram X Y + ∑ i, ∑ a, beta X Y U V i a ^ 2 + gram U V := by
  have hβ : ∑ i, ∑ a, beta X Y U V i a ^ 2 =
      dot X X * dot V V + dot Y Y * dot U U - 2 * (dot X Y * dot U V) := by
    unfold dot
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
    unfold beta; ring
  rw [hβ]; unfold totalGram gram; ring

/-- The homogeneous form of `eq:southlowerbound`. -/
theorem lower_hom (κ ε Λ h m k : ℝ) :
    min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε)) * (h ^ 2 + m ^ 2 + k ^ 2) ≤
      κ / 2 * h ^ 2 + ε * Λ / 8 * m ^ 2 + 1 / (8 * ε) * k ^ 2 := by
  set c := min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε))
  have h1 : c ≤ κ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : c ≤ ε * Λ / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : c ≤ 1 / (8 * ε) := min_le_right _ _
  have := mul_le_mul_of_nonneg_right h1 (sq_nonneg h)
  have := mul_le_mul_of_nonneg_right h2 (sq_nonneg m)
  have := mul_le_mul_of_nonneg_right h3 (sq_nonneg k)
  nlinarith

/-- **HLY Proposition 3.1 at a point.** Under the block formulas of §3.1 (as in `sharp_master`)
and the hypotheses of the ε-budget (as in `master_to_reserve`, with `ν` the lower bound for
`λ_min N`), every decomposable bivector satisfies `𝒦(ξ) ≥ c_S |ξ|²`,
`c_S = min{κ/2, εΛ/8, 1/(8ε)}`. -/
theorem prop31_pointwise (Rm : Tv n → Tv n → Tv n → Tv n → ℝ)
    (h1 : ∀ a b c d e, Rm (a + b) c d e = Rm a c d e + Rm b c d e)
    (h2 : ∀ a b c d e, Rm a (b + c) d e = Rm a b d e + Rm a c d e)
    (h3 : ∀ a b c d e, Rm a b (c + d) e = Rm a b c e + Rm a b d e)
    (h4 : ∀ a b c d e, Rm a b c (d + e) = Rm a b c d + Rm a b c e)
    (ha1 : ∀ a b c d, Rm b a c d = -Rm a b c d) (ha2 : ∀ a b c d, Rm a b d c = -Rm a b c d)
    (hp : ∀ a b c d, Rm c d a b = Rm a b c d)
    (N : Fin n → Fin n → ℝ) (Ω : Fin n → Fin n → Fin 3 → ℝ)
    (DΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ) (ϑ : Fin n → ℝ)
    (KB : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (r t ν κ M0 M1 ε Λ D0 : ℝ)
    (hr : 0 < r) (ht : 0 ≤ t) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hκ : 0 < κ) (hε : 0 < ε)
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
    -- the ε-budget
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 ≤ Λ)
    (hr2 : r ^ 2 ≤ 2 * ε) (htD : t ≤ ε * D0 / 2)
    (hνΛ : ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4 ≤ ν)
    (hA2 : 2 * ε * M0 ≤ 1) (hA3 : ε * D0 * M0 ≤ 1)
    (hB2 : 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ κ)
    (hC1 : ε * D0 ^ 2 ≤ Λ / 4) (hC2 : 2 * ε ^ 3 * D0 ^ 2 ≤ 1)
    (hC3 : 32 * 4 ^ 2 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 ≤ Λ)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε)) * totalGram X Y U V ≤
      Rm (X, U) (Y, V) (Y, V) (X, U) := by
  have hs := sharp_master Rm h1 h2 h3 h4 ha1 ha2 hp N Ω DΩ ϑ KB r t ν κ M0 M1 hr ht hM0 hM1
    hΩ hϑ hOm hDOm hν hKB hHHHH hHVHV hHHVV hHVVV hHHHV hVVVV X Y U V
  set h := √(gram X Y)
  set m := √(∑ i, ∑ a, beta X Y U V i a ^ 2)
  set k := √(gram U V)
  have hm := ExoticSpheres8And10.sharp_to_master κ r M0 M1 t ν h m k hr.le hM0 hM1 ht (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hres := ExoticSpheres8And10.master_to_reserve κ ε Λ M0 M1 D0 r t ν h m k hκ hε hM0 hM1 hr ht hΛ hr2 htD
    hνΛ hA2 hA3 hB2 hC1 hC2 hC3
  have hl := lower_hom κ ε Λ h m k
  have e : h ^ 2 + m ^ 2 + k ^ 2 = totalGram X Y U V := by
    rw [totalGram_eq, Real.sq_sqrt (gram_nonneg X Y), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (gram_nonneg U V)]
  rw [← e]
  linarith

end ExoticSpheres8And10.Prop31Algebra
