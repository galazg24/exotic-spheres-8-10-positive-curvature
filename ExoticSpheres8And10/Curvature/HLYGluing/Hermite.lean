/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib

/-! # D1(a,b). HLY Appendix B.2: cubic interpolation and its derivatives

[HLY] `app:gluing`, `\subsection{Cubic interpolation and its derivatives}` (PDF B.2).
For `0 < τ`, with `a = h₋(−τ)`, `b = h₊(τ)`, `P = h₋'(−τ)`, `Q = h₊'(τ)`, `D = (b−a)/(2τ)`:

`H_z = (z+τ)/(2τ) b − (z−τ)/(2τ) a + (z−τ)²(z+τ)/(4τ²) (P−D) + (z+τ)²(z−τ)/(4τ²) (Q−D)`
                                                                     (`eq:glue-hermite`)
with endpoint jets `eq:glue-endpoint-jets` and derivatives `eq:glue-hermite-first`,
`eq:glue-hermite-second`. The coefficients take values in any real normed space `E` (in HLY,
`C^j` sections of `Sym²T*X`; "the same calculations commute with tangential differentiation
because all scalar coefficients depend only on `z`" — here that is simply the choice of `E`).

The estimates `eq:glue-estimate-metric/first/second` are proved from explicit Taylor
hypotheses with **explicit constants** in place of `O(·)`.
-/

namespace ExoticSpheres8And10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Hermite

variable (τ : ℝ) (a b P Q : E)

/-- `D_τ = (b − a)/(2τ)`. -/
noncomputable def hermD : E := (1 / (2 * τ)) • (b - a)

/-- The cubic Hermite interpolant `eq:glue-hermite`. -/
noncomputable def hermite (z : ℝ) : E :=
  ((z + τ) / (2 * τ)) • b - ((z - τ) / (2 * τ)) • a
    + ((z - τ) ^ 2 * (z + τ) / (4 * τ ^ 2)) • (P - hermD τ a b)
    + ((z + τ) ^ 2 * (z - τ) / (4 * τ ^ 2)) • (Q - hermD τ a b)

/-- Its first derivative `eq:glue-hermite-first`. -/
noncomputable def hermite1 (z : ℝ) : E :=
  hermD τ a b + ((3 * z ^ 2 - τ ^ 2) / (4 * τ ^ 2)) • (P + Q - (2 : ℝ) • hermD τ a b)
    + (z / (2 * τ)) • (Q - P)

/-- Its second derivative `eq:glue-hermite-second`. -/
noncomputable def hermite2 (z : ℝ) : E :=
  (3 * z / (2 * τ ^ 2)) • (P + Q - (2 : ℝ) • hermD τ a b) + (1 / (2 * τ)) • (Q - P)

variable {τ}

/-- **`eq:glue-endpoint-jets`.** `H_{−τ} = a`, `H_τ = b`, `H'_{−τ} = P`, `H'_τ = Q`. -/
theorem hermite_endpoint_jets (hτ : τ ≠ 0) :
    hermite τ a b P Q (-τ) = a ∧ hermite τ a b P Q τ = b ∧
      hermite1 τ a b P Q (-τ) = P ∧ hermite1 τ a b P Q τ = Q := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hermite, hermite1, hermD] <;>
    match_scalars <;> field_simp <;> ring

/-- **`eq:glue-hermite-first`** as a genuine derivative. -/
theorem hasDerivAt_hermite (hτ : τ ≠ 0) (z : ℝ) :
    HasDerivAt (hermite τ a b P Q) (hermite1 τ a b P Q z) z := by
  have h1 : HasDerivAt (fun z : ℝ => (z + τ) / (2 * τ)) (1 / (2 * τ)) z :=
    ((hasDerivAt_id z).add_const τ).div_const _
  have h2 : HasDerivAt (fun z : ℝ => (z - τ) / (2 * τ)) (1 / (2 * τ)) z :=
    ((hasDerivAt_id z).sub_const τ).div_const _
  have h3 : HasDerivAt (fun z : ℝ => (z - τ) ^ 2 * (z + τ) / (4 * τ ^ 2))
      ((2 * (z - τ) * (z + τ) + (z - τ) ^ 2) / (4 * τ ^ 2)) z := by
    have := ((((hasDerivAt_id' z).sub_const τ).pow 2).mul ((hasDerivAt_id' z).add_const τ)).div_const
      (4 * τ ^ 2)
    exact this.congr_deriv (by simp only [Pi.pow_apply]; norm_num)
  have h4 : HasDerivAt (fun z : ℝ => (z + τ) ^ 2 * (z - τ) / (4 * τ ^ 2))
      ((2 * (z + τ) * (z - τ) + (z + τ) ^ 2) / (4 * τ ^ 2)) z := by
    have := ((((hasDerivAt_id' z).add_const τ).pow 2).mul ((hasDerivAt_id' z).sub_const τ)).div_const
      (4 * τ ^ 2)
    exact this.congr_deriv (by simp only [Pi.pow_apply]; norm_num)
  have := (((h1.smul_const b).sub (h2.smul_const a)).add
    (h3.smul_const (P - hermD τ a b))).add (h4.smul_const (Q - hermD τ a b))
  refine this.congr_deriv ?_
  simp only [hermite1, hermD]
  match_scalars <;> field_simp <;> ring

/-- **`eq:glue-hermite-second`** as a genuine derivative. -/
theorem hasDerivAt_hermite1 (hτ : τ ≠ 0) (z : ℝ) :
    HasDerivAt (hermite1 τ a b P Q) (hermite2 τ a b P Q z) z := by
  have h1 : HasDerivAt (fun z : ℝ => (3 * z ^ 2 - τ ^ 2) / (4 * τ ^ 2))
      (3 * (2 * z) / (4 * τ ^ 2)) z := by
    have := ((((hasDerivAt_id' z).pow 2).const_mul 3).sub_const (τ ^ 2)).div_const (4 * τ ^ 2)
    exact this.congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun z : ℝ => z / (2 * τ)) (1 / (2 * τ)) z :=
    (hasDerivAt_id z).div_const _
  have := ((hasDerivAt_const z (hermD τ a b)).add
    (h1.smul_const (P + Q - (2 : ℝ) • hermD τ a b))).add (h2.smul_const (Q - P))
  refine this.congr_deriv ?_
  simp only [hermite2]
  match_scalars <;> field_simp <;> ring

end Hermite

/-! ## The estimates, with explicit constants

Taylor hypotheses (HLY: "Taylor expansion of the fixed smooth families yields, in every fixed
tangential `C^j`-norm"): with a constant `K`,
`‖a − (h − τP₀)‖ ≤ Kτ²`, `‖b − (h + τQ₀)‖ ≤ Kτ²`, `‖P − P₀‖ ≤ Kτ`, `‖Q − Q₀‖ ≤ Kτ`.
Then for `|z| ≤ τ`, with `λ = (z+τ)/(2τ)` and `Δ = P₀ − Q₀` (`eq:glue-jump`):
* `‖H_z − h‖ ≤ τ(‖P₀‖ + ‖Q₀‖ + 2‖Δ‖) + 9Kτ²`                       (`eq:glue-estimate-metric`)
* `‖H'_z − ((1−λ)P₀ + λQ₀)‖ ≤ 4Kτ`                                     (`eq:glue-estimate-first`)
* `‖H''_z + Δ/(2τ)‖ ≤ 7K`                                              (`eq:glue-estimate-second`)
-/

section Estimates

variable {τ K : ℝ} {h P₀ Q₀ a b P Q : E}

/-- `‖D_τ − (P₀+Q₀)/2‖ ≤ Kτ`. -/
theorem norm_hermD_sub_le (hτ : 0 < τ) (ha : ‖a - (h - τ • P₀)‖ ≤ K * τ ^ 2)
    (hb : ‖b - (h + τ • Q₀)‖ ≤ K * τ ^ 2) :
    ‖hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀)‖ ≤ K * τ := by
  have e : hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀) =
      (1 / (2 * τ)) • (b - (h + τ • Q₀)) - (1 / (2 * τ)) • (a - (h - τ • P₀)) := by
    simp only [hermD]
    match_scalars <;> field_simp <;> ring
  rw [e]
  calc _ ≤ ‖(1 / (2 * τ)) • (b - (h + τ • Q₀))‖ + ‖(1 / (2 * τ)) • (a - (h - τ • P₀))‖ :=
        norm_sub_le _ _
    _ ≤ (1 / (2 * τ)) * (K * τ ^ 2) + (1 / (2 * τ)) * (K * τ ^ 2) := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
        gcongr
    _ = K * τ := by field_simp; ring

/-- `‖P + Q − 2D‖ ≤ 4Kτ`. -/
theorem norm_hermS_le (hτ : 0 < τ) (ha : ‖a - (h - τ • P₀)‖ ≤ K * τ ^ 2)
    (hb : ‖b - (h + τ • Q₀)‖ ≤ K * τ ^ 2) (hP : ‖P - P₀‖ ≤ K * τ) (hQ : ‖Q - Q₀‖ ≤ K * τ) :
    ‖P + Q - (2 : ℝ) • hermD τ a b‖ ≤ 4 * K * τ := by
  have hD := norm_hermD_sub_le hτ ha hb
  have e : P + Q - (2 : ℝ) • hermD τ a b =
      (P - P₀) + (Q - Q₀) - (2 : ℝ) • (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀)) := by
    module
  rw [e]
  calc _ ≤ ‖(P - P₀) + (Q - Q₀)‖ + ‖(2 : ℝ) • (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀))‖ :=
        norm_sub_le _ _
    _ ≤ (‖P - P₀‖ + ‖Q - Q₀‖) + 2 * ‖hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀)‖ := by
        rw [norm_smul, Real.norm_two]; gcongr; exact norm_add_le _ _
    _ ≤ (K * τ + K * τ) + 2 * (K * τ) := by gcongr
    _ = 4 * K * τ := by ring

/-- **`eq:glue-estimate-second`, explicit.** `‖H''_z + Δ/(2τ)‖ ≤ 7K` for `|z| ≤ τ`. -/
theorem hermite2_estimate (hτ : 0 < τ) (ha : ‖a - (h - τ • P₀)‖ ≤ K * τ ^ 2)
    (hb : ‖b - (h + τ • Q₀)‖ ≤ K * τ ^ 2) (hP : ‖P - P₀‖ ≤ K * τ) (hQ : ‖Q - Q₀‖ ≤ K * τ)
    {z : ℝ} (hz : |z| ≤ τ) :
    ‖hermite2 τ a b P Q z + (1 / (2 * τ)) • (P₀ - Q₀)‖ ≤ 7 * K := by
  have hS := norm_hermS_le hτ ha hb hP hQ
  have e : hermite2 τ a b P Q z + (1 / (2 * τ)) • (P₀ - Q₀) =
      (3 * z / (2 * τ ^ 2)) • (P + Q - (2 : ℝ) • hermD τ a b)
        + (1 / (2 * τ)) • ((Q - Q₀) - (P - P₀)) := by
    simp only [hermite2]; module
  rw [e]
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans hP
    nlinarith
  calc _ ≤ ‖(3 * z / (2 * τ ^ 2)) • (P + Q - (2 : ℝ) • hermD τ a b)‖
          + ‖(1 / (2 * τ)) • ((Q - Q₀) - (P - P₀))‖ := norm_add_le _ _
    _ ≤ (3 * τ / (2 * τ ^ 2)) * (4 * K * τ) + (1 / (2 * τ)) * (K * τ + K * τ) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
        gcongr
        · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * τ ^ 2), abs_mul,
            abs_of_pos (by norm_num : (0:ℝ) < 3)]
          gcongr
        · exact (norm_sub_le _ _).trans (by gcongr)
    _ = 7 * K := by field_simp; ring

/-- **`eq:glue-estimate-first`, explicit.** `‖H'_z − ((1−λ)P₀ + λQ₀)‖ ≤ 4Kτ` for `|z| ≤ τ`,
`λ = (z+τ)/(2τ)`. -/
theorem hermite1_estimate (hτ : 0 < τ) (ha : ‖a - (h - τ • P₀)‖ ≤ K * τ ^ 2)
    (hb : ‖b - (h + τ • Q₀)‖ ≤ K * τ ^ 2) (hP : ‖P - P₀‖ ≤ K * τ) (hQ : ‖Q - Q₀‖ ≤ K * τ)
    {z : ℝ} (hz : |z| ≤ τ) :
    ‖hermite1 τ a b P Q z - ((1 - (z + τ) / (2 * τ)) • P₀ + ((z + τ) / (2 * τ)) • Q₀)‖
      ≤ 4 * K * τ := by
  have hS := norm_hermS_le hτ ha hb hP hQ
  have hD := norm_hermD_sub_le hτ ha hb
  have e : hermite1 τ a b P Q z - ((1 - (z + τ) / (2 * τ)) • P₀ + ((z + τ) / (2 * τ)) • Q₀) =
      (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀))
        + ((3 * z ^ 2 - τ ^ 2) / (4 * τ ^ 2)) • (P + Q - (2 : ℝ) • hermD τ a b)
        + (z / (2 * τ)) • ((Q - Q₀) - (P - P₀)) := by
    simp only [hermite1]
    match_scalars <;> field_simp <;> ring
  rw [e]
  have hz2 : z ^ 2 ≤ τ ^ 2 := sq_le_sq' (abs_le.1 hz).1 (abs_le.1 hz).2
  have hc1 : |(3 * z ^ 2 - τ ^ 2) / (4 * τ ^ 2)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * τ ^ 2), div_le_iff₀ (by positivity),
      abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  have hc2 : |z / (2 * τ)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * τ), div_le_iff₀ (by positivity)]
    linarith
  calc _ ≤ ‖hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀)‖
          + ‖((3 * z ^ 2 - τ ^ 2) / (4 * τ ^ 2)) • (P + Q - (2 : ℝ) • hermD τ a b)‖
          + ‖(z / (2 * τ)) • ((Q - Q₀) - (P - P₀))‖ := norm_add₃_le
    _ ≤ K * τ + (1 / 2) * (4 * K * τ) + (1 / 2) * (K * τ + K * τ) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr)
    _ = 4 * K * τ := by ring

/-- **`eq:glue-estimate-metric`, explicit.**
`‖H_z − h‖ ≤ τ(‖P₀‖ + ‖Q₀‖ + 2‖P₀ − Q₀‖) + 9Kτ²` for `|z| ≤ τ`. -/
theorem hermite_estimate (hτ : 0 < τ) (ha : ‖a - (h - τ • P₀)‖ ≤ K * τ ^ 2)
    (hb : ‖b - (h + τ • Q₀)‖ ≤ K * τ ^ 2) (hP : ‖P - P₀‖ ≤ K * τ) (hQ : ‖Q - Q₀‖ ≤ K * τ)
    {z : ℝ} (hz : |z| ≤ τ) :
    ‖hermite τ a b P Q z - h‖ ≤ τ * (‖P₀‖ + ‖Q₀‖ + 2 * ‖P₀ - Q₀‖) + 9 * K * τ ^ 2 := by
  have hD := norm_hermD_sub_le hτ ha hb
  set l := (z + τ) / (2 * τ) with hl
  have hl0 : 0 ≤ l := by
    rw [hl]; apply div_nonneg _ (by positivity); linarith [(abs_le.1 hz).1]
  have hl1 : l ≤ 1 := by
    rw [hl, div_le_one (by positivity)]; linarith [(abs_le.1 hz).2]
  set c1 := (z - τ) ^ 2 * (z + τ) / (4 * τ ^ 2) with hc1d
  set c2 := (z + τ) ^ 2 * (z - τ) / (4 * τ ^ 2) with hc2d
  have hzl := abs_le.1 hz
  have hc1 : |c1| ≤ 2 * τ := by
    have : |c1| = (z - τ) ^ 2 * (z + τ) / (4 * τ ^ 2) := abs_of_nonneg (by
      apply div_nonneg _ (by positivity); apply mul_nonneg (sq_nonneg _); linarith)
    rw [this, div_le_iff₀ (by positivity)]
    have e1 : (z - τ) ^ 2 ≤ (2 * τ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : z + τ ≤ 2 * τ) (sq_nonneg (z - τ))]
  have hc2 : |c2| ≤ 2 * τ := by
    have : |c2| = (z + τ) ^ 2 * (τ - z) / (4 * τ ^ 2) := by
      rw [abs_of_nonpos (by
        apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _); linarith)]
      ring
    rw [this, div_le_iff₀ (by positivity)]
    have e1 : (z + τ) ^ 2 ≤ (2 * τ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : τ - z ≤ 2 * τ) (sq_nonneg (z + τ))]
  -- decomposition
  have e : hermite τ a b P Q z - h =
      l • (τ • Q₀ + (b - (h + τ • Q₀))) + (1 - l) • (-(τ • P₀) + (a - (h - τ • P₀)))
        + c1 • ((P - P₀) + (1 / 2 : ℝ) • (P₀ - Q₀) - (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀)))
        + c2 • ((Q - Q₀) - (1 / 2 : ℝ) • (P₀ - Q₀)
            - (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀))) := by
    simp only [hermite, hl, hc1d, hc2d]
    match_scalars <;> field_simp <;> ring
  rw [e]
  have hK : 0 ≤ K := by have := (norm_nonneg _).trans hP; nlinarith
  have hPD : ‖(P - P₀) + (1 / 2 : ℝ) • (P₀ - Q₀) - (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀))‖
      ≤ K * τ + (1 / 2) * ‖P₀ - Q₀‖ + K * τ := by
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    gcongr
  have hQD : ‖(Q - Q₀) - (1 / 2 : ℝ) • (P₀ - Q₀) - (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀))‖
      ≤ K * τ + (1 / 2) * ‖P₀ - Q₀‖ + K * τ := by
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    gcongr
  have hA : ‖τ • Q₀ + (b - (h + τ • Q₀))‖ ≤ τ * ‖Q₀‖ + K * τ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hτ.le]; gcongr
  have hB : ‖-(τ • P₀) + (a - (h - τ • P₀))‖ ≤ τ * ‖P₀‖ + K * τ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hτ.le]; gcongr
  calc _ ≤ ‖l • (τ • Q₀ + (b - (h + τ • Q₀)))‖ + ‖(1 - l) • (-(τ • P₀) + (a - (h - τ • P₀)))‖
          + ‖c1 • ((P - P₀) + (1 / 2 : ℝ) • (P₀ - Q₀)
              - (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀)))‖
          + ‖c2 • ((Q - Q₀) - (1 / 2 : ℝ) • (P₀ - Q₀)
              - (hermD τ a b - (1 / 2 : ℝ) • (P₀ + Q₀)))‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add₃_le
    _ ≤ l * (τ * ‖Q₀‖ + K * τ ^ 2) + (1 - l) * (τ * ‖P₀‖ + K * τ ^ 2)
          + (2 * τ) * (K * τ + (1 / 2) * ‖P₀ - Q₀‖ + K * τ)
          + (2 * τ) * (K * τ + (1 / 2) * ‖P₀ - Q₀‖ + K * τ) := by
        rw [norm_smul, norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hl0,
          Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l), Real.norm_eq_abs,
          Real.norm_eq_abs]
        gcongr
    _ ≤ τ * (‖P₀‖ + ‖Q₀‖ + 2 * ‖P₀ - Q₀‖) + 9 * K * τ ^ 2 := by
        nlinarith [mul_nonneg hl0 (norm_nonneg Q₀), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - l)
          (norm_nonneg P₀), norm_nonneg P₀, norm_nonneg Q₀, mul_nonneg hτ.le (norm_nonneg P₀),
          mul_nonneg hτ.le (norm_nonneg Q₀), mul_nonneg hK (sq_nonneg τ)]

end Estimates

end ExoticSpheres8And10
