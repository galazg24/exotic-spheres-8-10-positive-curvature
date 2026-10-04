/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Northern.Area

/-! # A6. The criterion algebra ([GG] `eq:fullcurvature` ⇒ positivity)

[GG] §4.3, "Criterion": "Suppose `F, r > 0`, `F', r' ≥ 0`, `r' < 1`, and [`eq:northcriterion`]
`(1−F'²)/F² > 8FF'r'/r³`, `−F''/F > 4F²(r'')₊/r³`. The two graph estimates then leave strictly
positive coefficients of `|λY−μX|²` and `|X∧Y|²` in the full numerator, with a nonnegative
vertical-area term. These two base areas cannot both vanish for an independent horizontal pair,
because projection of the graph to the base tangent space is injective. Thus every
star-horizontal two-plane is positive."

The numerator `eq:fullcurvature` is
`𝒦 = −(F''/F)|λY−μX|² − (r''/r)|λV−μU|² + ((1−F'²)/F²)|X∧Y|² + ((1−r'²)/r²)|U∧V|²
     − (F'r'/(Fr))|X⊗V − Y⊗U|²`.
It is taken here as a *definition* (its geometric derivation is `eq:fullcurvature`, proved in `Curvature.WarpedProduct`).
-/

namespace ExoticSpheres8And10

open scoped RealInnerProductSpace

/-- **Scalar criterion.** The algebra of [GG]'s criterion, on five abstract area quantities
`A = |λY−μX|²`, `B = |λV−μU|²`, `W = |X∧Y|²`, `UV = |U∧V|²`, `Tn = |X⊗V−Y⊗U|²`. -/
theorem criterion_scalar (F r Fp rp Fpp rpp A B W UV Tn : ℝ)
    (hF : 0 < F) (hr : 0 < r) (hFp : 0 ≤ Fp) (hrp : 0 ≤ rp) (hrp1 : rp < 1)
    (hc1 : 8 * F * Fp * rp / r ^ 3 < (1 - Fp ^ 2) / F ^ 2)
    (hc2 : 4 * F ^ 2 * max rpp 0 / r ^ 3 < -Fpp / F)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W) (hUV : 0 ≤ UV)
    (hBA : B ≤ 4 * F ^ 2 / r ^ 2 * A) (hTW : Tn ≤ 8 * F ^ 2 / r ^ 2 * W)
    (hpos : 0 < A ∨ 0 < W) :
    0 < -(Fpp / F) * A - rpp / r * B + (1 - Fp ^ 2) / F ^ 2 * W + (1 - rp ^ 2) / r ^ 2 * UV
      - Fp * rp / (F * r) * Tn := by
  have s1 : rpp / r * B ≤ 4 * F ^ 2 * max rpp 0 / r ^ 3 * A := by
    calc rpp / r * B ≤ max rpp 0 / r * B :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hr.le) hB
      _ ≤ max rpp 0 / r * (4 * F ^ 2 / r ^ 2 * A) :=
          mul_le_mul_of_nonneg_left hBA (div_nonneg (le_max_right _ _) hr.le)
      _ = 4 * F ^ 2 * max rpp 0 / r ^ 3 * A := by
          ring
  have s2 : Fp * rp / (F * r) * Tn ≤ 8 * F * Fp * rp / r ^ 3 * W := by
    calc Fp * rp / (F * r) * Tn ≤ Fp * rp / (F * r) * (8 * F ^ 2 / r ^ 2 * W) :=
          mul_le_mul_of_nonneg_left hTW (by positivity)
      _ = 8 * F * Fp * rp / r ^ 3 * W := by
          field_simp
  have s3 : 0 ≤ (1 - rp ^ 2) / r ^ 2 * UV := by
    have : 0 ≤ 1 - rp ^ 2 := by nlinarith
    positivity
  have hα : 0 < -Fpp / F - 4 * F ^ 2 * max rpp 0 / r ^ 3 := by linarith
  have hβ : 0 < (1 - Fp ^ 2) / F ^ 2 - 8 * F * Fp * rp / r ^ 3 := by linarith
  have s4 : 0 < (-Fpp / F - 4 * F ^ 2 * max rpp 0 / r ^ 3) * A +
      ((1 - Fp ^ 2) / F ^ 2 - 8 * F * Fp * rp / r ^ 3) * W := by
    rcases hpos with h | h
    · have := mul_pos hα h
      have := mul_nonneg hβ.le hW
      linarith
    · have := mul_nonneg hα.le hA
      have := mul_pos hβ h
      linarith
  have e : -(Fpp / F) = -Fpp / F := by ring
  rw [e]
  linarith

variable {H Vv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv]

/-- The full sectional numerator `eq:fullcurvature` of the two star-horizontal vectors
`λ∂_s + X + TX` and `μ∂_s + Y + TY`, with `U = TX`, `V = TY`. -/
noncomputable def northNumerator (F r Fp rp Fpp rpp : ℝ) (T : H →L[ℝ] Vv) (X Y : H)
    (lam mu : ℝ) : ℝ :=
  -(Fpp / F) * ‖lam • Y - mu • X‖ ^ 2 - rpp / r * ‖lam • T Y - mu • T X‖ ^ 2
    + (1 - Fp ^ 2) / F ^ 2 * wedgeSq X Y + (1 - rp ^ 2) / r ^ 2 * wedgeSq (T X) (T Y)
    - Fp * rp / (F * r) * tensorSq X Y (T X) (T Y)

/-- `‖Y − cX‖²‖X‖² = |X∧Y|²` for `c = ⟨X,Y⟩/‖X‖²`. -/
theorem norm_sub_proj_sq_mul (X Y : H) (hX : X ≠ 0) :
    ‖Y - (⟪X, Y⟫ / ‖X‖ ^ 2) • X‖ ^ 2 * ‖X‖ ^ 2 = wedgeSq X Y := by
  have hx : ‖X‖ ^ 2 ≠ 0 := by positivity
  rw [norm_sub_smul_sq, wedgeSq]
  field_simp
  ring

/-- **Injectivity of the graph projection.** If the two horizontal vectors
`(λ, X, TX)` and `(μ, Y, TY)` in `ℝ × H × Vv` are linearly independent, then the two base
areas `|λY − μX|²` and `|X ∧ Y|²` are not both zero. -/
theorem base_areas_pos_of_independent (T : H →L[ℝ] Vv) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ ![((lam, X, T X) : ℝ × H × Vv), (mu, Y, T Y)]) :
    0 < ‖lam • Y - mu • X‖ ^ 2 ∨ 0 < wedgeSq X Y := by
  rw [LinearIndependent.pair_iff] at hind
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hW⟩ := hcon
  have hA0 : lam • Y - mu • X = 0 := by
    have : ‖lam • Y - mu • X‖ ^ 2 = 0 := le_antisymm hA (sq_nonneg _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  have hW0 : wedgeSq X Y = 0 := le_antisymm hW (wedgeSq_nonneg X Y)
  by_cases hX : X = 0
  · subst hX
    by_cases hl : lam = 0
    · subst hl
      have := hind 1 0 (by simp)
      exact one_ne_zero this.1
    · have hY : Y = 0 := by
        simp only [smul_zero, sub_zero] at hA0
        exact (smul_eq_zero.1 hA0).resolve_left hl
      subst hY
      have := hind mu (-lam) (by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show mu * lam + -lam * mu = 0
          ring
        · simp
        · simp)
      exact hl (neg_eq_zero.1 this.2)
  · set c := ⟪X, Y⟫ / ‖X‖ ^ 2 with hc
    have hx : 0 < ‖X‖ ^ 2 := by positivity
    have hY : Y = c • X := by
      have h := norm_sub_proj_sq_mul X Y hX
      rw [← hc, hW0] at h
      have h' : ‖Y - c • X‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h with h1 | h1
        · exact h1
        · exact absurd h1 hx.ne'
      exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h'))
    have hmu : mu = lam * c := by
      rw [hY, smul_smul, ← sub_smul] at hA0
      have := (smul_eq_zero.1 hA0).resolve_right hX
      linarith
    have := hind c (-1) (by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show c * lam + -1 * mu = 0
        rw [hmu]; ring
      · show c • X + (-1 : ℝ) • Y = 0
        rw [hY]; simp
      · show c • T X + (-1 : ℝ) • T Y = 0
        rw [hY, map_smul]; simp)
    exact absurd this.2 (by norm_num)

/-- **A6.** Every star-horizontal two-plane of the northern filling is positive: under
`F, r > 0`, `F', r' ≥ 0`, `r' < 1`, `eq:northcriterion`, and `‖T‖ ≤ 2F/r`, the numerator
`eq:fullcurvature` is positive on every linearly independent horizontal pair. -/
theorem northNumerator_pos (F r Fp rp Fpp rpp : ℝ)
    (hF : 0 < F) (hr : 0 < r) (hFp : 0 ≤ Fp) (hrp : 0 ≤ rp) (hrp1 : rp < 1)
    (hc1 : 8 * F * Fp * rp / r ^ 3 < (1 - Fp ^ 2) / F ^ 2)
    (hc2 : 4 * F ^ 2 * max rpp 0 / r ^ 3 < -Fpp / F)
    (T : H →L[ℝ] Vv) (hT : ‖T‖ ≤ 2 * F / r) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ ![((lam, X, T X) : ℝ × H × Vv), (mu, Y, T Y)]) :
    0 < northNumerator F r Fp rp Fpp rpp T X Y lam mu := by
  obtain ⟨ha, hb⟩ := area_ineqs_graph T F r hT X Y lam mu
  exact criterion_scalar F r Fp rp Fpp rpp _ _ _ _ _ hF hr hFp hrp hrp1 hc1 hc2
    (sq_nonneg _) (sq_nonneg _) (wedgeSq_nonneg _ _) (wedgeSq_nonneg _ _) ha hb
    (base_areas_pos_of_independent T X Y lam mu hind)

/-! ### Non-vacuity

The hypotheses of `northNumerator_pos` are satisfiable: on `H = Vv = ℝ` with `T = 0`,
`F = r = 1`, `F' = r' = 0`, `F'' = −1`, `r'' = 0`, the pair `(0, 1, 0), (1, 0, 0)` is
independent. (A7 exhibits the actual profile inequalities.) -/

example : 0 < northNumerator (H := ℝ) (Vv := ℝ) 1 1 0 0 (-1) 0 0 1 0 0 1 := by
  apply northNumerator_pos 1 1 0 0 (-1) 0 one_pos one_pos le_rfl le_rfl one_pos
    (by norm_num) (by norm_num) 0 (by simp) 1 0 0 1
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun p => p.2.1) h
  simp at h1 h2
  exact ⟨h2, h1⟩

end ExoticSpheres8And10
