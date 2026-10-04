/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # D1(c–f). HLY Appendix B.4–B.5: the curvature bounds on the interpolation strip

[HLY] `app:gluing`, `\subsection{Tangential planes and the determinant identity}` (PDF B.4) and
`\subsection{Radial and arbitrary two-planes}` (PDF B.5, p. 29).

* (c) `eq:glue-determinant`: `det((1−λ)P + λQ) = (1−λ)det P + λ det Q − λ(1−λ)det(P−Q)`, and
  positivity of `det Δ` for positive definite `Δ`.
* (d) the tangential bound `eq:glue-tangent-bound` and reserve `eq:glue-tangent-reserve`, from the
  Gauss form `eq:glue-tangent-sectional` (a hypothesis), with **explicit** errors.
* (e) the radial reserve `eq:glue-radial-reserve` from `eq:glue-radial-sectional` (a hypothesis).
* (f) the all-planes bound `eq:glue-all-planes`, for an abstract algebraic curvature tensor on a
  real inner product space `W` with unit normal `e`.

**A simplification of HLY's (f).** HLY choose a basis `w, cos θ u + sin θ ∂_z` with `u, w`
tangential orthonormal, which needs dimension `≥ 3`, and treat dimension two separately. Here the
tangential vector `⟪y,e⟫x − ⟪x,e⟫y` of the plane is used directly; together with a shear this
proves the bound for **every** pair `x, y` (dependent pairs included) in **every** dimension, with
no case split and no finite-dimensionality.
-/

namespace ExoticSpheres8And10

open scoped RealInnerProductSpace

/-! ## (c) The determinant identity -/

/-- **`eq:glue-determinant`** (for all `2×2` matrices, symmetric or not). -/
theorem det_convex_comb (P Q : Matrix (Fin 2) (Fin 2) ℝ) (l : ℝ) :
    ((1 - l) • P + l • Q).det = (1 - l) * P.det + l * Q.det - l * (1 - l) * (P - Q).det := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  ring

/-- A positive definite symmetric `2×2` matrix has positive determinant (HLY: "`Δ` is positive
definite by `eq:glue-jump`, so `det_Π Δ > 0`"). -/
theorem det_pos_of_posDef2 (a b c : ℝ)
    (hpd : ∀ x y : ℝ, (x, y) ≠ (0, 0) → 0 < a * x ^ 2 + 2 * b * x * y + c * y ^ 2) :
    0 < a * c - b ^ 2 := by
  have ha : 0 < a := by simpa using hpd 1 0 (by simp)
  have h := hpd b (-a) (by simp [ha.ne'])
  have : a * b ^ 2 + 2 * b * b * (-a) + c * (-a) ^ 2 = a * (a * c - b ^ 2) := by ring
  rw [this] at h
  exact pos_of_mul_pos_right h ha.le

/-- The southern normal's sign does not change the determinant (HLY, after
`eq:glue-tangent-bound`). -/
theorem det_neg_fin_two (Q : Matrix (Fin 2) (Fin 2) ℝ) : (-Q).det = Q.det := by
  simp only [Matrix.det_fin_two, Matrix.neg_apply]; ring

/-! ## (d) The tangential bound, with explicit errors

Plane-level data in an `h`-orthonormal basis `u, v` of the plane `Π`: `X` is the matrix of
`H'_z|_Π`, `L = (1−λ)P₀ + λQ₀` its interpolation, `dH = det_Π H_z`, `KH = sec_{H_z}(Π)`,
`Kh = sec_h(Π)`. The Gauss form `eq:glue-tangent-sectional` is the hypothesis
`secG = KH − det X/(4 dH)`. -/

theorem abs_det_sub_le (X L : Matrix (Fin 2) (Fin 2) ℝ) (ε B : ℝ) (hε : 0 ≤ ε)
    (hXL : ∀ i j, |X i j - L i j| ≤ ε) (hL : ∀ i j, |L i j| ≤ B) :
    |X.det - L.det| ≤ 2 * ε * (2 * B + ε) := by
  have hX : ∀ i j, |X i j| ≤ B + ε := fun i j => by
    have := abs_sub_abs_le_abs_sub (X i j) (L i j)
    linarith [hXL i j, hL i j]
  have e : X.det - L.det = (X 0 0 - L 0 0) * X 1 1 + L 0 0 * (X 1 1 - L 1 1)
      - ((X 0 1 - L 0 1) * X 1 0 + L 0 1 * (X 1 0 - L 1 0)) := by
    simp only [Matrix.det_fin_two]; ring
  rw [e]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hL 0 0)
  have t : ∀ p q r s : ℝ, |p| ≤ ε → |q| ≤ B + ε → |r| ≤ B → |s| ≤ ε →
      |p * q + r * s| ≤ ε * (B + ε) + B * ε := fun p q r s hp hq hr hs => by
    calc |p * q + r * s| ≤ |p| * |q| + |r| * |s| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ε * (B + ε) + B * ε :=
          add_le_add (mul_le_mul hp hq (abs_nonneg _) hε) (mul_le_mul hr hs (abs_nonneg _) hB)
  calc _ ≤ |(X 0 0 - L 0 0) * X 1 1 + L 0 0 * (X 1 1 - L 1 1)|
          + |(X 0 1 - L 0 1) * X 1 0 + L 0 1 * (X 1 0 - L 1 0)| := abs_sub _ _
    _ ≤ (ε * (B + ε) + B * ε) + (ε * (B + ε) + B * ε) := by
        gcongr
        · exact t _ _ _ _ (hXL 0 0) (hX 1 1) (hL 0 0) (hXL 1 1)
        · exact t _ _ _ _ (hXL 0 1) (hX 1 0) (hL 0 1) (hXL 1 0)
    _ = 2 * ε * (2 * B + ε) := by ring

theorem abs_det_le (L : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (hL : ∀ i j, |L i j| ≤ B) :
    |L.det| ≤ 2 * B ^ 2 := by
  rw [Matrix.det_fin_two]
  calc _ ≤ |L 0 0 * L 1 1| + |L 0 1 * L 1 0| := abs_sub _ _
    _ ≤ B * B + B * B := by
        rw [abs_mul, abs_mul]
        gcongr <;> first | exact hL _ _ | exact (abs_nonneg _).trans (hL 0 0)
    _ = 2 * B ^ 2 := by ring

/-- **`eq:glue-tangent-bound`, explicit.** With `|X − L| ≤ ε₁` entrywise, `|L| ≤ B`,
`|KH − Kh| ≤ ε₂`, `|dH − 1| ≤ ε₃ < 1` and `L = (1−λ)P₀ + λQ₀`:
`secG ≥ (1−λ)(Kh − det P₀/4) + λ(Kh − det Q₀/4) + λ(1−λ)/4 · det(P₀ − Q₀) − err`,
`err = ε₂ + (2B²ε₃ + 2ε₁(2B+ε₁)) / (4(1−ε₃))`. -/
theorem tangent_bound (secG KH Kh dH ε₁ ε₂ ε₃ B l : ℝ) (X P₀ Q₀ : Matrix (Fin 2) (Fin 2) ℝ)
    (hgauss : secG = KH - X.det / (4 * dH))
    (hε₁ : 0 ≤ ε₁) (hε₃ : ε₃ < 1)
    (hXL : ∀ i j, |X i j - ((1 - l) • P₀ + l • Q₀) i j| ≤ ε₁)
    (hL : ∀ i j, |((1 - l) • P₀ + l • Q₀) i j| ≤ B)
    (hK : |KH - Kh| ≤ ε₂) (hd : |dH - 1| ≤ ε₃) :
    (1 - l) * (Kh - P₀.det / 4) + l * (Kh - Q₀.det / 4) + l * (1 - l) / 4 * (P₀ - Q₀).det
      - (ε₂ + (2 * B ^ 2 * ε₃ + 2 * ε₁ * (2 * B + ε₁)) / (4 * (1 - ε₃))) ≤ secG := by
  set L := (1 - l) • P₀ + l • Q₀ with hLdef
  have hdL := det_convex_comb P₀ Q₀ l
  rw [← hLdef] at hdL
  have hdpos : 1 - ε₃ ≤ dH := by linarith [(abs_le.1 hd).1]
  have hdH : 0 < dH := by linarith
  have h1 := abs_det_sub_le X L ε₁ B hε₁ hXL hL
  have h2 := abs_det_le L B hL
  -- secG − (Kh − det L/4) = (KH − Kh) + ((dH − 1) det L + (det L − det X))/(4 dH)
  have key : secG - (Kh - L.det / 4) =
      (KH - Kh) + ((dH - 1) * L.det + (L.det - X.det)) / (4 * dH) := by
    rw [hgauss]; field_simp; ring
  have hB : 0 ≤ B := (abs_nonneg _).trans (hL 0 0)
  have herr : |((dH - 1) * L.det + (L.det - X.det)) / (4 * dH)|
      ≤ (2 * B ^ 2 * ε₃ + 2 * ε₁ * (2 * B + ε₁)) / (4 * (1 - ε₃)) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * dH)]
    have hnum : |(dH - 1) * L.det + (L.det - X.det)| ≤ 2 * B ^ 2 * ε₃ + 2 * ε₁ * (2 * B + ε₁) := by
      calc _ ≤ |(dH - 1) * L.det| + |L.det - X.det| := abs_add_le _ _
        _ ≤ ε₃ * (2 * B ^ 2) + 2 * ε₁ * (2 * B + ε₁) := by
            rw [abs_mul, abs_sub_comm L.det]
            exact add_le_add (mul_le_mul hd h2 (abs_nonneg _) ((abs_nonneg _).trans hd)) h1
        _ = _ := by ring
    calc _ ≤ (2 * B ^ 2 * ε₃ + 2 * ε₁ * (2 * B + ε₁)) / (4 * dH) := by gcongr
      _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by
            have : 0 ≤ ε₃ := (abs_nonneg _).trans hd
            positivity) (by linarith) (by linarith)
  have hlow := (abs_le.1 hK).1
  have hlow2 := (abs_le.1 herr).1
  have : Kh - L.det / 4 = (1 - l) * (Kh - P₀.det / 4) + l * (Kh - Q₀.det / 4)
      + l * (1 - l) / 4 * (P₀ - Q₀).det := by rw [hdL]; ring
  linarith

/-- **`eq:glue-tangent-reserve`.** If both boundary curvatures are `≥ κ∂`, `det(P₀−Q₀) ≥ 0`,
`0 ≤ λ ≤ 1` and the error is at most `κ∂/2`, then `secG ≥ κ∂/2 = a₀`. -/
theorem tangent_reserve (secG KN KS dD err κ l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hbound : (1 - l) * KN + l * KS + l * (1 - l) / 4 * dD - err ≤ secG)
    (hN : κ ≤ KN) (hS : κ ≤ KS) (hD : 0 ≤ dD) (herr : err ≤ κ / 2) : κ / 2 ≤ secG := by
  have : 0 ≤ l * (1 - l) / 4 * dD := by
    have : 0 ≤ 1 - l := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hN (by linarith : (0:ℝ) ≤ 1 - l),
    mul_le_mul_of_nonneg_left hS hl0]

/-! ## (e) The radial reserve

For an `H_z`-unit tangential `u` (`Huu = 1`), with `½h ≤ H_z ≤ 2h` (so `½ ≤ huu ≤ 2`),
`Δ(u,u) ≥ 2b_* h(u,u)` and the second-derivative estimate
`|H''(u,u) + Δ(u,u)/(2τ)| ≤ C h(u,u)` (from `hermite2_estimate` through `|S(u,u)| ≤ ‖S‖ h(u,u)`),
the radial curvature `eq:glue-radial-sectional`
`sec(u,∂_z) = (−½H''(u,u) + ¼ q)/H(u,u)`, with `q = H'(u,·)H⁻¹H'(·,u) ≥ 0`, satisfies
`sec(u,∂_z) ≥ b_*/(4τ) − C` (`eq:glue-radial-reserve`, `β₀ = b_*/4`, `C₀ = C`). -/

theorem radial_reserve (secR H2uu Duu q huu bstar C τ : ℝ) (hτ : 0 < τ) (hb : 0 ≤ bstar)
    (hC : 0 ≤ C) (hsec : secR = (-(1 / 2) * H2uu + (1 / 4) * q) / 1) (hq : 0 ≤ q)
    (hhuu1 : 1 / 2 ≤ huu) (hhuu2 : huu ≤ 2) (hD : 2 * bstar * huu ≤ Duu)
    (hH2 : |H2uu + Duu / (2 * τ)| ≤ C * huu) :
    bstar / 4 / τ - C ≤ secR := by
  rw [hsec, div_one]
  have h1 := (abs_le.1 hH2).2
  have h2 : bstar / (2 * τ) ≤ Duu / (2 * τ) := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have h3 : bstar / 4 / τ = (1 / 2) * (bstar / (2 * τ)) := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hhuu2 hC]

/-- **Bridge (b) ⇒ (e).** An operator-norm estimate on bilinear forms of the slice gives the
pointwise estimate used in `radial_reserve`: if `‖H'' + Δ/(2τ)‖ ≤ C` (e.g. `C = 7K` from
`hermite2_estimate` with `E` the bilinear forms on `(T_xX, h)`), then
`|H''(u,u) + Δ(u,u)/(2τ)| ≤ C · h(u,u)`. -/
theorem pointwise_of_opNorm {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    (S Δ : T →L[ℝ] T →L[ℝ] ℝ) (τ C : ℝ) (hS : ‖S + (1 / (2 * τ)) • Δ‖ ≤ C) (u : T) :
    |S u u + Δ u u / (2 * τ)| ≤ C * ‖u‖ ^ 2 := by
  have h := (S + (1 / (2 * τ)) • Δ).le_opNorm₂ u u
  have e : (S + (1 / (2 * τ)) • Δ) u u = S u u + Δ u u / (2 * τ) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [e, Real.norm_eq_abs] at h
  calc _ ≤ ‖S + (1 / (2 * τ)) • Δ‖ * ‖u‖ * ‖u‖ := h
    _ ≤ C * ‖u‖ * ‖u‖ := by gcongr
    _ = C * ‖u‖ ^ 2 := by ring

/-! ## (f) All two-planes

`W` is the tangent space of the glued manifold at a strip point, with the inner product `G_τ`;
`e = ∂_z` is a unit normal and `T = eᗮ` the tangential space. `Rm` is an algebraic curvature
tensor, `Rm(x,y,z,w) = G(R(x,y)z, w)` (HLY: `R_{ABCD} = G(R(∂_A,∂_B)∂_C,∂_D)`), and the sectional
numerator of the plane `x ∧ y` is `Rm(x,y,y,x)`. -/

section AllPlanes

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (Rm : W →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
  (hA1 : ∀ x y z w, Rm y x z w = -Rm x y z w)
  (hA2 : ∀ x y z w, Rm x y w z = -Rm x y z w)
  (hP : ∀ x y z w, Rm z w x y = Rm x y z w)

/-- The Gram determinant `‖x‖²‖y‖² − ⟪x,y⟫²`. -/
noncomputable def gram (x y : W) : ℝ := ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ ^ 2

include hA1 in
theorem rm_self_left (x z w : W) : Rm x x z w = 0 := by
  have := hA1 x x z w; linarith

include hA1 in
/-- `Rm(αx+βy, γx+δy, ·, ·) = (αδ − βγ) Rm(x, y, ·, ·)`. -/
theorem rm_biv_left (α β γ δ : ℝ) (x y z w : W) :
    Rm (α • x + β • y) (γ • x + δ • y) z w = (α * δ - β * γ) * Rm x y z w := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [rm_self_left Rm hA1 x, rm_self_left Rm hA1 y, hA1 x y]
  ring

include hA1 hA2 hP in
/-- Reparametrisation: `Rm(x', y', y', x') = (αδ − βγ)² Rm(x, y, y, x)`. -/
theorem rm_reparam (α β γ δ : ℝ) (x y : W) :
    Rm (α • x + β • y) (γ • x + δ • y) (γ • x + δ • y) (α • x + β • y)
      = (α * δ - β * γ) ^ 2 * Rm x y y x := by
  rw [rm_biv_left Rm hA1, hP, rm_biv_left Rm hA1, hP, hA2 x y x y]
  ring

theorem gram_reparam (α β γ δ : ℝ) (x y : W) :
    gram (α • x + β • y) (γ • x + δ • y) = (α * δ - β * γ) ^ 2 * gram x y := by
  simp only [gram, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm y x]
  ring

variable (e : W) (he : ⟪e, e⟫ = 1) (a₀ β C₀ M : ℝ)

include hA1 hA2 hP he in
/-- The core case: `X ∈ T`, arbitrary `y`. -/
theorem all_planes_core (ha₀ : 0 < a₀)
    (htan : ∀ X Y : W, ⟪X, e⟫ = 0 → ⟪Y, e⟫ = 0 → a₀ * gram X Y ≤ Rm X Y Y X)
    (hrad : ∀ X : W, ⟪X, e⟫ = 0 → β * ⟪X, X⟫ ≤ Rm X e e X)
    (hcross : ∀ X Y : W, ⟪X, e⟫ = 0 → ⟪Y, e⟫ = 0 → ⟪X, Y⟫ = 0 →
      |Rm Y X X e| ≤ M * ⟪X, X⟫ * ‖Y‖)
    (hβ : a₀ / 2 + 2 * M ^ 2 / a₀ ≤ β) (X y : W) (hX : ⟪X, e⟫ = 0) :
    a₀ / 2 * gram X y ≤ Rm X y y X := by
  by_cases hX0 : X = 0
  · subst hX0; simp [gram]
  have hXX : 0 < ⟪X, X⟫ := real_inner_self_pos.2 hX0
  set b := ⟪y, e⟫
  set Y := y - b • e with hY
  have hYe : ⟪Y, e⟫ = 0 := by
    rw [hY, inner_sub_left, real_inner_smul_left, he]; ring
  set c := ⟪X, Y⟫ / ⟪X, X⟫ with hc
  set Y' := Y - c • X with hY'
  have hY'e : ⟪Y', e⟫ = 0 := by
    rw [hY', inner_sub_left, real_inner_smul_left, hYe, hX]; ring
  have hXY' : ⟪X, Y'⟫ = 0 := by
    rw [hY', inner_sub_right, real_inner_smul_right, hc, div_mul_cancel₀ _ hXX.ne', sub_self]
  -- `y − cX = Y' + b e`, and shearing does not change `Rm` or `gram`
  have hy : (-c) • X + y = Y' + b • e := by
    rw [hY', hY]; module
  have hshear := rm_reparam Rm hA1 hA2 hP 1 0 (-c) 1 X y
  have hgshear := gram_reparam (1 : ℝ) 0 (-c) 1 X y
  simp only [one_smul, zero_smul, add_zero, mul_one, zero_mul, sub_zero, one_pow,
    one_mul] at hshear hgshear
  rw [hy] at hshear hgshear
  rw [← hshear, ← hgshear]
  -- expand
  have hexp : Rm X (Y' + b • e) (Y' + b • e) X =
      Rm X Y' Y' X + 2 * b * Rm Y' X X e + b ^ 2 * Rm X e e X := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have h1 : Rm X Y' e X = Rm Y' X X e := by rw [hA1, hA2]; ring
    have h2 : Rm X e Y' X = Rm Y' X X e := by rw [hP]
    rw [h1, h2]; ring
  have hg : gram X (Y' + b • e) = ⟪X, X⟫ * (⟪Y', Y'⟫ + b ^ 2) := by
    simp only [gram, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hXY', hX, hY'e, he, real_inner_comm Y' e]
    ring
  rw [hexp, hg]
  have ht := htan X Y' hX hY'e
  have hgt : gram X Y' = ⟪X, X⟫ * ⟪Y', Y'⟫ := by simp [gram, hXY']
  rw [hgt] at ht
  have hr := hrad X hX
  have hc := hcross X Y' hX hY'e hXY'
  have hnY : ⟪Y', Y'⟫ = ‖Y'‖ ^ 2 := real_inner_self_eq_norm_sq Y'
  rw [hnY] at ht ⊢
  set t := ‖Y'‖
  have ht0 : 0 ≤ t := norm_nonneg _
  have hcross' : -(M * ⟪X, X⟫ * t * |b|) ≤ b * Rm Y' X X e := by
    have := neg_abs_le (b * Rm Y' X X e)
    rw [abs_mul] at this
    nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg b)]
  -- AM–GM: 2M t |b| ≤ (a₀/2) t² + (2M²/a₀) b²
  have hamgm : 2 * M * t * |b| ≤ a₀ / 2 * t ^ 2 + 2 * M ^ 2 / a₀ * b ^ 2 := by
    have hsq : 0 ≤ (a₀ / 2) * (t - 2 * M / a₀ * |b|) ^ 2 := by positivity
    have e1 : (a₀ / 2) * (t - 2 * M / a₀ * |b|) ^ 2
        = a₀ / 2 * t ^ 2 - 2 * M * t * |b| + 2 * M ^ 2 / a₀ * |b| ^ 2 := by
      field_simp; ring
    rw [e1, sq_abs] at hsq; linarith
  have hb2 : (a₀ / 2 + 2 * M ^ 2 / a₀) * b ^ 2 ≤ β * b ^ 2 :=
    mul_le_mul_of_nonneg_right hβ (sq_nonneg b)
  nlinarith [mul_le_mul_of_nonneg_left hamgm hXX.le, mul_le_mul_of_nonneg_left hb2 hXX.le,
    mul_le_mul_of_nonneg_left hr (sq_nonneg b)]

include hA1 hA2 hP he in
/-- **`eq:glue-all-planes`, conclusion.** Under the tangential reserve (`sec ≥ a₀` on `T`), the
radial reserve (`sec(u, e) ≥ β = β₀/τ − C₀`), the cross bound (`|Rm(u,w,w,e)| ≤ M` for
orthonormal `u, w ∈ T`, written homogeneously), and `β ≥ a₀/2 + 2M²/a₀` (HLY: "choose `τ` small
enough that the coefficient in parentheses is at least `a₀/2`"), every plane has
`Rm(x,y,y,x) ≥ (a₀/2) gram(x,y)`, i.e. `sec ≥ a₀/2`. In every dimension; `x, y` arbitrary. -/
theorem all_planes (ha₀ : 0 < a₀)
    (htan : ∀ X Y : W, ⟪X, e⟫ = 0 → ⟪Y, e⟫ = 0 → a₀ * gram X Y ≤ Rm X Y Y X)
    (hrad : ∀ X : W, ⟪X, e⟫ = 0 → β * ⟪X, X⟫ ≤ Rm X e e X)
    (hcross : ∀ X Y : W, ⟪X, e⟫ = 0 → ⟪Y, e⟫ = 0 → ⟪X, Y⟫ = 0 →
      |Rm Y X X e| ≤ M * ⟪X, X⟫ * ‖Y‖)
    (hβ : a₀ / 2 + 2 * M ^ 2 / a₀ ≤ β) (x y : W) :
    a₀ / 2 * gram x y ≤ Rm x y y x := by
  have core := all_planes_core Rm hA1 hA2 hP e he a₀ β M ha₀ htan hrad hcross hβ
  by_cases hα : ⟪x, e⟫ = 0
  · exact core x y hα
  · -- `x' = ⟪y,e⟫x − ⟪x,e⟫y ∈ T`, and `(x', x)` has determinant `⟪x,e⟫ ≠ 0` over `(x, y)`
    set α := ⟪x, e⟫
    set β' := ⟪y, e⟫
    have hx'e : ⟪β' • x + (-α) • y, e⟫ = 0 := by
      simp only [inner_add_left, real_inner_smul_left]; ring
    have h := core (β' • x + (-α) • y) ((1 : ℝ) • x + (0 : ℝ) • y) hx'e
    rw [rm_reparam Rm hA1 hA2 hP, gram_reparam] at h
    have hα2 : 0 < (β' * 0 - -α * 1) ^ 2 := by
      have : β' * 0 - -α * 1 = α := by ring
      rw [this]; exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hα))
    nlinarith

end AllPlanes

/-! ### Non-vacuity of (f)

The round unit sphere's curvature tensor `Rm(x,y,z,w) = ⟪y,z⟫⟪x,w⟫ − ⟪x,z⟫⟪y,w⟫` on `ℝ²`, with
`e = e₁`, satisfies every hypothesis with `a₀ = 1`, `β = 1`, `M = 0`… except `β ≥ a₀/2 + 0`,
which holds. So `all_planes` fires (giving `sec ≥ 1/2` for the curvature-one metric). -/

section Model

/-- The constant-curvature-one algebraic curvature tensor. -/
noncomputable def rmConst (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    W →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => LinearMap.mk₂ ℝ (fun z w => ⟪y, z⟫ * ⟪x, w⟫ - ⟪x, z⟫ * ⟪y, w⟫)
      (fun _ _ _ => by simp only [inner_add_right]; ring)
      (fun _ _ _ => by simp only [real_inner_smul_right]; ring)
      (fun _ _ _ => by simp only [inner_add_right]; ring)
      (fun _ _ _ => by simp only [real_inner_smul_right]; ring))
    (fun _ _ _ => by ext; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, inner_add_left]; ring)
    (fun _ _ _ => by ext; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        real_inner_smul_left]; ring)
    (fun _ _ _ => by ext; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, inner_add_left]; ring)
    (fun _ _ _ => by ext; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        real_inner_smul_left]; ring)

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

@[simp] theorem rmConst_apply (x y z w : W) :
    rmConst W x y z w = ⟪y, z⟫ * ⟪x, w⟫ - ⟪x, z⟫ * ⟪y, w⟫ := rfl

example (e : W) (he : ⟪e, e⟫ = 1) (x y : W) :
    1 / 2 * gram x y ≤ rmConst W x y y x :=
  all_planes (rmConst W) (fun x y z w => by simp only [rmConst_apply]; ring)
    (fun x y z w => by simp only [rmConst_apply]; ring)
    (fun x y z w => by
      simp only [rmConst_apply]
      rw [real_inner_comm x w, real_inner_comm y z, real_inner_comm x z, real_inner_comm y w]
      ring)
    e he 1 1 0 one_pos
    (fun X Y _ _ => by
      simp only [rmConst_apply, gram]; rw [real_inner_comm X Y]; apply le_of_eq; ring)
    (fun X hX => by
      simp only [rmConst_apply]; rw [he, real_inner_comm X e, hX]; apply le_of_eq; ring)
    (fun X Y hX hY _ => by
      simp only [rmConst_apply]; rw [hY, hX]; simp)
    (by norm_num) x y

end Model

end ExoticSpheres8And10
