/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.WarpedProduct
import ExoticSpheres8And10.Curvature.Criterion

/-! # §4: positive curvature of the northern doubly warped metric on star-horizontal planes

[D] §4, "Curvature of star-horizontal planes": for star-horizontal vectors
`λ∂_s + X + U`, `μ∂_s + Y + V` with `U = TX`, `V = TY`, the numerator of the doubly warped metric
is `eq:fullcurvature`. Under `eq:northcriterion` and `‖T‖ ≤ 2F/r` it is positive: "every
star-horizontal two-plane has positive sectional-curvature numerator".

`riemannTensorAt_wG` computes `RiemannianGeometry`'s Riemann tensor of the doubly warped metric in coordinates.
Here it is specialised to [D]'s setting and composed with A6.

* `riemannTensorAt_wG_orthonormal`: at a point where the fibre metrics are the Euclidean inner
  products with sectional curvature `1` (round fibres in normal coordinates), and in the scaled
  components `X = F·X_coord`, `U = r·U_coord` of [D], **`RiemannianGeometry`'s `Rm(u,v,v,u)` equals A6's
  `northNumerator`**, i.e. `eq:fullcurvature`;
* `sectionalCurvatureAt_wG_pos`: **`RiemannianGeometry`'s sectional curvature of the doubly warped metric is
  positive on every star-horizontal plane** at a point where `eq:northcriterion` holds and
  `‖T‖ ≤ 2F/r`.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section North

variable {F₁ F₂ : Type} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {F r : ℝ → ℝ} {H₁ : F₁ → F₁ →L[ℝ] F₁ →L[ℝ] ℝ} {H₂ : F₂ → F₂ →L[ℝ] F₂ →L[ℝ] ℝ}
  {Γ₁ : F₁ → F₁ →L[ℝ] F₁ →L[ℝ] F₁} {Γ₂ : F₂ → F₂ →L[ℝ] F₂ →L[ℝ] F₂}

local notation "Ew" => ℝ × F₁ × F₂

/-- The coordinate vector with scaled components `(λ, X, U)`: `(λ, X/F, U/r)`. -/
def scaledVec (F r : ℝ → ℝ) (s lam : ℝ) (X : F₁) (U : F₂) : Ew :=
  (lam, (F s)⁻¹ • X, (r s)⁻¹ • U)

/-- **`eq:fullcurvature` for `RiemannianGeometry`'s Riemann tensor.** At `p = (s, x, y)` where `H₁(x)`, `H₂(y)`
are the inner products and both fibres have sectional curvature `1`, for star-horizontal vectors
with scaled components `(λ, X, TX)`, `(μ, Y, TY)`, `Rm(u,v,v,u)` is A6's `northNumerator`. -/
theorem riemannTensorAt_wG_orthonormal (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r)
    (hH₁ : ContDiff ℝ ∞ H₁) (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁)
    (hΓ₂s : ContDiff ℝ ∞ Γ₂) (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0)
    (hs₁ : IsSymm (cmet H₁)) (hs₂ : IsSymm (cmet H₂)) (hp₁ : IsPosDef (cmet H₁))
    (hp₂ : IsPosDef (cmet H₂))
    (hΓ₁ : ∀ x ξ ζ c, H₁ x (Γ₁ x ξ ζ) c = kz H₁ x ξ ζ c)
    (hΓ₂ : ∀ y η θ κ, H₂ y (Γ₂ y η θ) κ = kz H₂ y η θ κ) (p : Ew)
    (hx : ∀ a b, H₁ p.2.1 a b = ⟪a, b⟫) (hy : ∀ a b, H₂ p.2.2 a b = ⟪a, b⟫)
    (hK₁ : ∀ ξ ζ, fibreRm H₁ Γ₁ p.2.1 ξ ζ =
      H₁ p.2.1 ξ ξ * H₁ p.2.1 ζ ζ - H₁ p.2.1 ξ ζ ^ 2)
    (hK₂ : ∀ η θ, fibreRm H₂ Γ₂ p.2.2 η θ =
      H₂ p.2.2 η η * H₂ p.2.2 θ θ - H₂ p.2.2 η θ ^ 2)
    (T : F₁ →L[ℝ] F₂) (X Y : F₁) (lam mu : ℝ) :
    riemannTensorAt (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂).isNondegenerate
      (isContMDiffMetricSection_cmet (contDiff2_wG hF hr hH₁ hH₂)) p
      (toTSv p (scaledVec F r p.1 lam X (T X))) (toTSv p (scaledVec F r p.1 mu Y (T Y)))
      (toTSv p (scaledVec F r p.1 mu Y (T Y))) (toTSv p (scaledVec F r p.1 lam X (T X))) =
    northNumerator (F p.1) (r p.1) (deriv F p.1) (deriv r p.1) (deriv (deriv F) p.1)
      (deriv (deriv r) p.1) T X Y lam mu := by
  rw [riemannTensorAt_wG hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0 hs₁ hs₂ hp₁ hp₂ hΓ₁ hΓ₂ p _ _ 1 1
    (by rw [hK₁, one_mul]) (by rw [hK₂, one_mul])]
  have hF0' := hF0 p.1
  have hr0' := hr0 p.1
  simp only [scaledVec, map_sub, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hx, hy, northNumerator, wedgeSq, tensorSq,
    ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm X Y, real_inner_comm (T X) (T Y)]
  field_simp

/-- **Positive numerator gives positive sectional curvature.** If A6's `northNumerator` is positive
on an independent star-horizontal pair, `RiemannianGeometry`'s sectional curvature of the doubly warped metric is
positive on the plane it spans. -/
theorem sectionalCurvatureAt_wG_pos_of_num (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r)
    (hH₁ : ContDiff ℝ ∞ H₁) (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁)
    (hΓ₂s : ContDiff ℝ ∞ Γ₂) (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0)
    (hs₁ : IsSymm (cmet H₁)) (hs₂ : IsSymm (cmet H₂)) (hp₁ : IsPosDef (cmet H₁))
    (hp₂ : IsPosDef (cmet H₂))
    (hΓ₁ : ∀ x ξ ζ c, H₁ x (Γ₁ x ξ ζ) c = kz H₁ x ξ ζ c)
    (hΓ₂ : ∀ y η θ κ, H₂ y (Γ₂ y η θ) κ = kz H₂ y η θ κ) (p : Ew)
    (hx : ∀ a b, H₁ p.2.1 a b = ⟪a, b⟫) (hy : ∀ a b, H₂ p.2.2 a b = ⟪a, b⟫)
    (hK₁ : ∀ ξ ζ, fibreRm H₁ Γ₁ p.2.1 ξ ζ =
      H₁ p.2.1 ξ ξ * H₁ p.2.1 ζ ζ - H₁ p.2.1 ξ ζ ^ 2)
    (hK₂ : ∀ η θ, fibreRm H₂ Γ₂ p.2.2 η θ =
      H₂ p.2.2 η η * H₂ p.2.2 θ θ - H₂ p.2.2 η θ ^ 2)
    (T : F₁ →L[ℝ] F₂) (X Y : F₁) (lam mu : ℝ)
    (hN : 0 < northNumerator (F p.1) (r p.1) (deriv F p.1) (deriv r p.1) (deriv (deriv F) p.1)
      (deriv (deriv r) p.1) T X Y lam mu)
    (hind : LinearIndependent ℝ ![((lam, X, T X) : ℝ × F₁ × F₂), (mu, Y, T Y)]) :
    0 < sectionalCurvatureAt (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂)
      (isContMDiffMetricSection_cmet (contDiff2_wG hF hr hH₁ hH₂)) p
      (toTSv p (scaledVec F r p.1 lam X (T X))) (toTSv p (scaledVec F r p.1 mu Y (T Y))) := by
  rw [sectionalCurvatureAt_def]
  refine div_pos ?_ ?_
  · rw [riemannTensorAt_wG_orthonormal hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0 hs₁ hs₂ hp₁ hp₂ hΓ₁ hΓ₂ p
      hx hy hK₁ hK₂]
    exact hN
  · -- the scaling `(a, b, c) ↦ (a, b/F, c/r)` is injective, so the pair stays independent
    set L : Ew →ₗ[ℝ] Ew := LinearMap.prodMap LinearMap.id
      (LinearMap.prodMap ((F p.1)⁻¹ • LinearMap.id) ((r p.1)⁻¹ • LinearMap.id))
    have hL : LinearMap.ker L = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      have h0 := congrArg Prod.fst hw
      have h1 := congrArg (fun q : Ew => q.2.1) hw
      have h2 := congrArg (fun q : Ew => q.2.2) hw
      simp [L, inv_ne_zero (hF0 p.1), inv_ne_zero (hr0 p.1)] at h0 h1 h2
      exact Prod.ext h0 (Prod.ext h1 h2)
    have hli := hind.map' L hL
    have e : L ∘ ![((lam, X, T X) : ℝ × F₁ × F₂), (mu, Y, T Y)] =
        ![scaledVec F r p.1 lam X (T X), scaledVec F r p.1 mu Y (T Y)] := by
      funext i
      fin_cases i <;> rfl
    rw [e] at hli
    exact gramDet_pos (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂) hli

/-- **The northern filling has positive sectional curvature on star-horizontal planes**, for
`RiemannianGeometry`'s sectional curvature of the doubly warped metric. The hypotheses are those of A6
(`northNumerator_pos`): `F, r > 0`, `F', r' ≥ 0`, `r' < 1`, `eq:northcriterion` and
`‖T‖ ≤ 2F/r`, all at `s`. The plane is spanned by the star-horizontal vectors with scaled
components `(λ, X, TX)`, `(μ, Y, TY)`, assumed independent. -/
theorem sectionalCurvatureAt_wG_pos (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r)
    (hH₁ : ContDiff ℝ ∞ H₁) (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁)
    (hΓ₂s : ContDiff ℝ ∞ Γ₂) (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0)
    (hs₁ : IsSymm (cmet H₁)) (hs₂ : IsSymm (cmet H₂)) (hp₁ : IsPosDef (cmet H₁))
    (hp₂ : IsPosDef (cmet H₂))
    (hΓ₁ : ∀ x ξ ζ c, H₁ x (Γ₁ x ξ ζ) c = kz H₁ x ξ ζ c)
    (hΓ₂ : ∀ y η θ κ, H₂ y (Γ₂ y η θ) κ = kz H₂ y η θ κ) (p : Ew)
    (hx : ∀ a b, H₁ p.2.1 a b = ⟪a, b⟫) (hy : ∀ a b, H₂ p.2.2 a b = ⟪a, b⟫)
    (hK₁ : ∀ ξ ζ, fibreRm H₁ Γ₁ p.2.1 ξ ζ =
      H₁ p.2.1 ξ ξ * H₁ p.2.1 ζ ζ - H₁ p.2.1 ξ ζ ^ 2)
    (hK₂ : ∀ η θ, fibreRm H₂ Γ₂ p.2.2 η θ =
      H₂ p.2.2 η η * H₂ p.2.2 θ θ - H₂ p.2.2 η θ ^ 2)
    (hFp : 0 < F p.1) (hrp : 0 < r p.1) (hF' : 0 ≤ deriv F p.1) (hr' : 0 ≤ deriv r p.1)
    (hr'1 : deriv r p.1 < 1)
    (hc1 : 8 * F p.1 * deriv F p.1 * deriv r p.1 / r p.1 ^ 3 <
      (1 - deriv F p.1 ^ 2) / F p.1 ^ 2)
    (hc2 : 4 * F p.1 ^ 2 * max (deriv (deriv r) p.1) 0 / r p.1 ^ 3 <
      -deriv (deriv F) p.1 / F p.1)
    (T : F₁ →L[ℝ] F₂) (hT : ‖T‖ ≤ 2 * F p.1 / r p.1) (X Y : F₁) (lam mu : ℝ)
    (hind : LinearIndependent ℝ ![((lam, X, T X) : ℝ × F₁ × F₂), (mu, Y, T Y)]) :
    0 < sectionalCurvatureAt (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂)
      (isContMDiffMetricSection_cmet (contDiff2_wG hF hr hH₁ hH₂)) p
      (toTSv p (scaledVec F r p.1 lam X (T X))) (toTSv p (scaledVec F r p.1 mu Y (T Y))) := by
  exact sectionalCurvatureAt_wG_pos_of_num hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0 hs₁ hs₂ hp₁ hp₂ hΓ₁ hΓ₂
    p hx hy hK₁ hK₂ T X Y lam mu
    (northNumerator_pos _ _ _ _ _ _ hFp hrp hF' hr' hr'1 hc1 hc2 T hT X Y lam mu hind) hind

end North

end

end ExoticSpheres8And10
