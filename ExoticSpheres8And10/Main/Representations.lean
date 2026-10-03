/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.StarBundles.Model
import ExoticSpheres8And10.PolarBundles.AttachingSphere
import ExoticSpheres8And10.ActionField.Derivative

/-! # §5: the representations `ρ₈`, `ρ₁₀`, the action-field bound, and Theorems A and B

[D] §5 applies `prop:polar` and `thm:HLYgeneral` to Sperança's bundles `E¹¹ → S⁸` and
`E¹³ → S¹⁰`, which are star bundles for

* `ρ₈(q)(λ, x, w) = (λ, qx, qwq⁻¹)` on `ℝ ⊕ ℍ ⊕ ℍ`, with `e₈ = (1, 0, 0)` (`eq:rho8`);
* `ρ₁₀(q)(p, w, x) = (p, qw, qxq⁻¹)` on `Im ℍ ⊕ ℍ ⊕ ℍ`, with `e₁₀ = (0, 0, 1)` (`eq:rho10`).

Both have the form `ρ(q)(p, y) = (p, ρ₈'(q)y)` on `W = P ⊕ (ℍ ⊕ ℍ)`, with `ρ₈'(q)(x,w) = (qx, qwq⁻¹)`
and `P = ℝ` or `P = ℝ³ ≅ Im ℍ`. This file:

* `rhoRep P`: this `ρ` as a smooth orthogonal representation `S³ →* O(W)` (the data of a
  `StarRep`), with `rep8 : StarRep e₈` and `rep10 : StarRep e₁₀`;
* `hasDerivAt_actionField`: `K_y ξ = d/dτ|₀ ρ(e^{τξ})y` is `(0, ξx, ξw − wξ)`;
* `lem_K`: **[D] `lem:K`**, `‖K_y ξ‖ ≤ 2‖ξ‖` for `‖y‖ ≤ 1`, in both dimensions;
* `polar_and_K8`, `polar_and_K10`: the Lean part of the proofs of Theorems A and B. Every star
  bundle for `ρ₈` (resp. `ρ₁₀`) is isomorphic to a polar bundle `P_θ` with the same `ρ`, and
  `‖K_y‖ ≤ 2` holds for it. These are exactly the hypotheses of `thm:HLYgeneral` (`n = 8, 10`);
* `prodBundle`: a star bundle for any `StarRep` (the product with the diagonal action), so that
  the hypotheses are satisfiable for `ρ₈` and `ρ₁₀` themselves.

Imported, not formalised: Sperança's theorem that `E¹¹`, `E¹³` are such star bundles, with
the stated quotients (`thm:speranca`); `thm:HLYgeneral` itself; Hitchin's `α`-invariant.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Quaternion NormedSpace

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

/-! ### `ρ₈'` on `V8 = ℍ ⊕ ℍ` -/

/-- `(x, w) ↦ (qx, qwq̄)` on `V8`; equal to `ρ₈'(q)` on unit `q`. -/
def rhoV (q : ℍ[ℝ]) : V8 →L[ℝ] V8 :=
  LinearMap.toContinuousLinearMap
    ((eV8.symm : (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] V8).toLinearMap ∘ₗ
      (LinearMap.prodMap (LinearMap.mulLeft ℝ q)
        (LinearMap.mulLeft ℝ q ∘ₗ LinearMap.mulRight ℝ (Star.star q))) ∘ₗ
      (eV8 : V8 →L[ℝ] (ℍ[ℝ] × ℍ[ℝ])).toLinearMap)

theorem eV8_rhoV (q : ℍ[ℝ]) (z : V8) :
    eV8 (rhoV q z) = (q * (eV8 z).1, q * (eV8 z).2 * Star.star q) := by
  simp [rhoV, mul_assoc]

theorem rhoV_eq (q : ℍ[ℝ]) (z : V8) :
    rhoV q z = eV8.symm (q * (eV8 z).1, q * (eV8 z).2 * Star.star q) := by
  rw [← eV8_rhoV, ContinuousLinearEquiv.symm_apply_apply]

theorem rhoV_mul (a b : ℍ[ℝ]) (z : V8) : rhoV (a * b) z = rhoV a (rhoV b z) := by
  apply eV8.injective
  rw [eV8_rhoV, eV8_rhoV, eV8_rhoV, StarMul.star_mul]
  simp only [mul_assoc]

theorem rhoV_one (z : V8) : rhoV 1 z = z := by
  apply eV8.injective
  rw [eV8_rhoV, star_one, one_mul, one_mul, mul_one]

theorem rhoV_rho8 {q : ℍ[ℝ]} (hq : ‖q‖ = 1) (z : V8) : rhoV q z = eV8.symm (rho8 q (eV8 z)) := by
  rw [rhoV_eq, rho8, inv_eq_star_of_norm_one hq]

theorem norm_rhoV {q : ℍ[ℝ]} (hq : ‖q‖ = 1) (z : V8) : ‖rhoV q z‖ = ‖z‖ := by
  rw [rhoV_rho8 hq]; exact norm_rho8V hq z

theorem contDiff_rhoV_apply (z : V8) : ContDiff ℝ ∞ fun q : ℍ[ℝ] => rhoV q z := by
  have hst : ContDiff ℝ ∞ (Star.star : ℍ[ℝ] → ℍ[ℝ]) := (starL' ℝ : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]).contDiff
  have : ContDiff ℝ ∞ fun q : ℍ[ℝ] =>
      eV8.symm (q * (eV8 z).1, q * (eV8 z).2 * Star.star q) :=
    eV8.symm.contDiff.comp ((contDiff_id.mul contDiff_const).prodMk
      ((contDiff_id.mul contDiff_const).mul hst))
  have e : (fun q : ℍ[ℝ] => rhoV q z) =
      fun q => eV8.symm (q * (eV8 z).1, q * (eV8 z).2 * Star.star q) :=
    funext fun q => rhoV_eq q z
  rw [e]; exact this

/-! ### `ρ` on `W = P ⊕ V8` -/

section Rep

variable (P : Type) [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- `W = P ⊕ ℍ ⊕ ℍ` with the Euclidean norm. -/
abbrev WP := WithLp 2 (P × V8)

/-- `ρ(q)(p, y) = (p, ρ₈'(q) y)`. -/
def rhoW (q : ℍ[ℝ]) : WP P →L[ℝ] WP P :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ P V8).symm : P × V8 →L[ℝ] WP P) ∘L
    ((ContinuousLinearMap.id ℝ P).prodMap (rhoV q)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ P V8 : WP P →L[ℝ] P × V8)

theorem rhoW_apply (q : ℍ[ℝ]) (w : WP P) : rhoW P q w = WithLp.toLp 2 (w.fst, rhoV q w.snd) :=
  rfl

@[simp] theorem rhoW_fst (q : ℍ[ℝ]) (w : WP P) : (rhoW P q w).fst = w.fst := rfl

@[simp] theorem rhoW_snd (q : ℍ[ℝ]) (w : WP P) : (rhoW P q w).snd = rhoV q w.snd := rfl

theorem rhoW_mul (a b : ℍ[ℝ]) (w : WP P) : rhoW P (a * b) w = rhoW P a (rhoW P b w) := by
  simp only [rhoW_apply, rhoV_mul]; rfl

theorem rhoW_one (w : WP P) : rhoW P 1 w = w := by
  simp only [rhoW_apply, rhoV_one]; rfl

theorem norm_rhoW {q : ℍ[ℝ]} (hq : ‖q‖ = 1) (w : WP P) : ‖rhoW P q w‖ = ‖w‖ := by
  have h : ‖rhoW P q w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2 (rhoW P q w), WithLp.prod_norm_sq_eq_of_L2 w, rhoW_fst,
      rhoW_snd, norm_rhoV hq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem contDiff_rhoW : ContDiff ℝ ∞ (rhoW P) := by
  rw [contDiff_clm_apply_iff]
  intro w
  have : ContDiff ℝ ∞ fun q : ℍ[ℝ] =>
      ((WithLp.prodContinuousLinearEquiv 2 ℝ P V8).symm : P × V8 →L[ℝ] WP P) (w.fst, rhoV q w.snd) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ P V8).symm.contDiff.comp
      (contDiff_const.prodMk (contDiff_rhoV_apply w.snd))
  exact this

/-- `ρ(q)` as a linear isometry of `W`, for `q ∈ S³`. -/
def rhoLI (q : S3) : WP P ≃ₗᵢ[ℝ] WP P :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (rhoW P q).toLinearMap
      norm_map' := norm_rhoW P (mem_sphere_zero_iff_norm.1 q.2) }
    fun w => ⟨rhoW P (Star.star (q : ℍ[ℝ])) w, by
      show rhoW P q (rhoW P (Star.star (q : ℍ[ℝ])) w) = w
      rw [← rhoW_mul, mul_star_of_norm_one (mem_sphere_zero_iff_norm.1 q.2), rhoW_one]⟩

@[simp] theorem rhoLI_apply (q : S3) (w : WP P) : rhoLI P q w = rhoW P q w := rfl

/-- **The representation** `S³ →* O(W)`. -/
def rhoHom : S3 →* (WP P ≃ₗᵢ[ℝ] WP P) where
  toFun := rhoLI P
  map_one' := LinearIsometryEquiv.ext fun w => rhoW_one P w
  map_mul' a b := LinearIsometryEquiv.ext fun w => rhoW_mul P a b w

theorem rhoHom_smooth :
    ContMDiff (𝓡 3) 𝓘(ℝ, WP P →L[ℝ] WP P) ∞
      fun q : S3 => ((rhoHom P q : WP P ≃L[ℝ] WP P) : WP P →L[ℝ] WP P) := by
  have h := (contDiff_rhoW P).contMDiff.comp (contMDiff_coe_sphere (n := 3))
  exact h.congr fun q => ContinuousLinearMap.ext fun w => rfl

/-- The infinitesimal action `K_y ξ = (0, ξx, ξw − wξ)` at `y = (p, x, w)`. -/
def Kf (w : WP P) (ξ : ℍ[ℝ]) : WP P := WithLp.toLp 2 (0, eV8.symm (K8 (eV8 w.snd) ξ))

/-- The one-parameter subgroup `τ ↦ e^{τξ} ∈ S³` for imaginary `ξ`. -/
def expS {ξ : ℍ[ℝ]} (hξ : ξ.re = 0) (τ : ℝ) : S3 :=
  ⟨exp (τ • ξ), by
    rw [mem_sphere_zero_iff_norm, Quaternion.norm_exp]
    simp [hξ]⟩

/-- **`K_y ξ = d/dτ|₀ ρ(e^{τξ}) y`** ([D] §5, definition of `K_y`). -/
theorem hasDerivAt_actionField {ξ : ℍ[ℝ]} (hξ : ξ.re = 0) (w : WP P) :
    HasDerivAt (fun τ : ℝ => rhoHom P (expS hξ τ) w) (Kf P w ξ) 0 := by
  obtain ⟨-, hd, -⟩ := exp_curve ξ
  set y := eV8 w.snd
  have hunit : ∀ τ : ℝ, ‖exp (τ • ξ)‖ = 1 := fun τ => mem_sphere_zero_iff_norm.1 (expS hξ τ).2
  have hv := (hd.mul_const y.1).prodMk (hasDerivAt_conj_orbit _ ξ y.2 (by simp) hd)
  set L : ℍ[ℝ] × ℍ[ℝ] →L[ℝ] WP P :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ P V8).symm : P × V8 →L[ℝ] WP P) ∘L
      (ContinuousLinearMap.inr ℝ P V8) ∘L (eV8.symm : (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] V8)
  have hL := (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv).const_add (WithLp.toLp 2 (w.fst, (0 : V8)))
  have hfun : (fun τ : ℝ => rhoHom P (expS hξ τ) w) = fun τ =>
      WithLp.toLp 2 (w.fst, (0 : V8)) +
        L (exp (τ • ξ) * y.1, exp (τ • ξ) * y.2 * (exp (τ • ξ))⁻¹) := by
    funext τ
    show rhoW P (exp (τ • ξ)) w = _
    rw [rhoW_apply, rhoV_rho8 (hunit τ)]
    simp only [L, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe,
      WithLp.prodContinuousLinearEquiv_symm_apply, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero,
      zero_add]
    rfl
  rw [hfun]
  refine hL.congr_deriv ?_
  show L (ξ * y.1, ξ * y.2 - y.2 * ξ) = Kf P w ξ
  rfl

/-- **[D] `lem:K`**: `‖K_y ξ‖ ≤ 2‖ξ‖` for every `y` with `‖y‖ ≤ 1`, in particular on `S(V)`. -/
theorem lem_K (w : WP P) (hw : ‖w‖ ≤ 1) (ξ : ℍ[ℝ]) : ‖Kf P w ξ‖ ≤ 2 * ‖ξ‖ := by
  set y := eV8 w.snd
  have hy : ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 ≤ 1 := by
    have h1 := WithLp.prod_norm_sq_eq_of_L2 w
    have h2 := norm_sq_V8 w.snd
    rw [dot2, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h2
    have : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    nlinarith [sq_nonneg ‖w.fst‖]
  have hK : ‖Kf P w ξ‖ ^ 2 = ‖ξ * y.1‖ ^ 2 + ‖ξ * y.2 - y.2 * ξ‖ ^ 2 := by
    rw [Kf, WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 _)]
    show ‖(0 : P)‖ ^ 2 + ‖eV8.symm (K8 y ξ)‖ ^ 2 = _
    rw [norm_zero, norm_sq_V8, ContinuousLinearEquiv.apply_symm_apply, dot2,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp [K8]
  have h1 : ‖ξ * y.1‖ ^ 2 = ‖ξ‖ ^ 2 * ‖y.1‖ ^ 2 := by rw [norm_mul, mul_pow]
  have h2 := norm_commutator_sq_le ξ y.2
  have h3 := norm_im_sq_le y.2
  have hsq : ‖Kf P w ξ‖ ^ 2 ≤ (2 * ‖ξ‖) ^ 2 := by
    rw [hK, h1]
    nlinarith [sq_nonneg ‖ξ‖, sq_nonneg ‖y.1‖, mul_nonneg (sq_nonneg ‖ξ‖) (sq_nonneg ‖y.1‖)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end Rep

/-! ### `ρ₈` and `ρ₁₀` as star representations -/

/-- `W₈ = ℝ ⊕ ℍ ⊕ ℍ`. -/
abbrev W8 := WP ℝ

/-- `W₁₀ = Im ℍ ⊕ ℍ ⊕ ℍ`, with `Im ℍ ≅ ℝ³`. -/
abbrev W10 := WP (EuclideanSpace ℝ (Fin 3))

set_option synthInstance.maxHeartbeats 400000 in
instance continuousSMul_W10 : ContinuousSMul ℝ W10 := inferInstance

instance fact_finrank_W8 : Fact (finrank ℝ W8 = (7 + 1) + 1) :=
  ⟨by rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (ℝ × V8)), Module.finrank_prod,
    Module.finrank_self, Fact.out (p := finrank ℝ V8 = 7 + 1)]⟩

instance fact_finrank_W10 : Fact (finrank ℝ W10 = (9 + 1) + 1) :=
  ⟨by rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 3) × V8)),
    Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin,
    Fact.out (p := finrank ℝ V8 = 7 + 1)]⟩

/-- `e₈ = (1, 0, 0)`. -/
def e8 : W8 := WithLp.toLp 2 ((1 : ℝ), (0 : V8))

/-- `e₁₀ = (0, 0, 1)`. -/
def e10 : W10 := WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 3)), eV8.symm ((0 : ℍ[ℝ]), (1 : ℍ[ℝ])))

theorem norm_e8 : ‖e8‖ = 1 := by
  have h : ‖e8‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2 e8]; show ‖(1 : ℝ)‖ ^ 2 + ‖(0 : V8)‖ ^ 2 = 1; simp
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h.trans (one_pow 2).symm)

theorem norm_e10 : ‖e10‖ = 1 := by
  have h : ‖e10‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2 e10]
    show ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 + ‖eV8.symm ((0 : ℍ[ℝ]), (1 : ℍ[ℝ]))‖ ^ 2 = 1
    rw [norm_zero, norm_sq_V8, ContinuousLinearEquiv.apply_symm_apply, dot2,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h.trans (one_pow 2).symm)

/-- **`ρ₈`** (`eq:rho8`) as a star representation with pole `e₈`. -/
def rep8 : StarRep e8 where
  e_norm := norm_e8
  ρ := rhoHom ℝ
  ρ_e q := by
    show rhoW ℝ q e8 = e8
    rw [rhoW_apply]
    show WithLp.toLp 2 ((1 : ℝ), rhoV q 0) = e8
    rw [map_zero]; rfl
  ρ_smooth := rhoHom_smooth ℝ

/-- **`ρ₁₀`** (`eq:rho10`) as a star representation with pole `e₁₀`. -/
def rep10 : StarRep e10 where
  e_norm := norm_e10
  ρ := rhoHom (EuclideanSpace ℝ (Fin 3))
  ρ_e q := by
    show rhoW _ q e10 = e10
    rw [rhoW_apply]
    show WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 3)),
      rhoV q (eV8.symm ((0 : ℍ[ℝ]), (1 : ℍ[ℝ])))) = e10
    rw [rhoV_eq, ContinuousLinearEquiv.apply_symm_apply, mul_zero, mul_one,
      mul_star_of_norm_one (mem_sphere_zero_iff_norm.1 q.2)]
    rfl
  ρ_smooth := rhoHom_smooth _

/-! ### Non-vacuity: the product star bundle for any representation -/

section Prod

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} (R : StarRep e)

local notation "Sn" => sphere (0 : W) 1

theorem contMDiff_ρS :
    ContMDiff ((𝓡 3).prod (𝓡 (m + 1))) (𝓡 (m + 1)) ∞ fun x : S3 × Sn => R.ρS x.1 x.2 := by
  refine contMDiff_sphere_of_coe ?_
  exact (R.ρ_smooth.comp contMDiff_fst).clm_apply (contMDiff_coe_sphere.comp contMDiff_snd)

/-- **The product star bundle** `S^n × S³`, `(ζ,u)h = (ζ,uh)`, `q ⋆ (ζ,u) = (ρ(q)ζ, qu)`. -/
def prodBundle : StarBundle (m := m) R (Sn × S3) where
  proj p := p.1
  ract p h := (p.1, p.2 * h)
  star q p := (R.ρS q p.1, q * p.2)
  proj_smooth := contMDiff_fst
  ract_smooth := (contMDiff_fst.comp contMDiff_fst).prodMk
    (ContMDiff.comp (g := fun p : S3 × S3 => p.1 * p.2)
      (f := fun x : (Sn × S3) × S3 => (x.1.2, x.2)) contMDiff_mulS3
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))
  star_smooth :=
    (ContMDiff.comp (g := fun x : S3 × Sn => R.ρS x.1 x.2)
      (f := fun x : S3 × (Sn × S3) => (x.1, x.2.1)) (contMDiff_ρS R)
      (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
    (ContMDiff.comp (g := fun p : S3 × S3 => p.1 * p.2)
      (f := fun x : S3 × (Sn × S3) => (x.1, x.2.2)) contMDiff_mulS3
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))
  ract_one p := by simp
  ract_mul p h h' := by simp [mul_assoc]
  star_one p := by
    refine Prod.ext (Subtype.ext ?_) (by simp)
    simp [StarRep.ρS]
  star_mul q q' p := by
    refine Prod.ext (Subtype.ext ?_) (by simp [mul_assoc])
    simp [StarRep.ρS, map_mul]
  proj_ract _ _ := rfl
  star_ract q p h := by simp [mul_assoc]
  proj_star q p := rfl
  star_free q p h := by
    have h2 := congrArg Prod.snd h
    simpa using h2
  nbhd _ := univ
  nbhd_open _ := isOpen_univ
  mem_nbhd _ := mem_univ _
  sec _ z := (z, 1)
  sec_smooth _ := (contMDiff_id.prodMk contMDiff_const).contMDiffOn
  proj_sec _ _ _ := rfl
  fib _ p := p.2
  fib_smooth _ := contMDiff_snd.contMDiffOn
  sec_fib _ p _ := by simp
  fib_sec _ _ _ u := by simp

end Prod

/-! ### Theorems A and B: the formalised part -/

section Main

variable {E : Type} [TopologicalSpace E]

/-- **The formalised part of the proof of Theorem A.** Every star bundle `E → S⁸` for `ρ₈` (as
Sperança's `E¹¹` is, `thm:speranca`) is isomorphic to a polar bundle `P_θ` with the same
representation, and `P_θ` satisfies the hypothesis `‖K_y‖ ≤ 2` of `thm:HLYgeneral` (`n = 8`),
where `K_y ξ = d/dτ|₀ ρ(e^{τξ}) y`. -/
theorem polar_and_K8
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (7 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 7) ∞ E] [T2Space E] (B : StarBundle (m := 7) rep8 E) :
    letI := rep8.factVs 7
    ∃ D : PolarData (m := 7) e8, D.ρ = rep8.ρ ∧
      (∃ Φ : Diffeomorph (IP 7) (IP 7) (PolarBundle D) E ∞,
        (∀ x, B.proj (Φ x) = D.proj x) ∧ (∀ x h, Φ (D.ract x h) = B.ract (Φ x) h) ∧
        (∀ (q : S3) x, Φ (q • x) = B.star q (Φ x))) ∧
      (∀ (ξ : ℍ[ℝ]) (hξ : ξ.re = 0) (y : W8),
        HasDerivAt (fun τ : ℝ => D.ρ (expS hξ τ) y) (Kf ℝ y ξ) 0) ∧
      ∀ y : W8, ‖y‖ ≤ 1 → ∀ ξ : ℍ[ℝ], ‖Kf ℝ y ξ‖ ≤ 2 * ‖ξ‖ := by
  letI := rep8.factVs 7
  obtain ⟨D, hD, Φ, h1, h2, h3, -⟩ := B.prop_polar
  refine ⟨D, hD, ⟨Φ, h1, h2, h3⟩, fun ξ hξ y => ?_, fun y hy ξ => lem_K ℝ y hy ξ⟩
  rw [hD]; exact hasDerivAt_actionField ℝ hξ y

/-- **The formalised part of the proof of Theorem B** (`n = 10`, `ρ₁₀`). -/
theorem polar_and_K10
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (9 + 1))) (EuclideanSpace ℝ (Fin 3))) E]
    [IsManifold (IP 9) ∞ E] [T2Space E] (B : StarBundle (m := 9) rep10 E) :
    letI := rep10.factVs 9
    ∃ D : PolarData (m := 9) e10, D.ρ = rep10.ρ ∧
      (∃ Φ : Diffeomorph (IP 9) (IP 9) (PolarBundle D) E ∞,
        (∀ x, B.proj (Φ x) = D.proj x) ∧ (∀ x h, Φ (D.ract x h) = B.ract (Φ x) h) ∧
        (∀ (q : S3) x, Φ (q • x) = B.star q (Φ x))) ∧
      (∀ (ξ : ℍ[ℝ]) (hξ : ξ.re = 0) (y : W10),
        HasDerivAt (fun τ : ℝ => D.ρ (expS hξ τ) y) (Kf (EuclideanSpace ℝ (Fin 3)) y ξ) 0) ∧
      ∀ y : W10, ‖y‖ ≤ 1 → ∀ ξ : ℍ[ℝ], ‖Kf (EuclideanSpace ℝ (Fin 3)) y ξ‖ ≤ 2 * ‖ξ‖ := by
  letI := rep10.factVs 9
  obtain ⟨D, hD, Φ, h1, h2, h3, -⟩ := B.prop_polar
  refine ⟨D, hD, ⟨Φ, h1, h2, h3⟩, fun ξ hξ y => ?_, fun y hy ξ => lem_K (EuclideanSpace ℝ (Fin 3)) y hy ξ⟩
  rw [hD]; exact hasDerivAt_actionField (EuclideanSpace ℝ (Fin 3)) hξ y

end Main

/-- **Non-vacuity**: `polar_and_K8` applies to a star bundle for `ρ₈` (the product bundle). -/
example := polar_and_K8 (prodBundle rep8)

/-- **Non-vacuity**: `polar_and_K10` applies to a star bundle for `ρ₁₀`. -/
example := polar_and_K10 (prodBundle rep10)

end

end ExoticSpheres8And10
