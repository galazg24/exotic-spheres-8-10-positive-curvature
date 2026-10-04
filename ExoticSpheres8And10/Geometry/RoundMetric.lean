/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.WarpedProduct

/-! # The round metric in coordinates (non-vacuity of the fibre hypotheses)

`riemannTensorAt_wG` and the northern positivity theorem take the fibre metrics as inputs,
together with their Christoffel forms and the hypothesis that the fibres have sectional
curvature `1` at the point. This file shows those hypotheses are satisfiable by a genuine
round metric: the rescaled stereographic metric of the unit sphere,

  `H(x) = ψ(x) ⟪·,·⟫`, `ψ(x) = (1 + ‖x‖²/4)⁻²`,

on any finite-dimensional real inner product space `K`, with Christoffel form

  `Γ_x(a,b) = ⟪g,a⟫b + ⟪g,b⟫a − ⟪a,b⟫g`, `g(x) = −(2 + ‖x‖²/2)⁻¹ x`

(the Christoffel form of the conformal metric `e^{2f}⟪·,·⟫`, `g = ∇f`). At the origin `H` is
the inner product and the sectional curvature is `1`.

* `HR`, `ΓR`: the metric and its Christoffel form; smooth, symmetric, positive definite;
* `HR_ΓR`: the Koszul identity `H(Γ(a,b), c) = kz(a,b,c)` everywhere;
* `HR_zero`, `fibreRm_round`: `H(0) = ⟪·,·⟫` and `Rm(ξ,ζ,ζ,ξ) = |ξ|²|ζ|² − ⟪ξ,ζ⟫²` at `0`.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section Round

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- The conformal factor `ψ(x) = (1 + ‖x‖²/4)⁻²`. -/
def ψR (x : K) : ℝ := ((1 + ‖x‖ ^ 2 / 4) ^ 2)⁻¹

/-- `g(x) = −(2 + ‖x‖²/2)⁻¹ x`, the gradient of `log √ψ`. -/
def gR (x : K) : K := (-(2 + ‖x‖ ^ 2 / 2)⁻¹) • x

theorem ψR_pos (x : K) : 0 < ψR x := by unfold ψR; positivity

/-- The inner product as a bilinear map. -/
def ipR : K →L[ℝ] K →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem ipR_apply (a b : K) : ipR a b = ⟪a, b⟫ := rfl

/-- **The round metric** `H(x) = ψ(x) ⟪·,·⟫`. -/
def HR (x : K) : K →L[ℝ] K →L[ℝ] ℝ := ψR x • ipR

@[simp] theorem HR_apply (x a b : K) : HR x a b = ψR x * ⟪a, b⟫ := rfl

/-- The Christoffel form for a given gradient `g`. -/
def Γgl (g : K) : K →ₗ[ℝ] K →ₗ[ℝ] K :=
  LinearMap.mk₂ ℝ (fun a b => ⟪g, a⟫ • b + ⟪g, b⟫ • a - ⟪a, b⟫ • g)
    (fun a a' b => by simp only [inner_add_left, inner_add_right, add_smul, smul_add]; abel)
    (fun c a b => by
      simp only [real_inner_smul_left, real_inner_smul_right, smul_smul, smul_sub, smul_add]
      module)
    (fun a b b' => by simp only [inner_add_left, inner_add_right, add_smul, smul_add]; abel)
    (fun c a b => by
      simp only [real_inner_smul_left, real_inner_smul_right, smul_smul, smul_sub, smul_add]
      module)

/-- The Christoffel form as a continuous bilinear map. -/
def Γg (g : K) : K →L[ℝ] K →L[ℝ] K :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (K →ₗ[ℝ] K) ≃ₗ[ℝ] (K →L[ℝ] K)).toLinearMap ∘ₗ Γgl g)

@[simp] theorem Γg_apply (g a b : K) : Γg g a b = ⟪g, a⟫ • b + ⟪g, b⟫ • a - ⟪a, b⟫ • g := rfl

/-- **The Christoffel form of the round metric.** -/
def ΓR (x : K) : K →L[ℝ] K →L[ℝ] K := Γg (gR x)

@[simp] theorem ΓR_apply (x a b : K) :
    ΓR x a b = ⟪gR x, a⟫ • b + ⟪gR x, b⟫ • a - ⟪a, b⟫ • gR x := rfl

theorem contDiff_ψR : ContDiff ℝ ∞ (ψR (K := K)) := by
  unfold ψR
  exact ((contDiff_const.add ((contDiff_norm_sq ℝ).div_const 4)).pow 2).inv fun x => by positivity

theorem contDiff_gR : ContDiff ℝ ∞ (gR (K := K)) := by
  unfold gR
  exact ((contDiff_const.add ((contDiff_norm_sq ℝ).div_const 2)).inv fun x => by positivity).neg.smul
    contDiff_id

theorem contDiff_HR : ContDiff ℝ ∞ (HR (K := K)) := by
  rw [contDiff_clm_apply_iff]
  intro a
  rw [contDiff_clm_apply_iff]
  intro b
  have : (fun x : K => HR x a b) = fun x => ψR x * ⟪a, b⟫ := funext fun x => HR_apply x a b
  rw [show (fun x : K => (HR x) a b) = _ from this]
  exact contDiff_ψR.mul contDiff_const

theorem contDiff_ΓR : ContDiff ℝ ∞ (ΓR (K := K)) := by
  rw [contDiff_clm_apply_iff]
  intro a
  rw [contDiff_clm_apply_iff]
  intro b
  have e : (fun x : K => ΓR x a b) = fun x => ⟪gR x, a⟫ • b + ⟪gR x, b⟫ • a - ⟪a, b⟫ • gR x :=
    funext fun x => ΓR_apply x a b
  rw [show (fun x : K => (ΓR x) a b) = _ from e]
  exact (((contDiff_gR.inner ℝ contDiff_const).smul contDiff_const).add
    ((contDiff_gR.inner ℝ contDiff_const).smul contDiff_const)).sub
    (contDiff_const.smul contDiff_gR)

theorem isSymm_HR : IsSymm (cmet (HR (K := K))) := fun x a b => by
  show HR x (fromTS a) (fromTS b) = HR x (fromTS b) (fromTS a)
  rw [HR_apply, HR_apply, real_inner_comm]

theorem isPosDef_HR : IsPosDef (cmet (HR (K := K))) := fun x v hv => by
  show 0 < HR x (fromTS v) (fromTS v)
  rw [HR_apply]
  have : (fromTS v : K) ≠ 0 := hv
  exact mul_pos (ψR_pos x) (real_inner_self_pos.2 this)

/-- The scalar profile `φ(t) = (1 + t/4)⁻²`, so that `ψ(x) = φ(‖x‖²)`. -/
theorem hasDerivAt_φR (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => ((1 + t / 4) ^ 2)⁻¹) (-(2 * (1 + t / 4) * (1 / 4)) / ((1 + t / 4) ^ 2) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t / 4) (1 / 4) t := by
    simpa using ((hasDerivAt_id t).div_const 4).const_add 1
  have h2 := h1.pow 2
  have hne : (1 + t / 4) ^ 2 ≠ 0 := by positivity
  have h3 := h2.inv hne
  refine h3.congr_deriv ?_
  norm_num

/-- `∂_a ψ = 2ψ⟪g, a⟫`. -/
theorem fderiv_ψR_apply (x a : K) : fderiv ℝ (ψR (K := K)) x a = 2 * ψR x * ⟪gR x, a⟫ := by
  have hn : HasFDerivAt (fun y : K => ‖y‖ ^ 2) ((2 : ℕ) • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := (hasDerivAt_φR (‖x‖ ^ 2) (by positivity)).comp_hasFDerivAt x hn
  have e : ((fun t : ℝ => ((1 + t / 4) ^ 2)⁻¹) ∘ fun y : K => ‖y‖ ^ 2) = ψR := by
    funext y; simp [ψR]
  rw [e] at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, nsmul_eq_mul, smul_eq_mul, gR, real_inner_smul_left,
    ψR]
  have hia : (innerSL ℝ x) a = ⟪x, a⟫ := rfl
  rw [hia]
  have h1 : 0 < 1 + ‖x‖ ^ 2 / 4 := by positivity
  have h2 : (2 + ‖x‖ ^ 2 / 2) = 2 * (1 + ‖x‖ ^ 2 / 4) := by ring
  rw [h2]
  field_simp
  push_cast
  ring

theorem fderiv_HR_apply (x a b c : K) :
    fderiv ℝ (HR (K := K)) x a b c = 2 * ψR x * ⟪gR x, a⟫ * ⟪b, c⟫ := by
  have hd : DifferentiableAt ℝ (HR (K := K)) x := (contDiff_HR.differentiable (by simp)) x
  have hp := fderiv_pair (A := fun _ => b) (B := fun _ => c) hd (differentiableAt_const b)
    (differentiableAt_const c) a
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at hp
  rw [← hp]
  have e : (fun y : K => HR y b c) = fun y => ψR y * ⟪b, c⟫ := funext fun y => HR_apply y b c
  rw [e, fderiv_mul_const ((contDiff_ψR.differentiable (by simp)) x), ContinuousLinearMap.smul_apply,
    fderiv_ψR_apply, smul_eq_mul]
  ring

/-- **The Koszul identity** for the round metric, everywhere. -/
theorem HR_ΓR (x a b c : K) : HR x (ΓR x a b) c = kz HR x a b c := by
  rw [kz, fderiv_HR_apply, fderiv_HR_apply, fderiv_HR_apply, HR_apply]
  simp only [ΓR_apply, inner_sub_left, inner_add_left, real_inner_smul_left]
  ring

theorem HR_zero (a b : K) : HR 0 a b = ⟪a, b⟫ := by simp [ψR]

theorem gR_zero : gR (0 : K) = 0 := by simp [gR]

theorem fderiv_gR_zero (ξ : K) : fderiv ℝ (gR (K := K)) 0 ξ = (-(1 / 2 : ℝ)) • ξ := by
  have hn : HasFDerivAt (fun y : K => ‖y‖ ^ 2) ((2 : ℕ) • innerSL ℝ (0 : K)) (0 : K) :=
    (hasStrictFDerivAt_norm_sq (0 : K)).hasFDerivAt
  have hχ : HasDerivAt (fun t : ℝ => -(2 + t / 2)⁻¹) _ (‖(0 : K)‖ ^ 2) :=
    ((((hasDerivAt_id (‖(0 : K)‖ ^ 2)).div_const 2).const_add 2).inv (by simp)).neg
  have hc := hχ.comp_hasFDerivAt (0 : K) hn
  have h := hc.smul (hasFDerivAt_id (0 : K))
  have h' : HasFDerivAt (gR (K := K)) _ (0 : K) := h
  rw [h'.fderiv]
  simp

/-- The derivative of the Christoffel form at `0`: `∂_ξΓ(a,b) = Γ_{Dg(ξ)}(a,b)`. -/
theorem fderiv_ΓR_zero (ξ a b : K) :
    fderiv ℝ (ΓR (K := K)) 0 ξ a b =
      ⟪(-(1 / 2 : ℝ)) • ξ, a⟫ • b + ⟪(-(1 / 2 : ℝ)) • ξ, b⟫ • a - ⟪a, b⟫ • ((-(1 / 2 : ℝ)) • ξ) := by
  have hd : DifferentiableAt ℝ (ΓR (K := K)) 0 := (contDiff_ΓR.differentiable (by simp)) 0
  have h1 : HasFDerivAt (fun y : K => ΓR y a b) _ (0 : K) :=
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const a 0)).clm_apply (hasFDerivAt_const b 0)
  have hgd : HasFDerivAt (gR (K := K)) (fderiv ℝ gR (0 : K)) (0 : K) :=
    ((contDiff_gR.differentiable (by simp)) (0 : K)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : K => ⟪gR y, a⟫ • b + ⟪gR y, b⟫ • a - ⟪a, b⟫ • gR y) _ (0 : K) :=
    (((hgd.inner ℝ (hasFDerivAt_const a 0)).smul_const b).add
      ((hgd.inner ℝ (hasFDerivAt_const b 0)).smul_const a)).sub (hgd.const_smul ⟪a, b⟫)
  have e : (fun y : K => ΓR y a b) = fun y => ⟪gR y, a⟫ • b + ⟪gR y, b⟫ • a - ⟪a, b⟫ • gR y :=
    funext fun y => ΓR_apply y a b
  rw [e] at h1
  have := h1.unique h2
  have hv := congrArg (fun L => L ξ) this
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] at hv
  rw [hv]
  simp [fderiv_gR_zero, fderivInnerCLM_apply]

/-- **The round metric has sectional curvature `1` at the origin.** -/
theorem fibreRm_round (ξ ζ : K) :
    fibreRm HR ΓR 0 ξ ζ = HR 0 ξ ξ * HR 0 ζ ζ - HR 0 ξ ζ ^ 2 := by
  simp only [fibreRm, fderiv_ΓR_zero, ΓR_apply, gR_zero, inner_zero_left, zero_smul, sub_zero,
    add_zero, map_zero, HR_zero]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, inner_zero_left, inner_zero_right, smul_zero, sub_zero,
    mul_zero, zero_mul, add_zero, sub_self]
  rw [real_inner_comm ζ ξ]
  ring

/-! ### Curvature `1` at every point -/

/-- `c(x) = (2 + ‖x‖²/2)⁻¹`, so that `g = −c x` and `ψ = 4c²`. -/
def cR (x : K) : ℝ := (2 + ‖x‖ ^ 2 / 2)⁻¹

theorem gR_eq (x : K) : gR x = (-cR x) • x := rfl

theorem ψR_eq (x : K) : ψR x = 4 * cR x ^ 2 := by
  unfold ψR cR
  have h1 : 0 < 1 + ‖x‖ ^ 2 / 4 := by positivity
  have h2 : 0 < 2 + ‖x‖ ^ 2 / 2 := by positivity
  field_simp
  ring

theorem fderiv_gR (x ξ : K) :
    fderiv ℝ (gR (K := K)) x ξ = (-cR x) • ξ + (cR x ^ 2 * ⟪x, ξ⟫) • x := by
  have hn : HasFDerivAt (fun y : K => ‖y‖ ^ 2) ((2 : ℕ) • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hχ : HasDerivAt (fun t : ℝ => -(2 + t / 2)⁻¹) _ (‖x‖ ^ 2) :=
    ((((hasDerivAt_id (‖x‖ ^ 2)).div_const 2).const_add 2).inv
      (by simp only [id]; positivity)).neg
  have hc := hχ.comp_hasFDerivAt x hn
  have h := hc.smul (hasFDerivAt_id x)
  have h' : HasFDerivAt (gR (K := K)) _ x := h
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, id, Function.comp_apply,
    nsmul_eq_mul, smul_eq_mul]
  have hia : (innerSL ℝ x) ξ = ⟪x, ξ⟫ := rfl
  rw [hia]
  unfold cR
  have h2 : (2 + ‖x‖ ^ 2 / 2) ≠ 0 := by positivity
  congr 1
  congr 1
  field_simp
  push_cast
  ring

theorem fderiv_ΓR (x ξ a b : K) :
    fderiv ℝ (ΓR (K := K)) x ξ a b =
      ⟪fderiv ℝ gR x ξ, a⟫ • b + ⟪fderiv ℝ gR x ξ, b⟫ • a - ⟪a, b⟫ • fderiv ℝ gR x ξ := by
  have hd : DifferentiableAt ℝ (ΓR (K := K)) x := (contDiff_ΓR.differentiable (by simp)) x
  have h1 : HasFDerivAt (fun y : K => ΓR y a b) _ x :=
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hgd : HasFDerivAt (gR (K := K)) (fderiv ℝ gR x) x :=
    ((contDiff_gR.differentiable (by simp)) x).hasFDerivAt
  have h2 : HasFDerivAt (fun y : K => ⟪gR y, a⟫ • b + ⟪gR y, b⟫ • a - ⟪a, b⟫ • gR y) _ x :=
    (((hgd.inner ℝ (hasFDerivAt_const a x)).smul_const b).add
      ((hgd.inner ℝ (hasFDerivAt_const b x)).smul_const a)).sub (hgd.const_smul ⟪a, b⟫)
  have e : (fun y : K => ΓR y a b) = fun y => ⟪gR y, a⟫ • b + ⟪gR y, b⟫ • a - ⟪a, b⟫ • gR y :=
    funext fun y => ΓR_apply y a b
  rw [e] at h1
  have := h1.unique h2
  have hv := congrArg (fun L => L ξ) this
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] at hv
  rw [hv]
  simp [fderivInnerCLM_apply]

/-- **The round metric has sectional curvature `1` everywhere.** -/
theorem fibreRm_round_all (x ξ ζ : K) :
    fibreRm HR ΓR x ξ ζ = HR x ξ ξ * HR x ζ ζ - HR x ξ ζ ^ 2 := by
  simp only [fibreRm, fderiv_ΓR, fderiv_gR, ΓR_apply, HR_apply, gR_eq, ψR_eq]
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, map_sub, map_add,
    map_smul, smul_eq_mul, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc : cR x * (2 + ‖x‖ ^ 2 / 2) = 1 := by
    unfold cR; have : (2 + ‖x‖ ^ 2 / 2) ≠ 0 := by positivity
    field_simp
  rw [real_inner_comm ζ ξ, real_inner_comm ξ x, real_inner_comm ζ x]
  linear_combination (8 * cR x ^ 3 * (⟪ζ, ξ⟫ ^ 2 - ‖ζ‖ ^ 2 * ‖ξ‖ ^ 2)) * hc

end Round

end

end ExoticSpheres8And10
