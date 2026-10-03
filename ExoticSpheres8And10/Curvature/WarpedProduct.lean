/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.Coordinates
import Mathlib

/-! # §4: the doubly warped metric and its curvature (`eq:fullcurvature`)

[D] §4, northern filling: the metric `G_N = ds² + F(s)² h_{S^{n−1}} + r(s)² h_{S³}` (`eq:north`)
has, on the star-horizontal planes, the sectional-curvature numerator `eq:fullcurvature`.
"This is the dimension-independent form of [HLY, (5.7)]. It follows from the standard curvature
formulas for a doubly warped product."

Here the doubly warped metric is treated in coordinates, on `E = ℝ × F₁ × F₂`:
`G_{(s,x,y)} = ds² + F(s)² H₁(x) + r(s)² H₂(y)`, for arbitrary smooth fibre metrics `H₁`, `H₂`
with Christoffel forms `Γ₁`, `Γ₂`. Its curvature is that of `RiemannianGeometry`'s Levi-Civita connection,
computed through `S4_Coord`.

* `wG`, `contDiff_wG`, `isSymm_wG`, `isPosDef_wG`: the metric;
* `wΓ`, `wG_wΓ`: its Christoffel form, `Γ(v,w) =
  (−FF'H₁(ξ,ζ) − rr'H₂(η,θ), (F'/F)(aζ+bξ) + Γ₁(ξ,ζ), (r'/r)(aθ+bη) + Γ₂(η,θ))`.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section Warped

variable {F₁ F₂ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]

local notation "Ew" => ℝ × F₁ × F₂

variable (F r : ℝ → ℝ) (H₁ : F₁ → F₁ →L[ℝ] F₁ →L[ℝ] ℝ) (H₂ : F₂ → F₂ →L[ℝ] F₂ →L[ℝ] ℝ)

/-- **The doubly warped metric** `ds² + F(s)² H₁(x) + r(s)² H₂(y)`. -/
def wG (p : Ew) : Ew →L[ℝ] Ew →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ (F₁ × F₂))
      (ContinuousLinearMap.fst ℝ ℝ (F₁ × F₂)) +
    (F p.1 ^ 2) • (H₁ p.2.1).bilinearComp
      ((ContinuousLinearMap.fst ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂)))
      ((ContinuousLinearMap.fst ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂))) +
    (r p.1 ^ 2) • (H₂ p.2.2).bilinearComp
      ((ContinuousLinearMap.snd ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂)))
      ((ContinuousLinearMap.snd ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂)))

theorem wG_apply (p a b : Ew) :
    wG F r H₁ H₂ p a b = a.1 * b.1 + F p.1 ^ 2 * H₁ p.2.1 a.2.1 b.2.1 +
      r p.1 ^ 2 * H₂ p.2.2 a.2.2 b.2.2 := by
  simp [wG]

variable {F r H₁ H₂}

theorem contDiff_wG_apply (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r) (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) (a b : Ew) : ContDiff ℝ ∞ fun p => wG F r H₁ H₂ p a b := by
  simp only [wG_apply]
  have h1 : ContDiff ℝ ∞ fun p : Ew => H₁ p.2.1 a.2.1 b.2.1 :=
    ((hH₁.comp (contDiff_fst.comp contDiff_snd)).clm_apply contDiff_const).clm_apply
      contDiff_const
  have h2 : ContDiff ℝ ∞ fun p : Ew => H₂ p.2.2 a.2.2 b.2.2 :=
    ((hH₂.comp (contDiff_snd.comp contDiff_snd)).clm_apply contDiff_const).clm_apply
      contDiff_const
  exact (contDiff_const.add (((hF.comp contDiff_fst).pow 2).mul h1)).add
    (((hr.comp contDiff_fst).pow 2).mul h2)

theorem contDiff_wG (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r) (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) : ContDiff ℝ ∞ (wG F r H₁ H₂) := by
  rw [contDiff_clm_apply_iff]
  intro a
  rw [contDiff_clm_apply_iff]
  intro b
  exact contDiff_wG_apply hF hr hH₁ hH₂ a b

theorem isSymm_wG (hH₁ : IsSymm (cmet H₁)) (hH₂ : IsSymm (cmet H₂)) :
    IsSymm (cmet (wG F r H₁ H₂)) := fun p a b => by
  show wG F r H₁ H₂ p (fromTS a) (fromTS b) = wG F r H₁ H₂ p (fromTS b) (fromTS a)
  rw [wG_apply, wG_apply, G_symm hH₁, G_symm hH₂, mul_comm (fromTS a).1]

theorem isPosDef_wG (hF : ∀ s, F s ≠ 0) (hr : ∀ s, r s ≠ 0) (hH₁ : IsPosDef (cmet H₁))
    (hH₂ : IsPosDef (cmet H₂)) : IsPosDef (cmet (wG F r H₁ H₂)) := fun p v hv => by
  show 0 < wG F r H₁ H₂ p (fromTS v) (fromTS v)
  set w : Ew := fromTS v
  have hw : w ≠ 0 := hv
  rw [wG_apply]
  have n1 : ∀ ξ : F₁, 0 ≤ H₁ p.2.1 ξ ξ := fun ξ => by
    by_cases h : ξ = 0
    · simp [h]
    · exact (hH₁ p.2.1 (toTSv p.2.1 ξ) h).le
  have n2 : ∀ η : F₂, 0 ≤ H₂ p.2.2 η η := fun η => by
    by_cases h : η = 0
    · simp [h]
    · exact (hH₂ p.2.2 (toTSv p.2.2 η) h).le
  have hF2 : 0 < F p.1 ^ 2 := by have := hF p.1; positivity
  have hr2 : 0 < r p.1 ^ 2 := by have := hr p.1; positivity
  rcases eq_or_ne w.1 0 with h1 | h1
  · rcases eq_or_ne w.2.1 0 with h2 | h2
    · have h3 : w.2.2 ≠ 0 := by
        intro h3; exact hw (Prod.ext h1 (Prod.ext h2 h3))
      have := hH₂ p.2.2 (toTSv p.2.2 w.2.2) h3
      have : 0 < r p.1 ^ 2 * H₂ p.2.2 w.2.2 w.2.2 := mul_pos hr2 this
      nlinarith [n1 w.2.1, mul_self_nonneg w.1, mul_nonneg hF2.le (n1 w.2.1)]
    · have := hH₁ p.2.1 (toTSv p.2.1 w.2.1) h2
      have : 0 < F p.1 ^ 2 * H₁ p.2.1 w.2.1 w.2.1 := mul_pos hF2 this
      nlinarith [n2 w.2.2, mul_self_nonneg w.1, mul_nonneg hr2.le (n2 w.2.2)]
  · have : 0 < w.1 * w.1 := mul_self_pos.2 h1
    nlinarith [mul_nonneg hF2.le (n1 w.2.1), mul_nonneg hr2.le (n2 w.2.2)]

/-! ### The Christoffel form -/

variable (F r H₁ H₂) (Γ₁ : F₁ → F₁ →L[ℝ] F₁ →L[ℝ] F₁) (Γ₂ : F₂ → F₂ →L[ℝ] F₂ →L[ℝ] F₂)

/-- **The Christoffel form of the doubly warped metric.** -/
def wΓ (p v w : Ew) : Ew :=
  (-(F p.1 * deriv F p.1) * H₁ p.2.1 v.2.1 w.2.1 - r p.1 * deriv r p.1 * H₂ p.2.2 v.2.2 w.2.2,
    (deriv F p.1 / F p.1) • (v.1 • w.2.1 + w.1 • v.2.1) + Γ₁ p.2.1 v.2.1 w.2.1,
    (deriv r p.1 / r p.1) • (v.1 • w.2.2 + w.1 • v.2.2) + Γ₂ p.2.2 v.2.2 w.2.2)

variable {F r H₁ H₂ Γ₁ Γ₂}

/-- The derivative of the metric, `∂_vG(a,b)`. -/
theorem fderiv_wG_apply (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r) (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) (p v a b : Ew) :
    fderiv ℝ (wG F r H₁ H₂) p v a b =
      2 * F p.1 * deriv F p.1 * v.1 * H₁ p.2.1 a.2.1 b.2.1 +
        F p.1 ^ 2 * fderiv ℝ H₁ p.2.1 v.2.1 a.2.1 b.2.1 +
      2 * r p.1 * deriv r p.1 * v.1 * H₂ p.2.2 a.2.2 b.2.2 +
        r p.1 ^ 2 * fderiv ℝ H₂ p.2.2 v.2.2 a.2.2 b.2.2 := by
  have hGd : DifferentiableAt ℝ (wG F r H₁ H₂) p :=
    ((contDiff_wG hF hr hH₁ hH₂).differentiable (by simp)) p
  have hpair := fderiv_pair (A := fun _ => a) (B := fun _ => b) hGd (differentiableAt_const a)
    (differentiableAt_const b) v
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at hpair
  rw [← hpair]
  have e : (fun y : Ew => wG F r H₁ H₂ y a b) = fun y =>
      a.1 * b.1 + F y.1 ^ 2 * H₁ y.2.1 a.2.1 b.2.1 + r y.1 ^ 2 * H₂ y.2.2 a.2.2 b.2.2 :=
    funext fun y => wG_apply F r H₁ H₂ y a b
  rw [e]
  have hFd : HasDerivAt F (deriv F p.1) p.1 :=
    ((hF.differentiable (by simp)) p.1).hasDerivAt
  have hrd : HasDerivAt r (deriv r p.1) p.1 :=
    ((hr.differentiable (by simp)) p.1).hasDerivAt
  have hfst : HasFDerivAt (fun y : Ew => y.1) (ContinuousLinearMap.fst ℝ ℝ (F₁ × F₂)) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun y : Ew => y.2.1)
      ((ContinuousLinearMap.fst ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂))) p :=
    hasFDerivAt_fst.comp p hasFDerivAt_snd
  have hy : HasFDerivAt (fun y : Ew => y.2.2)
      ((ContinuousLinearMap.snd ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂))) p :=
    hasFDerivAt_snd.comp p hasFDerivAt_snd
  have hH1d : HasFDerivAt H₁ (fderiv ℝ H₁ p.2.1) p.2.1 :=
    ((hH₁.differentiable (by simp)) p.2.1).hasFDerivAt
  have hH2d : HasFDerivAt H₂ (fderiv ℝ H₂ p.2.2) p.2.2 :=
    ((hH₂.differentiable (by simp)) p.2.2).hasFDerivAt
  have t1 : HasFDerivAt (fun y : Ew => H₁ y.2.1 a.2.1 b.2.1) _ p :=
    ((hH1d.comp p hx).clm_apply (hasFDerivAt_const a.2.1 p)).clm_apply
      (hasFDerivAt_const b.2.1 p)
  have t2 : HasFDerivAt (fun y : Ew => H₂ y.2.2 a.2.2 b.2.2) _ p :=
    ((hH2d.comp p hy).clm_apply (hasFDerivAt_const a.2.2 p)).clm_apply
      (hasFDerivAt_const b.2.2 p)
  have f1 : HasFDerivAt (fun y : Ew => F y.1 ^ 2) _ p := (hFd.comp_hasFDerivAt p hfst).pow 2
  have r1 : HasFDerivAt (fun y : Ew => r y.1 ^ 2) _ p := (hrd.comp_hasFDerivAt p hfst).pow 2
  have htot : HasFDerivAt (fun y : Ew =>
      a.1 * b.1 + F y.1 ^ 2 * H₁ y.2.1 a.2.1 b.2.1 + r y.1 ^ 2 * H₂ y.2.2 a.2.2 b.2.2) _ p :=
    ((hasFDerivAt_const (a.1 * b.1) p).add (f1.mul t1)).add (r1.mul t2)
  rw [htot.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, map_zero, zero_add,
    add_zero, Function.comp_apply]
  push_cast
  ring

/-- **`wΓ` is the Christoffel form of `wG`.** -/
theorem wG_wΓ (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r) (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0)
    (hs₁ : IsSymm (cmet H₁)) (hs₂ : IsSymm (cmet H₂))
    (hΓ₁ : ∀ x ξ ζ c, H₁ x (Γ₁ x ξ ζ) c = kz H₁ x ξ ζ c)
    (hΓ₂ : ∀ y η θ κ, H₂ y (Γ₂ y η θ) κ = kz H₂ y η θ κ) (p v w z : Ew) :
    wG F r H₁ H₂ p (wΓ F r H₁ H₂ Γ₁ Γ₂ p v w) z = kz (wG F r H₁ H₂) p v w z := by
  have hH1d : DifferentiableAt ℝ H₁ p.2.1 := (hH₁.differentiable (by simp)) p.2.1
  have hH2d : DifferentiableAt ℝ H₂ p.2.2 := (hH₂.differentiable (by simp)) p.2.2
  rw [wG_apply, kz, fderiv_wG_apply hF hr hH₁ hH₂, fderiv_wG_apply hF hr hH₁ hH₂,
    fderiv_wG_apply hF hr hH₁ hH₂]
  simp only [wΓ, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hΓ₁, hΓ₂, kz]
  have s1 := fderiv_symm hs₁ hH1d w.2.1 z.2.1 v.2.1
  have s2 := fderiv_symm hs₂ hH2d w.2.2 z.2.2 v.2.2
  have g1 := G_symm hs₁ p.2.1 v.2.1 z.2.1
  have g2 := G_symm hs₂ p.2.2 v.2.2 z.2.2
  have g3 := G_symm hs₁ p.2.1 w.2.1 z.2.1
  have g4 := G_symm hs₂ p.2.2 w.2.2 z.2.2
  have hF0' := hF0 p.1
  have hr0' := hr0 p.1
  field_simp
  ring

/-! ### The derivative of the Christoffel form -/

theorem contDiff_deriv' {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) := by
  simpa using hf.iterate_deriv 1

theorem hasDerivAt_self' {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (s : ℝ) :
    HasDerivAt f (deriv f s) s := ((hf.differentiable (by simp)) s).hasDerivAt

/-- **`∂_u Γ(v, w)`** for the doubly warped metric. -/
theorem fderiv_wΓ (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r) (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁) (hΓ₂s : ContDiff ℝ ∞ Γ₂)
    (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0) (p u v w : Ew) :
    fderiv ℝ (fun q => wΓ F r H₁ H₂ Γ₁ Γ₂ q v w) p u =
      (-(deriv F p.1 ^ 2 + F p.1 * deriv (deriv F) p.1) * u.1 * H₁ p.2.1 v.2.1 w.2.1
          - F p.1 * deriv F p.1 * fderiv ℝ H₁ p.2.1 u.2.1 v.2.1 w.2.1
          - (deriv r p.1 ^ 2 + r p.1 * deriv (deriv r) p.1) * u.1 * H₂ p.2.2 v.2.2 w.2.2
          - r p.1 * deriv r p.1 * fderiv ℝ H₂ p.2.2 u.2.2 v.2.2 w.2.2,
        (((deriv (deriv F) p.1 * F p.1 - deriv F p.1 * deriv F p.1) / F p.1 ^ 2) * u.1) •
            (v.1 • w.2.1 + w.1 • v.2.1) + fderiv ℝ Γ₁ p.2.1 u.2.1 v.2.1 w.2.1,
        (((deriv (deriv r) p.1 * r p.1 - deriv r p.1 * deriv r p.1) / r p.1 ^ 2) * u.1) •
            (v.1 • w.2.2 + w.1 • v.2.2) + fderiv ℝ Γ₂ p.2.2 u.2.2 v.2.2 w.2.2) := by
  have hfst : HasFDerivAt (fun y : Ew => y.1) (ContinuousLinearMap.fst ℝ ℝ (F₁ × F₂)) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun y : Ew => y.2.1)
      ((ContinuousLinearMap.fst ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂))) p :=
    hasFDerivAt_fst.comp p hasFDerivAt_snd
  have hy : HasFDerivAt (fun y : Ew => y.2.2)
      ((ContinuousLinearMap.snd ℝ F₁ F₂).comp (ContinuousLinearMap.snd ℝ ℝ (F₁ × F₂))) p :=
    hasFDerivAt_snd.comp p hasFDerivAt_snd
  have hFd := hasDerivAt_self' hF p.1
  have hF'd := hasDerivAt_self' (contDiff_deriv' hF) p.1
  have hrd := hasDerivAt_self' hr p.1
  have hr'd := hasDerivAt_self' (contDiff_deriv' hr) p.1
  have hH1d : HasFDerivAt H₁ (fderiv ℝ H₁ p.2.1) p.2.1 :=
    ((hH₁.differentiable (by simp)) p.2.1).hasFDerivAt
  have hH2d : HasFDerivAt H₂ (fderiv ℝ H₂ p.2.2) p.2.2 :=
    ((hH₂.differentiable (by simp)) p.2.2).hasFDerivAt
  have hG1d : HasFDerivAt Γ₁ (fderiv ℝ Γ₁ p.2.1) p.2.1 :=
    ((hΓ₁s.differentiable (by simp)) p.2.1).hasFDerivAt
  have hG2d : HasFDerivAt Γ₂ (fderiv ℝ Γ₂ p.2.2) p.2.2 :=
    ((hΓ₂s.differentiable (by simp)) p.2.2).hasFDerivAt
  have tH1 : HasFDerivAt (fun q : Ew => H₁ q.2.1 v.2.1 w.2.1) _ p :=
    ((hH1d.comp p hx).clm_apply (hasFDerivAt_const v.2.1 p)).clm_apply
      (hasFDerivAt_const w.2.1 p)
  have tH2 : HasFDerivAt (fun q : Ew => H₂ q.2.2 v.2.2 w.2.2) _ p :=
    ((hH2d.comp p hy).clm_apply (hasFDerivAt_const v.2.2 p)).clm_apply
      (hasFDerivAt_const w.2.2 p)
  have tG1 : HasFDerivAt (fun q : Ew => Γ₁ q.2.1 v.2.1 w.2.1) _ p :=
    ((hG1d.comp p hx).clm_apply (hasFDerivAt_const v.2.1 p)).clm_apply
      (hasFDerivAt_const w.2.1 p)
  have tG2 : HasFDerivAt (fun q : Ew => Γ₂ q.2.2 v.2.2 w.2.2) _ p :=
    ((hG2d.comp p hy).clm_apply (hasFDerivAt_const v.2.2 p)).clm_apply
      (hasFDerivAt_const w.2.2 p)
  have fF : HasFDerivAt (fun q : Ew => F q.1 * deriv F q.1) _ p :=
    (hFd.mul hF'd).comp_hasFDerivAt p hfst
  have fr : HasFDerivAt (fun q : Ew => r q.1 * deriv r q.1) _ p :=
    (hrd.mul hr'd).comp_hasFDerivAt p hfst
  have qF : HasFDerivAt (fun q : Ew => deriv F q.1 / F q.1) _ p :=
    (hF'd.div hFd (hF0 p.1)).comp_hasFDerivAt p hfst
  have qr : HasFDerivAt (fun q : Ew => deriv r q.1 / r q.1) _ p :=
    (hr'd.div hrd (hr0 p.1)).comp_hasFDerivAt p hfst
  have hA : HasFDerivAt (fun q : Ew =>
      -(F q.1 * deriv F q.1) * H₁ q.2.1 v.2.1 w.2.1 - r q.1 * deriv r q.1 * H₂ q.2.2 v.2.2 w.2.2)
      _ p := (fF.neg.mul tH1).sub (fr.mul tH2)
  have hB : HasFDerivAt (fun q : Ew =>
      (deriv F q.1 / F q.1) • (v.1 • w.2.1 + w.1 • v.2.1) + Γ₁ q.2.1 v.2.1 w.2.1) _ p :=
    (qF.smul_const (v.1 • w.2.1 + w.1 • v.2.1)).add tG1
  have hC : HasFDerivAt (fun q : Ew =>
      (deriv r q.1 / r q.1) • (v.1 • w.2.2 + w.1 • v.2.2) + Γ₂ q.2.2 v.2.2 w.2.2) _ p :=
    (qr.smul_const (v.1 • w.2.2 + w.1 • v.2.2)).add tG2
  have htot : HasFDerivAt (fun q => wΓ F r H₁ H₂ Γ₁ Γ₂ q v w) _ p := hA.prodMk (hB.prodMk hC)
  rw [htot.fderiv]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, map_zero, zero_add, add_zero, Function.comp_apply, Pi.neg_apply]
    ring
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, map_zero, zero_add, add_zero, Function.comp_apply]
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, map_zero, zero_add, add_zero, Function.comp_apply]

theorem contDiff_wΓ (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r) (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁) (hΓ₂s : ContDiff ℝ ∞ Γ₂)
    (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0) (v w : Ew) :
    ContDiff ℝ ∞ fun q => wΓ F r H₁ H₂ Γ₁ Γ₂ q v w := by
  have cF := hF.comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := F₁ × F₂))
  have cF' := (contDiff_deriv' hF).comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := F₁ × F₂))
  have cr := hr.comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := F₁ × F₂))
  have cr' := (contDiff_deriv' hr).comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := F₁ × F₂))
  have cx : ContDiff ℝ ∞ fun q : Ew => q.2.1 := contDiff_fst.comp contDiff_snd
  have cy : ContDiff ℝ ∞ fun q : Ew => q.2.2 := contDiff_snd.comp contDiff_snd
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_)
  · exact ((cF.mul cF').neg.mul (((hH₁.comp cx).clm_apply contDiff_const).clm_apply
      contDiff_const)).sub ((cr.mul cr').mul (((hH₂.comp cy).clm_apply contDiff_const).clm_apply
      contDiff_const))
  · exact ((cF'.div cF fun q => hF0 q.1).smul contDiff_const).add
      (((hΓ₁s.comp cx).clm_apply contDiff_const).clm_apply contDiff_const)
  · exact ((cr'.div cr fun q => hr0 q.1).smul contDiff_const).add
      (((hΓ₂s.comp cy).clm_apply contDiff_const).clm_apply contDiff_const)

/-! ### The curvature -/

omit [FiniteDimensional ℝ F₁] in
/-- The Christoffel form of a symmetric metric is symmetric. -/
theorem Γ_symm {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
    {H : K → K →L[ℝ] K →L[ℝ] ℝ} {Γ : K → K →L[ℝ] K →L[ℝ] K} (hs : IsSymm (cmet H))
    (hp : IsPosDef (cmet H)) (hH : ContDiff ℝ ∞ H) (hΓ : ∀ x a b c, H x (Γ x a b) c = kz H x a b c)
    (x a b : K) : Γ x a b = Γ x b a := by
  refine eq_of_G_eq (x := x) hp.isNondegenerate fun c => ?_
  rw [hΓ, hΓ, kz, kz, fderiv_symm hs ((hH.differentiable (by simp)) x) c a b]
  ring

/-- The sectional-curvature numerator `Rm(ξ,ζ,ζ,ξ)` of a fibre metric, in coordinates. -/
def fibreRm {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (H : K → K →L[ℝ] K →L[ℝ] ℝ) (Γ : K → K →L[ℝ] K →L[ℝ] K) (x ξ ζ : K) : ℝ :=
  H x (fderiv ℝ Γ x ξ ζ ζ - fderiv ℝ Γ x ζ ξ ζ + Γ x ξ (Γ x ζ ζ) - Γ x ζ (Γ x ξ ζ)) ξ

theorem contDiff2_wG (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r) (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) : ContDiff ℝ 2 (wG F r H₁ H₂) :=
  (contDiff_wG hF hr hH₁ hH₂).of_le (WithTop.coe_le_coe.mpr le_top)

set_option maxHeartbeats 1000000 in
/-- **The curvature of the doubly warped metric** (`eq:fullcurvature`, in coordinates). At
`p = (s, x, y)`, for `u = (λ, X, U)` and `v = (μ, Y, V)`, if the fibres have sectional curvature
`κ₁` on `X ∧ Y` and `κ₂` on `U ∧ V`, then
`Rm(u,v,v,u) = −(F''/F)|λY−μX|² − (r''/r)|λV−μU|² + ((κ₁−F'²)/F²)|X∧Y|²
  + ((κ₂−r'²)/r²)|U∧V|² − (F'r'/(Fr))|X⊗V−Y⊗U|²`,
with the norms of the scaled components `|X|² = F²H₁(X,X)`, `|U|² = r²H₂(U,U)`. -/
theorem riemannTensorAt_wG (hF : ContDiff ℝ ∞ F) (hr : ContDiff ℝ ∞ r)
    (hH₁ : ContDiff ℝ ∞ H₁) (hH₂ : ContDiff ℝ ∞ H₂) (hΓ₁s : ContDiff ℝ ∞ Γ₁)
    (hΓ₂s : ContDiff ℝ ∞ Γ₂) (hF0 : ∀ s, F s ≠ 0) (hr0 : ∀ s, r s ≠ 0)
    (hs₁ : IsSymm (cmet H₁)) (hs₂ : IsSymm (cmet H₂)) (hp₁ : IsPosDef (cmet H₁))
    (hp₂ : IsPosDef (cmet H₂))
    (hΓ₁ : ∀ x ξ ζ c, H₁ x (Γ₁ x ξ ζ) c = kz H₁ x ξ ζ c)
    (hΓ₂ : ∀ y η θ κ, H₂ y (Γ₂ y η θ) κ = kz H₂ y η θ κ) (p u v : Ew) (κ₁ κ₂ : ℝ)
    (hK₁ : fibreRm H₁ Γ₁ p.2.1 u.2.1 v.2.1 = κ₁ * (H₁ p.2.1 u.2.1 u.2.1 * H₁ p.2.1 v.2.1 v.2.1 -
      H₁ p.2.1 u.2.1 v.2.1 ^ 2))
    (hK₂ : fibreRm H₂ Γ₂ p.2.2 u.2.2 v.2.2 = κ₂ * (H₂ p.2.2 u.2.2 u.2.2 * H₂ p.2.2 v.2.2 v.2.2 -
      H₂ p.2.2 u.2.2 v.2.2 ^ 2)) :
    riemannTensorAt (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂).isNondegenerate
      (isContMDiffMetricSection_cmet (contDiff2_wG hF hr hH₁ hH₂)) p
      (toTSv p u) (toTSv p v) (toTSv p v) (toTSv p u) =
    -(deriv (deriv F) p.1 / F p.1) *
        (F p.1 ^ 2 * H₁ p.2.1 (u.1 • v.2.1 - v.1 • u.2.1) (u.1 • v.2.1 - v.1 • u.2.1))
      - (deriv (deriv r) p.1 / r p.1) *
        (r p.1 ^ 2 * H₂ p.2.2 (u.1 • v.2.2 - v.1 • u.2.2) (u.1 • v.2.2 - v.1 • u.2.2))
      + (κ₁ - deriv F p.1 ^ 2) / F p.1 ^ 2 * (F p.1 ^ 4 * (H₁ p.2.1 u.2.1 u.2.1 *
          H₁ p.2.1 v.2.1 v.2.1 - H₁ p.2.1 u.2.1 v.2.1 ^ 2))
      + (κ₂ - deriv r p.1 ^ 2) / r p.1 ^ 2 * (r p.1 ^ 4 * (H₂ p.2.2 u.2.2 u.2.2 *
          H₂ p.2.2 v.2.2 v.2.2 - H₂ p.2.2 u.2.2 v.2.2 ^ 2))
      - deriv F p.1 * deriv r p.1 / (F p.1 * r p.1) * (F p.1 ^ 2 * r p.1 ^ 2 *
          (H₁ p.2.1 u.2.1 u.2.1 * H₂ p.2.2 v.2.2 v.2.2 + H₁ p.2.1 v.2.1 v.2.1 *
            H₂ p.2.2 u.2.2 u.2.2 - 2 * H₁ p.2.1 u.2.1 v.2.1 * H₂ p.2.2 u.2.2 v.2.2)) := by
  have hG2 : ContDiff ℝ 2 (wG F r H₁ H₂) := contDiff2_wG hF hr hH₁ hH₂
  have hΓ := wG_wΓ (Γ₁ := Γ₁) (Γ₂ := Γ₂) hF hr hH₁ hH₂ hF0 hr0 hs₁ hs₂ hΓ₁ hΓ₂
  have cΓ : ∀ a b, ContDiffAt ℝ 1 (fun q => wΓ F r H₁ H₂ Γ₁ Γ₂ q a b) p := fun a b =>
    ((contDiff_wΓ hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0 a b).of_le (by exact_mod_cast (le_top : ((1 : ℕ∞)) ≤ ⊤))).contDiffAt
  rw [riemannTensorAt_cmet (isSymm_wG hs₁ hs₂) (isPosDef_wG hF0 hr0 hp₁ hp₂).isNondegenerate hG2
    hΓ p u v v u (cΓ u v) (cΓ v v)]
  rw [fderiv_wΓ hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0, fderiv_wΓ hF hr hH₁ hH₂ hΓ₁s hΓ₂s hF0 hr0]
  obtain ⟨s, x, y⟩ := p
  obtain ⟨lam, X, U⟩ := u
  obtain ⟨mu, Y, V⟩ := v
  -- symmetry of the fibre Christoffel forms, and the Koszul identities for the single terms
  have σ₁ := Γ_symm hs₁ hp₁ hH₁ hΓ₁ x Y X
  have σ₂ := Γ_symm hs₂ hp₂ hH₂ hΓ₂ y V U
  simp only [wG_apply, wΓ, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, map_add, map_sub, map_smul,
    map_neg, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul, σ₁, σ₂]
  simp only [fibreRm, map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply] at hK₁ hK₂
  have hH1d : DifferentiableAt ℝ H₁ x := (hH₁.differentiable (by simp)) x
  have hH2d : DifferentiableAt ℝ H₂ y := (hH₂.differentiable (by simp)) y
  rw [G_symm hs₁ x X (Γ₁ x Y Y), hΓ₁, G_symm hs₁ x Y (Γ₁ x X Y), hΓ₁,
    G_symm hs₂ y U (Γ₂ y V V), hΓ₂, G_symm hs₂ y V (Γ₂ y U V), hΓ₂]
  simp only [hΓ₁, hΓ₂, kz]
  simp only [hΓ₁, hΓ₂, kz] at hK₁ hK₂
  rw [fderiv_symm hs₁ hH1d Y Y X, fderiv_symm hs₂ hH2d V V U, G_symm hs₁ x Y X,
    G_symm hs₂ y V U]
  have hF0' := hF0 s
  have hr0' := hr0 s
  field_simp
  linear_combination (2 * F s ^ 2) * hK₁ + (2 * r s ^ 2) * hK₂

end Warped

end

end ExoticSpheres8And10
