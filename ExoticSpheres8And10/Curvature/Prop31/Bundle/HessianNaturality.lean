/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Intrinsic
import ExoticSpheres8And10.Geometry.Naturality

/-! # The Hessian under local isometries, and the height function of the round metric

* `hessF_mpullback`: for a local isometry `f : M → N`,
  `Hess^M(φ ∘ f)(f^*X, f^*Y) = Hess^N φ(X, Y) ∘ f`.
* `hessF_cmet_const`: for a coordinate metric `cmet G` on a vector space, with Christoffel form
  `Γ`, and constant fields, `Hess φ(w, w) = D²φ(w, w) − Dφ(Γ(w, w))`.
* `hess_hR`: for the round metric `HR = (1 + |x|²/4)⁻²|dx|²` and the height function
  `hR = (1 − |x|²/4)/(1 + |x|²/4)` (`= cos t`), `Hess hR = −hR · HR`. This is the identity
  `(cos t)'' = −cos t` of the unit sphere.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section Natural

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] {H' : Type} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {f : M → N}
  {gM : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {gN : Π y : N, TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ}

/-- **The Hessian is natural under local isometries.** -/
theorem hessF_mpullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsMDiffMetric E gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsMDiffMetric E' gN)
    {φ : N → ℝ} (hφ : ContMDiff I' 𝓘(ℝ) ∞ φ) {X Y : Π y : N, TangentSpace I' y} {x : M}
    (hY : ∀ᶠ z in 𝓝 (f x), ContMDiffAt I' I'.tangent ∞ (T% Y) z) :
    hessF gM (φ ∘ f) (mpullback I I' f X) (mpullback I I' f Y) x = hessF gN φ X Y (f x) := by
  have hφd : ∀ z, MDifferentiableAt I' 𝓘(ℝ) φ z := fun z => (hφ z).mdifferentiableAt (by simp)
  have hfd : ∀ z, MDifferentiableAt I I' f z := fun z => (hf z).mdifferentiableAt (by simp)
  have hinner : (fun z => mvfderiv I (φ ∘ f) z (mpullback I I' f Y z)) =
      (fun w => mvfderiv I' φ w (Y w)) ∘ f := by
    funext z
    rw [mvfderiv_comp_apply (hφd _) (hfd z), mfderiv_mpullback hfi]
    rfl
  have hYφ : MDifferentiableAt I' 𝓘(ℝ) (fun w => mvfderiv I' φ w (Y w)) (f x) :=
    (S3Connection.contMDiffAt_mvfderiv_field (Eventually.of_forall fun w => hφ w)
      hY.self_of_nhds).mdifferentiableAt (by simp)
  have hLC := leviCivita_mpullback_eq hf hfi hpull hsM hndM hgM hsN hndN hgN (X := X)
    (hY.self_of_nhds.mdifferentiableAt (by simp))
  unfold hessF
  rw [hinner, mvfderiv_comp_apply hYφ (hfd x), mfderiv_mpullback hfi, hLC,
    mvfderiv_comp_apply (hφd _) (hfd x), mfderiv_mpullback hfi]

end Natural

section Coord

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- `Hess φ(w, w) = D²φ(w, w) − Dφ(Γ(w, w))` for the round metric and constant fields. -/
theorem hessF_cmet_const {φ : K → ℝ} (hφ : ContDiff ℝ 2 φ) (w x : K) :
    hessF (cmet (HR (K := K))) φ (toTS fun _ => w) (toTS fun _ => w) x =
      fderiv ℝ (fun z => fderiv ℝ φ z w) x w - fderiv ℝ φ x (ΓR x w w) := by
  have hLC := leviCivita_cmet (G := HR (K := K)) isSymm_HR isPosDef_HR.isNondegenerate
    (contDiff_HR.of_le (by norm_num)) (Γ := fun z v u => ΓR z v u) (x := x)
    (fun v u z => HR_ΓR x v u z) (X := fun _ => w) (Y := fun _ => w) contDiffAt_const
    contDiffAt_const
  have hinner : (fun z => mvfderiv 𝓘(ℝ, K) φ z ((toTS fun _ => w) z)) =
      fun z => fderiv ℝ φ z w := funext fun z => mvfderiv_model φ z w
  unfold hessF
  rw [hinner]
  show mvfderiv 𝓘(ℝ, K) (fun z => fderiv ℝ φ z w) x (toTSv x w) -
    mvfderiv 𝓘(ℝ, K) φ x (toTSv x (fromTS (leviCivita (cmet HR) (toTS fun _ => w) x
      (toTSv x w)))) = _
  rw [hLC, mvfderiv_model, mvfderiv_model]
  simp

/-- The height function `hR = (1 − |x|²/4)/(1 + |x|²/4)` (`= cos t` on the unit sphere). -/
def hR (x : K) : ℝ := (1 - ‖x‖ ^ 2 / 4) / (1 + ‖x‖ ^ 2 / 4)

/-- The profile `F(s) = (1 − s/4)/(1 + s/4)` and its derivatives. -/
def FhR (s : ℝ) : ℝ := (1 - s / 4) / (1 + s / 4)
def FhR1 (s : ℝ) : ℝ := -(1 / (2 * (1 + s / 4) ^ 2))
def FhR2 (s : ℝ) : ℝ := 1 / (4 * (1 + s / 4) ^ 3)

theorem hasDerivAt_FhR {s : ℝ} (hs : 0 ≤ s) : HasDerivAt FhR (FhR1 s) s := by
  have hq : (1 + s / 4) ≠ 0 := by positivity
  have h := ((hasDerivAt_id s).div_const 4 |>.const_sub 1).div
    ((hasDerivAt_id s).div_const 4 |>.const_add 1) hq
  have e : FhR = fun y => (1 - id y / 4) / (1 + id y / 4) := rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [FhR1, id]
  field_simp
  ring

theorem hasDerivAt_FhR1 {s : ℝ} (hs : 0 ≤ s) : HasDerivAt FhR1 (FhR2 s) s := by
  have hq : (2 * (1 + s / 4) ^ 2) ≠ 0 := by positivity
  have h := (((((hasDerivAt_id s).div_const 4).const_add 1).pow 2).const_mul 2).inv hq |>.neg
  have e : FhR1 = fun y => -(2 * (1 + id y / 4) ^ 2)⁻¹ := by
    funext y; rw [FhR1, one_div]; rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [FhR2, id, Pi.pow_apply]
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  field_simp
  ring

theorem hasFDerivAt_normsq (z : K) :
    HasFDerivAt (fun z : K => ‖z‖ ^ 2) (2 • innerSL ℝ z) z := by
  simpa using (hasFDerivAt_id z).norm_sq

theorem hasFDerivAt_hR (z : K) :
    HasFDerivAt (hR (K := K)) (FhR1 (‖z‖ ^ 2) • (2 • innerSL ℝ z)) z :=
  (hasDerivAt_FhR (sq_nonneg ‖z‖)).comp_hasFDerivAt (h₂ := FhR) z (hasFDerivAt_normsq z)

theorem fderiv_hR (z v : K) : fderiv ℝ hR z v = FhR1 (‖z‖ ^ 2) * (2 * ⟪z, v⟫) := by
  rw [(hasFDerivAt_hR z).fderiv]
  simp [smul_eq_mul]

theorem differentiable_hR : Differentiable ℝ (hR (K := K)) := fun z =>
  (hasFDerivAt_hR z).differentiableAt

theorem contDiff_hR : ContDiff ℝ ∞ (hR (K := K)) := by
  unfold hR
  have hq : ∀ x : K, 1 + ‖x‖ ^ 2 / 4 ≠ 0 := fun x => by positivity
  exact (contDiff_const.sub (contDiff_norm_sq ℝ |>.div_const 4)).div
    (contDiff_const.add (contDiff_norm_sq ℝ |>.div_const 4)) hq

theorem fderiv_hR_fun (w : K) :
    (fun z => fderiv ℝ hR z w) = fun z => FhR1 (‖z‖ ^ 2) * (2 * (innerSL ℝ w) z) :=
  funext fun z => by rw [fderiv_hR, innerSL_apply_apply, real_inner_comm]

theorem hasFDerivAt_dhR (x w : K) :
    HasFDerivAt (fun z => fderiv ℝ hR z w)
      (FhR1 (‖x‖ ^ 2) • ((2 : ℝ) • innerSL ℝ w) +
        (2 * (innerSL ℝ w) x) • (FhR2 (‖x‖ ^ 2) • (2 • innerSL ℝ x))) x := by
  have hd1 : HasFDerivAt (fun z : K => FhR1 (‖z‖ ^ 2)) (FhR2 (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x :=
    (hasDerivAt_FhR1 (sq_nonneg ‖x‖)).comp_hasFDerivAt (h₂ := FhR1) x (hasFDerivAt_normsq x)
  have hd2 : HasFDerivAt (fun z : K => 2 * (innerSL ℝ w) z) ((2 : ℝ) • innerSL ℝ w) x :=
    ((innerSL ℝ w).hasFDerivAt (x := x)).const_mul 2
  rw [fderiv_hR_fun]
  exact hd1.mul hd2

/-- **`Hess hR = −hR · HR`** in coordinates, for constant `w`. -/
theorem hess_hR (x w : K) :
    fderiv ℝ (fun z => fderiv ℝ hR z w) x w - fderiv ℝ hR x (ΓR x w w) =
      -(hR x * HR x w w) := by
  rw [(hasFDerivAt_dhR x w).fderiv, fderiv_hR]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, ΓR_apply, inner_add_right, inner_sub_right,
    real_inner_smul_right, HR_apply, gR, real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat]
  have hn : ⟪x, x⟫ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have hc : ⟪w, x⟫ = ⟪x, w⟫ := real_inner_comm x w
  rw [hn, hc]
  simp only [hR, FhR1, FhR2, ψR]
  have hq : (1 + ‖x‖ ^ 2 / 4) ≠ 0 := by positivity
  have hq2 : (2 + ‖x‖ ^ 2 / 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **`Hess(A·hR) = −A·hR·HR`.** -/
theorem hess_hRA (A : ℝ) (x w : K) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => A * hR y) z w) x w -
      fderiv ℝ (fun y => A * hR y) x (ΓR x w w) = -(A * (hR x * HR x w w)) := by
  have hfd : ∀ z, fderiv ℝ (fun y => A * hR y) z = A • fderiv ℝ hR z :=
    fun z => fderiv_const_mul (differentiable_hR (K := K) z) A
  have hfun : (fun z => fderiv ℝ (fun y => A * hR y) z w) = fun z => A * fderiv ℝ hR z w :=
    funext fun z => by rw [hfd]; rfl
  rw [hfun, fderiv_const_mul (hasFDerivAt_dhR x w).differentiableAt, hfd]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← mul_sub, hess_hR, mul_neg]

end Coord

end

end ExoticSpheres8And10
