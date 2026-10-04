/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.BaseCurvature

/-! # The Hessian, the warping function, and D2's `N ≥ ν`

* `hessF g φ X Y x = X(Yφ)(x) − (∇_X Y)φ(x)`, with `RiemannianGeometry`'s Levi-Civita connection `∇` of `g`. This
  is the Hessian of `φ` evaluated on vector fields.
* `hessF_frame_sum`: in a smooth `g`-orthonormal frame `e` on `U`, for `X = Σ x_i e_i` with
  constant coefficients, `hessF φ X X = Σ x_i x_j H_{ij}`, where
  `H_{ij} = e_i(e_j φ) + Σ_k Γ^B_{ikj} e_k φ`.
* `rOf ε φ = √ε e^{εφ/2}`, so that `r² = ε e^{εφ}`; then `ϑ_i = (ε/2) e_iφ` and
  `N_{ij} = −(ε/2) H_{ij} − (ε²/4) φ_i φ_j`.
* `NB_quad_ge`: from `−Hess φ ≥ Λ g` and `|dφ|² ≤ D²`, `N ≥ εΛ/2 − ε²D²/4`. This is D2's `hν`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff

noncomputable section

section Hess

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] {n : ℕ}

variable (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) in
/-- **The Hessian on vector fields**: `Hess φ (X, Y) = X(Yφ) − (∇_X Y)φ`. -/
def hessF (φ : B → ℝ) (X Y : Π x : B, TangentSpace I x) (x : B) : ℝ :=
  mvfderiv I (fun z => mvfderiv I φ z (Y z)) x (X x) - mvfderiv I φ x (leviCivita g Y x (X x))

variable (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
  (e : Fin n → Π b : B, TangentSpace I b) in
/-- The frame Hessian `H_{ij} = e_i(e_j φ) + Σ_k Γ^B_{ikj} e_k φ`. -/
def HB (φ : B → ℝ) (b : B) (i j : Fin n) : ℝ :=
  mvfderiv I (fun z => mvfderiv I φ z (e j z)) b (e i b) +
    ∑ k, ΓBf (S3Connection.cBb g e) i k j b * mvfderiv I φ b (e k b)

/-- `√ε e^{εφ/2}`: the fibre scale with `r² = ε e^{εφ}`. -/
def rOf (ε : ℝ) (φ : B → ℝ) (b : B) : ℝ := √ε * Real.exp (ε * φ b / 2)

theorem mvfderiv_sum_const_mul {f : Fin n → B → ℝ} {b : B}
    (hf : ∀ j, MDifferentiableAt I 𝓘(ℝ) (f j) b) (c : Fin n → ℝ) (v : TangentSpace I b) :
    mvfderiv I (fun z => ∑ j, c j * f j z) b v = ∑ j, c j * mvfderiv I (f j) b v := by
  classical
  have key : ∀ s : Finset (Fin n), MDifferentiableAt I 𝓘(ℝ) (fun z => ∑ j ∈ s, c j * f j z) b ∧
      mvfderiv I (fun z => ∑ j ∈ s, c j * f j z) b v = ∑ j ∈ s, c j * mvfderiv I (f j) b v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨mdifferentiableAt_const, mvfderiv_const_real 0 b v⟩
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hd : MDifferentiableAt I 𝓘(ℝ) (fun z => c a * f a z) b :=
        mdifferentiableAt_const.mul (hf a)
      refine ⟨hd.add ih.1, ?_⟩
      have h := (hd.hasMFDerivAt.add ih.1.hasMFDerivAt).mfderiv
      have h2 : mvfderiv I (fun z => c a * f a z + ∑ j ∈ s, c j * f j z) b v =
          mvfderiv I (fun z => c a * f a z) b v +
            mvfderiv I (fun z => ∑ j ∈ s, c j * f j z) b v := congrArg (fun L => L v) h
      rw [h2, ih.2, mvfderiv_const_mul_real (hf a)]
  exact (key Finset.univ).2

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B} {φ : B → ℝ}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g) (hUo : IsOpen U)
  (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
  (horthB : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) (hn : finrank ℝ E = n)
  (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)

include hφ he in
theorem mdiffAt_dφ_e {b : B} (hb : b ∈ U) (j : Fin n) :
    MDifferentiableAt I 𝓘(ℝ) (fun z => mvfderiv I φ z (e j z)) b :=
  (S3Connection.contMDiffAt_mvfderiv_field (Eventually.of_forall fun b' => hφ b')
    (he j b hb)).mdifferentiableAt (by simp)

include hsg hpg hgs hUo he horthB hn hφ in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The Hessian in an orthonormal frame**, for a constant-coefficient field. -/
theorem hessF_frame_sum {b : B} (hb : b ∈ U) (x : Fin n → ℝ) :
    hessF g φ (fun z => ∑ i, x i • e i z) (fun z => ∑ i, x i • e i z) b =
      ∑ i, ∑ j, x i * x j * HB g e φ b i j := by
  have hgm : IsMDiffMetric E g :=
    (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω).isMDiffMetric (by simp)
  have hFd : ∀ α, ∀ y ∈ U, MDiffAt (T% (e α)) y :=
    fun α y hy => (he α y hy).mdifferentiableAt (by simp)
  have hbr : ∀ α β, ∀ y ∈ U, mlieBracket I (e α) (e β) y =
      ∑ γ, S3Connection.cBb g e α β γ y • e γ y :=
    fun α β y hy => span_base_frame hpg horthB hn hy _
  have hLCf : ∀ i j, leviCivita g (e j) b (e i b) =
      ∑ k, frameΓ (S3Connection.cBb g e) i j k b • e k b := fun i j =>
    leviCivita_frame_loc hsg hpg.isNondegenerate hgm hUo hFd (fun α β y hy => horthB y hy α β)
      (fun y hy w => span_base_frame hpg horthB hn hy w) hbr i j hb
  have hX : (fun z => ∑ i, x i • e i z) = ∑ i, (fun _ : B => x i) • e i := by
    funext z; simp only [Finset.sum_apply, Pi.smul_apply']
  have hLC : ∀ w : TangentSpace I b, leviCivita g (fun z => ∑ i, x i • e i z) b w =
      ∑ i, x i • leviCivita g (e i) b w := by
    intro w
    rw [hX, leviCivita_sum_smul hsg hpg.isNondegenerate hgm Finset.univ (fun i _ => x i) e
      (fun i => mdifferentiableAt_const) (fun i => hFd i b hb), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      mvfderiv_const_real (x i) b w, zero_smul, add_zero, ContinuousLinearMap.smul_apply]
  have h1 : (fun z => mvfderiv I φ z (∑ i, x i • e i z)) =
      fun z => ∑ j, x j * mvfderiv I φ z (e j z) := by
    funext z; simp only [map_sum, map_smul, smul_eq_mul]
  have hT1 : mvfderiv I (fun z => mvfderiv I φ z (∑ i, x i • e i z)) b (∑ i, x i • e i b) =
      ∑ i, ∑ j, x i * x j * mvfderiv I (fun z => mvfderiv I φ z (e j z)) b (e i b) := by
    rw [h1, mvfderiv_sum_const_mul (fun j => mdiffAt_dφ_e he hφ hb j) x]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hT2 : mvfderiv I φ b (leviCivita g (fun z => ∑ i, x i • e i z) b (∑ i, x i • e i b)) =
      ∑ i, ∑ j, x i * x j *
        ∑ k, frameΓ (S3Connection.cBb g e) i j k b * mvfderiv I φ b (e k b) := by
    simp only [map_sum, map_smul, hLC, hLCf, smul_eq_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have hanti : ∀ i j k, ΓBf (S3Connection.cBb g e) i k j b =
      -frameΓ (S3Connection.cBb g e) i j k b := by
    intro i j k
    simp only [ΓBf, frameΓ, S3Connection.cBb_anti k j i b]
    ring
  unfold hessF
  rw [hT1, hT2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [HB, hanti, neg_mul, Finset.sum_neg_distrib]
  ring

/-! ### The fibre scale `r = √ε e^{εφ/2}` -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem rOf_pos {ε : ℝ} (hε : 0 < ε) (b : B) : 0 < rOf ε φ b :=
  mul_pos (Real.sqrt_pos.2 hε) (Real.exp_pos _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem rOf_sq {ε : ℝ} (hε : 0 < ε) (b : B) : rOf ε φ b ^ 2 = ε * Real.exp (ε * φ b) := by
  unfold rOf
  rw [mul_pow, Real.sq_sqrt hε.le, sq, ← Real.exp_add]
  congr 2
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
include hφ in
theorem contMDiff_rOf (ε : ℝ) : ContMDiff I 𝓘(ℝ) ∞ (rOf ε φ) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => √ε * Real.exp (ε * t / 2)) := by fun_prop
  exact h.contMDiff.comp hφ

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
include hφ in
theorem mvfderiv_rOf (ε : ℝ) (b : B) (v : TangentSpace I b) :
    mvfderiv I (rOf ε φ) b v = rOf ε φ b * (ε / 2 * mvfderiv I φ b v) := by
  have hd : HasDerivAt (fun t : ℝ => √ε * Real.exp (ε * t / 2))
      (√ε * (Real.exp (ε * φ b / 2) * (ε / 2))) (φ b) := by
    have h := (((hasDerivAt_id (φ b)).const_mul ε).div_const 2).exp.const_mul (√ε)
    simp only [id_eq, mul_one] at h
    exact h
  rw [show rOf ε φ = (fun t : ℝ => √ε * Real.exp (ε * t / 2)) ∘ φ from rfl,
    mvfderiv_comp_apply hd.differentiableAt.mdifferentiableAt ((hφ b).mdifferentiableAt (by simp)),
    mvfderiv_vs, hd.hasFDerivAt.fderiv]
  show (mvfderiv I φ b v) * (√ε * (Real.exp (ε * φ b / 2) * (ε / 2))) = _
  simp only [Function.comp_apply]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
include hφ in
/-- `ϑ_i = e_i(r)/r = (ε/2) e_iφ`. -/
theorem ϑb_rOf {ε : ℝ} (hε : 0 < ε) (i : Fin n) (b : B) :
    S3Connection.ϑb (rOf ε φ) e i b = ε / 2 * mvfderiv I φ b (e i b) := by
  unfold S3Connection.ϑb
  rw [mvfderiv_rOf hφ, mul_div_right_comm, div_self (rOf_pos hε b).ne', one_mul]

include hφ he in
theorem dϑB_rOf {ε : ℝ} (hε : 0 < ε) {b : B} (hb : b ∈ U) (k i : Fin n) :
    S3Connection.dϑB e (rOf ε φ) b k i =
      ε / 2 * mvfderiv I (fun z => mvfderiv I φ z (e i z)) b (e k b) := by
  unfold S3Connection.dϑB
  have h : S3Connection.ϑb (rOf ε φ) e i = fun z => ε / 2 * mvfderiv I φ z (e i z) :=
    funext fun z => ϑb_rOf hφ hε i z
  rw [h, mvfderiv_const_mul_real (mdiffAt_dφ_e he hφ hb i)]

include hφ he in
/-- `N_{ij} = −(ε/2) H_{ij} − (ε²/4) φ_iφ_j`. -/
theorem NB_rOf {ε : ℝ} (hε : 0 < ε) {b : B} (hb : b ∈ U) (i j : Fin n) :
    S3Connection.NB g e (rOf ε φ) b i j =
      -(ε / 2) * HB g e φ b i j - ε ^ 2 / 4 * (mvfderiv I φ b (e i b) * mvfderiv I φ b (e j b)) := by
  simp only [S3Connection.NB, Nf, dϑB_rOf he hφ hε hb, ϑb_rOf hφ hε, HB]
  rw [show ∑ k, ΓBf (S3Connection.cBb g e) i k j b * (ε / 2 * mvfderiv I φ b (e k b)) =
      ε / 2 * ∑ k, ΓBf (S3Connection.cBb g e) i k j b * mvfderiv I φ b (e k b) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring]
  ring

include hsg hpg hgs hUo he horthB hn hφ in
/-- **D2's `N ≥ ν`**, with `ν = εΛ/2 − ε²D²/4`, from `−Hess φ ≥ Λ g` and `|dφ|² ≤ D²`. -/
theorem NB_quad_ge {ε Λ D : ℝ} (hε : 0 < ε)
    (hHess : ∀ (b : B) (X : Π x : B, TangentSpace I x), ContMDiffAt I I.tangent ∞ (T% X) b →
      Λ * g b (X b) (X b) ≤ -hessF g φ X X b)
    {b : B} (hb : b ∈ U) (hD : ∑ k, mvfderiv I φ b (e k b) ^ 2 ≤ D ^ 2) (x : Fin n → ℝ) :
    (ε * Λ / 2 - ε ^ 2 * D ^ 2 / 4) * ∑ i, x i ^ 2 ≤
      ∑ i, ∑ j, S3Connection.NB g e (rOf ε φ) b i j * x i * x j := by
  set X : Π z : B, TangentSpace I z := fun z => ∑ i, x i • e i z with hXdef
  have hXs : ContMDiffAt I I.tangent ∞ (T% X) b :=
    ContMDiffAt.sum_section (t := fun i z => x i • e i z) fun i _ =>
      contMDiffAt_const.smul_section (he i b hb)
  have hH := hHess b X hXs
  rw [hXdef, hessF_frame_sum hsg hpg hgs hUo he horthB hn hφ hb x,
    pairing_base_sum horthB hb] at hH
  set φk : Fin n → ℝ := fun k => mvfderiv I φ b (e k b)
  have e1 : ∑ i, ∑ j, S3Connection.NB g e (rOf ε φ) b i j * x i * x j =
      -(ε / 2) * (∑ i, ∑ j, x i * x j * HB g e φ b i j) - ε ^ 2 / 4 * (∑ i, φk i * x i) ^ 2 := by
    simp only [NB_rOf he hφ hε hb]
    rw [show (∑ i, φk i * x i) ^ 2 = ∑ i, ∑ j, φk i * x i * (φk j * x j) by
      rw [sq, Finset.sum_mul_sum], Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [φk]; ring
  have hS : Prop31Algebra.dot x x = ∑ i, x i ^ 2 := by simp only [Prop31Algebra.dot, sq]
  have hx : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ φk x
  have a1 : ε / 2 * (Λ * ∑ i, x i ^ 2) ≤ ε / 2 * -(∑ i, ∑ j, x i * x j * HB g e φ b i j) :=
    mul_le_mul_of_nonneg_left (hS ▸ hH) (by positivity)
  have a2 : (∑ i, φk i * x i) ^ 2 ≤ D ^ 2 * ∑ i, x i ^ 2 :=
    cs.trans (mul_le_mul_of_nonneg_right hD hx)
  have a3 : ε ^ 2 / 4 * (∑ i, φk i * x i) ^ 2 ≤ ε ^ 2 / 4 * (D ^ 2 * ∑ i, x i ^ 2) :=
    mul_le_mul_of_nonneg_left a2 (by positivity)
  rw [e1]
  nlinarith [a1, a3]

end Hess

end

end ExoticSpheres8And10
