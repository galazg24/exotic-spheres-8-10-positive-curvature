/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.SFF.Coordinates
import ExoticSpheres8And10.Geometry.Naturality

/-! # Naturality of the second fundamental form

For a local isometry `f : (M, g_M) → (N, g_N)` (smooth, invertible differential everywhere,
`g_M = f^*g_N`) and `h : N → ℝ`:

* `mfderiv_gradAt_pullback`: `df(grad_M (h ∘ f)) = grad_N h`;
* `unitNormal_pullback`: `ν_M(h ∘ f) = f^*ν_N(h)`;
* **`sff_pullback`**: `sff_M(h ∘ f)(v, w) = sff_N(h)(df v, df w)`.

Also, on one manifold:
* `unitNormal_comp_of_pos`, **`sff_comp_of_pos`**: the second fundamental form depends only on
  the level set and its side. `φ ∘ h` with `φ' > 0` has the same unit normal and the same `sff`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff

noncomputable section

section Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {f : M → N}
  {gM : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {gN : Π y : N, TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ}

theorem mfderiv_gradAt_pullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hndM : IsNondegenerate gM) (hndN : IsNondegenerate gN) {h : N → ℝ}
    (hh : ContMDiff I' 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    mfderiv I I' f x (gradAt hndM (h ∘ f) x) = gradAt hndN h (f x) := by
  refine eq_gradAt hndN h (f x) fun w => ?_
  obtain ⟨u, rfl⟩ : ∃ u, mfderiv I I' f x u = w := ⟨(mfderiv I I' f x).inverse w,
    (hfi x).self_apply_inverse w⟩
  rw [← hpull, g_gradAt, mvfderiv_comp' ((hh (f x)).mdifferentiableAt (by simp))
    ((hf x).mdifferentiableAt (by simp))]

theorem unitNormal_pullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hndM : IsNondegenerate gM) (hndN : IsNondegenerate gN) {h : N → ℝ}
    (hh : ContMDiff I' 𝓘(ℝ, ℝ) ∞ h) :
    unitNormal hndM (h ∘ f) = mpullback I I' f (unitNormal hndN h) := by
  funext x
  have hg := mfderiv_gradAt_pullback hf hfi hpull hndM hndN hh x
  rw [mpullback_apply]
  refine ((hfi x).inverse_apply_self _).symm.trans ?_
  congr 1
  simp only [unitNormal, map_smul, hg, hpull x, hg]

/-- **The second fundamental form is natural under local isometries.** -/
theorem sff_pullback (hf : ContMDiff I I' ∞ f)
    (hfi : ∀ x, (mfderiv I I' f x).IsInvertible)
    (hpull : ∀ x u v, gM x u v = gN (f x) (mfderiv I I' f x u) (mfderiv I I' f x v))
    (hsM : IsSymm gM) (hndM : IsNondegenerate gM) (hgM : IsMDiffMetric E gM)
    (hsN : IsSymm gN) (hndN : IsNondegenerate gN) (hgN : IsMDiffMetric E' gN) {h : N → ℝ}
    (hh : ContMDiff I' 𝓘(ℝ, ℝ) ∞ h) {x : M}
    (hν : MDiffAt (T% (unitNormal hndN h)) (f x)) (v w : TangentSpace I x) :
    sff hndM (h ∘ f) x v w = sff hndN h (f x) (mfderiv I I' f x v) (mfderiv I I' f x w) := by
  unfold sff
  rw [unitNormal_pullback hf hfi hpull hndM hndN hh, hpull,
    mfderiv_leviCivita_mpullback hf hfi hpull hsM hndM hgM hsN hndN hgN hν]

end Nat

section Reparam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

theorem gradAt_comp (hnd : IsNondegenerate g) {h : M → ℝ} {φ : ℝ → ℝ} {y : M}
    (hh : MDiffAt h y) (hφ : DifferentiableAt ℝ φ (h y)) :
    gradAt hnd (φ ∘ h) y = deriv φ (h y) • gradAt hnd h y := by
  symm
  refine eq_gradAt hnd (φ ∘ h) y fun w => ?_
  rw [map_smul, ContinuousLinearMap.smul_apply, g_gradAt,
    mvfderiv_comp' (J := 𝓘(ℝ, ℝ)) hφ.hasFDerivAt.hasMFDerivAt.mdifferentiableAt hh]
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, smul_eq_mul]
  have key : ∀ a : ℝ, fderiv ℝ φ (h y) a = deriv φ (h y) * a := fun a => by
    rw [hφ.hasDerivAt.hasFDerivAt.fderiv]; simp [mul_comm]
  erw [ContinuousLinearMap.comp_apply, key]
  rfl

theorem unitNormal_comp_of_pos (hnd : IsNondegenerate g) {h : M → ℝ} {φ : ℝ → ℝ} {y : M}
    (hh : MDiffAt h y) (hφ : DifferentiableAt ℝ φ (h y)) (hpos : 0 < deriv φ (h y)) :
    unitNormal hnd (φ ∘ h) y = unitNormal hnd h y := by
  simp only [unitNormal, gradAt_comp hnd hh hφ, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul, smul_smul]
  set c := deriv φ (h y)
  set A := g y (gradAt hnd h y) (gradAt hnd h y)
  have hs : √(c * (c * A)) = c * √A := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ c * c), Real.sqrt_mul_self hpos.le]
  rw [hs, mul_inv, mul_comm c⁻¹ (√A)⁻¹, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]

/-- **The second fundamental form depends only on the level set and its side.** -/
theorem sff_comp_of_pos (hnd : IsNondegenerate g) {h : M → ℝ} {φ : ℝ → ℝ} {x : M}
    (hev : ∀ᶠ y in 𝓝 x, MDiffAt h y ∧ DifferentiableAt ℝ φ (h y) ∧ 0 < deriv φ (h y)) :
    sff hnd (φ ∘ h) x = sff hnd h x := by
  funext v w
  unfold sff
  rw [leviCivita_congr_of_eventuallyEq (hev.mono fun y hy =>
    unitNormal_comp_of_pos hnd hy.1 hy.2.1 hy.2.2)]

theorem gradAt_neg (hnd : IsNondegenerate g) {h : M → ℝ} {y : M} (hh : MDiffAt h y) :
    gradAt hnd (fun z => -h z) y = -gradAt hnd h y := by
  symm
  refine eq_gradAt hnd _ y fun w => ?_
  rw [map_neg, ContinuousLinearMap.neg_apply, g_gradAt]
  have e : (fun z => -h z) = (-ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ) ∘ h := by
    funext z; simp
  rw [e, mvfderiv_clm_comp _ hh]
  simp

theorem unitNormal_neg (hnd : IsNondegenerate g) {h : M → ℝ} {y : M} (hh : MDiffAt h y) :
    unitNormal hnd (fun z => -h z) y = -unitNormal hnd h y := by
  simp only [unitNormal, gradAt_neg hnd hh, map_neg, ContinuousLinearMap.neg_apply, neg_neg,
    smul_neg]

/-- The second fundamental form of the other side is the negative. -/
theorem sff_neg (hsymm : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    {h : M → ℝ} {x : M} (hev : ∀ᶠ y in 𝓝 x, MDiffAt h y)
    (hν : MDiffAt (T% (unitNormal hnd h)) x) (v w : TangentSpace I x) :
    sff hnd (fun z => -h z) x v w = -sff hnd h x v w := by
  unfold sff
  have e : ∀ᶠ y in 𝓝 x, unitNormal hnd (fun z => -h z) y =
      ((fun _ : M => (-1 : ℝ)) • unitNormal hnd h) y :=
    hev.mono fun y hy => by rw [unitNormal_neg hnd hy]; simp
  rw [leviCivita_congr_of_eventuallyEq e,
    leviCivita_smul_section hsymm hnd hgm mdifferentiableAt_const hν]
  have h0 : mvfderiv I (fun _ : M => (-1 : ℝ)) x = 0 := by
    simp [mvfderiv, mfderiv_const]
  simp [h0]

end Reparam

end

end ExoticSpheres8And10
