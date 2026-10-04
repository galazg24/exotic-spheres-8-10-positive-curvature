/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.HLYModel.Derivatives

/-! # §4, HLY model: the curvature blocks at the base point ([HLY] `eq:HVHV`–`eq:VVVV`)

At `z₀ = (0, u)`, `|u| = 1`, where the round frame is normal (`c^B = Γ^B = 0`). The data are:

* `Ω0 i j a = Ω_{ij}^a(z₀)`;
* `ϑ0 i = ϑ_i(0)`;
* `r0 = r(0)`;
* `DΩ0 k i j a = X_k(Ω_{ij}^a)(z₀)`, the covariant derivative `(D_kΩ)_{ij}^a` in the normal frame;
* `N0 i j = −X_i(ϑ_j) − ϑ_i ϑ_j`, which is `−r⁻¹ Hess r` ([HLY]: `N_{ij} = −∂_iϑ_j − ϑ_iϑ_j`).

The blocks of `RmA` are [HLY]'s formulas. They are proved here by direct computation, in the
frame calculus, of `RiemannianGeometry`'s curvature (`riemannTensorAt_Fr`).
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section Blocks

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

theorem Fa_H_fst (k : Fin n) (u : Quaternion ℝ) : (Fa b A r (.inl k) ((0 : K), u)).1 = b k :=
  eb_zero k

theorem Fa_V_fst (c : Fin 3) (u : Quaternion ℝ) : (Fa b A r (.inr c) ((0 : K), u)).1 = 0 := rfl

theorem Fa_V_eq (c : Fin 3) (u : Quaternion ℝ) :
    Fa b A r (.inr c) ((0 : K), u) = ((0 : K), (r 0)⁻¹ • (u * qe c)) := rfl

/-- Derivatives of base functions along the frame at `z₀`. -/
theorem dbase_H {φ : K → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : Fin n) (u : Quaternion ℝ) :
    fderiv ℝ (fun z : K × Quaternion ℝ => φ z.1) ((0 : K), u) (Fa b A r (.inl k) ((0 : K), u)) =
      fderiv ℝ φ 0 (b k) := by
  rw [fderiv_fst_apply hφ, Fa_H_fst]

theorem dbase_V {φ : K → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : Fin 3) (u : Quaternion ℝ) :
    fderiv ℝ (fun z : K × Quaternion ℝ => φ z.1) ((0 : K), u) (Fa b A r (.inr c) ((0 : K), u)) = 0 := by
  rw [fderiv_fst_apply hφ, Fa_V_fst, map_zero]

/-- The product rule for `f(x) · Ω(z)`. -/
theorem dprod {f : K → ℝ} (hf : ContDiff ℝ ∞ f) {g : K × Quaternion ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (z v : K × Quaternion ℝ) :
    fderiv ℝ (fun y : K × Quaternion ℝ => f y.1 * g y) z v =
      f z.1 * fderiv ℝ g z v + g z * fderiv ℝ f z.1 v.1 := by
  have hf' : HasFDerivAt (fun y : K × Quaternion ℝ => f y.1) _ z :=
    ((hf.differentiable (by simp)) z.1).hasFDerivAt.comp z (hasFDerivAt_fst (p := z))
  have h : HasFDerivAt (fun y : K × Quaternion ℝ => f y.1 * g y) _ z :=
    hf'.mul ((hg.differentiable (by simp)) z).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']

variable (b A r) in
/-- The data at `z₀ = (0, u)`. -/
def Ω0 (u : Quaternion ℝ) (i j : Fin n) (a : Fin 3) : ℝ := Ωc b A i j a ((0 : K), u)

variable (b r) in
def ϑ0 (i : Fin n) : ℝ := ϑf b r i 0

variable (b r) in
def dϑ0 (k i : Fin n) : ℝ := fderiv ℝ (ϑf b r i) 0 (b k)

variable (b r) in
/-- `N = −r⁻¹ Hess r` in the normal frame: `N_{ij} = −∂_iϑ_j − ϑ_iϑ_j`. -/
def N0 (i j : Fin n) : ℝ := -dϑ0 b r i j - ϑ0 b r i * ϑ0 b r j

variable (b A r) in
def DΩ0 (u : Quaternion ℝ) (k i j : Fin n) (a : Fin 3) : ℝ :=
  fderiv ℝ (Ωc b A i j a) ((0 : K), u) (Fa b A r (.inl k) ((0 : K), u))

theorem r_deriv (hr0 : ∀ x, r x ≠ 0) (k : Fin n) : fderiv ℝ r 0 (b k) = r 0 * ϑ0 b r k := by
  have := hr0 0
  simp only [ϑ0, ϑf, eb_zero]
  field_simp

/-- **[HLY] `eq:HVHV`**: `⟨R(X_i, E_a) E_c, X_j⟩ = N_{ij} δ_{ac} + (r²/4) Σ_k Ω_{ik}^c Ω_{jk}^a
− ¼ Σ_d cst_{acd} Ω_{ij}^d`. -/
theorem RmA_HVHV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j : Fin n)
    (a c : Fin 3) :
    RmA b A r (.inl i) (.inr a) (.inr c) (.inl j) ((0 : K), u) =
      N0 b r i j * kron a c + r 0 ^ 2 / 4 * ∑ k, Ω0 b A u i k c * Ω0 b A u j k a -
        1 / 4 * ∑ d, Prop31Algebra.cst a c d * Ω0 b A u i j d := by
  have hϑ : ∀ l, ContDiff ℝ ∞ (ϑf b r l) := contDiff_ϑf hr hr0
  have hr0' := hr0 0
  unfold RmA
  rw [Γ_VVH, Γ_HVH]
  -- the two derivative terms
  have d1 : fderiv ℝ (fun z : K × Quaternion ℝ => -(ϑf b r j z.1 * kron a c)) ((0 : K), u)
      (Fa b A r (.inl i) ((0 : K), u)) = -(dϑ0 b r i j * kron a c) := by
    have e : (fun z : K × Quaternion ℝ => -(ϑf b r j z.1 * kron a c)) =
        fun z => (fun x => -(ϑf b r j x * kron a c)) z.1 := rfl
    rw [e, dbase_H ((hϑ j).mul contDiff_const |>.neg)]
    simp [dϑ0, fderiv_mul_const ((hϑ j).differentiable (by simp) 0)]
    ring
  have d2 : fderiv ℝ (fun z : K × Quaternion ℝ => r z.1 / 2 * Ωc b A i j c z) ((0 : K), u)
      (Fa b A r (.inr a) ((0 : K), u)) = 1 / 2 * ∑ d, Ω0 b A u i j d * Prop31Algebra.cst d a c := by
    have e : (fun z : K × Quaternion ℝ => r z.1 / 2 * Ωc b A i j c z) =
        fun z => (fun x => r x / 2) z.1 * Ωc b A i j c z := rfl
    rw [e, dprod (hr.div_const 2) (contDiff_Ωc hA i j c), Fa_V_fst, map_zero, mul_zero, add_zero,
      Fa_V_eq, fderiv_Ωc_vert hA hAim i j c a _ hu]
    simp only [Ω0]
    field_simp
  rw [d1, d2, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_VVH, Γ_HHH, Γ_VVV, Γ_HVH, Γ_HVV, Γ_VHH, cA, ΓB_zero, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, Finset.sum_const_zero]
  -- normalise the sums
  have hkron : ∑ d : Fin 3, kron a d * kron d c = kron a c := by
    simp only [kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hcst : ∀ d : Fin 3, Prop31Algebra.cst d a c = Prop31Algebra.cst a c d := fun d => by
    rw [cst_cycle c d a, cst_cycle a c d]
  have hsw : ∀ k : Fin n, Ωc b A k j a ((0 : K), u) = -Ω0 b A u j k a := fun k => by
    rw [Ωc_swap]; rfl
  simp only [hsw, hcst]
  have t1 : ∑ x : Fin 3, Ω0 b A u i j x * Prop31Algebra.cst a c x = ∑ d, Prop31Algebra.cst a c d * Ω0 b A u i j d :=
    Finset.sum_congr rfl fun x _ => by ring
  have t2 : ∑ x : Fin n, -(r 0 / 2 * Ωc b A i x c ((0 : K), u) * (r 0 / 2 * -Ω0 b A u j x a)) =
      r 0 ^ 2 / 4 * ∑ k, Ω0 b A u i k c * Ω0 b A u j k a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ω0]; ring
  have t3 : ∑ x : Fin 3, (r 0)⁻¹ / 2 * Prop31Algebra.cst a c x * (r 0 / 2 * Ωc b A i j x ((0 : K), u)) =
      1 / 4 * ∑ d, Prop31Algebra.cst a c d * Ω0 b A u i j d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ω0]; field_simp; ring
  have t4 : ∑ x : Fin 3, -ϑf b r i 0 * kron a x * -(ϑf b r j 0 * kron x c) =
      ϑ0 b r i * ϑ0 b r j * kron a c := by
    rw [← hkron, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ϑ0]; ring
  rw [t1, t2, t3, t4]
  simp only [N0, dϑ0, ϑ0]
  ring

theorem cst_rot (d a c : Fin 3) : Prop31Algebra.cst d a c = Prop31Algebra.cst a c d := by
  rw [cst_cycle c d a, cst_cycle a c d]

theorem sum_kron_left {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (a : ι) :
    ∑ x, kron a x * f x = f a := by
  rw [Finset.sum_congr rfl fun x _ => by rw [kron_comm, mul_comm]]
  exact sum_smul_kron (V := ℝ) f a

/-- `¼ Σ_f (cst_cdf cst_afe − cst_adf cst_cfe) − ½ Σ_f cst_acf cst_fde = δ_cd δ_ae − δ_ad δ_ce`:
the round `S³` of radius `1` has curvature `1`. -/
theorem cst_quad (a c d e : Fin 3) :
    1 / 4 * ∑ f, (Prop31Algebra.cst c d f * Prop31Algebra.cst a f e - Prop31Algebra.cst a d f * Prop31Algebra.cst c f e) -
      1 / 2 * ∑ f, Prop31Algebra.cst a c f * Prop31Algebra.cst f d e = kron c d * kron a e - kron a d * kron c e := by
  fin_cases a <;> fin_cases c <;> fin_cases d <;> fin_cases e <;>
    simp [Prop31Algebra.cst, Prop31Algebra.lc, Fin.sum_univ_three, kron] <;> norm_num

theorem fderiv_zero_fun (z v : K × Quaternion ℝ) :
    fderiv ℝ (fun _ : K × Quaternion ℝ => (0 : ℝ)) z v = 0 := by simp

/-- **[HLY] `eq:HHVV`**. -/
theorem RmA_HHVV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j : Fin n)
    (a c : Fin 3) :
    RmA b A r (.inl i) (.inl j) (.inr a) (.inr c) ((0 : K), u) =
      r 0 ^ 2 / 4 * ∑ k, (Ω0 b A u i k a * Ω0 b A u j k c - Ω0 b A u j k a * Ω0 b A u i k c) +
        1 / 2 * ∑ d, Prop31Algebra.cst a c d * Ω0 b A u i j d := by
  have hr0' := hr0 0
  unfold RmA
  rw [Γ_HVV, Γ_HVV, fderiv_zero_fun, fderiv_zero_fun, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_HVH, Γ_HHV, Γ_HVV, Γ_VVV, cA, cB_zero, zero_mul, mul_zero, sub_zero, zero_sub,
    zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (r 0 / 2 * Ωc b A j x a ((0 : K), u) * (-(r 0 / 2) * Ωc b A i x c ((0 : K), u)) -
      r 0 / 2 * Ωc b A i x a ((0 : K), u) * (-(r 0 / 2) * Ωc b A j x c ((0 : K), u))) =
      r 0 ^ 2 / 4 * ∑ k, (Ω0 b A u i k a * Ω0 b A u j k c - Ω0 b A u j k a * Ω0 b A u i k c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ω0]; ring
  have t2 : ∑ x : Fin 3, -r 0 * Ωc b A i j x ((0 : K), u) * ((r 0)⁻¹ / 2 * Prop31Algebra.cst x a c) =
      -(1 / 2 * ∑ d, Prop31Algebra.cst a c d * Ω0 b A u i j d) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cst_rot]
    simp only [Ω0]; field_simp
  rw [t1, t2]
  ring

/-- **[HLY] `eq:HVVV`**. -/
theorem RmA_HVVV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i : Fin n)
    (a c d : Fin 3) :
    RmA b A r (.inl i) (.inr a) (.inr c) (.inr d) ((0 : K), u) =
      r 0 / 2 * ∑ k, ϑ0 b r k * (kron a c * Ω0 b A u i k d - kron a d * Ω0 b A u i k c) := by
  have hr0' := hr0 0
  unfold RmA
  rw [Γ_VVV, Γ_HVV, fderiv_zero_fun, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have d1 : fderiv ℝ (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst a c d) ((0 : K), u)
      (Fa b A r (.inl i) ((0 : K), u)) = -(ϑ0 b r i / r 0) / 2 * Prop31Algebra.cst a c d := by
    have e : (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst a c d) =
        fun z => (fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d) z.1 := rfl
    have hφ : ContDiff ℝ ∞ fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d :=
      ((hr.inv hr0).div_const 2).mul contDiff_const
    rw [e, dbase_H (φ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d) hφ]
    have hinv : HasFDerivAt (fun x => (r x)⁻¹) _ (0 : K) :=
      (hasDerivAt_inv hr0').comp_hasFDerivAt (0 : K)
        ((hr.differentiable (by simp)) 0).hasFDerivAt
    have h := (hinv.const_mul (Prop31Algebra.cst a c d / 2)).congr_of_eventuallyEq
      (f₁ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d)
      (Eventually.of_forall fun y => by beta_reduce; ring)
    rw [h.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, r_deriv hr0]
    field_simp
  rw [d1]
  simp only [Γ_VVH, Γ_HHV, Γ_HVH, Γ_VHV, Γ_VVV, Γ_HVV, cA, zero_mul, mul_zero, sub_zero,
    zero_sub, zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (-(ϑf b r x 0 * kron a c) * (-(r 0 / 2) * Ωc b A i x d ((0 : K), u)) -
      r 0 / 2 * Ωc b A i x c ((0 : K), u) * (ϑf b r x 0 * kron a d)) =
      r 0 / 2 * ∑ k, ϑ0 b r k * (kron a c * Ω0 b A u i k d - kron a d * Ω0 b A u i k c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ω0, ϑ0]; ring
  have t2 : ∑ x : Fin 3, -ϑf b r i 0 * kron a x * ((r 0)⁻¹ / 2 * Prop31Algebra.cst x c d) =
      -(ϑ0 b r i * ((r 0)⁻¹ / 2 * Prop31Algebra.cst a c d)) := by
    rw [Finset.sum_congr rfl fun x _ => show -ϑf b r i 0 * kron a x * ((r 0)⁻¹ / 2 * Prop31Algebra.cst x c d)
      = kron a x * (-ϑf b r i 0 * ((r 0)⁻¹ / 2 * Prop31Algebra.cst x c d)) by ring]
    refine (sum_kron_left (fun x => -ϑf b r i 0 * ((r 0)⁻¹ / 2 * Prop31Algebra.cst x c d)) a).trans ?_
    simp only [ϑ0]; ring
  rw [t1, t2]
  field_simp
  ring

/-- **[HLY] `eq:HHHV`**. -/
theorem RmA_HHHV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j k : Fin n)
    (a : Fin 3) :
    RmA b A r (.inl i) (.inl j) (.inl k) (.inr a) ((0 : K), u) =
      -(r 0 / 2) * (DΩ0 b A r u i j k a - DΩ0 b A r u j i k a) -
        r 0 / 2 * (ϑ0 b r i * Ω0 b A u j k a - ϑ0 b r j * Ω0 b A u i k a) +
        r 0 * ϑ0 b r k * Ω0 b A u i j a := by
  have hr0' := hr0 0
  unfold RmA
  rw [Γ_HHV, Γ_HHV]
  have dH : ∀ p q l : Fin n, fderiv ℝ (fun z : K × Quaternion ℝ => -(r z.1 / 2) * Ωc b A p q a z)
      ((0 : K), u) (Fa b A r (.inl l) ((0 : K), u)) =
      -(r 0 / 2) * DΩ0 b A r u l p q a - Ω0 b A u p q a * (r 0 * ϑ0 b r l / 2) := by
    intro p q l
    have e : (fun z : K × Quaternion ℝ => -(r z.1 / 2) * Ωc b A p q a z) =
        fun z => (fun x => -(r x / 2)) z.1 * Ωc b A p q a z := rfl
    rw [e, dprod ((hr.div_const 2).neg) (contDiff_Ωc hA p q a), Fa_H_fst]
    have hrd := ((((hr.differentiable (by simp)) 0).hasFDerivAt).const_mul
      (-(1 / 2 : ℝ))).congr_of_eventuallyEq (f₁ := fun x => -(r x / 2))
      (Eventually.of_forall fun y => by beta_reduce; ring)
    rw [hrd.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, r_deriv hr0, DΩ0, Ω0]
    ring
  rw [dH, dH, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_HHH, Γ_HHV, Γ_HVH, Γ_VHH, Γ_HVV, Γ_VHV, cA, ΓB_zero, cB_zero, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, Finset.sum_const_zero]
  have t : ∑ x : Fin 3, -r 0 * Ωc b A i j x ((0 : K), u) * (ϑf b r k 0 * kron x a) =
      -(r 0 * ϑ0 b r k * Ω0 b A u i j a) := by
    have := sum_smul_kron (V := ℝ) (fun x => -r 0 * Ωc b A i j x ((0 : K), u) * ϑf b r k 0) a
    rw [Finset.sum_congr rfl fun x _ => show -r 0 * Ωc b A i j x ((0 : K), u) * (ϑf b r k 0 * kron x a)
      = -r 0 * Ωc b A i j x ((0 : K), u) * ϑf b r k 0 * kron x a by ring, this]
    simp only [Ω0, ϑ0]; ring
  rw [t]
  ring

/-- **[HLY] `eq:VVVV`**. -/
theorem RmA_VVVV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (a c d e : Fin 3) :
    RmA b A r (.inr a) (.inr c) (.inr d) (.inr e) ((0 : K), u) =
      (1 / r 0 ^ 2 - ∑ k, ϑ0 b r k ^ 2) * (kron c d * kron a e - kron a d * kron c e) := by
  have hr0' := hr0 0
  unfold RmA
  rw [Γ_VVV, Γ_VVV]
  have e1 : (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst c d e) =
      fun z => (fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst c d e) z.1 := rfl
  have e2 : (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst a d e) =
      fun z => (fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a d e) z.1 := rfl
  rw [e1, e2, dbase_V (φ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst c d e)
    (((hr.inv hr0).div_const 2).mul contDiff_const),
    dbase_V (φ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a d e)
    (((hr.inv hr0).div_const 2).mul contDiff_const), Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_VVH, Γ_VHV, Γ_VVV, cA, zero_mul, mul_zero, sub_zero, zero_sub, zero_add,
    Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (-(ϑf b r x 0 * kron c d) * (ϑf b r x 0 * kron a e) -
      -(ϑf b r x 0 * kron a d) * (ϑf b r x 0 * kron c e)) =
      -(∑ k, ϑ0 b r k ^ 2) * (kron c d * kron a e - kron a d * kron c e) := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ϑ0]; ring
  have t2 : ∑ x : Fin 3, ((r 0)⁻¹ / 2 * Prop31Algebra.cst c d x * ((r 0)⁻¹ / 2 * Prop31Algebra.cst a x e) -
      (r 0)⁻¹ / 2 * Prop31Algebra.cst a d x * ((r 0)⁻¹ / 2 * Prop31Algebra.cst c x e)) =
      (r 0)⁻¹ ^ 2 * (1 / 4 * ∑ f, (Prop31Algebra.cst c d f * Prop31Algebra.cst a f e - Prop31Algebra.cst a d f * Prop31Algebra.cst c f e)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t3 : ∑ x : Fin 3, (r 0)⁻¹ * Prop31Algebra.cst a c x * ((r 0)⁻¹ / 2 * Prop31Algebra.cst x d e) =
      (r 0)⁻¹ ^ 2 * (1 / 2 * ∑ f, Prop31Algebra.cst a c f * Prop31Algebra.cst f d e) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [t1, t2, t3]
  linear_combination (r 0)⁻¹ ^ 2 * cst_quad a c d e

/-- **[HLY] `eq:HHHH`**, in components. -/
theorem RmA_HHHH (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j k l : Fin n) :
    RmA b A r (.inl i) (.inl j) (.inl k) (.inl l) ((0 : K), u) =
      (kron i l * kron j k - kron i k * kron j l) +
        r 0 ^ 2 / 4 * ∑ d, (Ω0 b A u i k d * Ω0 b A u j l d - Ω0 b A u j k d * Ω0 b A u i l d) +
        r 0 ^ 2 / 2 * ∑ d, Ω0 b A u i j d * Ω0 b A u k l d := by
  have hr0' := hr0 0
  unfold RmA
  rw [Γ_HHH, Γ_HHH]
  have dB : ∀ p q s t : Fin n, fderiv ℝ (fun z : K × Quaternion ℝ => ΓB b p q s z.1) ((0 : K), u)
      (Fa b A r (.inl t) ((0 : K), u)) = (kron t s * kron p q - kron t q * kron p s) / 2 := by
    intro p q s t
    have hΓ : ContDiff ℝ ∞ (ΓB b p q s) := by
      have e : ΓB b p q s = fun x => (⟪x, b s⟫ * kron p q - ⟪x, b q⟫ * kron p s) / 2 :=
        funext (ΓB_eq p q s)
      rw [e]
      exact (((contDiff_id.inner ℝ contDiff_const).mul contDiff_const).sub
        ((contDiff_id.inner ℝ contDiff_const).mul contDiff_const)).div_const 2
    rw [dbase_H hΓ]
    have e : ΓB b p q s = fun x => (⟪x, b s⟫ * kron p q - ⟪x, b q⟫ * kron p s) / 2 :=
      funext (ΓB_eq p q s)
    rw [e]
    have h1 : HasFDerivAt (fun x : K => ⟪x, b s⟫) (innerSL ℝ (b s)) (0 : K) := by
      have := ((innerSL ℝ (b s)).hasFDerivAt (x := (0 : K)))
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp [real_inner_comm]
    have h2 : HasFDerivAt (fun x : K => ⟪x, b q⟫) (innerSL ℝ (b q)) (0 : K) := by
      have := ((innerSL ℝ (b q)).hasFDerivAt (x := (0 : K)))
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp [real_inner_comm]
    have h := (((h1.mul_const (kron p q)).sub (h2.mul_const (kron p s))).const_mul
      (1 / 2 : ℝ)).congr_of_eventuallyEq
      (f₁ := fun x : K => (⟪x, b s⟫ * kron p q - ⟪x, b q⟫ * kron p s) / 2)
      (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)
    rw [h.fderiv]
    simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sub', Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul, innerSL_apply_apply]
    rw [b.inner_eq_ite, b.inner_eq_ite, kron_comm t s, kron_comm t q]
    simp only [kron]
    ring
  rw [dB, dB, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_HHH, Γ_HHV, Γ_HVH, Γ_VHH, cA, ΓB_zero, cB_zero, zero_mul, mul_zero, sub_zero,
    zero_sub, zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin 3, (-(r 0 / 2) * Ωc b A j k x ((0 : K), u) * (r 0 / 2 * Ωc b A i l x ((0 : K), u)) -
      -(r 0 / 2) * Ωc b A i k x ((0 : K), u) * (r 0 / 2 * Ωc b A j l x ((0 : K), u))) =
      r 0 ^ 2 / 4 * ∑ d, (Ω0 b A u i k d * Ω0 b A u j l d - Ω0 b A u j k d * Ω0 b A u i l d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ω0]; ring
  have t2 : ∑ x : Fin 3, -r 0 * Ωc b A i j x ((0 : K), u) * (r 0 / 2 * Ωc b A k l x ((0 : K), u)) =
      -(r 0 ^ 2 / 2 * ∑ d, Ω0 b A u i j d * Ω0 b A u k l d) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ω0]; ring
  rw [t1, t2]
  ring

/-- The hypotheses of the block theorems are satisfiable: the flat potential `A = 0`, the
constant radius `r = 1` and `u = 1` (the product metric on `K × S³`). -/
theorem hly_blocks_hyps_satisfiable :
    ContDiff ℝ ∞ (fun _ : K => (0 : K →L[ℝ] Quaternion ℝ)) ∧
      (∀ x v : K, ((fun _ : K => (0 : K →L[ℝ] Quaternion ℝ)) x v).re = 0) ∧
      ContDiff ℝ ∞ (fun _ : K => (1 : ℝ)) ∧ (∀ _ : K, (1 : ℝ) ≠ 0) ∧
      Quaternion.normSq (1 : Quaternion ℝ) = 1 :=
  ⟨contDiff_const, fun _ _ => rfl, contDiff_const, fun _ => one_ne_zero, map_one Quaternion.normSq⟩

end Blocks

end

end ExoticSpheres8And10
