/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.HLYModel.Package

/-! # §4, HLY model: the curvature blocks at every base point

The blocks of `S4_HLYBlocks` at an arbitrary point `z = (y, u)`, `|u| = 1`, where the round frame
`e_i = (1+|y|²/4) b_i` is orthonormal but not normal. The base connection coefficients
`Γ^B_{ijk}(y) = ½(⟨y, b_k⟩δ_{ij} − ⟨y, b_j⟩δ_{ik})` enter through the covariant expressions:

* `Ny i j = −e_i(ϑ_j) − ϑ_iϑ_j − Σ_k Γ^B_{ikj} ϑ_k`, which is `−r⁻¹ Hess r`;
* `DΩy k i j a = e_k(Ω_{ij}^a) − Σ_l Γ^B_{kil} Ω_{lj}^a − Σ_l Γ^B_{kjl} Ω_{il}^a`, which is
  `(D_kΩ)_{ij}^a`;
* the base part of `eq:HHHH` is the curvature of the round unit sphere, `δ_{il}δ_{jk} − δ_{ik}δ_{jl}`.

The whole southern cap `{t ≥ a}`, `a > π/2`, lies in this one chart, centred at the south pole.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section BlocksY

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

theorem Fa_H_fstx (k : Fin n) (y : K) (u : Quaternion ℝ) : (Fa b A r (.inl k) (y, u)).1 = eb b k y :=
  rfl

theorem Fa_V_fstx (c : Fin 3) (y : K) (u : Quaternion ℝ) : (Fa b A r (.inr c) (y, u)).1 = 0 := rfl

theorem Fa_V_eqx (c : Fin 3) (y : K) (u : Quaternion ℝ) :
    Fa b A r (.inr c) (y, u) = (0, (r y)⁻¹ • (u * qe c)) := rfl

theorem dbase_Hx {φ : K → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : Fin n) (y : K) (u : Quaternion ℝ) :
    fderiv ℝ (fun z : K × Quaternion ℝ => φ z.1) (y, u) (Fa b A r (.inl k) (y, u)) =
      fderiv ℝ φ y (eb b k y) := by
  rw [fderiv_fst_apply hφ, Fa_H_fstx]

theorem dbase_Vx {φ : K → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : Fin 3) (y : K) (u : Quaternion ℝ) :
    fderiv ℝ (fun z : K × Quaternion ℝ => φ z.1) (y, u) (Fa b A r (.inr c) (y, u)) = 0 := by
  rw [fderiv_fst_apply hφ, Fa_V_fstx, map_zero]

variable (b A r) in
/-- The data at `z = (y, u)`. -/
def Ωy (y : K) (u : Quaternion ℝ) (i j : Fin n) (a : Fin 3) : ℝ := Ωc b A i j a (y, u)

variable (b r) in
def ϑy (y : K) (i : Fin n) : ℝ := ϑf b r i y

variable (b r) in
def dϑy (y : K) (k i : Fin n) : ℝ := fderiv ℝ (ϑf b r i) y (eb b k y)

variable (b r) in
/-- `N = −r⁻¹ Hess r` in the frame: `N_{ij} = −e_iϑ_j − ϑ_iϑ_j − Σ_k Γ^B_{ikj} ϑ_k`. -/
def Ny (y : K) (i j : Fin n) : ℝ :=
  -dϑy b r y i j - ϑy b r y i * ϑy b r y j - ∑ k, ΓB b i k j y * ϑy b r y k

variable (b A r) in
/-- The frame derivative `e_k(Ω_{ij}^a)`. -/
def dΩy (y : K) (u : Quaternion ℝ) (k i j : Fin n) (a : Fin 3) : ℝ :=
  fderiv ℝ (Ωc b A i j a) (y, u) (Fa b A r (.inl k) (y, u))

variable (b A r) in
/-- The covariant derivative `(D_kΩ)_{ij}^a`. -/
def DΩy (y : K) (u : Quaternion ℝ) (k i j : Fin n) (a : Fin 3) : ℝ :=
  dΩy b A r y u k i j a - ∑ l, ΓB b k i l y * Ωy b A y u l j a -
    ∑ l, ΓB b k j l y * Ωy b A y u i l a

theorem r_derivx (hr0 : ∀ x, r x ≠ 0) (k : Fin n) (y : K) :
    fderiv ℝ r y (eb b k y) = r y * ϑy b r y k := by
  have := hr0 y
  simp only [ϑy, ϑf]
  field_simp

theorem sum_inner_kron (y : K) (p : Fin n) : ∑ x, ⟪y, b x⟫ * kron p x = ⟪y, b p⟫ := by
  rw [Finset.sum_congr rfl fun x _ => mul_comm _ _]
  exact sum_kron_left (fun x => ⟪y, b x⟫) p

theorem sum_kron_kron (p q : Fin n) : ∑ x : Fin n, kron p x * kron q x = kron p q := by
  rw [sum_kron_left (fun x => kron q x) p, kron_comm]

theorem sum_sq_inner (y : K) : ∑ x, ⟪y, b x⟫ * ⟪y, b x⟫ = ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner y y]
  exact Finset.sum_congr rfl fun x _ => by rw [real_inner_comm (b x) y]

theorem ΓB_sub_swap (i j l : Fin n) (y : K) : ΓB b i j l y - ΓB b j i l y = cB b i j l y := by
  rw [ΓB_eq, ΓB_eq, cB_eq, kron_comm j i]; ring

variable (b) in
/-- **The round unit sphere has curvature `1`**: the quadratic part of the base curvature in the
frame `e_i` at `y`. With the derivative part `cfac(y)(δ_{il}δ_{jk} − δ_{ik}δ_{jl})`, the total is
`δ_{il}δ_{jk} − δ_{ik}δ_{jl}`. -/
theorem base_curv (y : K) (i j k l : Fin n) :
    ∑ x, (ΓB b j k x y * ΓB b i x l y - ΓB b i k x y * ΓB b j x l y) -
      ∑ x, cB b i j x y * ΓB b x k l y =
      -(‖y‖ ^ 2 / 4) * (kron i l * kron j k - kron i k * kron j l) := by
  set Y : Fin n → ℝ := fun m => ⟪y, b m⟫ with hY
  rw [← Finset.sum_sub_distrib]
  have hx : ∀ x : Fin n, ΓB b j k x y * ΓB b i x l y - ΓB b i k x y * ΓB b j x l y -
      cB b i j x y * ΓB b x k l y = 1 / 4 * (
        (⟪y, b l⟫ * kron j k) * (⟪y, b x⟫ * kron i x) -
        (kron j k * kron i l) * (⟪y, b x⟫ * ⟪y, b x⟫) -
        (⟪y, b k⟫ * ⟪y, b l⟫) * (kron j x * kron i x) +
        (⟪y, b k⟫ * kron i l) * (⟪y, b x⟫ * kron j x) -
        (⟪y, b l⟫ * kron i k) * (⟪y, b x⟫ * kron j x) +
        (kron i k * kron j l) * (⟪y, b x⟫ * ⟪y, b x⟫) +
        (⟪y, b k⟫ * ⟪y, b l⟫) * (kron i x * kron j x) -
        (⟪y, b k⟫ * kron j l) * (⟪y, b x⟫ * kron i x) -
        (⟪y, b i⟫ * ⟪y, b l⟫) * (kron j x * kron k x) +
        (⟪y, b i⟫ * ⟪y, b k⟫) * (kron j x * kron l x) +
        (⟪y, b j⟫ * ⟪y, b l⟫) * (kron i x * kron k x) -
        (⟪y, b j⟫ * ⟪y, b k⟫) * (kron i x * kron l x)) := by
    intro x
    simp only [ΓB_eq, cB_eq]
    rw [kron_comm x k, kron_comm x l]
    ring
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_inner_kron,
    sum_sq_inner, sum_kron_kron]
  rw [kron_comm j i]
  ring

/-- **[HLY] `eq:HVHV`**: `⟨R(X_i, E_a) E_c, X_j⟩ = N_{ij} δ_{ac} + (r²/4) Σ_k Ω_{ik}^c Ω_{jk}^a
− ¼ Σ_d cst_{acd} Ω_{ij}^d`. -/
theorem RmAy_HVHV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (y : K) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j : Fin n)
    (a c : Fin 3) :
    RmA b A r (.inl i) (.inr a) (.inr c) (.inl j) (y, u) =
      Ny b r y i j * kron a c + r y ^ 2 / 4 * ∑ k, Ωy b A y u i k c * Ωy b A y u j k a -
        1 / 4 * ∑ d, Prop31Algebra.cst a c d * Ωy b A y u i j d := by
  have hϑ : ∀ l, ContDiff ℝ ∞ (ϑf b r l) := contDiff_ϑf hr hr0
  have hr0' := hr0 y
  unfold RmA
  rw [Γ_VVH, Γ_HVH]
  -- the two derivative terms
  have d1 : fderiv ℝ (fun z : K × Quaternion ℝ => -(ϑf b r j z.1 * kron a c)) (y, u)
      (Fa b A r (.inl i) (y, u)) = -(dϑy b r y i j * kron a c) := by
    have e : (fun z : K × Quaternion ℝ => -(ϑf b r j z.1 * kron a c)) =
        fun z => (fun x => -(ϑf b r j x * kron a c)) z.1 := rfl
    rw [e, dbase_Hx ((hϑ j).mul contDiff_const |>.neg)]
    simp [dϑy, fderiv_mul_const ((hϑ j).differentiable (by simp) y)]
    ring
  have d2 : fderiv ℝ (fun z : K × Quaternion ℝ => r z.1 / 2 * Ωc b A i j c z) (y, u)
      (Fa b A r (.inr a) (y, u)) = 1 / 2 * ∑ d, Ωy b A y u i j d * Prop31Algebra.cst d a c := by
    have e : (fun z : K × Quaternion ℝ => r z.1 / 2 * Ωc b A i j c z) =
        fun z => (fun x => r x / 2) z.1 * Ωc b A i j c z := rfl
    rw [e, dprod (hr.div_const 2) (contDiff_Ωc hA i j c), Fa_V_fstx, map_zero, mul_zero, add_zero,
      Fa_V_eqx, fderiv_Ωc_vert hA hAim i j c a _ hu]
    simp only [Ωy]
    field_simp
  rw [d1, d2, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_VVH, Γ_HHH, Γ_VVV, Γ_HVH, Γ_HVV, Γ_VHH, cA, ΓB_zero, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, Finset.sum_const_zero]
  -- normalise the sums
  have hkron : ∑ d : Fin 3, kron a d * kron d c = kron a c := by
    simp only [kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hcst : ∀ d : Fin 3, Prop31Algebra.cst d a c = Prop31Algebra.cst a c d := fun d => by
    rw [cst_cycle c d a, cst_cycle a c d]
  have hsw : ∀ k : Fin n, Ωc b A k j a (y, u) = -Ωy b A y u j k a := fun k => by
    rw [Ωc_swap]; rfl
  simp only [hsw, hcst]
  have t1 : ∑ x : Fin 3, Ωy b A y u i j x * Prop31Algebra.cst a c x = ∑ d, Prop31Algebra.cst a c d * Ωy b A y u i j d :=
    Finset.sum_congr rfl fun x _ => by ring
  have t2 : ∑ x : Fin n, (-(ϑf b r x y * kron a c) * ΓB b i x j y -
      r y / 2 * Ωc b A i x c (y, u) * (r y / 2 * -Ωy b A y u j x a)) =
      r y ^ 2 / 4 * ∑ k, Ωy b A y u i k c * Ωy b A y u j k a -
        kron a c * ∑ k, ΓB b i k j y * ϑy b r y k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ωy, ϑy]; ring
  have t3 : ∑ x : Fin 3, (r y)⁻¹ / 2 * Prop31Algebra.cst a c x * (r y / 2 * Ωc b A i j x (y, u)) =
      1 / 4 * ∑ d, Prop31Algebra.cst a c d * Ωy b A y u i j d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ωy]; field_simp; ring
  have t4 : ∑ x : Fin 3, -ϑf b r i y * kron a x * -(ϑf b r j y * kron x c) =
      ϑy b r y i * ϑy b r y j * kron a c := by
    rw [← hkron, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ϑy]; ring
  rw [t1, t2, t3, t4]
  simp only [Ny, dϑy, ϑy]
  ring

/-- **[HLY] `eq:HHVV`**. -/
theorem RmAy_HHVV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (y : K) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j : Fin n)
    (a c : Fin 3) :
    RmA b A r (.inl i) (.inl j) (.inr a) (.inr c) (y, u) =
      r y ^ 2 / 4 * ∑ k, (Ωy b A y u i k a * Ωy b A y u j k c - Ωy b A y u j k a * Ωy b A y u i k c) +
        1 / 2 * ∑ d, Prop31Algebra.cst a c d * Ωy b A y u i j d := by
  have hr0' := hr0 y
  unfold RmA
  rw [Γ_HVV, Γ_HVV, fderiv_zero_fun, fderiv_zero_fun, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_HVH, Γ_HHV, Γ_HVV, Γ_VVV, cA, cB_zero, zero_mul, mul_zero, sub_zero, zero_sub,
    zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (r y / 2 * Ωc b A j x a (y, u) * (-(r y / 2) * Ωc b A i x c (y, u)) -
      r y / 2 * Ωc b A i x a (y, u) * (-(r y / 2) * Ωc b A j x c (y, u))) =
      r y ^ 2 / 4 * ∑ k, (Ωy b A y u i k a * Ωy b A y u j k c - Ωy b A y u j k a * Ωy b A y u i k c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ωy]; ring
  have t2 : ∑ x : Fin 3, -r y * Ωc b A i j x (y, u) * ((r y)⁻¹ / 2 * Prop31Algebra.cst x a c) =
      -(1 / 2 * ∑ d, Prop31Algebra.cst a c d * Ωy b A y u i j d) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cst_rot]
    simp only [Ωy]; field_simp
  rw [t1, t2]
  ring

/-- **[HLY] `eq:HVVV`**. -/
theorem RmAy_HVVV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (y : K) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i : Fin n)
    (a c d : Fin 3) :
    RmA b A r (.inl i) (.inr a) (.inr c) (.inr d) (y, u) =
      r y / 2 * ∑ k, ϑy b r y k * (kron a c * Ωy b A y u i k d - kron a d * Ωy b A y u i k c) := by
  have hr0' := hr0 y
  unfold RmA
  rw [Γ_VVV, Γ_HVV, fderiv_zero_fun, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have d1 : fderiv ℝ (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst a c d) (y, u)
      (Fa b A r (.inl i) (y, u)) = -(ϑy b r y i / r y) / 2 * Prop31Algebra.cst a c d := by
    have e : (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst a c d) =
        fun z => (fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d) z.1 := rfl
    have hφ : ContDiff ℝ ∞ fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d :=
      ((hr.inv hr0).div_const 2).mul contDiff_const
    rw [e, dbase_Hx (φ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d) hφ]
    have hinv : HasFDerivAt (fun x => (r x)⁻¹) _ y :=
      (hasDerivAt_inv hr0').comp_hasFDerivAt y
        ((hr.differentiable (by simp)) y).hasFDerivAt
    have h := (hinv.const_mul (Prop31Algebra.cst a c d / 2)).congr_of_eventuallyEq
      (f₁ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a c d)
      (Eventually.of_forall fun y => by beta_reduce; ring)
    rw [h.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, r_derivx hr0]
    field_simp
  rw [d1]
  simp only [Γ_VVH, Γ_HHV, Γ_HVH, Γ_VHV, Γ_VVV, Γ_HVV, cA, zero_mul, mul_zero, sub_zero,
    zero_sub, zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (-(ϑf b r x y * kron a c) * (-(r y / 2) * Ωc b A i x d (y, u)) -
      r y / 2 * Ωc b A i x c (y, u) * (ϑf b r x y * kron a d)) =
      r y / 2 * ∑ k, ϑy b r y k * (kron a c * Ωy b A y u i k d - kron a d * Ωy b A y u i k c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ωy, ϑy]; ring
  have t2 : ∑ x : Fin 3, -ϑf b r i y * kron a x * ((r y)⁻¹ / 2 * Prop31Algebra.cst x c d) =
      -(ϑy b r y i * ((r y)⁻¹ / 2 * Prop31Algebra.cst a c d)) := by
    rw [Finset.sum_congr rfl fun x _ => show -ϑf b r i y * kron a x * ((r y)⁻¹ / 2 * Prop31Algebra.cst x c d)
      = kron a x * (-ϑf b r i y * ((r y)⁻¹ / 2 * Prop31Algebra.cst x c d)) by ring]
    refine (sum_kron_left (fun x => -ϑf b r i y * ((r y)⁻¹ / 2 * Prop31Algebra.cst x c d)) a).trans ?_
    simp only [ϑy]; ring
  rw [t1, t2]
  field_simp
  ring

/-- **[HLY] `eq:HHHV`**. -/
theorem RmAy_HHHV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (y : K) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j k : Fin n)
    (a : Fin 3) :
    RmA b A r (.inl i) (.inl j) (.inl k) (.inr a) (y, u) =
      -(r y / 2) * (DΩy b A r y u i j k a - DΩy b A r y u j i k a) -
        r y / 2 * (ϑy b r y i * Ωy b A y u j k a - ϑy b r y j * Ωy b A y u i k a) +
        r y * ϑy b r y k * Ωy b A y u i j a := by
  have hr0' := hr0 y
  unfold RmA
  rw [Γ_HHV, Γ_HHV]
  have dH : ∀ p q l : Fin n, fderiv ℝ (fun z : K × Quaternion ℝ => -(r z.1 / 2) * Ωc b A p q a z)
      (y, u) (Fa b A r (.inl l) (y, u)) =
      -(r y / 2) * dΩy b A r y u l p q a - Ωy b A y u p q a * (r y * ϑy b r y l / 2) := by
    intro p q l
    have e : (fun z : K × Quaternion ℝ => -(r z.1 / 2) * Ωc b A p q a z) =
        fun z => (fun x => -(r x / 2)) z.1 * Ωc b A p q a z := rfl
    rw [e, dprod ((hr.div_const 2).neg) (contDiff_Ωc hA p q a), Fa_H_fstx]
    have hrd := ((((hr.differentiable (by simp)) y).hasFDerivAt).const_mul
      (-(1 / 2 : ℝ))).congr_of_eventuallyEq (f₁ := fun x => -(r x / 2))
      (Eventually.of_forall fun y => by beta_reduce; ring)
    rw [hrd.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, r_derivx hr0, dΩy, Ωy]
    ring
  rw [dH, dH, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_HHH, Γ_HHV, Γ_HVH, Γ_VHH, Γ_HVV, Γ_VHV, cA, ΓB_zero, cB_zero, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, Finset.sum_const_zero]
  have t : ∑ x : Fin 3, -r y * Ωc b A i j x (y, u) * (ϑf b r k y * kron x a) =
      -(r y * ϑy b r y k * Ωy b A y u i j a) := by
    have := sum_smul_kron (V := ℝ) (fun x => -r y * Ωc b A i j x (y, u) * ϑf b r k y) a
    rw [Finset.sum_congr rfl fun x _ => show -r y * Ωc b A i j x (y, u) * (ϑf b r k y * kron x a)
      = -r y * Ωc b A i j x (y, u) * ϑf b r k y * kron x a by ring, this]
    simp only [Ωy, ϑy]; ring
  have g1 : ∑ x, (ΓB b j k x y * (-(r y / 2) * Ωc b A i x a (y, u)) -
      ΓB b i k x y * (-(r y / 2) * Ωc b A j x a (y, u))) =
      r y / 2 * (∑ l, ΓB b i k l y * Ωy b A y u j l a - ∑ l, ΓB b j k l y * Ωy b A y u i l a) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Ωy]; ring
  have g2 : ∑ l, cB b i j l y * (-(r y / 2) * Ωc b A l k a (y, u)) =
      -(r y / 2) * (∑ l, ΓB b i j l y * Ωy b A y u l k a - ∑ l, ΓB b j i l y * Ωy b A y u l k a) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← ΓB_sub_swap]
    simp only [Ωy]; ring
  rw [t, g1, g2]
  simp only [DΩy]
  ring

/-- **[HLY] `eq:VVVV`**. -/
theorem RmAy_VVVV (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (y : K) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (a c d e : Fin 3) :
    RmA b A r (.inr a) (.inr c) (.inr d) (.inr e) (y, u) =
      (1 / r y ^ 2 - ∑ k, ϑy b r y k ^ 2) * (kron c d * kron a e - kron a d * kron c e) := by
  have hr0' := hr0 y
  unfold RmA
  rw [Γ_VVV, Γ_VVV]
  have e1 : (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst c d e) =
      fun z => (fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst c d e) z.1 := rfl
  have e2 : (fun z : K × Quaternion ℝ => (r z.1)⁻¹ / 2 * Prop31Algebra.cst a d e) =
      fun z => (fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a d e) z.1 := rfl
  rw [e1, e2, dbase_Vx (φ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst c d e)
    (((hr.inv hr0).div_const 2).mul contDiff_const),
    dbase_Vx (φ := fun x => (r x)⁻¹ / 2 * Prop31Algebra.cst a d e)
    (((hr.inv hr0).div_const 2).mul contDiff_const), Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_VVH, Γ_VHV, Γ_VVV, cA, zero_mul, mul_zero, sub_zero, zero_sub, zero_add,
    Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (-(ϑf b r x y * kron c d) * (ϑf b r x y * kron a e) -
      -(ϑf b r x y * kron a d) * (ϑf b r x y * kron c e)) =
      -(∑ k, ϑy b r y k ^ 2) * (kron c d * kron a e - kron a d * kron c e) := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ϑy]; ring
  have t2 : ∑ x : Fin 3, ((r y)⁻¹ / 2 * Prop31Algebra.cst c d x * ((r y)⁻¹ / 2 * Prop31Algebra.cst a x e) -
      (r y)⁻¹ / 2 * Prop31Algebra.cst a d x * ((r y)⁻¹ / 2 * Prop31Algebra.cst c x e)) =
      (r y)⁻¹ ^ 2 * (1 / 4 * ∑ f, (Prop31Algebra.cst c d f * Prop31Algebra.cst a f e - Prop31Algebra.cst a d f * Prop31Algebra.cst c f e)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t3 : ∑ x : Fin 3, (r y)⁻¹ * Prop31Algebra.cst a c x * ((r y)⁻¹ / 2 * Prop31Algebra.cst x d e) =
      (r y)⁻¹ ^ 2 * (1 / 2 * ∑ f, Prop31Algebra.cst a c f * Prop31Algebra.cst f d e) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [t1, t2, t3]
  linear_combination (r y)⁻¹ ^ 2 * cst_quad a c d e

/-- **[HLY] `eq:HHHH`**, in components. -/
theorem RmAy_HHHH (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
    (hr0 : ∀ x, r x ≠ 0) (y : K) (u : Quaternion ℝ) (hu : Quaternion.normSq u = 1) (i j k l : Fin n) :
    RmA b A r (.inl i) (.inl j) (.inl k) (.inl l) (y, u) =
      (kron i l * kron j k - kron i k * kron j l) +
        r y ^ 2 / 4 * ∑ d, (Ωy b A y u i k d * Ωy b A y u j l d - Ωy b A y u j k d * Ωy b A y u i l d) +
        r y ^ 2 / 2 * ∑ d, Ωy b A y u i j d * Ωy b A y u k l d := by
  have hr0' := hr0 y
  unfold RmA
  rw [Γ_HHH, Γ_HHH]
  have dB : ∀ p q s t : Fin n, fderiv ℝ (fun z : K × Quaternion ℝ => ΓB b p q s z.1) (y, u)
      (Fa b A r (.inl t) (y, u)) = cfac y * ((kron t s * kron p q - kron t q * kron p s) / 2) := by
    intro p q s t
    have hΓ : ContDiff ℝ ∞ (ΓB b p q s) := by
      have e : ΓB b p q s = fun x => (⟪x, b s⟫ * kron p q - ⟪x, b q⟫ * kron p s) / 2 :=
        funext (ΓB_eq p q s)
      rw [e]
      exact (((contDiff_id.inner ℝ contDiff_const).mul contDiff_const).sub
        ((contDiff_id.inner ℝ contDiff_const).mul contDiff_const)).div_const 2
    rw [dbase_Hx hΓ]
    have e : ΓB b p q s = fun x => (⟪x, b s⟫ * kron p q - ⟪x, b q⟫ * kron p s) / 2 :=
      funext (ΓB_eq p q s)
    rw [e]
    have h1 : HasFDerivAt (fun x : K => ⟪x, b s⟫) (innerSL ℝ (b s)) y := by
      have := ((innerSL ℝ (b s)).hasFDerivAt (x := y))
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp [real_inner_comm]
    have h2 : HasFDerivAt (fun x : K => ⟪x, b q⟫) (innerSL ℝ (b q)) y := by
      have := ((innerSL ℝ (b q)).hasFDerivAt (x := y))
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp [real_inner_comm]
    have h := (((h1.mul_const (kron p q)).sub (h2.mul_const (kron p s))).const_mul
      (1 / 2 : ℝ)).congr_of_eventuallyEq
      (f₁ := fun x : K => (⟪x, b s⟫ * kron p q - ⟪x, b q⟫ * kron p s) / 2)
      (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)
    rw [h.fderiv]
    simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sub', Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul, innerSL_apply_apply]
    rw [eb, real_inner_smul_right, real_inner_smul_right, b.inner_eq_ite, b.inner_eq_ite, kron_comm t s,
      kron_comm t q]
    simp only [kron]
    ring
  rw [dB, dB, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Γ_HHH, Γ_HHV, Γ_HVH, Γ_VHH, cA, ΓB_zero, cB_zero, zero_mul, mul_zero, sub_zero,
    zero_sub, zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin 3, (-(r y / 2) * Ωc b A j k x (y, u) * (r y / 2 * Ωc b A i l x (y, u)) -
      -(r y / 2) * Ωc b A i k x (y, u) * (r y / 2 * Ωc b A j l x (y, u))) =
      r y ^ 2 / 4 * ∑ d, (Ωy b A y u i k d * Ωy b A y u j l d - Ωy b A y u j k d * Ωy b A y u i l d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ωy]; ring
  have t2 : ∑ x : Fin 3, -r y * Ωc b A i j x (y, u) * (r y / 2 * Ωc b A k l x (y, u)) =
      -(r y ^ 2 / 2 * ∑ d, Ωy b A y u i j d * Ωy b A y u k l d) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Ωy]; ring
  rw [t1, t2, show cfac y = 1 + ‖y‖ ^ 2 / 4 from rfl]
  linear_combination base_curv b y i j k l


end BlocksY

/-! ## D2's interface at every point `(y, u)` -/

section PackageY

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

theorem emb_y (y : K) (u : S3) : emb (y, u) = (y, (u : Quaternion ℝ)) := rfl

section Hyp

variable (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
  (hr0 : ∀ x, r x ≠ 0)

include hA hAim hr hr0

theorem RmPy_HVHV (y : K) (u : S3) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    RmP b A r (y, u) (Prop31Algebra.hv X) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.hv Y) =
      ∑ i, ∑ j, ∑ a, ∑ c, X i * U a * V c * Y j *
        Prop31Algebra.FHVHV (Ny b r y) (Ωy b A y u) (r y) i j a c := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_y,
    RmAy_HVHV hA hAim hr hr0 y _ (normSq_sphere u)]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  rfl

theorem RmPy_HHVV (y : K) (u : S3) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    RmP b A r (y, u) (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.vv U) (Prop31Algebra.vv V) =
      ∑ i, ∑ j, ∑ a, ∑ c, X i * Y j * U a * V c *
        Prop31Algebra.FHHVV (Ωy b A y u) (r y) i j a c := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_y,
    RmAy_HHVV hA hAim hr hr0 y _ (normSq_sphere u)]
  rfl

theorem RmPy_HVVV (y : K) (u : S3) (X : Fin n → ℝ) (U V Z : Fin 3 → ℝ) :
    RmP b A r (y, u) (Prop31Algebra.hv X) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.vv Z) =
      ∑ i, ∑ a, ∑ c, ∑ d, X i * U a * V c * Z d *
        Prop31Algebra.FHVVV (Ωy b A y u) (ϑy b r y) (r y) i a c d := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_y,
    RmAy_HVVV hA hAim hr hr0 y _ (normSq_sphere u)]
  rfl

theorem RmPy_HHHV (y : K) (u : S3) (X Y Z : Fin n → ℝ) (U : Fin 3 → ℝ) :
    RmP b A r (y, u) (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.hv Z) (Prop31Algebra.vv U) =
      ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * Z k * U a *
        Prop31Algebra.FHHHV (Ωy b A y u) (DΩy b A r y u) (ϑy b r y) (r y) i j k a := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_y,
    RmAy_HHHV hA hAim hr hr0 y _ (normSq_sphere u)]
  rfl

theorem RmPy_VVVV (y : K) (u : S3) (U V Z T : Fin 3 → ℝ) :
    RmP b A r (y, u) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.vv Z) (Prop31Algebra.vv T) =
      (1 / r y ^ 2 - ∑ k, ϑy b r y k ^ 2) *
        (Prop31Algebra.dot V Z * Prop31Algebra.dot U T - Prop31Algebra.dot U Z * Prop31Algebra.dot V T) := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_y,
    RmAy_VVVV hA hAim hr hr0 y _ (normSq_sphere u)]
  simp only [Fin.sum_univ_three, Prop31Algebra.dot, kron]
  simp
  ring

theorem RmPy_HHHH (y : K) (u : S3) (X Y : Fin n → ℝ) :
    RmP b A r (y, u) (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.hv Y) (Prop31Algebra.hv X) =
      Prop31Algebra.gram X Y - 3 / 4 * r y ^ 2 * ∑ c, Prop31Algebra.ΩXY (Ωy b A y u) X Y c ^ 2 := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_y,
    RmAy_HHHH hA hAim hr hr0 y _ (normSq_sphere u)]
  set Ω := Ωy b A y u
  have key : ∀ i j k l : Fin n, X i * Y j * Y k * X l *
      (kron i l * kron j k - kron i k * kron j l +
        r y ^ 2 / 4 * ∑ d, (Ω i k d * Ω j l d - Ω j k d * Ω i l d) +
        r y ^ 2 / 2 * ∑ d, Ω i j d * Ω k l d) =
      X i * Y j * Y k * X l * (kron j k * kron i l) - X i * Y j * Y k * X l * (kron i k * kron j l) +
        r y ^ 2 / 4 * (X i * Y j * Y k * X l * ∑ d, Ω i k d * Ω j l d) -
        r y ^ 2 / 4 * (X i * Y j * Y k * X l * ∑ d, Ω j k d * Ω i l d) +
        r y ^ 2 / 2 * (X i * Y j * Y k * X l * ∑ d, Ω i j d * Ω k l d) := by
    intro i j k l; rw [Finset.sum_sub_distrib]; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl
    fun k _ => Finset.sum_congr rfl fun l _ => key i j k l]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [pair23 kron kron X Y Y X, pair13 kron kron X Y Y X, pair13d Ω Ω X Y Y X, pair23d Ω Ω X Y Y X,
    pair12d Ω Ω X Y Y X]
  have hanti : ∀ d, ∀ i j, (fun a b => Ω a b d) j i = -(fun a b => Ω a b d) i j :=
    fun d i j => Ωc_swap i j d _
  have hYX : ∀ d, bf2 (fun a b => Ω a b d) Y X = -bf2 (fun a b => Ω a b d) X Y :=
    fun d => bf2_anti (hanti d) X Y
  have hYY : ∀ d, bf2 (fun a b => Ω a b d) Y Y = 0 := fun d => bf2_anti_self (hanti d) Y
  have hXX : ∀ d, bf2 (fun a b => Ω a b d) X X = 0 := fun d => bf2_anti_self (hanti d) X
  have hW : ∀ c, Prop31Algebra.ΩXY Ω X Y c = bf2 (fun a b => Ω a b c) X Y := fun c => rfl
  simp only [hYX, hYY, hXX, hW, bf2_kron, mul_zero, Finset.sum_const_zero, mul_neg,
    Finset.sum_neg_distrib, Prop31Algebra.gram, Prop31Algebra.dot_comm Y X, sq]
  ring

end Hyp

/-- **[HLY] Prop. 3.1, pointwise, for `RiemannianGeometry`'s curvature of the connection metric**, at the point `(y, u)` of the chart. The curvature blocks are no longer hypotheses: they are the theorems above.
What remains assumed is the quantitative data of D2 (`‖Ω‖ ≤ M₀`, `‖DΩ‖ ≤ M₁`, `N ≥ ν`, the
ε-budget), with `κ = 1` (the round base) and `t = |ϑ|`. -/
theorem hly_prop31_at (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hr : ContDiff ℝ ∞ r) (hrpos : ∀ x, 0 < r x) (y : K) (u : S3) (ν M0 M1 ε Λ D0 : ℝ)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hε : 0 < ε)
    (hOm : Prop31Algebra.OmSq (Ωy b A y u) ≤ 2 * M0 ^ 2)
    (hDOm : ∑ i, ∑ j, ∑ k, ∑ a, DΩy b A r y u i j k a ^ 2 ≤ 2 * M1 ^ 2)
    (hν : ∀ x : Fin n → ℝ, ν * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, Ny b r y i j * x i * x j)
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 * (M1 + 1) ^ 2 ≤ Λ)
    (hr2 : r y ^ 2 ≤ 2 * ε) (htD : √(∑ k, ϑy b r y k ^ 2) ≤ ε * D0 / 2)
    (hνΛ : ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4 ≤ ν)
    (hA2 : 2 * ε * M0 ≤ 1) (hA3 : ε * D0 * M0 ≤ 1)
    (hB2 : 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ 1)
    (hC1 : ε * D0 ^ 2 ≤ Λ / 4) (hC2 : 2 * ε ^ 3 * D0 ^ 2 ≤ 1)
    (hC3 : 32 * 4 ^ 2 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 ≤ Λ)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    min (min (1 / 2) (ε * Λ / 8)) (1 / (8 * ε)) * Prop31Algebra.totalGram X Y U V ≤
      riemannTensorAt isSymm_GH (isPosDef_GH (A := A) fun x => (hrpos x).ne').isNondegenerate
        (isContMDiffMetricSection_GH hA hr) (y, u) (vecF b A r _ (X, U))
        (vecF b A r _ (Y, V)) (vecF b A r _ (Y, V)) (vecF b A r _ (X, U)) := by
  have hr0 : ∀ x, r x ≠ 0 := fun x => (hrpos x).ne'
  rw [riemannTensorAt_vecF hA hAim hr hr0]
  have hS : 0 ≤ ∑ k, ϑy b r y k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  exact Prop31Algebra.prop31_pointwise (RmP b A r (y, u))
    (RmP_add1 _) (RmP_add2 _) (RmP_add3 _) (RmP_add4 _)
    (fun a b c d => RmP_swap_left hA hAim hr hr0 _ a b c d)
    (fun a b c d => RmP_swap_right hA hAim hr hr0 _ a b c d)
    (fun a b c d => RmP_pair hA hAim hr hr0 _ a b c d)
    (Ny b r y) (Ωy b A y u) (DΩy b A r y u) (ϑy b r y) Prop31Algebra.gram (r y)
    (√(∑ k, ϑy b r y k ^ 2)) ν 1 M0 M1 ε Λ D0
    (hrpos y) (Real.sqrt_nonneg _) hM0 hM1 one_pos hε
    (fun i j a => Ωc_swap i j a _) (Real.sq_sqrt hS).symm hOm hDOm hν
    (fun X Y => by rw [one_mul])
    (RmPy_HHHH hA hAim hr hr0 y u)
    (fun X U V Y => RmPy_HVHV hA hAim hr hr0 y u X Y U V)
    (RmPy_HHVV hA hAim hr hr0 y u) (RmPy_HVVV hA hAim hr hr0 y u) (RmPy_HHHV hA hAim hr hr0 y u)
    (fun U V Z T => by rw [RmPy_VVVV hA hAim hr hr0 y u, Real.sq_sqrt hS])
    (by rw [div_one]; exact hΛ) hr2 htD hνΛ hA2 hA3 hB2 hC1 hC2 hC3 X Y U V


/-- At `y = 0` the general-point data are the centre data of `S4_HLYBlocks`, so
`hly_prop31_centre_satisfiable` is also a model of the hypotheses of `hly_prop31_at`. -/
theorem data_y_zero (u : Quaternion ℝ) :
    Ωy b A 0 u = Ω0 b A u ∧ ϑy b r 0 = ϑ0 b r ∧ Ny b r 0 = N0 b r ∧ DΩy b A r 0 u = DΩ0 b A r u := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · funext i j
    simp [Ny, N0, dϑy, dϑ0, ϑy, ϑ0, eb_zero, ΓB_zero]
  · funext k i j a
    simp [DΩy, dΩy, DΩ0, ΓB_zero]

end PackageY

end

end ExoticSpheres8And10
