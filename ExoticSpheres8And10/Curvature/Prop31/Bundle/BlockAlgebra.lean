/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.FrameLocal
import ExoticSpheres8And10.Curvature.HLYModel.Christoffel
import ExoticSpheres8And10.Curvature.HLYModel.BlocksCentre

/-! # The HLY curvature blocks from an abstract bracket table

On any manifold `M` (any model, boundary allowed), consider a frame `F : Fin n ⊕ Fin 3 → fields`
whose bracket table has [HLY]'s shape. The table `cT` is built from functions
`c^B_{ijk}, Ω_{ij}^a, r, ϑ_i` on `M`:
* `[X_i, X_j] = Σ c^B_{ijk} X_k − r Ω_{ij}^a E_a`;
* `[X_i, E_a] = −ϑ_i E_a`;
* `[E_a, E_b] = r⁻¹ cst_{abc} E_c`.

Fix their frame derivatives at a point `x`, as numbers:
* along `X_k`: `dcB`, `r ϑ_k`, `dϑ`, `dΩ`;
* along `E_a`: `0` for `c^B, r, ϑ`, and `r⁻¹ Σ_d Ω_{ij}^d cst_{dac}` for `Ω`.

Then the frame-calculus curvature `RmF` (the right side of `riemannTensorAt_frame_loc`) has
[HLY]'s six blocks, in D2's form, with:
* `N_{ij} = −dϑ_{ij} − ϑ_iϑ_j − Σ_k Γ^B_{ikj} ϑ_k`;
* `DΩ_{kij}^a = dΩ_{kij}^a − Σ_l Γ^B_{kil}Ω_{lj}^a − Σ_l Γ^B_{kjl}Ω_{il}^a`;
* the base curvature `RB`, the frame formula of `c^B`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section BlockAlg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ}

variable (cBf : Fin n → Fin n → Fin n → M → ℝ) (Ωf : Fin n → Fin n → Fin 3 → M → ℝ)
  (rf : M → ℝ) (ϑf : Fin n → M → ℝ)

/-- **The HLY bracket table**, abstractly. -/
def cT : Fin n ⊕ Fin 3 → Fin n ⊕ Fin 3 → Fin n ⊕ Fin 3 → M → ℝ
  | .inl i, .inl j, .inl k => cBf i j k
  | .inl i, .inl j, .inr a => fun z => -(rf z) * Ωf i j a z
  | .inl i, .inr a, .inr c => fun z => -(ϑf i z) * kron a c
  | .inr a, .inl i, .inr c => fun z => ϑf i z * kron a c
  | .inr a, .inr c, .inr d => fun z => (rf z)⁻¹ * Prop31Algebra.cst a c d
  | _, _, _ => fun _ => 0

/-- The base connection coefficients `Γ^B_{ijk} = ½(c^B_{ijk} − c^B_{ikj} − c^B_{jki})`. -/
def ΓBf (i j k : Fin n) (z : M) : ℝ := (cBf i j k z - cBf i k j z - cBf j k i z) / 2

variable {cBf Ωf rf ϑf}

theorem TΓ_HHH (i j k : Fin n) :
    frameΓ (cT cBf Ωf rf ϑf) (.inl i) (.inl j) (.inl k) = ΓBf cBf i j k := rfl

theorem TΓ_HHV (i j : Fin n) (a : Fin 3) :
    frameΓ (cT cBf Ωf rf ϑf) (.inl i) (.inl j) (.inr a) = fun z => -(rf z / 2) * Ωf i j a z := by
  funext z; simp only [frameΓ, cT]; ring

theorem TΓ_HVH (i j : Fin n) (a : Fin 3) :
    frameΓ (cT cBf Ωf rf ϑf) (.inl i) (.inr a) (.inl j) = fun z => rf z / 2 * Ωf i j a z := by
  funext z; simp only [frameΓ, cT]; ring

theorem TΓ_HVV (i : Fin n) (a c : Fin 3) :
    frameΓ (cT cBf Ωf rf ϑf) (.inl i) (.inr a) (.inr c) = fun _ => 0 := by
  funext z; simp only [frameΓ, cT, kron_comm c a]; ring

theorem TΓ_VHH (i j : Fin n) (a : Fin 3) :
    frameΓ (cT cBf Ωf rf ϑf) (.inr a) (.inl i) (.inl j) = fun z => rf z / 2 * Ωf i j a z := by
  funext z; simp only [frameΓ, cT]; ring

theorem TΓ_VHV (i : Fin n) (a c : Fin 3) :
    frameΓ (cT cBf Ωf rf ϑf) (.inr a) (.inl i) (.inr c) = fun z => ϑf i z * kron a c := by
  funext z; simp only [frameΓ, cT, kron_comm c a]; ring

theorem TΓ_VVH (i : Fin n) (a c : Fin 3) :
    frameΓ (cT cBf Ωf rf ϑf) (.inr a) (.inr c) (.inl i) = fun z => -(ϑf i z * kron a c) := by
  funext z; simp only [frameΓ, cT, kron_comm c a]; ring

theorem TΓ_VVV (a c d : Fin 3) :
    frameΓ (cT cBf Ωf rf ϑf) (.inr a) (.inr c) (.inr d) = fun z => (rf z)⁻¹ / 2 * Prop31Algebra.cst a c d := by
  funext z; simp only [frameΓ, cT]; rw [cst_swap23 a c d, cst_cycle a c d]; ring

variable (cBf Ωf rf ϑf) in
/-- **The frame-calculus curvature** `Rm(F_α, F_β, F_γ, F_δ)` at `x`. -/
def RmF (F : Fin n ⊕ Fin 3 → Π y : M, TangentSpace I y) (x : M) (α β γ δ : Fin n ⊕ Fin 3) : ℝ :=
  mvfderiv I (frameΓ (cT cBf Ωf rf ϑf) β γ δ) x (F α x) -
    mvfderiv I (frameΓ (cT cBf Ωf rf ϑf) α γ δ) x (F β x) +
    ∑ ε, (frameΓ (cT cBf Ωf rf ϑf) β γ ε x * frameΓ (cT cBf Ωf rf ϑf) α ε δ x -
      frameΓ (cT cBf Ωf rf ϑf) α γ ε x * frameΓ (cT cBf Ωf rf ϑf) β ε δ x) -
    ∑ ε, cT cBf Ωf rf ϑf α β ε x * frameΓ (cT cBf Ωf rf ϑf) ε γ δ x

/-! ### Real-valued derivative rules -/

theorem mvfderiv_mul_real {f g : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) (v : TangentSpace I x) :
    mvfderiv I (fun z => f z * g z) x v = f x * mvfderiv I g x v + g x * mvfderiv I f x v := by
  have h := (hf.hasMFDerivAt.mul hg.hasMFDerivAt).mfderiv
  have h' := congrArg (fun L => L v) h
  exact h'

theorem mvfderiv_const_real (k : ℝ) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun _ : M => k) x v = 0 := by
  simp [mvfderiv, mfderiv_const]

theorem mvfderiv_neg_real {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (v : TangentSpace I x) : mvfderiv I (fun z => -f z) x v = -mvfderiv I f x v := by
  have h := mvfderiv_clm_comp (-(ContinuousLinearMap.id ℝ ℝ)) hf v
  exact h

theorem mvfderiv_mul_const_real {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x) (k : ℝ)
    (v : TangentSpace I x) : mvfderiv I (fun z => f z * k) x v = mvfderiv I f x v * k := by
  rw [mvfderiv_mul_real hf mdifferentiableAt_const, mvfderiv_const_real]; ring

theorem mvfderiv_const_mul_real {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x) (k : ℝ)
    (v : TangentSpace I x) : mvfderiv I (fun z => k * f z) x v = k * mvfderiv I f x v := by
  rw [mvfderiv_mul_real mdifferentiableAt_const hf, mvfderiv_const_real]; ring

end BlockAlg

section Blocks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} {cBf : Fin n → Fin n → Fin n → M → ℝ} {Ωf : Fin n → Fin n → Fin 3 → M → ℝ}
  {rf : M → ℝ} {ϑf : Fin n → M → ℝ}
  {F : Fin n ⊕ Fin 3 → Π y : M, TangentSpace I y} {z₀ : M}
  {dcB : Fin n → Fin n → Fin n → Fin n → ℝ} {dϑ : Fin n → Fin n → ℝ}
  {dΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ}

theorem mvfderiv_inv_real {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x) (h0 : f x ≠ 0)
    (v : TangentSpace I x) :
    mvfderiv I (fun z => (f z)⁻¹) x v = -((f x ^ 2)⁻¹) * mvfderiv I f x v := by
  have hinv : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => t⁻¹) (f x) :=
    ((hasDerivAt_inv h0).differentiableAt).mdifferentiableAt
  rw [show (fun z => (f z)⁻¹) = (fun t : ℝ => t⁻¹) ∘ f from rfl, mvfderiv_comp_apply hinv hf,
    mvfderiv_vs, (hasDerivAt_inv h0).hasFDerivAt.fderiv]
  show (mvfderiv I f x v) * (-(f x ^ 2)⁻¹) = -((f x ^ 2)⁻¹) * mvfderiv I f x v
  rw [mul_comm]

/-- `N_{ij} = −dϑ_{ij} − ϑ_iϑ_j − Σ_k Γ^B_{ikj}ϑ_k`. -/
def Nf (cBf : Fin n → Fin n → Fin n → M → ℝ) (ϑf : Fin n → M → ℝ) (z₀ : M)
    (dϑ : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  -dϑ i j - ϑf i z₀ * ϑf j z₀ - ∑ k, ΓBf cBf i k j z₀ * ϑf k z₀

/-- `DΩ_{kij}^a = dΩ_{kij}^a − Σ_l Γ^B_{kil}Ω_{lj}^a − Σ_l Γ^B_{kjl}Ω_{il}^a`. -/
def DΩf (cBf : Fin n → Fin n → Fin n → M → ℝ) (Ωf : Fin n → Fin n → Fin 3 → M → ℝ) (z₀ : M)
    (dΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ) (k i j : Fin n) (a : Fin 3) : ℝ :=
  dΩ k i j a - ∑ l, ΓBf cBf k i l z₀ * Ωf l j a z₀ - ∑ l, ΓBf cBf k j l z₀ * Ωf i l a z₀

/-- The frame derivative of `Γ^B_{pqs}` along `X_t`. -/
def dΓB (dcB : Fin n → Fin n → Fin n → Fin n → ℝ) (t p q s : Fin n) : ℝ :=
  (dcB t p q s - dcB t p s q - dcB t q s p) / 2

/-- **The base curvature** in the frame `e_i`: the frame formula of `c^B`. -/
def RBf (cBf : Fin n → Fin n → Fin n → M → ℝ) (z₀ : M) (dcB : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j k l : Fin n) : ℝ :=
  dΓB dcB i j k l - dΓB dcB j i k l +
    ∑ x, (ΓBf cBf j k x z₀ * ΓBf cBf i x l z₀ - ΓBf cBf i k x z₀ * ΓBf cBf j x l z₀) -
    ∑ x, cBf i j x z₀ * ΓBf cBf x k l z₀

variable (hcBd : ∀ i j k, MDifferentiableAt I 𝓘(ℝ) (cBf i j k) z₀)
  (hΩd : ∀ i j a, MDifferentiableAt I 𝓘(ℝ) (Ωf i j a) z₀)
  (hrd : MDifferentiableAt I 𝓘(ℝ) rf z₀) (hϑd : ∀ i, MDifferentiableAt I 𝓘(ℝ) (ϑf i) z₀)
  (hr0 : rf z₀ ≠ 0)
  (hcB_H : ∀ l i j k, mvfderiv I (cBf i j k) z₀ (F (.inl l) z₀) = dcB l i j k)
  (hr_H : ∀ k, mvfderiv I rf z₀ (F (.inl k) z₀) = rf z₀ * ϑf k z₀)
  (hr_V : ∀ a, mvfderiv I rf z₀ (F (.inr a) z₀) = 0)
  (hϑ_H : ∀ k i, mvfderiv I (ϑf i) z₀ (F (.inl k) z₀) = dϑ k i)
  (hΩ_H : ∀ k i j c, mvfderiv I (Ωf i j c) z₀ (F (.inl k) z₀) = dΩ k i j c)
  (hΩ_V : ∀ a i j c, mvfderiv I (Ωf i j c) z₀ (F (.inr a) z₀) =
    (rf z₀)⁻¹ * ∑ d, Ωf i j d z₀ * Prop31Algebra.cst d a c)
  (hΩanti : ∀ i j a, Ωf j i a z₀ = -Ωf i j a z₀)
  (hcBanti : ∀ i j l, cBf j i l z₀ = -cBf i j l z₀)

include hϑd hrd hΩd hr0 hϑ_H hr_V hΩ_V hΩanti in
/-- **[HLY] `eq:HVHV`**, abstractly. -/
theorem RmF_HVHV (i j : Fin n) (a c : Fin 3) :
    RmF cBf Ωf rf ϑf F z₀ (.inl i) (.inr a) (.inr c) (.inl j) =
      Nf cBf ϑf z₀ dϑ i j * kron a c + rf z₀ ^ 2 / 4 * ∑ k, Ωf i k c z₀ * Ωf j k a z₀ -
        1 / 4 * ∑ d, Prop31Algebra.cst a c d * Ωf i j d z₀ := by
  unfold RmF
  rw [TΓ_VVH, TΓ_HVH]
  have d1 : mvfderiv I (fun z => -(ϑf j z * kron a c)) z₀ (F (.inl i) z₀) = -(dϑ i j * kron a c) := by
    rw [mvfderiv_neg_real (f := fun z => ϑf j z * kron a c) ((hϑd j).mul mdifferentiableAt_const),
      mvfderiv_mul_const_real (hϑd j), hϑ_H]
  have d2 : mvfderiv I (fun z => rf z / 2 * Ωf i j c z) z₀ (F (.inr a) z₀) =
      1 / 2 * ∑ d, Ωf i j d z₀ * Prop31Algebra.cst d a c := by
    have hrd2 : MDifferentiableAt I 𝓘(ℝ) (fun z => rf z / 2) z₀ := hrd.mul mdifferentiableAt_const
    rw [mvfderiv_mul_real hrd2 (hΩd i j c), hΩ_V]
    rw [show (fun z => rf z / 2) = fun z => rf z * (1 / 2) from funext fun z => by ring,
      mvfderiv_mul_const_real hrd, hr_V]
    simp only [zero_mul, mul_zero, add_zero]
    field_simp
  rw [d1, d2, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [TΓ_VVH, TΓ_HHH, TΓ_VVV, TΓ_HVH, TΓ_HVV, TΓ_VHH, cT, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, Finset.sum_const_zero]
  have hkron : ∑ d : Fin 3, kron a d * kron d c = kron a c := by
    simp only [kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hcst : ∀ d : Fin 3, Prop31Algebra.cst d a c = Prop31Algebra.cst a c d := fun d => by
    rw [cst_cycle c d a, cst_cycle a c d]
  have hsw : ∀ k : Fin n, Ωf k j a z₀ = -Ωf j k a z₀ := fun k => hΩanti j k a
  simp only [hsw, hcst]
  have t1 : ∑ x : Fin 3, Ωf i j x z₀ * Prop31Algebra.cst a c x = ∑ d, Prop31Algebra.cst a c d * Ωf i j d z₀ :=
    Finset.sum_congr rfl fun x _ => by ring
  have t2 : ∑ x : Fin n, (-(ϑf x z₀ * kron a c) * ΓBf cBf i x j z₀ -
      rf z₀ / 2 * Ωf i x c z₀ * (rf z₀ / 2 * -Ωf j x a z₀)) =
      rf z₀ ^ 2 / 4 * ∑ k, Ωf i k c z₀ * Ωf j k a z₀ -
        kron a c * ∑ k, ΓBf cBf i k j z₀ * ϑf k z₀ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t3 : ∑ x : Fin 3, (rf z₀)⁻¹ / 2 * Prop31Algebra.cst a c x * (rf z₀ / 2 * Ωf i j x z₀) =
      1 / 4 * ∑ d, Prop31Algebra.cst a c d * Ωf i j d z₀ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (rf z₀)⁻¹ / 2 * Prop31Algebra.cst a c x * (rf z₀ / 2 * Ωf i j x z₀) =
      ((rf z₀)⁻¹ * rf z₀) * (1 / 4 * (Prop31Algebra.cst a c x * Ωf i j x z₀)) by ring,
      inv_mul_cancel₀ hr0, one_mul]
  have t4 : ∑ x : Fin 3, -ϑf i z₀ * kron a x * -(ϑf j z₀ * kron x c) =
      ϑf i z₀ * ϑf j z₀ * kron a c := by
    rw [← hkron, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [t1, t2, t3, t4]
  simp only [Nf]
  ring

include hrd hr0 hΩanti in
/-- **[HLY] `eq:HHVV`**, abstractly. -/
theorem RmF_HHVV (i j : Fin n) (a c : Fin 3) :
    RmF cBf Ωf rf ϑf F z₀ (.inl i) (.inl j) (.inr a) (.inr c) =
      rf z₀ ^ 2 / 4 * ∑ k, (Ωf i k a z₀ * Ωf j k c z₀ - Ωf j k a z₀ * Ωf i k c z₀) +
        1 / 2 * ∑ d, Prop31Algebra.cst a c d * Ωf i j d z₀ := by
  unfold RmF
  rw [TΓ_HVV, TΓ_HVV, mvfderiv_const_real, mvfderiv_const_real, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp only [TΓ_HVH, TΓ_HHV, TΓ_HVV, TΓ_VVV, cT, zero_mul, mul_zero, sub_zero, zero_sub,
    zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (rf z₀ / 2 * Ωf j x a z₀ * (-(rf z₀ / 2) * Ωf i x c z₀) -
      rf z₀ / 2 * Ωf i x a z₀ * (-(rf z₀ / 2) * Ωf j x c z₀)) =
      rf z₀ ^ 2 / 4 * ∑ k, (Ωf i k a z₀ * Ωf j k c z₀ - Ωf j k a z₀ * Ωf i k c z₀) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t2 : ∑ x : Fin 3, -rf z₀ * Ωf i j x z₀ * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst x a c) =
      -(1 / 2 * ∑ d, Prop31Algebra.cst a c d * Ωf i j d z₀) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cst_rot]
    field_simp
  rw [t1, t2]
  ring

include hrd hr0 hr_H in
/-- **[HLY] `eq:HVVV`**, abstractly. -/
theorem RmF_HVVV (i : Fin n) (a c d : Fin 3) :
    RmF cBf Ωf rf ϑf F z₀ (.inl i) (.inr a) (.inr c) (.inr d) =
      rf z₀ / 2 * ∑ k, ϑf k z₀ * (kron a c * Ωf i k d z₀ - kron a d * Ωf i k c z₀) := by
  unfold RmF
  rw [TΓ_VVV, TΓ_HVV, mvfderiv_const_real, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have d1 : mvfderiv I (fun z => (rf z)⁻¹ / 2 * Prop31Algebra.cst a c d) z₀ (F (.inl i) z₀) =
      -(ϑf i z₀ / rf z₀) / 2 * Prop31Algebra.cst a c d := by
    have hinv : MDifferentiableAt I 𝓘(ℝ) (fun z => (rf z)⁻¹) z₀ :=
      ((hasDerivAt_inv hr0).differentiableAt.mdifferentiableAt).comp z₀ hrd
    rw [show (fun z => (rf z)⁻¹ / 2 * Prop31Algebra.cst a c d) = fun z => (rf z)⁻¹ * (Prop31Algebra.cst a c d / 2)
      from funext fun z => by ring, mvfderiv_mul_const_real hinv, mvfderiv_inv_real hrd hr0,
      hr_H]
    field_simp
  rw [d1]
  simp only [TΓ_VVH, TΓ_HHV, TΓ_HVH, TΓ_VHV, TΓ_VVV, TΓ_HVV, cT, zero_mul, mul_zero, sub_zero,
    zero_sub, zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (-(ϑf x z₀ * kron a c) * (-(rf z₀ / 2) * Ωf i x d z₀) -
      rf z₀ / 2 * Ωf i x c z₀ * (ϑf x z₀ * kron a d)) =
      rf z₀ / 2 * ∑ k, ϑf k z₀ * (kron a c * Ωf i k d z₀ - kron a d * Ωf i k c z₀) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t2 : ∑ x : Fin 3, -ϑf i z₀ * kron a x * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst x c d) =
      -(ϑf i z₀ * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst a c d)) := by
    rw [Finset.sum_congr rfl fun x _ => show -ϑf i z₀ * kron a x * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst x c d)
      = kron a x * (-ϑf i z₀ * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst x c d)) by ring]
    refine (sum_kron_left (fun x => -ϑf i z₀ * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst x c d)) a).trans ?_
    ring
  rw [t1, t2]
  field_simp
  ring

include hrd hΩd hr_H hΩ_H hcBanti in
/-- **[HLY] `eq:HHHV`**, abstractly. -/
theorem RmF_HHHV (i j k : Fin n) (a : Fin 3) :
    RmF cBf Ωf rf ϑf F z₀ (.inl i) (.inl j) (.inl k) (.inr a) =
      -(rf z₀ / 2) * (DΩf cBf Ωf z₀ dΩ i j k a - DΩf cBf Ωf z₀ dΩ j i k a) -
        rf z₀ / 2 * (ϑf i z₀ * Ωf j k a z₀ - ϑf j z₀ * Ωf i k a z₀) +
        rf z₀ * ϑf k z₀ * Ωf i j a z₀ := by
  unfold RmF
  rw [TΓ_HHV, TΓ_HHV]
  have dH : ∀ p q l : Fin n, mvfderiv I (fun z => -(rf z / 2) * Ωf p q a z) z₀ (F (.inl l) z₀) =
      -(rf z₀ / 2) * dΩ l p q a - Ωf p q a z₀ * (rf z₀ * ϑf l z₀ / 2) := by
    intro p q l
    have hr2 : MDifferentiableAt I 𝓘(ℝ) (fun z => -(rf z / 2)) z₀ :=
      (hrd.mul mdifferentiableAt_const).neg
    rw [mvfderiv_mul_real hr2 (hΩd p q a), hΩ_H,
      show (fun z => -(rf z / 2)) = fun z => rf z * (-(1 / 2)) from funext fun z => by ring,
      mvfderiv_mul_const_real hrd, hr_H]
    ring
  rw [dH, dH, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [TΓ_HHH, TΓ_HHV, TΓ_HVH, TΓ_VHH, TΓ_HVV, TΓ_VHV, cT, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, Finset.sum_const_zero]
  have t : ∑ x : Fin 3, -rf z₀ * Ωf i j x z₀ * (ϑf k z₀ * kron x a) =
      -(rf z₀ * ϑf k z₀ * Ωf i j a z₀) := by
    have := sum_smul_kron (V := ℝ) (fun x => -rf z₀ * Ωf i j x z₀ * ϑf k z₀) a
    rw [Finset.sum_congr rfl fun x _ => show -rf z₀ * Ωf i j x z₀ * (ϑf k z₀ * kron x a)
      = -rf z₀ * Ωf i j x z₀ * ϑf k z₀ * kron x a by ring, this]
    ring
  have hsub : ∀ l, ΓBf cBf i j l z₀ - ΓBf cBf j i l z₀ = cBf i j l z₀ := fun l => by
    simp only [ΓBf]; rw [hcBanti i j l]; ring
  have g1 : ∑ x, (ΓBf cBf j k x z₀ * (-(rf z₀ / 2) * Ωf i x a z₀) -
      ΓBf cBf i k x z₀ * (-(rf z₀ / 2) * Ωf j x a z₀)) =
      rf z₀ / 2 * (∑ l, ΓBf cBf i k l z₀ * Ωf j l a z₀ - ∑ l, ΓBf cBf j k l z₀ * Ωf i l a z₀) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have g2 : ∑ l, cBf i j l z₀ * (-(rf z₀ / 2) * Ωf l k a z₀) =
      -(rf z₀ / 2) * (∑ l, ΓBf cBf i j l z₀ * Ωf l k a z₀ - ∑ l, ΓBf cBf j i l z₀ * Ωf l k a z₀) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hsub]
    ring
  rw [t, g1, g2]
  simp only [DΩf]
  ring

include hrd hr0 hr_V in
/-- **[HLY] `eq:VVVV`**, abstractly. -/
theorem RmF_VVVV (a c d e : Fin 3) :
    RmF cBf Ωf rf ϑf F z₀ (.inr a) (.inr c) (.inr d) (.inr e) =
      (1 / rf z₀ ^ 2 - ∑ k, ϑf k z₀ ^ 2) * (kron c d * kron a e - kron a d * kron c e) := by
  unfold RmF
  rw [TΓ_VVV, TΓ_VVV]
  have dV : ∀ (k : ℝ) (b : Fin 3), mvfderiv I (fun z => (rf z)⁻¹ / 2 * k) z₀ (F (.inr b) z₀) = 0 := by
    intro k b
    have hinv : MDifferentiableAt I 𝓘(ℝ) (fun z => (rf z)⁻¹) z₀ :=
      ((hasDerivAt_inv hr0).differentiableAt.mdifferentiableAt).comp z₀ hrd
    rw [show (fun z => (rf z)⁻¹ / 2 * k) = fun z => (rf z)⁻¹ * (k / 2)
      from funext fun z => by ring, mvfderiv_mul_const_real hinv, mvfderiv_inv_real hrd hr0, hr_V]
    ring
  rw [dV, dV, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [TΓ_VVH, TΓ_VHV, TΓ_VVV, cT, zero_mul, mul_zero, sub_zero, zero_sub, zero_add,
    Finset.sum_const_zero]
  have t1 : ∑ x : Fin n, (-(ϑf x z₀ * kron c d) * (ϑf x z₀ * kron a e) -
      -(ϑf x z₀ * kron a d) * (ϑf x z₀ * kron c e)) =
      -(∑ k, ϑf k z₀ ^ 2) * (kron c d * kron a e - kron a d * kron c e) := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t2 : ∑ x : Fin 3, ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst c d x * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst a x e) -
      (rf z₀)⁻¹ / 2 * Prop31Algebra.cst a d x * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst c x e)) =
      (rf z₀)⁻¹ ^ 2 * (1 / 4 * ∑ f, (Prop31Algebra.cst c d f * Prop31Algebra.cst a f e - Prop31Algebra.cst a d f * Prop31Algebra.cst c f e)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t3 : ∑ x : Fin 3, (rf z₀)⁻¹ * Prop31Algebra.cst a c x * ((rf z₀)⁻¹ / 2 * Prop31Algebra.cst x d e) =
      (rf z₀)⁻¹ ^ 2 * (1 / 2 * ∑ f, Prop31Algebra.cst a c f * Prop31Algebra.cst f d e) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [t1, t2, t3]
  rw [show 1 / rf z₀ ^ 2 = (rf z₀)⁻¹ ^ 2 by field_simp]
  linear_combination (rf z₀)⁻¹ ^ 2 * cst_quad a c d e

include hcBd hcB_H in
/-- **[HLY] `eq:HHHH`**, abstractly: the base curvature plus the `Ω²` terms. -/
theorem RmF_HHHH (i j k l : Fin n) :
    RmF cBf Ωf rf ϑf F z₀ (.inl i) (.inl j) (.inl k) (.inl l) =
      RBf cBf z₀ dcB i j k l +
        rf z₀ ^ 2 / 4 * ∑ d, (Ωf i k d z₀ * Ωf j l d z₀ - Ωf j k d z₀ * Ωf i l d z₀) +
        rf z₀ ^ 2 / 2 * ∑ d, Ωf i j d z₀ * Ωf k l d z₀ := by
  unfold RmF
  rw [TΓ_HHH, TΓ_HHH]
  have dB : ∀ p q s t : Fin n, mvfderiv I (ΓBf cBf p q s) z₀ (F (.inl t) z₀) = dΓB dcB t p q s := by
    intro p q s t
    have e : ΓBf cBf p q s = fun z => (cBf p q s z - cBf p s q z - cBf q s p z) * (1 / 2) := by
      funext z; simp only [ΓBf]; ring
    rw [e, mvfderiv_mul_const_real (f := fun z => cBf p q s z - cBf p s q z - cBf q s p z)
      (((hcBd p q s).sub (hcBd p s q)).sub (hcBd q s p))]
    have hs : ∀ (f g : M → ℝ), MDifferentiableAt I 𝓘(ℝ) f z₀ → MDifferentiableAt I 𝓘(ℝ) g z₀ →
        mvfderiv I (fun z => f z - g z) z₀ (F (.inl t) z₀) =
          mvfderiv I f z₀ (F (.inl t) z₀) - mvfderiv I g z₀ (F (.inl t) z₀) := fun f g hf hg => by
      have := (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv
      exact congrArg (fun L => L (F (.inl t) z₀)) this
    rw [hs (fun z => cBf p q s z - cBf p s q z) (cBf q s p) ((hcBd p q s).sub (hcBd p s q))
      (hcBd q s p), hs (cBf p q s) (cBf p s q) (hcBd p q s) (hcBd p s q), hcB_H, hcB_H, hcB_H]
    simp only [dΓB]; ring
  rw [dB, dB, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [TΓ_HHH, TΓ_HHV, TΓ_HVH, TΓ_VHH, cT, zero_mul, mul_zero, sub_zero,
    zero_sub, zero_add, Finset.sum_const_zero]
  have t1 : ∑ x : Fin 3, (-(rf z₀ / 2) * Ωf j k x z₀ * (rf z₀ / 2 * Ωf i l x z₀) -
      -(rf z₀ / 2) * Ωf i k x z₀ * (rf z₀ / 2 * Ωf j l x z₀)) =
      rf z₀ ^ 2 / 4 * ∑ d, (Ωf i k d z₀ * Ωf j l d z₀ - Ωf j k d z₀ * Ωf i l d z₀) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have t2 : ∑ x : Fin 3, -rf z₀ * Ωf i j x z₀ * (rf z₀ / 2 * Ωf k l x z₀) =
      -(rf z₀ ^ 2 / 2 * ∑ d, Ωf i j d z₀ * Ωf k l d z₀) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [t1, t2]
  simp only [RBf]
  ring

end Blocks

end

end ExoticSpheres8And10
