/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.Stereographic

/-! # §4, HLY model: the ambient bracket identities `eq:brackets`

On `K × ℍ`, for a gauge potential `A : K → L(K, ℍ)` and a fibre radius `r : K → ℝ`:

* `hlA A X (x, u) = (X x, −A_x(X x) u)`, the horizontal lift of a base field `X`;
* `vfA r e (x, u) = (0, r(x)⁻¹ u e)`, the normalised fundamental field `E_e = r⁻¹ e^#`.

Their Lie brackets are [HLY] `eq:brackets`, ambiently:

* `lieBracket_hlA`: `[X̃, Ỹ] = [X, Y]~ − (0, F(X, Y) u)`, with
  `F(X,Y) = (DA·X)(Y) − (DA·Y)(X) + A(X)A(Y) − A(Y)A(X)`, the curvature in this gauge;
* `lieBracket_hlA_vfA`: `[X̃, E_e] = −(X r / r) E_e`, i.e. `−ϑ(X) E_e`;
* `lieBracket_vfA`: `[E_e, E_{e'}] = r⁻¹ E_{ee' − e'e}`.
-/

namespace ExoticSpheres8And10

open Set Function Filter Topology Real VectorField

open scoped ContDiff

noncomputable section

section Ambient

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- The horizontal lift of the base field `X`. -/
def hlA (A : K → K →L[ℝ] Quaternion ℝ) (X : K → K) (z : K × Quaternion ℝ) :
    K × Quaternion ℝ :=
  (X z.1, -(A z.1 (X z.1)) * z.2)

/-- The normalised fundamental field `r⁻¹ e^#`. -/
def vfA (r : K → ℝ) (e : Quaternion ℝ) (z : K × Quaternion ℝ) : K × Quaternion ℝ :=
  (0, (r z.1)⁻¹ • (z.2 * e))

/-- The curvature of the gauge potential `A`, `F(v, w)`. -/
def curvA (A : K → K →L[ℝ] Quaternion ℝ) (x v w : K) : Quaternion ℝ :=
  fderiv ℝ A x v w - fderiv ℝ A x w v + A x v * A x w - A x w * A x v

variable {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ} {X Y : K → K}

/-- `d(hlA)` applied to `(a, ξ)`. -/
theorem fderiv_hlA_apply (hA : ContDiff ℝ ∞ A) (hX : ContDiff ℝ ∞ X) (z v : K × Quaternion ℝ) :
    fderiv ℝ (hlA A X) z v = (fderiv ℝ X z.1 v.1,
      -(A z.1 (fderiv ℝ X z.1 v.1) + fderiv ℝ A z.1 v.1 (X z.1)) * z.2 - A z.1 (X z.1) * v.2) := by
  have hXd : HasFDerivAt (fun y : K × Quaternion ℝ => X y.1)
      ((fderiv ℝ X z.1).comp (ContinuousLinearMap.fst ℝ K (Quaternion ℝ))) z :=
    ((hX.differentiable (by simp)) z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hAd : HasFDerivAt (fun y : K × Quaternion ℝ => A y.1)
      ((fderiv ℝ A z.1).comp (ContinuousLinearMap.fst ℝ K (Quaternion ℝ))) z :=
    ((hA.differentiable (by simp)) z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hAX := hAd.clm_apply hXd
  have hprod := hAX.neg.mul' (hasFDerivAt_snd (p := z))
  have h2 : HasFDerivAt (fun y : K × Quaternion ℝ => -(A y.1 (X y.1)) * y.2) _ z := hprod
  have h : HasFDerivAt (hlA A X) _ z := hXd.prodMk h2
  rw [h.fderiv]
  simp [sub_eq_add_neg, neg_mul, add_mul, add_comm]

/-- `d(vfA)` applied to `(a, ξ)`. -/
theorem fderiv_vfA_apply (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (e : Quaternion ℝ)
    (z v : K × Quaternion ℝ) :
    fderiv ℝ (vfA r e) z v = (0, (r z.1)⁻¹ • (v.2 * e) -
      (fderiv ℝ r z.1 v.1 / (r z.1) ^ 2) • (z.2 * e)) := by
  have hrd : HasFDerivAt (fun y : K × Quaternion ℝ => r y.1)
      ((fderiv ℝ r z.1).comp (ContinuousLinearMap.fst ℝ K (Quaternion ℝ))) z :=
    ((hr.differentiable (by simp)) z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hinv := (hasDerivAt_inv (hr0 z.1)).comp_hasFDerivAt z hrd
  have hs : HasFDerivAt (fun y : K × Quaternion ℝ => y.2) (ContinuousLinearMap.snd ℝ K (Quaternion ℝ)) z :=
    hasFDerivAt_snd
  have hue := hs.mul_const' e
  have h2 : HasFDerivAt (fun y : K × Quaternion ℝ => (r y.1)⁻¹ • (y.2 * e)) _ z :=
    hinv.smul hue
  have h : HasFDerivAt (vfA r e) _ z := (hasFDerivAt_const (0 : K) z).prodMk h2
  rw [h.fderiv]
  simp [sub_eq_add_neg, div_eq_inv_mul, neg_smul, smul_smul, add_comm]

/-- **`[X̃, Ỹ] = [X, Y]~ − (0, F(X, Y) u)`** ([HLY] `eq:brackets`, first identity). -/
theorem lieBracket_hlA (hA : ContDiff ℝ ∞ A) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (z : K × Quaternion ℝ) :
    lieBracket ℝ (hlA A X) (hlA A Y) z =
      hlA A (lieBracket ℝ X Y) z - (0, curvA A z.1 (X z.1) (Y z.1) * z.2) := by
  simp only [lieBracket_eq]
  rw [fderiv_hlA_apply hA hY, fderiv_hlA_apply hA hX]
  simp only [hlA, curvA]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_sub, map_sub, ContinuousLinearMap.sub_apply]
    noncomm_ring

/-- **`[X̃, E_e] = −(X r / r) E_e`** ([HLY] `eq:brackets`, second identity). -/
theorem lieBracket_hlA_vfA (hA : ContDiff ℝ ∞ A) (hX : ContDiff ℝ ∞ X)
    (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (e : Quaternion ℝ) (z : K × Quaternion ℝ) :
    lieBracket ℝ (hlA A X) (vfA r e) z =
      (-(fderiv ℝ r z.1 (X z.1) / r z.1)) • vfA r e z := by
  simp only [lieBracket_eq]
  rw [fderiv_vfA_apply hr hr0, fderiv_hlA_apply hA hX]
  simp only [hlA, vfA]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_sub, Prod.smul_snd, map_zero, zero_add, ContinuousLinearMap.zero_apply,
      neg_zero]
    simp only [map_zero, ContinuousLinearMap.zero_apply, zero_add, add_zero, neg_zero, zero_mul,
      mul_zero, sub_zero, zero_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, neg_mul, mul_neg,
      neg_smul, smul_neg, sub_neg_eq_add]
    module

/-- **`[E_e, E_{e'}] = r⁻¹ E_{ee' − e'e}`** ([HLY] `eq:brackets`, third identity). -/
theorem lieBracket_vfA (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (e e' : Quaternion ℝ)
    (z : K × Quaternion ℝ) :
    lieBracket ℝ (vfA r e) (vfA r e') z = (r z.1)⁻¹ • vfA r (e * e' - e' * e) z := by
  simp only [lieBracket_eq]
  rw [fderiv_vfA_apply hr hr0, fderiv_vfA_apply hr hr0]
  simp only [vfA]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_sub, Prod.smul_snd, map_zero, ContinuousLinearMap.zero_apply,
      zero_div, zero_smul, sub_zero]
    simp only [smul_mul_assoc, mul_assoc, mul_sub, smul_sub, smul_smul]

end Ambient

end

end ExoticSpheres8And10
