/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Southern.Quotient
import ExoticSpheres8And10.PolarBundles.PolarBundle

/-! # §4, the southern connection `A_S = (χ − 1) dθ θ⁻¹` from the polar data (`eq:potentials`)

On the chart `V = e^⊥` centred at the south pole:
- `ρVs`: the star representation restricted to `V`, a smooth `S³ →* (V ≃ₗᵢ V)`;
- `θh y = θ(y/|y|)`, smooth on `V ∖ {0}`, with unit values;
- `AS χt y = (χt(|y|²) − 1)·(dθh_y)·θh(y)⁻¹`, for a smooth cutoff `χt` equal to `1` near `0`
  (the south pole). [GG]'s `χ(t)` is `χt(|y|²)` with `|y| = 2 tan((π−t)/2)`.

Then:
- `contDiff_AS`: `A_S` is smooth on all of `V`, since it vanishes near `o_S`;
- `AS_im`: `A_S` is imaginary;
- `AS_equiv`: `A_S(ρ(q)y)(ρ(q)a) = q A_S(y)(a) q⁻¹` ([GG]: `ρ(q)^*A_S = qA_Sq⁻¹`).

So [GG]'s southern data satisfy the hypotheses of `southern_quotient_pos` (`southern_quotient_pos_D`).
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real Module

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

section Potential

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

namespace PolarData

theorem ρ_mem_Vs (q : S3) (y : Vs e) : D.ρ q (y : W) ∈ Vs e := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have h1 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 y.2
  calc ⟪e, D.ρ q (y : W)⟫ = ⟪D.ρ q e, D.ρ q (y : W)⟫ := by rw [D.ρ_e]
    _ = 0 := by rw [LinearIsometryEquiv.inner_map_map, h1]

/-- `ρ(q)` restricted to `V = e^⊥`. -/
def ρVsE (q : S3) : Vs e ≃ₗᵢ[ℝ] Vs e where
  toFun y := ⟨D.ρ q y, D.ρ_mem_Vs q y⟩
  invFun y := ⟨D.ρ q⁻¹ y, D.ρ_mem_Vs q⁻¹ y⟩
  map_add' y y' := by ext; simp
  map_smul' c y := by ext; simp
  left_inv y := by
    ext; show D.ρ q⁻¹ (D.ρ q (y : W)) = y
    rw [show D.ρ q⁻¹ (D.ρ q (y : W)) = (D.ρ q⁻¹ * D.ρ q) (y : W) from rfl, ← map_mul,
      inv_mul_cancel, map_one]; rfl
  right_inv y := by
    ext; show D.ρ q (D.ρ q⁻¹ (y : W)) = y
    rw [show D.ρ q (D.ρ q⁻¹ (y : W)) = (D.ρ q * D.ρ q⁻¹) (y : W) from rfl, ← map_mul,
      mul_inv_cancel, map_one]; rfl
  norm_map' y := by
    show ‖(⟨D.ρ q y, _⟩ : Vs e)‖ = ‖y‖
    rw [Submodule.coe_norm, LinearIsometryEquiv.norm_map]; rfl

@[simp] theorem coe_ρVsE (q : S3) (y : Vs e) : ((D.ρVsE q y : Vs e) : W) = D.ρ q (y : W) := rfl

/-- **The star representation on the southern chart `V`.** -/
def ρVs : S3 →* (Vs e ≃ₗᵢ[ℝ] Vs e) where
  toFun := D.ρVsE
  map_one' := by ext y; simp [map_one]
  map_mul' a b := by ext y; simp [map_mul]

theorem contMDiff_ρVs :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) ∞
      fun q : S3 => ((D.ρVs q : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e) := by
  set P : W →L[ℝ] Vs e := (Vs e).orthogonalProjectionOnto
  set ι : Vs e →L[ℝ] W := (Vs e).subtypeL
  have e1 : (fun q : S3 => ((D.ρVs q : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e)) =
      fun q => P.comp ((((D.ρ q : W ≃L[ℝ] W) : W →L[ℝ] W)).comp ι) := by
    funext q; ext y
    simp only [P, ι, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := Vs e)
      ⟨D.ρ q y, D.ρ_mem_Vs q y⟩
    exact (congrArg Subtype.val h).symm
  rw [e1]
  exact contMDiff_const.clm_comp (D.ρ_smooth.clm_comp contMDiff_const)

/-! ### `θ̂(y) = θ(y/|y|)` on the punctured chart -/

/-- The punctured chart `V ∖ {0}`. -/
def Vpunct (e : W) : TopologicalSpace.Opens (Vs e) := ⟨{y | y ≠ 0}, isOpen_ne⟩

theorem norm_nrm (y : Vpunct e) : ‖(‖(y : Vs e)‖⁻¹ • (y : Vs e))‖ = 1 := by
  have hy : (y : Vs e) ≠ 0 := y.2
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]

/-- The angular variable `y ↦ y/|y|`. -/
def nrmV : Vpunct e → Metric.sphere (0 : Vs e) 1 :=
  Set.codRestrict (fun y : Vpunct e => ‖(y : Vs e)‖⁻¹ • (y : Vs e)) _
    (fun y => by rw [mem_sphere_zero_iff_norm]; exact norm_nrm y)

theorem contMDiff_nrmV : ContMDiff 𝓘(ℝ, Vs e) (𝓡 m) ∞ (nrmV (e := e)) := by
  refine ContMDiff.codRestrict_sphere (fun y => ?_) _
  have hy : (y : Vs e) ≠ 0 := y.2
  have h : ContDiffAt ℝ ∞ (fun x : Vs e => ‖x‖⁻¹ • x) (y : Vs e) :=
    ((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.2 hy)).smul contDiffAt_id
  exact contMDiffAt_subtype_iff.2 h.contMDiffAt

open scoped Classical in
/-- `θ̂(y) = θ(y/|y|)` (and `1` at `y = 0`, where it is never used). -/
def θh (y : Vs e) : Quaternion ℝ :=
  if h : y = 0 then 1 else ((D.θ (nrmV ⟨y, h⟩) : S3) : Quaternion ℝ)

theorem θh_of_ne {y : Vs e} (hy : y ≠ 0) : D.θh y = ((D.θ (nrmV ⟨y, hy⟩) : S3) : Quaternion ℝ) := by
  classical
  exact dif_neg hy

theorem θh_zero : D.θh 0 = 1 := by
  classical
  exact dif_pos rfl

theorem contDiffAt_θh {y : Vs e} (hy : y ≠ 0) : ContDiffAt ℝ ∞ D.θh y := by
  have g : ContMDiff 𝓘(ℝ, Vs e) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun z : Vpunct e => ((D.θ (nrmV z) : S3) : Quaternion ℝ)) :=
    contMDiff_coe_sphere.comp (D.θ_smooth.comp contMDiff_nrmV)
  have h : ContMDiffAt 𝓘(ℝ, Vs e) 𝓘(ℝ, Quaternion ℝ) ∞ (fun z : Vpunct e => D.θh z)
      (⟨y, hy⟩ : Vpunct e) :=
    (g _).congr_of_eventuallyEq (Eventually.of_forall fun z => D.θh_of_ne z.2)
  exact (contMDiffAt_subtype_iff.1 h).contDiffAt

theorem norm_θh (y : Vs e) : ‖D.θh y‖ = 1 := by
  by_cases hy : y = 0
  · rw [hy, D.θh_zero, norm_one]
  · rw [D.θh_of_ne hy]; exact mem_sphere_zero_iff_norm.1 (D.θ _).2

theorem θh_ne_zero (y : Vs e) : D.θh y ≠ 0 := fun h => by
  have := D.norm_θh y; rw [h, norm_zero] at this; norm_num at this

/-- `θ̂` is star-equivariant: `θ̂(ρ(q)y) = qθ̂(y)q⁻¹`. -/
theorem θh_ρ (q : S3) (y : Vs e) :
    D.θh (D.ρVs q y) = (q : Quaternion ℝ) * D.θh y * (q : Quaternion ℝ)⁻¹ := by
  by_cases hy : y = 0
  · have h0 : D.ρVs q y = 0 := by rw [hy, map_zero]
    have hq : (q : Quaternion ℝ) ≠ 0 := fun h => by
      have := mem_sphere_zero_iff_norm.1 q.2; rw [h, norm_zero] at this; norm_num at this
    rw [h0, hy, D.θh_zero, mul_one, mul_inv_cancel₀ hq]
  · have hy' : D.ρVs q y ≠ 0 := fun h => hy ((D.ρVs q).map_eq_zero_iff.1 h)
    rw [D.θh_of_ne hy, D.θh_of_ne hy']
    have e1 : nrmV ⟨D.ρVs q y, hy'⟩ = D.ρV q (nrmV ⟨y, hy⟩) := by
      apply Subtype.ext; apply Subtype.ext
      simp only [nrmV, Set.val_codRestrict_apply, PolarData.ρV]
      simp [LinearIsometryEquiv.norm_map]
      rfl
    rw [e1, D.θ_ρV]
    simp [coe_inv_S3']

/-! ### The southern potential `A_S` -/

/-- **[GG]'s southern potential** `A_S = (χ − 1) dθ θ⁻¹` in the southern chart. -/
def AS (χt : ℝ → ℝ) (y : Vs e) : Vs e →L[ℝ] Quaternion ℝ :=
  (χt (‖y‖ ^ 2) - 1) • ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (D.θh y)⁻¹).comp
    (fderiv ℝ D.θh y)

theorem AS_apply (χt : ℝ → ℝ) (y a : Vs e) :
    D.AS χt y a = (χt (‖y‖ ^ 2) - 1) • (fderiv ℝ D.θh y a * (D.θh y)⁻¹) := rfl

/-- A cutoff equal to `1` near `0` (the south pole). -/
def IsSouthCutoff (χt : ℝ → ℝ) : Prop := ContDiff ℝ ∞ χt ∧ ∃ s1 > 0, ∀ s < s1, χt s = 1

theorem AS_eventually_zero {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) :
    D.AS χt =ᶠ[𝓝 (0 : Vs e)] fun _ => 0 := by
  obtain ⟨-, s1, hs1, h1⟩ := hχ
  have hU : {y : Vs e | ‖y‖ ^ 2 < s1} ∈ 𝓝 (0 : Vs e) :=
    IsOpen.mem_nhds (isOpen_lt (by fun_prop) continuous_const) (by simpa using hs1)
  filter_upwards [hU] with y hy
  refine ContinuousLinearMap.ext fun a => ?_
  rw [AS_apply, h1 _ hy, sub_self, zero_smul]
  rfl

/-- **`A_S` is smooth on the whole southern chart**, including the south pole. -/
theorem contDiff_AS {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) : ContDiff ℝ ∞ (D.AS χt) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    exact contDiffAt_const.congr_of_eventuallyEq (D.AS_eventually_zero hχ)
  · have hθ := D.contDiffAt_θh hy
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ D.θh) y := hθ.fderiv_right (m := ∞) le_rfl
    have hinv : ContDiffAt ℝ ∞ (fun z => (D.θh z)⁻¹) y := by
      have := (contDiffAt_ringInverse ℝ (Units.mk0 (D.θh y) (D.θh_ne_zero y)) (n := ∞)).comp y hθ
      simpa only [Function.comp_def, Ring.inverse_eq_inv'] using this
    have hm : ContDiffAt ℝ ∞ (fun z => (ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip
        (D.θh z)⁻¹) y :=
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip.contDiff.contDiffAt.comp y hinv
    have hc : ContDiffAt ℝ ∞ (fun z : Vs e => χt (‖z‖ ^ 2) - 1) y :=
      ((hχ.1.comp (contDiff_norm_sq ℝ)).sub contDiff_const).contDiffAt
    exact hc.smul (hm.clm_comp hd)

/-- **`A_S` is imaginary.** -/
theorem AS_im {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) (y a : Vs e) : (D.AS χt y a).re = 0 := by
  rw [AS_apply, Quaternion.re_smul, smul_eq_mul]
  by_cases hy : y = 0
  · obtain ⟨-, s1, hs1, h1⟩ := hχ
    rw [hy, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, h1 0 hs1, sub_self, zero_mul]
  · -- `⟪dθ̂ a, θ̂⟫ = ½ d|θ̂|² = 0`
    have hθ := (D.contDiffAt_θh hy).differentiableAt (by simp)
    have hc : (fun z => ⟪D.θh z, D.θh z⟫) =ᶠ[𝓝 y] fun _ => (1 : ℝ) :=
      Eventually.of_forall fun z => by
        show ⟪D.θh z, D.θh z⟫ = 1
        rw [real_inner_self_eq_norm_sq, D.norm_θh]; norm_num
    have h1 := hθ.hasFDerivAt.inner ℝ hθ.hasFDerivAt
    have h2 : fderiv ℝ (fun z => ⟪D.θh z, D.θh z⟫) y = 0 := by
      rw [hc.fderiv_eq]; simp
    rw [h1.fderiv] at h2
    have h3 := congrArg (fun L => L a) h2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.zero_apply] at h3
    have h4 : ⟪fderiv ℝ D.θh y a, D.θh y⟫ = 0 := by
      rw [real_inner_comm] at h3; linarith
    have hinv : (D.θh y)⁻¹ = Star.star (D.θh y) := by
      rw [Quaternion.inv_def, Quaternion.normSq_eq_norm_mul_self, D.norm_θh, mul_one, inv_one,
        one_smul]
    rw [hinv, ← Quaternion.inner_def, h4, mul_zero]

theorem conj_inv_mul (q x : Quaternion ℝ) (hq : q ≠ 0) (hx : x ≠ 0) :
    (q * x * q⁻¹)⁻¹ = q * x⁻¹ * q⁻¹ := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]

/-- **`A_S` is star-equivariant**: `A_S(ρ(q)y)(ρ(q)a) = q A_S(y)(a) q⁻¹`. -/
theorem AS_equiv {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) (q : S3) (y a : Vs e) :
    D.AS χt (D.ρVs q y) (D.ρVs q a) =
      (q : Quaternion ℝ) * D.AS χt y a * (q : Quaternion ℝ)⁻¹ := by
  have hq : (q : Quaternion ℝ) ≠ 0 := fun h => by
    have := mem_sphere_zero_iff_norm.1 q.2; rw [h, norm_zero] at this; norm_num at this
  by_cases hy : y = 0
  · obtain ⟨-, s1, hs1, h1⟩ := hχ
    have h0 : D.ρVs q y = 0 := by rw [hy, map_zero]
    simp [AS_apply, hy, h0, h1 0 hs1]
  · have hy' : D.ρVs q y ≠ 0 := fun h => hy ((D.ρVs q).map_eq_zero_iff.1 h)
    set ρL : Vs e →L[ℝ] Vs e := ((D.ρVs q : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e)
    set cL : Quaternion ℝ →L[ℝ] Quaternion ℝ :=
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (q : Quaternion ℝ)).comp
        ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q : Quaternion ℝ)⁻¹)
    have hcomp : D.θh ∘ ρL = cL ∘ D.θh := by
      funext z; simp only [Function.comp, ρL, cL, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]
      rw [show ((D.ρVs q : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e) z = D.ρVs q z from rfl, D.θh_ρ,
        mul_assoc]
    have hd1 := ((D.contDiffAt_θh hy').differentiableAt (by simp)).hasFDerivAt.comp y
      ρL.hasFDerivAt
    have hd2 := cL.hasFDerivAt.comp y ((D.contDiffAt_θh hy).differentiableAt (by simp)).hasFDerivAt
    rw [← hcomp] at hd2
    have hEq := congrArg (fun L => L a) (hd1.unique hd2)
    simp only [ContinuousLinearMap.comp_apply, ρL, cL, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.flip_apply] at hEq
    rw [show (((D.ρVs q : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e) a) = D.ρVs q a from rfl] at hEq
    rw [AS_apply, AS_apply, hEq, D.θh_ρ, conj_inv_mul _ _ hq (D.θh_ne_zero y),
      LinearIsometryEquiv.norm_map, mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [mul_assoc, inv_mul_cancel_left₀ hq]

end PolarData

/-! ### [GG]'s southern quotient -/

open PolarData in
/-- **[GG] §4, the southern filling, for [GG]'s own data.** Given polar data `D` and a cutoff `χ`
equal to `1` near the south pole, the southern connection `A_S = (χ−1)dθθ⁻¹` satisfies the
hypotheses of `southern_quotient_pos`. So [GG]'s parameter order gives a quotient metric on the
southern cap `−cos t ≥ c₀` with positive sectional curvature. -/
theorem southern_quotient_pos_D {χt : ℝ → ℝ} (hχ : IsSouthCutoff χt) {c0 : ℝ} (hc0 : 0 < c0) :
    ∃ Λ0 : ℝ, ∀ Λ, Λ0 ≤ Λ → ∀ A0 : ℝ, 0 ≤ A0 → Λ ≤ A0 * c0 →
      ∃ εS > 0, ∀ ε (hε : 0 < ε), ε < εS → ∀ Y ∈ capS (K := Vs e) c0,
        ∀ a c : TangentSpace 𝓘(ℝ, Vs e) Y, LinearIndependent ℝ ![a, c] →
          0 < sectionalCurvatureAt (SQ.isSymm_cmet_gB' (ρV := D.ρVs) (GsH_symm (A := D.AS χt)))
            (SQ.isPosDef_cmet_gB' (GsH_pos (A := D.AS χt) fun x => (rSy_pos hε A0 x).ne'))
            (isContMDiffMetricSection_cmet ((SQ.contDiff_gB D.ρVs
              (GsH_pos (A := D.AS χt) fun x => (rSy_pos hε A0 x).ne')
              (contDiff_GsH (D.contDiff_AS hχ) (contDiff_rSy ε A0))).of_le two_le_top_nat))
            Y a c :=
  southern_quotient_pos D.contMDiff_ρVs (D.contDiff_AS hχ) (D.AS_im hχ) (D.AS_equiv hχ) hc0

end Potential

end

end ExoticSpheres8And10
