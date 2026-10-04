/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.StarBundle

/-! # §3, Steps 5–6: from equivariant sections to a meridian-constant transition

Input (`EquivSections`): smooth sections `s_N` over `U_N`, `s_S` over `U_S` of a star bundle with
the equivariance `eq:sectionequiv`, `s(ρ(q)ζ) = (q ⋆ s(ζ)) q⁻¹`. Steps 1–4 of [GG] produce such
sections by parallel transport; here we derive the rest.

**Difference from [GG], Step 6.** [GG] obtains constancy of the transition along meridians from
uniqueness of horizontal lifts (both sections are radially parallel for one invariant
connection). Here the sections are modified instead: with `g = s_S⁻¹ s_N` on the overlap,
`θ := g|_{S(V)}` and a smooth `ρ`-equivariant map `F` that is the identity on
`{⟪ζ,e⟫ ≥ ½}` and the meridian retraction onto the equator on `{⟪ζ,e⟫ ≤ 0}`,
`s'_N := s_S · (g ∘ F)` (`= s_N` near `o_N`) and `s'_S := s'_N · θ(x)⁻¹` (`= s_S` near `o_S`).
These are smooth, equivariant, and `s'_N = s'_S · θ(x)` exactly (`sN'_eq`). This proves the
same conclusion without requiring the sections to be parallel.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Sphere

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] {H₀ : Type*}
  [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H₀ N] [IsManifold I₀ ∞ N]

/-- A map into a sphere is smooth on an open set if it is smooth into the ambient space there. -/
theorem contMDiffOn_sphere_of_coe {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {k : ℕ} [Fact (finrank ℝ F = k + 1)] {f : N → sphere (0 : F) 1} {s : Set N} (hs : IsOpen s)
    (h : ContMDiffOn I₀ 𝓘(ℝ, F) ∞ (fun x => (f x : F)) s) : ContMDiffOn I₀ (𝓡 k) ∞ f s := by
  intro x hx
  let U : TopologicalSpace.Opens N := ⟨s, hs⟩
  have h1 : ContMDiff I₀ 𝓘(ℝ, F) ∞ fun y : U => (f y : F) :=
    h.comp_contMDiff contMDiff_subtype_val fun y => y.2
  have h2 : ContMDiff I₀ (𝓡 k) ∞ fun y : U => f y := contMDiff_sphere_of_coe h1
  exact ((contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).1 (h2 ⟨x, hx⟩)).contMDiffWithinAt

end Sphere

section Cutoff

/-- The cutoff `χ(c) = smoothTransition(2c)`: `0` for `c ≤ 0`, `1` for `c ≥ ½`. -/
def chiC (c : ℝ) : ℝ := Real.smoothTransition (2 * c)

/-- `C(c) = c χ(c)`: the new height. -/
def Cc (c : ℝ) : ℝ := c * chiC c

/-- `K(c) = √((1 − C²)/(1 − c²))`: the new horizontal scale. -/
def Kc (c : ℝ) : ℝ := √((1 - Cc c ^ 2) / (1 - c ^ 2))

theorem contDiff_chiC : ContDiff ℝ ∞ chiC :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)

theorem contDiff_Cc : ContDiff ℝ ∞ Cc := contDiff_id.mul contDiff_chiC

theorem Cc_of_le {c : ℝ} (h : c ≤ 0) : Cc c = 0 := by
  rw [Cc, chiC, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

theorem Cc_of_ge {c : ℝ} (h : 1 / 2 ≤ c) : Cc c = c := by
  rw [Cc, chiC, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem Cc_nonneg (c : ℝ) : 0 ≤ Cc c := by
  rcases le_or_gt c 0 with h | h
  · rw [Cc_of_le h]
  · exact mul_nonneg h.le (Real.smoothTransition.nonneg _)

theorem Cc_le (c : ℝ) (h : 0 ≤ c) : Cc c ≤ c := by
  have := Real.smoothTransition.le_one (2 * c)
  unfold Cc chiC; nlinarith

theorem Cc_sq_lt {c : ℝ} (h1 : c < 1) : Cc c ^ 2 < 1 := by
  rcases le_or_gt c 0 with h | h
  · rw [Cc_of_le h]; norm_num
  · have h2 := Cc_le c h.le
    have h3 := Cc_nonneg c
    nlinarith

theorem Kc_ratio_pos {c : ℝ} (h : c ^ 2 < 1) : 0 < (1 - Cc c ^ 2) / (1 - c ^ 2) := by
  have hc : c < 1 := by nlinarith [sq_nonneg (c - 1)]
  exact div_pos (by linarith [Cc_sq_lt hc]) (by linarith)

theorem contDiffAt_Kc {c : ℝ} (h : c ^ 2 < 1) : ContDiffAt ℝ ∞ Kc c := by
  have hden : (1 : ℝ) - c ^ 2 ≠ 0 := by linarith
  have h1 : ContDiffAt ℝ ∞ (fun c : ℝ => (1 - Cc c ^ 2) / (1 - c ^ 2)) c :=
    ((contDiff_const.sub (contDiff_Cc.pow 2)).contDiffAt).div
      ((contDiff_const.sub (contDiff_id.pow 2)).contDiffAt) hden
  exact (Real.contDiffAt_sqrt (Kc_ratio_pos h).ne').comp c h1

theorem Kc_of_ge {c : ℝ} (h : 1 / 2 ≤ c) (h1 : c < 1) : Kc c = 1 := by
  rw [Kc, Cc_of_ge h, div_self (by nlinarith), Real.sqrt_one]

theorem Kc_of_le {c : ℝ} (h : c ≤ 0) : Kc c = (√(1 - c ^ 2))⁻¹ := by
  rw [Kc, Cc_of_le h, show (1 - (0 : ℝ) ^ 2) / (1 - c ^ 2) = (1 - c ^ 2)⁻¹ by ring, Real.sqrt_inv]

end Cutoff

section Sections

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

local notation "Sn" => sphere (0 : W) 1

local notation "SV" => sphere (0 : Vs e) 1

/-- The ambient meridian reparametrisation: `F(ζ) = C(c) e + K(c)(ζ − ce)`, `c = ⟪ζ, e⟫`. -/
def Famb (e : W) (ζ : W) : W := Cc ⟪ζ, e⟫ • e + Kc ⟪ζ, e⟫ • (ζ - ⟪ζ, e⟫ • e)

theorem contDiffAt_Famb {ζ : W} (h : ⟪ζ, e⟫ ^ 2 < 1) : ContDiffAt ℝ ∞ (Famb e) ζ := by
  have hi := contDiff_inner_e e
  exact ((contDiff_Cc.comp hi).smul contDiff_const).contDiffAt.add
    (((contDiffAt_Kc h).comp ζ hi.contDiffAt).smul
      (contDiff_id.sub (hi.smul contDiff_const)).contDiffAt)

theorem Famb_map (T : W →ₗᵢ[ℝ] W) (hT : T e = e) (ζ : W) : Famb e (T ζ) = T (Famb e ζ) := by
  have hi : ⟪T ζ, e⟫ = ⟪ζ, e⟫ := by rw [← hT, T.inner_map_map, hT]
  rw [Famb, Famb, hi, map_add, map_smul, map_smul, map_sub, map_smul, hT]

variable (he : ‖e‖ = 1)
include he

theorem inner_Famb (ζ : W) : ⟪Famb e ζ, e⟫ = Cc ⟪ζ, e⟫ := by
  rw [Famb, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring

theorem norm_Famb {ζ : W} (hζ : ‖ζ‖ = 1) (h : ⟪ζ, e⟫ ^ 2 < 1) : ‖Famb e ζ‖ = 1 := by
  have hw : ‖ζ - ⟪ζ, e⟫ • e‖ ^ 2 = 1 - ⟪ζ, e⟫ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hζ, he, Real.norm_eq_abs,
      mul_one, sq_abs]; ring
  have hwe : ⟪e, ζ - ⟪ζ, e⟫ • e⟫ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he, real_inner_comm]
    ring
  have hK := Kc_ratio_pos h
  have hsq : ‖Famb e ζ‖ ^ 2 = 1 := by
    rw [Famb, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hwe, norm_smul,
      norm_smul, he, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, hw,
      Kc, Real.sq_sqrt hK.le]
    have hden : (1 : ℝ) - ⟪ζ, e⟫ ^ 2 ≠ 0 := by linarith
    field_simp
    ring
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [hsq, one_pow])

theorem Famb_of_ge {ζ : W} (hc : 1 / 2 ≤ ⟪ζ, e⟫) (hc1 : ⟪ζ, e⟫ < 1) : Famb e ζ = ζ := by
  rw [Famb, Cc_of_ge hc, Kc_of_ge hc hc1, one_smul, add_sub_cancel]

theorem Famb_of_le {ζ : W} (hc : ⟪ζ, e⟫ ≤ 0) : Famb e ζ = pX e ζ := by
  rw [Famb, Cc_of_le hc, zero_smul, zero_add, Kc_of_le hc, pX]

end Sections


section Bundle

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  {R : StarRep e} {E : Type*} [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

local notation "SV" => sphere (0 : Vs e) 1

/-- `U_S = S^n ∖ {o_N}`. -/
def US (e : W) : TopologicalSpace.Opens Sn :=
  ⟨{ζ | (ζ : W) ≠ e}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

/-- The overlap `U_N ∩ U_S`. -/
def Ov (e : W) : TopologicalSpace.Opens Sn :=
  ⟨{ζ | (ζ : W) ≠ e ∧ (ζ : W) ≠ -e},
    (isOpen_ne_fun continuous_subtype_val continuous_const).inter
      (isOpen_ne_fun continuous_subtype_val continuous_const)⟩

/-- The height `⟪ζ, e⟫`. -/
def ht (e : W) (ζ : Sn) : ℝ := ⟪(ζ : W), e⟫

theorem continuous_ht : Continuous (ht e) :=
  continuous_subtype_val.inner continuous_const

/-- **Input of Steps 5–6** ([GG] `eq:sectionequiv`): smooth sections over `U_N` and `U_S`
(total functions, meaningful on `U_N`, `U_S`) with `s(ρ(q)ζ) = (q ⋆ s(ζ))q⁻¹`. -/
structure EquivSections where
  sN : Sn → E
  sS : Sn → E
  sN_smooth : ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ sN (UN e)
  sS_smooth : ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ sS (US e)
  proj_sN : ∀ ζ ∈ UN e, B.proj (sN ζ) = ζ
  proj_sS : ∀ ζ ∈ US e, B.proj (sS ζ) = ζ
  sN_equiv : ∀ q, ∀ ζ ∈ UN e, sN (R.ρS q ζ) = B.ract (B.star q (sN ζ)) q⁻¹
  sS_equiv : ∀ q, ∀ ζ ∈ US e, sS (R.ρS q ζ) = B.ract (B.star q (sS ζ)) q⁻¹

namespace StarRep

variable (R)

include R

theorem ht_ρS (q : S3) (ζ : Sn) : ht e (R.ρS q ζ) = ht e ζ := by
  show ⟪R.ρ q ζ, e⟫ = ⟪(ζ : W), e⟫
  calc ⟪R.ρ q ζ, e⟫ = ⟪R.ρ q ζ, R.ρ q e⟫ := by rw [R.ρ_e]
    _ = _ := LinearIsometryEquiv.inner_map_map _ _ _

theorem ρS_mem_UN (q : S3) {ζ : Sn} (h : ζ ∈ UN e) : R.ρS q ζ ∈ UN e := by
  intro h'; apply h
  exact (R.ρ q).injective (h'.trans (by rw [map_neg, R.ρ_e]))

theorem ρS_mem_US (q : S3) {ζ : Sn} (h : ζ ∈ US e) : R.ρS q ζ ∈ US e := by
  intro h'; apply h
  exact (R.ρ q).injective (h'.trans (R.ρ_e q).symm)

theorem ρS_mem_Ov (q : S3) {ζ : Sn} (h : ζ ∈ Ov e) : R.ρS q ζ ∈ Ov e :=
  ⟨R.ρS_mem_US q h.1, R.ρS_mem_UN q h.2⟩

theorem sq_lt_of_Ov {ζ : Sn} (h : ζ ∈ Ov e) : ⟪(ζ : W), e⟫ ^ 2 < 1 :=
  inner_sq_lt_one R.e_norm (by simp) h.1 h.2

def FS (ζ : Sn) : Sn :=
  if h : ⟪(ζ : W), e⟫ ^ 2 < 1 then ⟨Famb e ζ, by
    rw [mem_sphere_zero_iff_norm]; exact norm_Famb R.e_norm (by simp) h⟩ else ζ

def XS (ζ : Sn) : Sn :=
  if h : ⟪(ζ : W), e⟫ ^ 2 < 1 then ⟨pX e ζ, by
    rw [mem_sphere_zero_iff_norm]; exact norm_pX R.e_norm (by simp) h⟩ else ζ

theorem FS_val {ζ : Sn} (h : ζ ∈ Ov e) : (R.FS ζ : W) = Famb e ζ := by
  rw [FS, dif_pos (R.sq_lt_of_Ov h)]

theorem XS_val {ζ : Sn} (h : ζ ∈ Ov e) : (R.XS ζ : W) = pX e ζ := by
  rw [XS, dif_pos (R.sq_lt_of_Ov h)]

theorem FS_mem {ζ : Sn} (h : ζ ∈ Ov e) : R.FS ζ ∈ Ov e := by
  have hi := inner_Famb R.e_norm (ζ : W)
  have hc1 : ⟪(ζ : W), e⟫ < 1 := by nlinarith [R.sq_lt_of_Ov h]
  constructor
  · intro h'
    rw [show ((R.FS ζ : Sn) : W) = Famb e ζ from R.FS_val h] at h'
    rw [h', real_inner_self_eq_norm_sq, R.e_norm] at hi
    have := Cc_sq_lt hc1; rw [← hi] at this; norm_num at this
  · intro h'
    rw [show ((R.FS ζ : Sn) : W) = Famb e ζ from R.FS_val h] at h'
    rw [h', inner_neg_left, real_inner_self_eq_norm_sq, R.e_norm] at hi
    have := Cc_nonneg ⟪(ζ : W), e⟫; rw [← hi] at this; norm_num at this

theorem XS_mem {ζ : Sn} (h : ζ ∈ Ov e) : R.XS ζ ∈ Ov e := by
  have hi := inner_pX R.e_norm (ζ : W)
  constructor
  · intro h'
    rw [show ((R.XS ζ : Sn) : W) = pX e ζ from R.XS_val h] at h'
    rw [h', real_inner_self_eq_norm_sq, R.e_norm] at hi; norm_num at hi
  · intro h'
    rw [show ((R.XS ζ : Sn) : W) = pX e ζ from R.XS_val h] at h'
    rw [h', inner_neg_left, real_inner_self_eq_norm_sq, R.e_norm] at hi; norm_num at hi

theorem FS_of_ge {ζ : Sn} (h : ζ ∈ Ov e) (hc : 1 / 2 ≤ ht e ζ) : R.FS ζ = ζ :=
  Subtype.ext ((R.FS_val h).trans (Famb_of_ge R.e_norm hc (by nlinarith [R.sq_lt_of_Ov h])))

theorem FS_eq_XS {ζ : Sn} (h : ζ ∈ Ov e) (hc : ht e ζ ≤ 0) : R.FS ζ = R.XS ζ :=
  Subtype.ext ((R.FS_val h).trans ((Famb_of_le R.e_norm hc).trans (R.XS_val h).symm))

theorem FS_equiv (q : S3) {ζ : Sn} (h : ζ ∈ Ov e) : R.FS (R.ρS q ζ) = R.ρS q (R.FS ζ) :=
  Subtype.ext (by
    rw [R.FS_val (R.ρS_mem_Ov q h)]
    show Famb e ((R.ρ q).toLinearIsometry ζ) = R.ρ q (R.FS ζ : W)
    rw [Famb_map _ (R.ρ_e q), R.FS_val h]; rfl)

theorem XS_equiv (q : S3) {ζ : Sn} (h : ζ ∈ Ov e) : R.XS (R.ρS q ζ) = R.ρS q (R.XS ζ) :=
  Subtype.ext (by
    rw [R.XS_val (R.ρS_mem_Ov q h)]
    show pX e ((R.ρ q).toLinearIsometry ζ) = R.ρ q (R.XS ζ : W)
    rw [pX_map _ (R.ρ_e q), R.XS_val h]; rfl)

theorem contMDiffOn_FS : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ R.FS (Ov e) := by
  refine contMDiffOn_sphere_of_coe (Ov e).isOpen ?_
  intro ζ hζ
  have h1 : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, W) ∞ (fun ζ : Sn => Famb e ζ) ζ :=
    (contDiffAt_Famb (R.sq_lt_of_Ov hζ)).comp_contMDiffAt (f := fun ζ : Sn => (ζ : W))
      (contMDiff_coe_sphere ζ)
  refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(Ov e).isOpen.mem_nhds hζ] with y hy
  exact R.FS_val hy

theorem contMDiffOn_XS : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ R.XS (Ov e) := by
  refine contMDiffOn_sphere_of_coe (Ov e).isOpen ?_
  intro ζ hζ
  have h1 : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, W) ∞ (fun ζ : Sn => pX e ζ) ζ :=
    (contDiffAt_pX e (R.sq_lt_of_Ov hζ)).comp_contMDiffAt (f := fun ζ : Sn => (ζ : W))
      (contMDiff_coe_sphere ζ)
  refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(Ov e).isOpen.mem_nhds hζ] with y hy
  exact R.XS_val hy


theorem mem_Ov_of_UN {ζ : Sn} (h : ζ ∈ UN e) (hc : ht e ζ ≤ 1 / 2) : ζ ∈ Ov e := by
  refine ⟨fun h' => ?_, h⟩
  have : ht e ζ = 1 := by
    show ⟪(ζ : W), e⟫ = 1
    rw [show (ζ : W) = e from h', real_inner_self_eq_norm_sq, R.e_norm]; norm_num
  linarith

theorem mem_Ov_of_US {ζ : Sn} (h : ζ ∈ US e) (hc : 0 ≤ ht e ζ) : ζ ∈ Ov e := by
  refine ⟨h, fun h' => ?_⟩
  have : ht e ζ = -1 := by
    show ⟪(ζ : W), e⟫ = -1
    rw [show (ζ : W) = -e from h', inner_neg_left, real_inner_self_eq_norm_sq, R.e_norm]
    norm_num
  linarith

end StarRep

namespace EquivSections

variable {B} (S : EquivSections B)

/-- The transition `g = s_S⁻¹ s_N` on the overlap. -/
def g (ζ : Sn) : S3 := B.divE (S.sS ζ) (S.sN ζ)

theorem sN_eq (ζ : Sn) (h : ζ ∈ Ov e) : S.sN ζ = B.ract (S.sS ζ) (S.g ζ) :=
  (B.ract_divE _ _ (by rw [S.proj_sN ζ h.2, S.proj_sS ζ h.1])).symm

theorem divE_ract_ract (a b : E) (h h' : S3) (hab : B.proj b = B.proj a) :
    B.divE (B.ract a h) (B.ract b h') = h⁻¹ * B.divE a b * h' := by
  apply B.divE_unique
  rw [B.ract_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, ← B.ract_mul,
    B.ract_divE a b hab]

theorem divE_star (q : S3) (a b : E) (hab : B.proj b = B.proj a) :
    B.divE (B.star q a) (B.star q b) = B.divE a b := by
  apply B.divE_unique
  rw [← B.star_ract, B.ract_divE a b hab]

/-- The transition is conjugation-equivariant. -/
theorem g_equiv (q : S3) (ζ : Sn) (h : ζ ∈ Ov e) : S.g (R.ρS q ζ) = q * S.g ζ * q⁻¹ := by
  have hp : B.proj (S.sN ζ) = B.proj (S.sS ζ) := by rw [S.proj_sN ζ h.2, S.proj_sS ζ h.1]
  rw [g, S.sN_equiv q ζ h.2, S.sS_equiv q ζ h.1,
    divE_ract_ract _ _ _ _ (by rw [B.proj_star, B.proj_star, hp]), divE_star q _ _ hp, inv_inv]
  rfl

theorem contMDiffOn_g : ContMDiffOn (𝓡 (m + 1)) (𝓡 3) ∞ S.g (Ov e) :=
  B.contMDiffOn_divE (Ov e).isOpen (S.sS_smooth.mono fun _ h => h.1)
    (S.sN_smooth.mono fun _ h => h.2) fun ζ h => by rw [S.proj_sN ζ h.2, S.proj_sS ζ h.1]

/-! ### The modified sections -/

/-- `s'_N = s_S · g(F ζ)` (and `= s_N` near `o_N`). -/
def sN' (ζ : Sn) : E := if 1 / 2 < ht e ζ then S.sN ζ else B.ract (S.sS ζ) (S.g (R.FS ζ))

/-- `s'_S = s'_N · θ(x)⁻¹` (and `= s_S` near `o_S`). -/
def sS' (ζ : Sn) : E := if ht e ζ < 0 then S.sS ζ else B.ract (S.sN' ζ) (S.g (R.XS ζ))⁻¹

theorem sN'_eq_formula {ζ : Sn} (h : ζ ∈ Ov e) :
    S.sN' ζ = B.ract (S.sS ζ) (S.g (R.FS ζ)) := by
  unfold sN'
  split_ifs with hc
  · rw [R.FS_of_ge h hc.le]; exact S.sN_eq ζ h
  · rfl

/-- **The transition of the modified sections is `θ(x) = g(x(ζ))`** on the whole overlap. -/
theorem sN'_eq {ζ : Sn} (h : ζ ∈ Ov e) : S.sN' ζ = B.ract (S.sS' ζ) (S.g (R.XS ζ)) := by
  unfold sS'
  split_ifs with hc
  · rw [S.sN'_eq_formula h, R.FS_eq_XS h hc.le]
  · rw [B.ract_mul, inv_mul_cancel, B.ract_one]

theorem sS'_eq_formula {ζ : Sn} (h : ζ ∈ Ov e) :
    S.sS' ζ = B.ract (S.sN' ζ) (S.g (R.XS ζ))⁻¹ := by
  rw [S.sN'_eq h, B.ract_mul, mul_inv_cancel, B.ract_one]

theorem proj_sN' {ζ : Sn} (h : ζ ∈ UN e) : B.proj (S.sN' ζ) = ζ := by
  unfold sN'
  split_ifs with hc
  · exact S.proj_sN ζ h
  · rw [B.proj_ract]
    refine S.proj_sS ζ fun h' => ?_
    have : ht e ζ = 1 := by
      show ⟪(ζ : W), e⟫ = 1
      rw [show (ζ : W) = e from h', real_inner_self_eq_norm_sq, R.e_norm]; norm_num
    linarith

theorem proj_sS' {ζ : Sn} (h : ζ ∈ US e) : B.proj (S.sS' ζ) = ζ := by
  unfold sS'
  split_ifs with hc
  · exact S.proj_sS ζ h
  · rw [B.proj_ract]
    refine S.proj_sN' fun h' => ?_
    have : ht e ζ = -1 := by
      show ⟪(ζ : W), e⟫ = -1
      rw [show (ζ : W) = -e from h', inner_neg_left, real_inner_self_eq_norm_sq, R.e_norm]
      norm_num
    linarith

/-- **`s'_N` is equivariant.** -/
theorem sN'_equiv (q : S3) {ζ : Sn} (h : ζ ∈ UN e) :
    S.sN' (R.ρS q ζ) = B.ract (B.star q (S.sN' ζ)) q⁻¹ := by
  unfold sN'
  rw [R.ht_ρS]
  split_ifs with hc
  · exact S.sN_equiv q ζ h
  · have hO := R.mem_Ov_of_UN h (not_lt.1 hc)
    rw [S.sS_equiv q ζ hO.1, R.FS_equiv q hO, S.g_equiv q _ (R.FS_mem hO), B.ract_mul,
      B.star_ract, B.ract_mul]
    congr 1; group

/-- **`s'_S` is equivariant.** -/
theorem sS'_equiv (q : S3) {ζ : Sn} (h : ζ ∈ US e) :
    S.sS' (R.ρS q ζ) = B.ract (B.star q (S.sS' ζ)) q⁻¹ := by
  unfold sS'
  rw [R.ht_ρS]
  split_ifs with hc
  · exact S.sS_equiv q ζ h
  · have hO := R.mem_Ov_of_US h (not_lt.1 hc)
    rw [S.sN'_equiv q hO.2, R.XS_equiv q hO, S.g_equiv q _ (R.XS_mem hO), B.ract_mul,
      B.star_ract, B.ract_mul]
    congr 1; group

theorem contMDiffOn_formulaN :
    ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ (fun ζ => B.ract (S.sS ζ) (S.g (R.FS ζ))) (Ov e) := by
  have h1 : ContMDiffOn (𝓡 (m + 1)) (𝓡 3) ∞ (fun ζ => S.g (R.FS ζ)) (Ov e) :=
    S.contMDiffOn_g.comp R.contMDiffOn_FS fun _ h => R.FS_mem h
  have h2 : ContMDiffOn (𝓡 (m + 1)) ((IP m).prod (𝓡 3)) ∞
      (fun ζ => (S.sS ζ, S.g (R.FS ζ))) (Ov e) :=
    (S.sS_smooth.mono fun _ h => h.1).prodMk h1
  exact ContMDiff.comp_contMDiffOn (g := fun x : E × S3 => B.ract x.1 x.2)
    (f := fun ζ => (S.sS ζ, S.g (R.FS ζ))) B.ract_smooth h2

/-- **`s'_N` is smooth on `U_N`.** -/
theorem contMDiffOn_sN' : ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ S.sN' (UN e) := by
  intro ζ hζ
  by_cases hO : ζ ∈ Ov e
  · refine ((S.contMDiffOn_formulaN.contMDiffAt ((Ov e).isOpen.mem_nhds hO)).congr_of_eventuallyEq
      ?_).contMDiffWithinAt
    filter_upwards [(Ov e).isOpen.mem_nhds hO] with y hy
    exact S.sN'_eq_formula hy
  · have hc : 1 / 2 < ht e ζ := by
      by_contra hc; exact hO (R.mem_Ov_of_UN hζ (not_lt.1 hc))
    have hU : IsOpen ((UN e : Set Sn) ∩ {ζ | 1 / 2 < ht e ζ}) :=
      (UN e).isOpen.inter (isOpen_lt continuous_const (continuous_ht (e := e)))
    refine (((S.sN_smooth.mono inter_subset_left).contMDiffAt (hU.mem_nhds ⟨hζ, hc⟩)
      ).congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU.mem_nhds ⟨hζ, hc⟩] with y hy
    exact if_pos hy.2

theorem contMDiffOn_formulaS :
    ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ (fun ζ => B.ract (S.sN' ζ) (S.g (R.XS ζ))⁻¹) (Ov e) := by
  have h1 : ContMDiffOn (𝓡 (m + 1)) (𝓡 3) ∞ (fun ζ => (S.g (R.XS ζ))⁻¹) (Ov e) :=
    contMDiff_invS3.comp_contMDiffOn (S.contMDiffOn_g.comp R.contMDiffOn_XS fun _ h => R.XS_mem h)
  have h2 : ContMDiffOn (𝓡 (m + 1)) ((IP m).prod (𝓡 3)) ∞
      (fun ζ => (S.sN' ζ, (S.g (R.XS ζ))⁻¹)) (Ov e) :=
    (S.contMDiffOn_sN'.mono fun _ h => h.2).prodMk h1
  exact ContMDiff.comp_contMDiffOn (g := fun x : E × S3 => B.ract x.1 x.2)
    (f := fun ζ => (S.sN' ζ, (S.g (R.XS ζ))⁻¹)) B.ract_smooth h2

/-- **`s'_S` is smooth on `U_S`.** -/
theorem contMDiffOn_sS' : ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ S.sS' (US e) := by
  intro ζ hζ
  by_cases hO : ζ ∈ Ov e
  · refine ((S.contMDiffOn_formulaS.contMDiffAt ((Ov e).isOpen.mem_nhds hO)).congr_of_eventuallyEq
      ?_).contMDiffWithinAt
    filter_upwards [(Ov e).isOpen.mem_nhds hO] with y hy
    exact S.sS'_eq_formula hy
  · have hc : ht e ζ < 0 := by
      by_contra hc; exact hO (R.mem_Ov_of_US hζ (not_lt.1 hc))
    have hU : IsOpen ((US e : Set Sn) ∩ {ζ | ht e ζ < 0}) :=
      (US e).isOpen.inter (isOpen_lt (continuous_ht (e := e)) continuous_const)
    refine (((S.sS_smooth.mono inter_subset_left).contMDiffAt (hU.mem_nhds ⟨hζ, hc⟩)
      ).congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU.mem_nhds ⟨hζ, hc⟩] with y hy
    exact if_pos hy.2

end EquivSections

end Bundle

end

end ExoticSpheres8And10
