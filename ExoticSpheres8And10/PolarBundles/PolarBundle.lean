/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.Gluing
import ExoticSpheres8And10.PolarBundles.PolarCoordinates
import ExoticSpheres8And10.PolarBundles.OrientationSphere

/-! # §2: polar data and the polar bundle `P_θ` as a smooth manifold

[GG] §2, `def:starbundle` and `def:polar`.

* `PolarData e`: a Euclidean space `W` with unit vector `e`, `V = e^⊥`; a smooth orthogonal
  representation `ρ : S³ → O(W)` fixing `e`; a smooth `θ : S(V) → S³` with `eq:equiv`.
* `PolarBundle D`: `P_θ`, glued from two product charts along `eq:transition`.
  **Encoding of the southern chart.** The chart `U_S × S³` is identified with `U_N × S³` by the
  reflection `R` in `V` (`R ζ = ζ − 2⟪ζ,e⟫e`, an isometry commuting with `ρ` and fixing `S(V)`
  pointwise, with `R(U_S) = U_N`). In these coordinates the transition `u_S = θ(x)u_N` becomes
  `κ(ζ, u) = (Rζ, θ(x(ζ)) u)` on `(U_N ∖ {o_N}) × S³`.
* `isManifold_polarBundle`: `P_θ` is a `C^∞` manifold of dimension `n + 3`.

Ambient formulas: `pX ζ = (1 − ⟪ζ,e⟫²)^{−1/2} (ζ − ⟪ζ,e⟫e)` is the angular variable `x`
(`pX_eq_polarX`), smooth off the poles.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

instance fact_finrank_quat : Fact (finrank ℝ ℍ[ℝ] = 3 + 1) := ⟨Quaternion.finrank_eq_four⟩

theorem coe_mul_S3' (a b : S3) : ((a * b : S3) : ℍ[ℝ]) = a * b := rfl

theorem coe_inv_S3' (a : S3) : ((a⁻¹ : S3) : ℍ[ℝ]) = (a : ℍ[ℝ])⁻¹ :=
  Metric.unitSphere.coe_inv a

section SphereMaps

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] {H₀ : Type*}
  [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H₀ N] [IsManifold I₀ ∞ N]

/-- A map into a sphere is smooth if it is smooth into the ambient space. -/
theorem contMDiff_sphere_of_coe {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {k : ℕ} [Fact (finrank ℝ F = k + 1)] {f : N → sphere (0 : F) 1}
    (h : ContMDiff I₀ 𝓘(ℝ, F) ∞ fun x => (f x : F)) : ContMDiff I₀ (𝓡 k) ∞ f :=
  h.codRestrict_sphere fun x => (f x).2

end SphereMaps

/-! ## Ambient formulas: the reflection `R` and the angular variable `x` -/

section Ambient

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W)

/-- The reflection in `V = e^⊥`. -/
def reflE (ζ : W) : W := ζ - (2 * ⟪ζ, e⟫) • e

/-- The angular variable `x = (ζ − ⟪ζ,e⟫e)/√(1 − ⟪ζ,e⟫²)`. -/
noncomputable def pX (ζ : W) : W := (√(1 - ⟪ζ, e⟫ ^ 2))⁻¹ • (ζ - ⟪ζ, e⟫ • e)

theorem contDiff_inner_e : ContDiff ℝ ∞ fun ζ : W => ⟪ζ, e⟫ :=
  contDiff_id.inner ℝ contDiff_const

theorem contDiff_reflE : ContDiff ℝ ∞ (reflE e) :=
  contDiff_id.sub ((contDiff_const.mul (contDiff_inner_e e)).smul contDiff_const)

theorem contDiffAt_pX {ζ : W} (h : ⟪ζ, e⟫ ^ 2 < 1) : ContDiffAt ℝ ∞ (pX e) ζ := by
  have h0 : ContDiff ℝ ∞ fun ζ : W => 1 - ⟪ζ, e⟫ ^ 2 := contDiff_const.sub ((contDiff_inner_e e).pow 2)
  have h1 : ContDiffAt ℝ ∞ (fun ζ : W => √(1 - ⟪ζ, e⟫ ^ 2)) ζ :=
    (Real.contDiffAt_sqrt (by linarith : (1 : ℝ) - ⟪ζ, e⟫ ^ 2 ≠ 0)).comp ζ h0.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun ζ : W => (√(1 - ⟪ζ, e⟫ ^ 2))⁻¹) ζ :=
    (contDiffAt_inv ℝ (Real.sqrt_pos.2 (by linarith)).ne').comp ζ h1
  exact h2.smul (contDiff_id.sub ((contDiff_inner_e e).smul contDiff_const)).contDiffAt

variable {e}

theorem reflE_map (T : W →ₗᵢ[ℝ] W) (hT : T e = e) (ζ : W) : reflE e (T ζ) = T (reflE e ζ) := by
  rw [reflE, reflE, map_sub, map_smul, hT, ← hT, T.inner_map_map, hT]

theorem pX_map (T : W →ₗᵢ[ℝ] W) (hT : T e = e) (ζ : W) : pX e (T ζ) = T (pX e ζ) := by
  rw [pX, pX, map_smul, map_sub, map_smul, hT, ← hT, T.inner_map_map, hT]

variable (he : ‖e‖ = 1)
include he

theorem inner_reflE (ζ : W) : ⟪reflE e ζ, e⟫ = -⟪ζ, e⟫ := by
  rw [reflE, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring

theorem reflE_reflE (ζ : W) : reflE e (reflE e ζ) = ζ := by
  rw [reflE, inner_reflE he, reflE]
  rw [sub_sub, ← add_smul]; ring_nf; simp

theorem norm_reflE (ζ : W) : ‖reflE e ζ‖ = ‖ζ‖ := by
  have h : ‖reflE e ζ‖ ^ 2 = ‖ζ‖ ^ 2 := by
    rw [reflE, norm_sub_sq_real, real_inner_smul_right, norm_smul, he, Real.norm_eq_abs,
      mul_one, sq_abs]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem reflE_e : reflE e e = -e := by
  rw [reflE, real_inner_self_eq_norm_sq, he]; module

theorem reflE_neg_e : reflE e (-e) = e := by
  rw [reflE, inner_neg_left, real_inner_self_eq_norm_sq, he]; module

theorem reflE_ne_neg {ζ : W} (h : ζ ≠ e) : reflE e ζ ≠ -e := by
  intro h'; apply h; rw [← reflE_reflE he ζ, h', reflE_neg_e he]

theorem reflE_ne {ζ : W} (h : ζ ≠ -e) : reflE e ζ ≠ e := by
  intro h'; apply h; rw [← reflE_reflE he ζ, h', reflE_e he]

theorem pX_reflE (ζ : W) : pX e (reflE e ζ) = pX e ζ := by
  rw [pX, pX, inner_reflE he, neg_sq, reflE]
  congr 1; module

theorem inner_pX (ζ : W) : ⟪pX e ζ, e⟫ = 0 := by
  rw [pX, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he]; ring

theorem inner_sq_lt_one {ζ : W} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ e) (h2 : ζ ≠ -e) : ⟪ζ, e⟫ ^ 2 < 1 := by
  have hb := inner_bounds he hζ
  have hn1 := inner_ne_one he hζ h1
  have hn2 := inner_ne_neg_one he hζ h2
  have : -1 < ⟪ζ, e⟫ := lt_of_le_of_ne hb.1 (Ne.symm hn2)
  have : ⟪ζ, e⟫ < 1 := lt_of_le_of_ne hb.2 hn1
  nlinarith

theorem norm_pX {ζ : W} (hζ : ‖ζ‖ = 1) (h : ⟪ζ, e⟫ ^ 2 < 1) : ‖pX e ζ‖ = 1 := by
  have hs : 0 < √(1 - ⟪ζ, e⟫ ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hsq : ‖ζ - ⟪ζ, e⟫ • e‖ ^ 2 = √(1 - ⟪ζ, e⟫ ^ 2) ^ 2 := by
    rw [Real.sq_sqrt (by linarith), norm_sub_sq_real, real_inner_smul_right, norm_smul, hζ, he,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hn := (pow_left_inj₀ (norm_nonneg _) hs.le two_ne_zero).1 hsq
  rw [pX, norm_smul, hn, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_cancel₀ hs.ne']

/-- `pX` is the angular variable of `S2_Polar`. -/
theorem pX_eq_polarX {ζ : W} (hζ : ‖ζ‖ = 1) : pX e ζ = polarX e ζ := by
  rw [pX, polarX, polarT, Real.sin_arccos, Real.cos_arccos (inner_bounds he hζ).1
    (inner_bounds he hζ).2]

end Ambient

/-! ## Polar data -/

section Bundle

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)]

/-- `V = e^⊥`. -/
abbrev Vs (e : W) : Submodule ℝ W := (ℝ ∙ e)ᗮ

variable (e : W) [Fact (finrank ℝ (Vs e) = m + 1)]

local notation "Sn" => sphere (0 : W) 1

/-- **Polar data** ([GG] `def:starbundle` (1)–(2) and `def:polar`): a unit vector `e`, a smooth
orthogonal representation `ρ` of `S³` on `W` fixing `e`, and a smooth `θ : S(V) → S³` with
`θ(ρ(q)y) = qθ(y)q⁻¹` (`eq:equiv`). -/
structure PolarData where
  e_norm : ‖e‖ = 1
  ρ : S3 →* (W ≃ₗᵢ[ℝ] W)
  ρ_e : ∀ q, ρ q e = e
  ρ_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, W →L[ℝ] W) ∞ fun q => ((ρ q : W ≃L[ℝ] W) : W →L[ℝ] W)
  θ : sphere (0 : Vs e) 1 → S3
  θ_smooth : ContMDiff (𝓡 m) (𝓡 3) ∞ θ
  θ_equiv : ∀ (q : S3) (y y' : sphere (0 : Vs e) 1), ((y' : Vs e) : W) = ρ q ((y : Vs e) : W) →
    θ y' = q * θ y * q⁻¹

variable {e}

/-- `U_N = S^n ∖ {o_S}`, `o_S = −e`. -/
def UN (e : W) : TopologicalSpace.Opens Sn :=
  ⟨{ζ | (ζ : W) ≠ -e}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

/-- The product chart `U_N × S³`. -/
abbrev M0 (e : W) := UN e × S3

/-- The model of `P_θ`: `ℝⁿ × ℝ³`. -/
abbrev IP (m : ℕ) := (𝓡 (m + 1)).prod (𝓡 3)

theorem ne_neg_self_e (he : ‖e‖ = 1) : e ≠ -e := by
  intro h
  have : e = 0 := by
    have h2 : (2 : ℝ) • e = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel e
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [this, norm_zero] at he; exact zero_ne_one he

theorem nonempty_UN [Nontrivial W] : Nonempty (UN e) := by
  obtain ⟨v, hv⟩ : ∃ v : W, ‖v‖ = 1 := by
    obtain ⟨v, hv0⟩ := exists_ne (0 : W)
    exact ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]⟩
  by_cases h : v = -e
  · refine ⟨⟨⟨-v, by simp [hv]⟩, ?_⟩⟩
    show -v ≠ -e
    intro h'
    have hve : v = e := neg_injective h'
    have : e = -e := hve ▸ h
    have he0 : e = 0 := by
      have h2 : (2 : ℝ) • e = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel e
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
    rw [hve, he0, norm_zero] at hv; exact zero_ne_one hv
  · exact ⟨⟨⟨v, by simp [hv]⟩, h⟩⟩

theorem nonempty_M0 [Nontrivial W] : Nonempty (M0 e) :=
  ⟨((nonempty_UN (e := e)).some, 1)⟩

theorem nontrivial_of_polarData (_D : PolarData (m := m) e) : Nontrivial W :=
  Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ W = (m + 1) + 1)

namespace PolarData

variable (D : PolarData (m := m) e)

/-- `ζ` of a point of the product chart. -/
def ζ0 (p : M0 e) : W := ((p.1 : Sn) : W)

theorem norm_ζ0 (p : M0 e) : ‖ζ0 p‖ = 1 := by simp [ζ0]

theorem ζ0_ne (p : M0 e) : ζ0 p ≠ -e := p.1.2

theorem contMDiff_ζ0 : ContMDiff (IP m) 𝓘(ℝ, W) ∞ (ζ0 (e := e)) :=
  contMDiff_coe_sphere.comp (contMDiff_subtype_val.comp contMDiff_fst)

/-- `ρ(q)` on the sphere. -/
def ρS (q : S3) (ζ : Sn) : Sn :=
  ⟨D.ρ q ζ, by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]; exact mem_sphere_zero_iff_norm.1 ζ.2⟩

/-- `ρ(q)` on `S(V)`. -/
def ρV (q : S3) (y : sphere (0 : Vs e) 1) : sphere (0 : Vs e) 1 :=
  ⟨⟨D.ρ q ((y : Vs e) : W), by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have h1 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (y : Vs e).2
    calc ⟪e, D.ρ q ((y : Vs e) : W)⟫ = ⟪D.ρ q e, D.ρ q ((y : Vs e) : W)⟫ := by rw [D.ρ_e]
      _ = 0 := by rw [LinearIsometryEquiv.inner_map_map, h1]⟩, by
    rw [mem_sphere_zero_iff_norm]
    show ‖D.ρ q ((y : Vs e) : W)‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (mem_sphere_zero_iff_norm.1 y.2 : ‖(y : Vs e)‖ = 1)⟩

theorem θ_ρV (q : S3) (y : sphere (0 : Vs e) 1) : D.θ (D.ρV q y) = q * D.θ y * q⁻¹ :=
  D.θ_equiv q y _ rfl

theorem ρ_ne_neg_e (q : S3) {ζ : W} (h : ζ ≠ -e) : D.ρ q ζ ≠ -e := by
  intro h'; apply h
  exact (D.ρ q).injective (h'.trans (by rw [map_neg, D.ρ_e]))


/-! ## The transition `κ(ζ, u) = (Rζ, θ(x(ζ)) u)` -/

/-- The overlap `(U_N ∖ {o_N}) × S³` (in `N`-coordinates). -/
def OP (e : W) : TopologicalSpace.Opens (M0 e) :=
  ⟨{p | ζ0 p ≠ e}, isOpen_ne_fun
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)) continuous_const⟩

theorem mem_OP (p : OP e) : ζ0 (p : M0 e) ≠ e := p.2

include D in
theorem sq_lt {p : M0 e} (hp : ζ0 p ≠ e) : ⟪ζ0 p, e⟫ ^ 2 < 1 :=
  inner_sq_lt_one D.e_norm (norm_ζ0 p) hp (ζ0_ne p)

/-- `R ζ`, as a point of `U_N`. -/
def Rmap (p : M0 e) (hp : ζ0 p ≠ e) : UN e :=
  ⟨⟨reflE e (ζ0 p), by rw [mem_sphere_zero_iff_norm, norm_reflE D.e_norm, norm_ζ0]⟩,
    reflE_ne_neg D.e_norm hp⟩

/-- The angular variable `x(ζ) ∈ S(V)`. -/
def xS (p : M0 e) (hp : ζ0 p ≠ e) : sphere (0 : Vs e) 1 :=
  ⟨⟨pX e (ζ0 p), by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact inner_pX D.e_norm _⟩, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_pX D.e_norm (norm_ζ0 p) (D.sq_lt hp)⟩

/-- `κ` on the overlap. -/
def ΦP (p : OP e) : OP e :=
  ⟨(D.Rmap p (mem_OP p), D.θ (D.xS p (mem_OP p)) * (p : M0 e).2), reflE_ne D.e_norm (ζ0_ne _)⟩

/-- `κ⁻¹` on the overlap. -/
def ΦP' (p : OP e) : OP e :=
  ⟨(D.Rmap p (mem_OP p), (D.θ (D.xS p (mem_OP p)))⁻¹ * (p : M0 e).2), reflE_ne D.e_norm (ζ0_ne _)⟩

theorem xS_Rmap (p : M0 e) (hp : ζ0 p ≠ e) (u : S3) (h') :
    D.xS (D.Rmap p hp, u) h' = D.xS p hp :=
  Subtype.ext (Subtype.ext (pX_reflE D.e_norm _))

theorem Rmap_Rmap (p : M0 e) (hp : ζ0 p ≠ e) (u : S3) (h') :
    D.Rmap (D.Rmap p hp, u) h' = p.1 :=
  Subtype.ext (Subtype.ext (reflE_reflE D.e_norm _))

/-- `κ` as a self-equivalence of the overlap. -/
def ΦPe : OP e ≃ OP e where
  toFun := D.ΦP
  invFun := D.ΦP'
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext (by dsimp only [ΦP, ΦP']; exact D.Rmap_Rmap _ _ _ _) ?_
    dsimp only [ΦP, ΦP']
    rw [D.xS_Rmap, inv_mul_cancel_left]
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext (by dsimp only [ΦP, ΦP']; exact D.Rmap_Rmap _ _ _ _) ?_
    dsimp only [ΦP, ΦP']
    rw [D.xS_Rmap, mul_inv_cancel_left]

theorem contMDiff_ζOP : ContMDiff (IP m) 𝓘(ℝ, W) ∞ fun p : OP e => ζ0 (p : M0 e) :=
  contMDiff_ζ0.comp contMDiff_subtype_val

theorem contMDiff_Rmap : ContMDiff (IP m) (𝓡 (m + 1)) ∞ fun p : OP e => D.Rmap p (mem_OP p) :=
  (ContMDiff.subtypeVal_comp_iff (UN e) _).1
    (contMDiff_sphere_of_coe (by exact (contDiff_reflE e).contMDiff.comp (contMDiff_ζOP (e := e) (m := m))))

theorem contMDiff_xS : ContMDiff (IP m) (𝓡 m) ∞ fun p : OP e => D.xS p (mem_OP p) := by
  apply contMDiff_sphere_of_coe
  have h : (fun p : OP e => ((D.xS p (mem_OP p) : sphere (0 : Vs e) 1) : Vs e)) =
      fun p : OP e => (Vs e).orthogonalProjectionOnto (pX e (ζ0 (p : M0 e))) :=
    funext fun p => (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _).symm
  rw [h]
  intro p
  exact ((Vs e).orthogonalProjectionOnto.contDiff.contDiffAt.comp _
    (contDiffAt_pX e (D.sq_lt (mem_OP p)))).comp_contMDiffAt
    (f := fun q : OP e => ζ0 (q : M0 e)) ((contMDiff_ζOP (e := e) (m := m)) p)

theorem contMDiff_θxS : ContMDiff (IP m) (𝓡 3) ∞ fun p : OP e => D.θ (D.xS p (mem_OP p)) :=
  D.θ_smooth.comp D.contMDiff_xS

theorem contMDiff_uOP : ContMDiff (IP m) (𝓡 3) ∞ fun p : OP e => (p : M0 e).2 :=
  contMDiff_snd.comp contMDiff_subtype_val

theorem contMDiff_ΦP : ContMDiff (IP m) (IP m) ∞ fun p : OP e => ((D.ΦP p : OP e) : M0 e) :=
  D.contMDiff_Rmap.prodMk (contMDiff_sphere_of_coe (by
    exact contDiff_mul.comp_contMDiff ((contMDiff_coe_sphere.comp D.contMDiff_θxS).prodMk_space
      (contMDiff_coe_sphere.comp (contMDiff_uOP (e := e) (m := m))))))

theorem contMDiff_ΦP' : ContMDiff (IP m) (IP m) ∞ fun p : OP e => ((D.ΦP' p : OP e) : M0 e) := by
  refine D.contMDiff_Rmap.prodMk (contMDiff_sphere_of_coe ?_)
  have hinv : ContMDiff (IP m) 𝓘(ℝ, ℍ[ℝ]) ∞
      fun p : OP e => (((D.θ (D.xS p (mem_OP p)))⁻¹ : S3) : ℍ[ℝ]) := by
    have h : (fun p : OP e => (((D.θ (D.xS p (mem_OP p)))⁻¹ : S3) : ℍ[ℝ])) =
        fun p : OP e => ((D.θ (D.xS p (mem_OP p)) : S3) : ℍ[ℝ])⁻¹ := funext fun p => coe_inv_S3' _
    rw [h]
    intro p
    exact (contDiffAt_quat_inv (n := ⊤) (ne_zero_of_mem_unit_sphere _)).comp_contMDiffAt
      (f := fun q : OP e => ((D.θ (D.xS q (mem_OP q)) : S3) : ℍ[ℝ]))
      ((contMDiff_coe_sphere.comp D.contMDiff_θxS) p)
  exact contDiff_mul.comp_contMDiff (hinv.prodMk_space (contMDiff_coe_sphere.comp (contMDiff_uOP (e := e) (m := m))))

/-- `κ` as a homeomorphism of the overlap. -/
def ΦPh : OP e ≃ₜ OP e where
  toEquiv := D.ΦPe
  continuous_toFun := D.contMDiff_ΦP.continuous.subtype_mk _
  continuous_invFun := D.contMDiff_ΦP'.continuous.subtype_mk _

/-- **The transition** of `P_θ`: `(ζ, u) ↦ (Rζ, θ(x(ζ))u)` on `(U_N ∖ {o_N}) × S³`. -/
def κP : OpenPartialHomeomorph (M0 e) (M0 e) := opensPH (OP e) D.ΦPh

theorem κP_apply (p : OP e) : D.κP p = D.ΦP p := opensPH_apply _ _ p

theorem κP_source : D.κP.source = OP e := rfl

theorem hκP : ContMDiffOn (IP m) (IP m) ∞ D.κP D.κP.source :=
  contMDiffOn_opensPH (IP m) _ _ D.contMDiff_ΦP

theorem hκPs : ContMDiffOn (IP m) (IP m) ∞ D.κP.symm D.κP.target :=
  contMDiffOn_opensPH_symm (IP m) _ _ D.contMDiff_ΦP'

end PolarData

/-! ## The polar bundle -/

/-- **The polar bundle `P_θ`** ([GG] `def:polar`). -/
abbrev PolarBundle (D : PolarData (m := m) e) := Glued D.κP

instance chartedSpace_polarBundle (D : PolarData (m := m) e) :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3)))
      (PolarBundle D) :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_M0 (e := e)
  chartedSpaceGlued D.κP

/-- **`P_θ` is a `C^∞` manifold** (model `ℝⁿ × ℝ³`). -/
instance isManifold_polarBundle (D : PolarData (m := m) e) : IsManifold (IP m) ∞ (PolarBundle D) :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_M0 (e := e)
  isManifold_glued (IP m) D.hκP D.hκPs


/-! ## The actions and the projection -/

namespace PolarData

variable (D : PolarData (m := m) e)

/-- The star action in a product chart, `eq:staraction`: `q ⋆ (ζ, u) = (ρ(q)ζ, qu)`. -/
def starM (q : S3) (p : M0 e) : M0 e := (⟨D.ρS q p.1, D.ρ_ne_neg_e q p.1.2⟩, q * p.2)

/-- The principal action in a product chart: `(ζ, u)h = (ζ, uh)`. -/
def rightM (h : S3) (p : M0 e) : M0 e := (p.1, p.2 * h)

theorem starM_mem {q : S3} {p : M0 e} (hp : ζ0 p ≠ e) : ζ0 (D.starM q p) ≠ e := by
  intro h; apply hp
  exact (D.ρ q).injective (h.trans (D.ρ_e q).symm)

theorem κP_eq (p : M0 e) (hp : ζ0 p ≠ e) : D.κP p = (D.Rmap p hp, D.θ (D.xS p hp) * p.2) :=
  D.κP_apply ⟨p, hp⟩

/-- **The star action is compatible with the transition** ([GG] §2, after `def:polar`:
`θ(ρ(q)x) q u_N = q θ(x) u_N`). -/
theorem κP_starM (q : S3) (p : M0 e) (hp : ζ0 p ≠ e) :
    D.κP (D.starM q p) = D.starM q (D.κP p) := by
  rw [D.κP_eq _ (D.starM_mem hp), D.κP_eq _ hp]
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) ?_
  · exact reflE_map (D.ρ q).toLinearIsometry (D.ρ_e q) (ζ0 p)
  · have hx : D.xS (D.starM q p) (D.starM_mem hp) = D.ρV q (D.xS p hp) :=
      Subtype.ext (Subtype.ext (pX_map (D.ρ q).toLinearIsometry (D.ρ_e q) _))
    show D.θ (D.xS (D.starM q p) _) * (q * p.2) = q * (D.θ (D.xS p hp) * p.2)
    rw [hx, D.θ_ρV]; group

/-- The principal action is compatible with the transition. -/
theorem κP_rightM (h : S3) (p : M0 e) (hp : ζ0 p ≠ e) :
    D.κP (rightM h p) = rightM h (D.κP p) := by
  rw [D.κP_eq _ hp, D.κP_eq (rightM h p) hp]
  exact Prod.ext rfl (mul_assoc _ _ _).symm

/-- The star action on `P_θ`. -/
def star (q : S3) : PolarBundle D → PolarBundle D :=
  glueLift (fun a => ι₁ D.κP (D.starM q a)) (fun b => ι₂ D.κP (D.starM q b)) fun a ha => by
    show ι₂ D.κP (D.starM q (D.κP a)) = ι₁ D.κP (D.starM q a)
    rw [← D.κP_starM q a ha, ι₂_apply (show D.starM q a ∈ D.κP.source from D.starM_mem ha)]

/-- The principal right action on `P_θ`. -/
def ract (p : PolarBundle D) (h : S3) : PolarBundle D :=
  glueLift (fun a => ι₁ D.κP (rightM h a)) (fun b => ι₂ D.κP (rightM h b)) (fun a ha => by
    show ι₂ D.κP (rightM h (D.κP a)) = ι₁ D.κP (rightM h a)
    rw [← D.κP_rightM h a ha, ι₂_apply (show rightM h a ∈ D.κP.source from ha)]) p

/-- The bundle projection `π_θ : P_θ → S^n`. -/
def proj : PolarBundle D → Sn :=
  glueLift (fun a => (a.1 : Sn))
    (fun b => ⟨reflE e (ζ0 b), by rw [mem_sphere_zero_iff_norm, norm_reflE D.e_norm, norm_ζ0]⟩)
    fun a ha => by
      rw [D.κP_eq a ha]
      exact Subtype.ext (reflE_reflE D.e_norm _)

@[simp] theorem star_ι₁ (q : S3) (a : M0 e) : D.star q (ι₁ D.κP a) = ι₁ D.κP (D.starM q a) := rfl
@[simp] theorem star_ι₂ (q : S3) (b : M0 e) : D.star q (ι₂ D.κP b) = ι₂ D.κP (D.starM q b) := rfl
@[simp] theorem ract_ι₁ (a : M0 e) (h : S3) : D.ract (ι₁ D.κP a) h = ι₁ D.κP (rightM h a) := rfl
@[simp] theorem ract_ι₂ (b : M0 e) (h : S3) : D.ract (ι₂ D.κP b) h = ι₂ D.κP (rightM h b) := rfl
theorem proj_ι₁ (a : M0 e) : (D.proj (ι₁ D.κP a) : W) = ζ0 a := rfl
theorem proj_ι₂ (b : M0 e) : (D.proj (ι₂ D.κP b) : W) = reflE e (ζ0 b) := rfl

theorem starM_one (a : M0 e) : D.starM 1 a = a := by
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (one_mul _)
  show D.ρ 1 (ζ0 a) = ζ0 a
  rw [map_one]; rfl

theorem starM_mul (q q' : S3) (a : M0 e) : D.starM (q * q') a = D.starM q (D.starM q' a) := by
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (mul_assoc _ _ _)
  show D.ρ (q * q') (ζ0 a) = D.ρ q (D.ρ q' (ζ0 a))
  rw [map_mul]; rfl

theorem star_one (p : PolarBundle D) : D.star 1 p = p := by
  induction p using glued_induction with
  | h₁ a => rw [star_ι₁, starM_one]
  | h₂ b => rw [star_ι₂, starM_one]

theorem star_mul (q q' : S3) (p : PolarBundle D) : D.star (q * q') p = D.star q (D.star q' p) := by
  induction p using glued_induction with
  | h₁ a => rw [star_ι₁, star_ι₁, star_ι₁, starM_mul]
  | h₂ b => rw [star_ι₂, star_ι₂, star_ι₂, starM_mul]

/-- **The star action is an action of `S³` on `P_θ`.** -/
instance mulAction : MulAction S3 (PolarBundle D) where
  smul := D.star
  one_smul := D.star_one
  mul_smul := D.star_mul

theorem smul_def (q : S3) (p : PolarBundle D) : q • p = D.star q p := rfl

/-- **The star action commutes with the principal action**: `q ⋆ (ph) = (q ⋆ p)h`. -/
theorem star_ract (q h : S3) (p : PolarBundle D) : q • D.ract p h = D.ract (q • p) h :=
  glued_induction (P := fun p => q • D.ract p h = D.ract (q • p) h)
    (fun a => congrArg (ι₁ D.κP) (Prod.ext rfl (mul_assoc _ _ _).symm))
    (fun b => congrArg (ι₂ D.κP) (Prod.ext rfl (mul_assoc _ _ _).symm)) p

/-- **The star action is free.** -/
theorem star_free (q : S3) (p : PolarBundle D) (hq : q • p = p) : q = 1 := by
  induction p using glued_induction with
  | h₁ a =>
    have h := congrArg Prod.snd (ι₁_injective D.κP hq)
    exact mul_right_cancel (h.trans (one_mul _).symm)
  | h₂ b =>
    have h := congrArg Prod.snd (ι₂_injective D.κP hq)
    exact mul_right_cancel (h.trans (one_mul _).symm)

/-- **`π_θ` is equivariant**: `π(q ⋆ p) = ρ(q) π(p)` ([GG] `def:starbundle` (3)). -/
theorem proj_star (q : S3) (p : PolarBundle D) : D.proj (q • p) = D.ρS q (D.proj p) := by
  induction p using glued_induction with
  | h₁ a => rfl
  | h₂ b => exact Subtype.ext (reflE_map (D.ρ q).toLinearIsometry (D.ρ_e q) (ζ0 b))

/-- `π_θ` is invariant under the principal action. -/
theorem proj_ract (p : PolarBundle D) (h : S3) : D.proj (D.ract p h) = D.proj p := by
  induction p using glued_induction with
  | h₁ a => rfl
  | h₂ b => rfl

theorem ract_ract (p : PolarBundle D) (h h' : S3) : D.ract (D.ract p h) h' = D.ract p (h * h') := by
  induction p using glued_induction with
  | h₁ a => exact congrArg (ι₁ D.κP) (Prod.ext rfl (mul_assoc _ _ _))
  | h₂ b => exact congrArg (ι₂ D.κP) (Prod.ext rfl (mul_assoc _ _ _))

/-- **The principal action is free.** -/
theorem ract_free (p : PolarBundle D) (h : S3) (hh : D.ract p h = p) : h = 1 := by
  induction p using glued_induction with
  | h₁ a =>
    have h' := congrArg Prod.snd (ι₁_injective D.κP hh)
    exact mul_left_cancel (h'.trans (mul_one _).symm)
  | h₂ b =>
    have h' := congrArg Prod.snd (ι₂_injective D.κP hh)
    exact mul_left_cancel (h'.trans (mul_one _).symm)

theorem mem_range_ι₁ (p : PolarBundle D) (hp : (D.proj p : W) ≠ -e) : p ∈ range (ι₁ D.κP) := by
  induction p using glued_induction with
  | h₁ a => exact ⟨a, rfl⟩
  | h₂ b =>
    have hb : b ∈ D.κP.target := by
      show ζ0 b ≠ e
      intro h; apply hp; rw [proj_ι₂, h, reflE_e D.e_norm]
    exact ⟨_, ι₂_symm hb⟩

theorem mem_range_ι₂ (p : PolarBundle D) (hp : (D.proj p : W) ≠ e) : p ∈ range (ι₂ D.κP) := by
  induction p using glued_induction with
  | h₁ a => exact ⟨_, ι₂_apply (show a ∈ D.κP.source from hp)⟩
  | h₂ b => exact ⟨b, rfl⟩

/-- **The principal action is transitive on fibres.** -/
theorem ract_transitive (p p' : PolarBundle D) (h : D.proj p = D.proj p') :
    ∃ g : S3, p' = D.ract p g := by
  by_cases hN : (D.proj p : W) = -e
  · have hS : (D.proj p : W) ≠ e := by rw [hN]; exact (ne_neg_self_e D.e_norm).symm
    obtain ⟨b, rfl⟩ := D.mem_range_ι₂ p hS
    obtain ⟨b', rfl⟩ := D.mem_range_ι₂ p' (h ▸ hS)
    refine ⟨b.2⁻¹ * b'.2, congrArg (ι₂ D.κP) (Prod.ext ?_ (by simp [rightM]))⟩
    have h1 : reflE e (ζ0 b) = reflE e (ζ0 b') := congrArg Subtype.val h
    have h2 : ζ0 b = ζ0 b' := by
      rw [← reflE_reflE D.e_norm (ζ0 b), h1, reflE_reflE D.e_norm]
    exact (Subtype.ext (Subtype.ext h2)).symm
  · obtain ⟨a, rfl⟩ := D.mem_range_ι₁ p hN
    obtain ⟨a', rfl⟩ := D.mem_range_ι₁ p' (h ▸ hN)
    refine ⟨a.2⁻¹ * a'.2, congrArg (ι₁ D.κP) (Prod.ext ?_ (by simp [rightM]))⟩
    exact (Subtype.ext (Subtype.ext (congrArg Subtype.val h))).symm

/-! ### Smoothness -/

theorem contMDiff_mulS3 : ContMDiff ((𝓡 3).prod (IP m)) (𝓡 3) ∞
    fun x : S3 × M0 e => x.1 * x.2.2 := by
  have hc : ContMDiff ((𝓡 3).prod (IP m)) 𝓘(ℝ, ℍ[ℝ] × ℍ[ℝ]) ∞
      fun x : S3 × M0 e => ((x.1 : ℍ[ℝ]), ((x.2.2 : S3) : ℍ[ℝ])) :=
    (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space
      (contMDiff_coe_sphere.comp (contMDiff_snd.comp contMDiff_snd))
  exact contMDiff_sphere_of_coe ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℍ[ℝ])).comp_contMDiff hc)

theorem contMDiff_mulS3' : ContMDiff ((𝓡 3).prod (IP m)) (𝓡 3) ∞
    fun x : S3 × M0 e => x.2.2 * x.1 := by
  have hc : ContMDiff ((𝓡 3).prod (IP m)) 𝓘(ℝ, ℍ[ℝ] × ℍ[ℝ]) ∞
      fun x : S3 × M0 e => (((x.2.2 : S3) : ℍ[ℝ]), (x.1 : ℍ[ℝ])) :=
    (contMDiff_coe_sphere.comp (contMDiff_snd.comp contMDiff_snd)).prodMk_space
      (contMDiff_coe_sphere.comp contMDiff_fst)
  exact contMDiff_sphere_of_coe ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℍ[ℝ])).comp_contMDiff hc)

theorem contMDiff_starM : ContMDiff ((𝓡 3).prod (IP m)) (IP m) ∞
    fun x : S3 × M0 e => D.starM x.1 x.2 := by
  have h1 : ContMDiff ((𝓡 3).prod (IP m)) (𝓡 (m + 1)) ∞
      fun x : S3 × M0 e => (D.starM x.1 x.2).1 := by
    refine (ContMDiff.subtypeVal_comp_iff (UN e) _).1 (contMDiff_sphere_of_coe ?_)
    exact (D.ρ_smooth.comp contMDiff_fst).clm_apply (contMDiff_ζ0.comp contMDiff_snd)
  exact h1.prodMk (contMDiff_mulS3 (m := m) (e := e))

theorem contMDiff_rightM : ContMDiff ((𝓡 3).prod (IP m)) (IP m) ∞
    fun x : S3 × M0 e => rightM x.1 x.2 :=
  (contMDiff_fst.comp contMDiff_snd).prodMk (contMDiff_mulS3' (m := m) (e := e))

/-- **The star action is smooth** (jointly), including at the poles. -/
theorem contMDiff_star : ContMDiff ((𝓡 3).prod (IP m)) (IP m) ∞
    fun x : S3 × PolarBundle D => x.1 • x.2 := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_M0 (e := e)
  exact contMDiff_prod_glued (IP m) D.hκP D.hκPs
    ((contMDiff_ι₁ (IP m) D.hκP D.hκPs).comp D.contMDiff_starM)
    ((contMDiff_ι₂ (IP m) D.hκP D.hκPs).comp D.contMDiff_starM)

/-- **The principal action is smooth** (jointly). -/
theorem contMDiff_ract : ContMDiff ((𝓡 3).prod (IP m)) (IP m) ∞
    fun x : S3 × PolarBundle D => D.ract x.2 x.1 := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_M0 (e := e)
  exact contMDiff_prod_glued (IP m) D.hκP D.hκPs
    ((contMDiff_ι₁ (IP m) D.hκP D.hκPs).comp (contMDiff_rightM (e := e) (m := m)))
    ((contMDiff_ι₂ (IP m) D.hκP D.hκPs).comp (contMDiff_rightM (e := e) (m := m)))

/-- **The projection is smooth.** -/
theorem contMDiff_proj : ContMDiff (IP m) (𝓡 (m + 1)) ∞ D.proj := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_M0 (e := e)
  exact contMDiff_glueLift (IP m) D.hκP D.hκPs _
    (contMDiff_subtype_val.comp contMDiff_fst)
    (contMDiff_sphere_of_coe ((contDiff_reflE e).contMDiff.comp contMDiff_ζ0))

end PolarData

end Bundle

end

end ExoticSpheres8And10
