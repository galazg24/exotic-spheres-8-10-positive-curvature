/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.Average
import ExoticSpheres8And10.StarBundles.NormalForm

/-! # §3, Steps 3–5: equivariant radial sections, and `prop:polar`

With the invariant potential `Ā` of `S3_Average` (in the trivialisation `s⁰`), [GG] Step 3's
section is `s_N(φ(v)) = s⁰(v) · u_v(1)`, where `u_v` solves the transport equation
`u' = −Ā(τv, v) u`, `u(0) = 1`, along the ray `τ ↦ τv`.

* `sV`: this section in stereographic coordinates; smooth (`contMDiff_sV`, from the smooth
  dependence of ODE solutions on parameters, `LinCoeff.contDiff_T`);
* `T_equiv`, `sV_equiv`: **[GG] Step 4**, `s_N(ρ(q)ζ) = (q ⋆ s_N(ζ)) q⁻¹` (`eq:sectionequiv`).
  [GG] argues that `q ⋆ s_N ∘ c_x` and `(s_N ∘ c_{ρ(q)x}) q` are horizontal lifts of the same
  curve with the same initial point; in the trivialisation this is the statement that
  `h(q, τv) u_v(τ) q⁻¹` solves the transport equation for `ρ(q)v` (by the invariance `Abar_inv`)
  with initial value `h(q,0) q⁻¹ = 1`, and ODE uniqueness;
* `psiN`: the stereographic chart `U_N → V`, and the section `sN` over `U_N`;
* the south: the same construction for the pole `−e` (`StarRep.flip`, `StarBundle.flip`);
* `equivSections`: the output of Steps 1–4, and **`prop_polar`**.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real Filter Topology MeasureTheory

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Radial

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E) [T2Space E]

local notation "Sn" => sphere (0 : W) 1

local notation "V" => Vs e

namespace StarBundle

/-- The transport equation for `Ā` along rays, `u' = −Ā(σv, v) u`. -/
def Cbar : LinCoeff V where
  M p := -B.Abar (p.1 • p.2, p.2)
  smooth := (B.contDiff_Abar.comp ((contDiff_fst.smul contDiff_snd).prodMk contDiff_snd)).neg
  pure p := by rw [Quaternion.re_neg, B.Abar_re, neg_zero]

/-- The time-one transport `u_v(1) ∈ S³`. -/
def T3 (v : V) : S3 :=
  ⟨B.Cbar.T v, mem_sphere_zero_iff_norm.2 (B.Cbar.norm_sol v 1 ⟨zero_le_one, le_rfl⟩)⟩

theorem contMDiff_T3 : ContMDiff 𝓘(ℝ, V) (𝓡 3) ∞ B.T3 :=
  contMDiff_sphere_of_coe B.Cbar.contDiff_T.contMDiff

/-- **[GG] Step 3: the radial section** `s_N(φ(v)) = s⁰(v) u_v(1)`. -/
def sV (v : V) : E := B.ract (B.s0 v) (B.T3 v)

theorem contMDiff_sV : ContMDiff 𝓘(ℝ, V) (IP m) ∞ B.sV :=
  ContMDiff.comp (g := fun x : E × S3 => B.ract x.1 x.2) (f := fun v => (B.s0 v, B.T3 v))
    B.ract_smooth (B.contMDiff_s0.prodMk B.contMDiff_T3)

theorem proj_sV (v : V) : B.proj (B.sV v) = R.phiN v := by rw [sV, B.proj_ract, B.proj_s0]

/-- The transport is equivariant: `u_{ρ(q)v}(1) = h(q,v) u_v(1) q⁻¹`. -/
theorem T_equiv (q : S3) (v : V) :
    B.Cbar.T (R.ρL q v) = ((B.hq q v : S3) : ℍ[ℝ]) * B.Cbar.T v * ((q⁻¹ : S3) : ℍ[ℝ]) := by
  set u : ℝ → ℍ[ℝ] := fun σ =>
    ((B.hq q (σ • v) : S3) : ℍ[ℝ]) * B.Cbar.sol v σ * ((q⁻¹ : S3) : ℍ[ℝ])
  have hu0 : u 0 = 1 := by
    simp only [u, zero_smul, B.hq_zero, B.Cbar.sol_zero, mul_one, coe_inv_S3]
    exact mul_inv_cancel₀ (ne_zero_of_mem_unit_sphere q)
  have hu : ∀ σ ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u (B.Cbar.M (σ, R.ρL q v) * u σ) (Icc 0 1) σ := by
    intro σ hσ
    have hH : HasDerivAt (fun σ : ℝ => ((B.hq q (σ • v) : S3) : ℍ[ℝ]))
        (fderiv ℝ (fun y : V => ((B.hq q y : S3) : ℍ[ℝ])) (σ • v) ((1 : ℝ) • v)) σ := by
      have := (B.hasFDerivAt_hq q (σ • v)).comp_hasDerivAt σ ((hasDerivAt_id' σ).smul_const v)
      exact this
    have hd := ((hH.hasDerivWithinAt (s := Icc 0 1)).mul (B.Cbar.hasDeriv_sol v σ hσ)).mul_const
      ((q⁻¹ : S3) : ℍ[ℝ])
    refine hd.congr_deriv ?_
    set Hx : ℍ[ℝ] := ((B.hq q (σ • v) : S3) : ℍ[ℝ])
    set Dv := fderiv ℝ (fun y : V => ((B.hq q y : S3) : ℍ[ℝ])) (σ • v) v
    have hinv := B.Abar_inv q (σ • v) v
    rw [map_smul] at hinv
    have hunit : Hx * Star.star Hx = 1 :=
      mul_star_of_norm_one (mem_sphere_zero_iff_norm.1 (B.hq q (σ • v)).2)
    have key : Dv = Hx * B.Abar (σ • v, v) - B.Abar (σ • R.ρL q v, R.ρL q v) * Hx := by
      rw [hinv, mu]
      have : Hx * (Star.star Hx * B.Abar (σ • R.ρL q v, R.ρL q v) * Hx +
          Star.star Hx * Dv) = (Hx * Star.star Hx) * B.Abar (σ • R.ρL q v, R.ρL q v) * Hx +
          (Hx * Star.star Hx) * Dv := by noncomm_ring
      rw [this, hunit]; noncomm_ring
    simp only [Cbar, one_smul, u]
    change (Dv * B.Cbar.sol v σ + Hx * (-B.Abar (σ • v, v) * B.Cbar.sol v σ)) *
        ((q⁻¹ : S3) : ℍ[ℝ]) =
      -B.Abar (σ • R.ρL q v, R.ρL q v) * (Hx * B.Cbar.sol v σ * ((q⁻¹ : S3) : ℍ[ℝ]))
    rw [key]; noncomm_ring
  have := B.Cbar.sol_unique (R.ρL q v) u hu0 hu 1 ⟨zero_le_one, le_rfl⟩
  simp only [u, one_smul] at this
  rw [LinCoeff.T, ← this]; rfl

/-- **[GG] Step 4, `eq:sectionequiv`** in stereographic coordinates. -/
theorem sV_equiv (q : S3) (v : V) : B.sV (R.ρL q v) = B.ract (B.star q (B.sV v)) q⁻¹ := by
  rw [sV, sV, B.star_ract, ← B.ract_hq, B.ract_mul, B.ract_mul]
  congr 1
  apply Subtype.ext
  rw [coe_mul_S3, coe_mul_S3, ← mul_assoc]
  exact B.T_equiv q v

end StarBundle

/-! ### From stereographic coordinates to `U_N` -/

/-- The stereographic chart `U_N → V`. -/
def psiN (e : W) (ζ : Sn) : Vs e := (Vs e).orthogonalProjectionOnto (stereo e ζ)

namespace StarRep

variable (R)

include R

theorem stereo_mem_V (ζ : Sn) : stereo e (ζ : W) ∈ V := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
  exact inner_stereo R.e_norm _

theorem coe_psiN (ζ : Sn) : ((psiN e ζ : V) : W) = stereo e ζ := by
  have := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := Vs e)
    ⟨stereo e (ζ : W), R.stereo_mem_V ζ⟩
  exact congrArg Subtype.val this

theorem phiN_psiN {ζ : Sn} (hζ : ζ ∈ UN e) : R.phiN (psiN e ζ) = ζ := by
  apply Subtype.ext
  show stereoInv e (psiN e ζ : W) = ζ
  rw [R.coe_psiN]
  exact stereoInv_stereo R.e_norm (mem_sphere_zero_iff_norm.1 ζ.2)
    (inner_ne_neg_one R.e_norm (mem_sphere_zero_iff_norm.1 ζ.2) hζ)

theorem psiN_ρS (q : S3) (ζ : Sn) : psiN e (R.ρS q ζ) = R.ρL q (psiN e ζ) := by
  apply Subtype.ext
  rw [R.coe_psiN, coe_ρL, R.coe_psiN]
  exact stereo_map e (R.ρ q).toLinearIsometry (R.ρ_e q) ζ

theorem contMDiffOn_psiN : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, V) ∞ (psiN e) (UN e) := by
  intro ζ hζ
  have h1 : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, W) ∞ (fun ζ : Sn => stereo e (ζ : W)) ζ :=
    (contDiffAt_stereo e (inner_ne_neg_one R.e_norm (mem_sphere_zero_iff_norm.1 ζ.2) hζ)
      ).contMDiffAt.comp ζ contMDiff_coe_sphere.contMDiffAt
  exact ((Vs e).orthogonalProjectionOnto.contDiff.contMDiff.contMDiffAt.comp ζ h1
    ).contMDiffWithinAt

end StarRep

namespace StarBundle

/-- **The equivariant section `s_N` over `U_N`.** -/
def sN (ζ : Sn) : E := B.sV (psiN e ζ)

theorem contMDiffOn_sN : ContMDiffOn (𝓡 (m + 1)) (IP m) ∞ B.sN (UN e) :=
  B.contMDiff_sV.comp_contMDiffOn R.contMDiffOn_psiN

theorem proj_sN {ζ : Sn} (hζ : ζ ∈ UN e) : B.proj (B.sN ζ) = ζ := by
  rw [sN, B.proj_sV, R.phiN_psiN hζ]

theorem sN_equiv (q : S3) (ζ : Sn) : B.sN (R.ρS q ζ) = B.ract (B.star q (B.sN ζ)) q⁻¹ := by
  rw [sN, R.psiN_ρS, B.sV_equiv]; rfl

end StarBundle

end Radial

/-! ### The south pole -/

section South

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W}

/-- The same representation, with the distinguished pole `−e`. -/
def StarRep.flip (R : StarRep e) : StarRep (-e) where
  e_norm := by rw [norm_neg, R.e_norm]
  ρ := R.ρ
  ρ_e q := by rw [map_neg, R.ρ_e]
  ρ_smooth := R.ρ_smooth

variable {R : StarRep e} {E : Type} [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]

/-- A star bundle for `R` is one for `R.flip`. -/
def StarBundle.flip (B : StarBundle (m := m) R E) : StarBundle (m := m) R.flip E :=
  { B with proj_star := B.proj_star }

theorem UN_neg (ζ : sphere (0 : W) 1) : ζ ∈ UN (-e) ↔ ζ ∈ US e := by
  show (ζ : W) ≠ - -e ↔ (ζ : W) ≠ e
  rw [neg_neg]

end South

/-! ### `prop:polar` -/

section Polar

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E) [T2Space E]

namespace StarBundle

/-- **The output of [GG] Steps 1–4**: smooth equivariant sections over `U_N` and `U_S`. -/
def equivSections : EquivSections B where
  sN := B.sN
  sS := B.flip.sN
  sN_smooth := B.contMDiffOn_sN
  sS_smooth := B.flip.contMDiffOn_sN.mono fun ζ hζ => (UN_neg ζ).2 hζ
  proj_sN ζ hζ := B.proj_sN hζ
  proj_sS ζ hζ := B.flip.proj_sN ((UN_neg ζ).2 hζ)
  sN_equiv q ζ _ := B.sN_equiv q ζ
  sS_equiv q ζ _ := B.flip.sN_equiv q ζ

/-- `dim V = n` (needed to regard `S(V)` as a manifold). -/
theorem _root_.ExoticSpheres8And10.StarRep.factVs (m : ℕ) [Fact (finrank ℝ W = (m + 1) + 1)] (R : StarRep e) :
    Fact (finrank ℝ (Vs e) = m + 1) :=
  ⟨Submodule.finrank_orthogonal_span_singleton (n := m + 1) (fun h => by
    have := R.e_norm; rw [h, norm_zero] at this; exact zero_ne_one this)⟩

/-- **[GG] `prop:polar`.** Every star bundle `π : E → S^n` is isomorphic to a polar bundle: there
are polar data `D` (with the same representation `ρ` and a smooth `θ : S(V) → S³` satisfying
`θ(ρ(q)x) = qθ(x)q⁻¹`, a field of `PolarData`) and a `C^∞` diffeomorphism `Φ : P_θ → E`
covering the identity of `S^n`, equivariant for the principal actions (a principal-bundle
isomorphism) and for the star actions. Consequently `E/S³_⋆ ≃ₜ P_θ/S³_⋆`. -/
theorem prop_polar :
    letI := R.factVs m
    ∃ D : PolarData (m := m) e, D.ρ = R.ρ ∧
      ∃ Φ : Diffeomorph (IP m) (IP m) (PolarBundle D) E ∞,
        (∀ x, B.proj (Φ x) = D.proj x) ∧
        (∀ x h, Φ (D.ract x h) = B.ract (Φ x) h) ∧
        (∀ (q : S3) x, Φ (q • x) = B.star q (Φ x)) ∧
        Nonempty (Quotient (EquivSections.starSetoid B) ≃ₜ D.OrbitSpace) := by
  letI := R.factVs m
  set S := B.equivSections
  exact ⟨S.polarData, rfl, S.normalFormDiffeo, S.proj_Φ, S.Φ_ract, S.Φ_star,
    ⟨S.starQuotientHomeo⟩⟩

/-! ### `E/S³_⋆` as a manifold -/

section QuotE

variable [Fact (finrank ℝ (Vs e) = m + 1)]

/-- The quotient map `E → E/S³_⋆ = QuotSpace`, `p ↦ [Φ⁻¹ p]`. -/
def starQuotMap : E → QuotSpace B.equivSections.polarData :=
  B.equivSections.polarData.orbitMap ∘ B.equivSections.Ψ

theorem contMDiff_starQuotMap : ContMDiff (IP m) (𝓡 (m + 1)) ∞ B.starQuotMap :=
  B.equivSections.polarData.contMDiff_orbitMap.comp B.equivSections.contMDiff_Ψ

theorem starQuotMap_surjective : Surjective B.starQuotMap := fun y => by
  obtain ⟨x, rfl⟩ := B.equivSections.polarData.orbitMap_surjective y
  exact ⟨B.equivSections.Φ x, by simp only [starQuotMap, comp_apply, B.equivSections.Ψ_Φ]⟩

/-- **The fibres of `E → QuotSpace` are exactly the star orbits.** -/
theorem starQuotMap_eq_iff (p p' : E) :
    B.starQuotMap p = B.starQuotMap p' ↔ ∃ q : S3, p' = B.star q p := by
  set S := B.equivSections
  simp only [starQuotMap, comp_apply]
  rw [S.polarData.orbitMap_eq_iff]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [← S.Φ_Ψ p', hq, S.Φ_star, S.Φ_Ψ]
  · rintro ⟨q, rfl⟩
    exact ⟨q, S.Ψ_star q p⟩

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N]

/-- **Universal property**: `f : E/S³_⋆ → N` is smooth iff `f ∘ (E → E/S³_⋆)` is. -/
theorem contMDiff_iff_comp_starQuotMap (f : QuotSpace B.equivSections.polarData → N) :
    ContMDiff (𝓡 (m + 1)) I' ∞ f ↔ ContMDiff (IP m) I' ∞ (f ∘ B.starQuotMap) := by
  set S := B.equivSections
  rw [S.polarData.contMDiff_iff_comp_orbitMap]
  constructor
  · intro h; exact h.comp S.contMDiff_Ψ
  · intro h
    have := h.comp S.contMDiff_Φ
    refine this.congr fun x => ?_
    simp only [starQuotMap, comp_apply]
    exact congrArg _ (congrArg _ (S.Ψ_Φ x).symm)

end QuotE

end StarBundle

end Polar

end

end ExoticSpheres8And10
