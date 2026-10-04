/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.PolarBundles.PolarBundle

/-! # §2: the star quotient `P_θ/S³_⋆` as a smooth manifold

[GG] `lem:attaching`: "`Ψ_α(ζ_α, u_α) = ρ(u_α)⁻¹ζ_α` is constant on star orbits. [...] every star
orbit contains a unique point with fibre coordinate `1`." Mathlib has no quotient manifolds. For
the star action on `P_θ` the slices `{u = 1}` are global in each chart, so the quotient manifold
can be constructed directly.

* `QuotSpace D`: two copies of `U_N` glued along `κ_Σ(z) = ρ(θ(x(z)))⁻¹ R z`, which is what `Ψ`
  makes of `eq:transition`. It is a `C^∞` manifold of dimension `n`.
* `orbitMap D : P_θ → QuotSpace D`, induced by `Ψ` on each chart. It is:
  - smooth (`contMDiff_orbitMap`) and surjective (`orbitMap_surjective`);
  - constant on star orbits (`orbitMap_star`), with fibres exactly the star orbits
    (`orbitMap_eq_iff`);
  - equipped with smooth sections `z ↦ [(z, 1)]` over both charts (`orbitMap_section₁`,
    `orbitMap_section₂`);
  - universal for smooth maps (`contMDiff_iff_comp_orbitMap`): a map out of `QuotSpace D` is
    smooth iff its composite with `orbitMap` is.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

theorem contMDiff_invS3 : ContMDiff (𝓡 3) (𝓡 3) ∞ fun q : S3 => q⁻¹ := by
  apply contMDiff_sphere_of_coe
  have h : (fun q : S3 => ((q⁻¹ : S3) : ℍ[ℝ])) = fun q : S3 => (q : ℍ[ℝ])⁻¹ :=
    funext coe_inv_S3'
  rw [h]
  intro q
  exact (contDiffAt_quat_inv (n := ⊤) (ne_zero_of_mem_unit_sphere q)).comp_contMDiffAt
    (f := fun q : S3 => (q : ℍ[ℝ])) (contMDiff_coe_sphere q)

section Quotient

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

local notation "Sn" => sphere (0 : W) 1

namespace PolarData

variable (D : PolarData (m := m) e)

/-- `ζ` of a point of `U_N`. -/
def ζU (z : UN e) : W := ((z : Sn) : W)

/-- `U_N ∖ {o_N}`. -/
def OS (e : W) : TopologicalSpace.Opens (UN e) :=
  ⟨{z | ζU z ≠ e}, isOpen_ne_fun (continuous_subtype_val.comp continuous_subtype_val)
    continuous_const⟩

theorem mem_OS (z : OS e) : ζ0 ((z : UN e), (1 : S3)) ≠ e := z.2

theorem ρ_mul_apply (a b : S3) (w : W) : D.ρ a (D.ρ b w) = D.ρ (a * b) w := by
  rw [map_mul]; rfl

theorem ρ_ne_e (q : S3) {w : W} (h : w ≠ e) : D.ρ q w ≠ e := by
  intro h'; apply h; exact (D.ρ q).injective (h'.trans (D.ρ_e q).symm)

theorem inner_ρ_e (q : S3) (w : W) : ⟪D.ρ q w, e⟫ = ⟪w, e⟫ :=
  calc ⟪D.ρ q w, e⟫ = ⟪D.ρ q w, D.ρ q e⟫ := by rw [D.ρ_e]
    _ = ⟪w, e⟫ := LinearIsometryEquiv.inner_map_map _ _ _

/-- `ρ(q)` on `U_N`. -/
def ρU (q : S3) (z : UN e) : UN e := ⟨D.ρS q z, D.ρ_ne_neg_e q z.2⟩

/-- `R` on `U_N ∖ {o_N}`. -/
def RU (z : UN e) (hz : ζ0 (z, (1 : S3)) ≠ e) : UN e := D.Rmap (z, 1) hz

/-- `θ(x(z))`. -/
def gS (z : UN e) (hz : ζ0 (z, (1 : S3)) ≠ e) : S3 := D.θ (D.xS (z, 1) hz)

theorem ρU_RU_mem (q : S3) (z : UN e) (hz : ζ0 (z, (1 : S3)) ≠ e) :
    ζ0 (D.ρU q (D.RU z hz), (1 : S3)) ≠ e :=
  D.ρ_ne_e q (reflE_ne D.e_norm z.2)

/-- `κ_Σ` on the overlap: `z ↦ ρ(θ(x z))⁻¹ R z`. -/
def ΦS (z : OS e) : OS e :=
  ⟨D.ρU (D.gS z (mem_OS z))⁻¹ (D.RU z (mem_OS z)), D.ρU_RU_mem _ _ _⟩

/-- `κ_Σ⁻¹` on the overlap: `z ↦ ρ(θ(x z)) R z`. -/
def ΦS' (z : OS e) : OS e :=
  ⟨D.ρU (D.gS z (mem_OS z)) (D.RU z (mem_OS z)), D.ρU_RU_mem _ _ _⟩

theorem xS_ρU_RU (q : S3) (z : UN e) (hz) (h') :
    D.xS (D.ρU q (D.RU z hz), 1) h' = D.ρV q (D.xS (z, 1) hz) :=
  Subtype.ext (Subtype.ext ((pX_map (D.ρ q).toLinearIsometry (D.ρ_e q) _).trans
    (congrArg (D.ρ q) (pX_reflE D.e_norm _))))

theorem gS_ρU_RU (q : S3) (z : UN e) (hz) (h') :
    D.gS (D.ρU q (D.RU z hz)) h' = q * D.gS z hz * q⁻¹ := by
  rw [gS, D.xS_ρU_RU, D.θ_ρV]; rfl

theorem ζU_ρU_RU (q : S3) (z : UN e) (hz) :
    ζU (D.ρU q (D.RU z hz)) = D.ρ q (reflE e (ζU z)) := rfl

theorem RU_ρU_RU (q : S3) (z : UN e) (hz) (h') :
    ζU (D.RU (D.ρU q (D.RU z hz)) h') = D.ρ q (ζU z) := by
  show reflE e (D.ρ q (reflE e (ζU z))) = D.ρ q (ζU z)
  rw [show D.ρ q (reflE e (ζU z)) = (D.ρ q).toLinearIsometry (reflE e (ζU z)) from rfl,
    ← reflE_map _ (D.ρ_e q), reflE_reflE D.e_norm]; rfl

theorem ΦS_aux₁ (z : UN e) (hz) (z' : UN e) (hz')
    (h : z' = D.ρU (D.gS z hz)⁻¹ (D.RU z hz)) :
    D.ρ (D.gS z' hz') (ζU (D.RU z' hz')) = ζU z := by
  subst h
  rw [D.RU_ρU_RU, D.gS_ρU_RU, D.ρ_mul_apply]
  simp

theorem ΦS_aux₂ (z : UN e) (hz) (z' : UN e) (hz')
    (h : z' = D.ρU (D.gS z hz) (D.RU z hz)) :
    D.ρ (D.gS z' hz')⁻¹ (ζU (D.RU z' hz')) = ζU z := by
  subst h
  rw [D.RU_ρU_RU, D.gS_ρU_RU, D.ρ_mul_apply]
  simp

/-- `κ_Σ` as a self-equivalence of the overlap. -/
def ΦSe : OS e ≃ OS e where
  toFun := D.ΦS
  invFun := D.ΦS'
  left_inv z := Subtype.ext (Subtype.ext (Subtype.ext
    (D.ΦS_aux₁ (z : UN e) (mem_OS z) (D.ΦS z : UN e) (mem_OS _) rfl)))
  right_inv z := Subtype.ext (Subtype.ext (Subtype.ext
    (D.ΦS_aux₂ (z : UN e) (mem_OS z) (D.ΦS' z : UN e) (mem_OS _) rfl)))

theorem contMDiff_ζOS : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, W) ∞ fun z : OS e => ζU (z : UN e) :=
  contMDiff_coe_sphere.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)

theorem contMDiff_gOS : ContMDiff (𝓡 (m + 1)) (𝓡 3) ∞ fun z : OS e => D.gS z (mem_OS z) := by
  refine D.θ_smooth.comp (contMDiff_sphere_of_coe ?_)
  have h : (fun z : OS e => ((D.xS ((z : UN e), (1 : S3)) (mem_OS z) :
      sphere (0 : Vs e) 1) : Vs e)) =
      fun z : OS e => (Vs e).orthogonalProjectionOnto (pX e (ζU (z : UN e))) :=
    funext fun z => (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _).symm
  rw [h]
  intro z
  exact ((Vs e).orthogonalProjectionOnto.contDiff.contDiffAt.comp _
    (contDiffAt_pX e (D.sq_lt (mem_OS z)))).comp_contMDiffAt
    (f := fun z : OS e => ζU (z : UN e)) ((contMDiff_ζOS (e := e) (m := m)) z)

theorem contMDiff_ΦS : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞
    fun z : OS e => ((D.ΦS z : OS e) : UN e) := by
  refine (ContMDiff.subtypeVal_comp_iff (UN e) _).1 (contMDiff_sphere_of_coe ?_)
  exact (D.ρ_smooth.comp (contMDiff_invS3.comp D.contMDiff_gOS)).clm_apply
    ((contDiff_reflE e).contMDiff.comp (contMDiff_ζOS (e := e) (m := m)))

theorem contMDiff_ΦS' : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞
    fun z : OS e => ((D.ΦS' z : OS e) : UN e) := by
  refine (ContMDiff.subtypeVal_comp_iff (UN e) _).1 (contMDiff_sphere_of_coe ?_)
  exact (D.ρ_smooth.comp D.contMDiff_gOS).clm_apply
    ((contDiff_reflE e).contMDiff.comp (contMDiff_ζOS (e := e) (m := m)))

/-- `κ_Σ` as a homeomorphism of the overlap. -/
def ΦSh : OS e ≃ₜ OS e where
  toEquiv := D.ΦSe
  continuous_toFun := D.contMDiff_ΦS.continuous.subtype_mk _
  continuous_invFun := D.contMDiff_ΦS'.continuous.subtype_mk _

/-- **The transition of the quotient**: `z ↦ ρ(θ(x z))⁻¹ R z` on `U_N ∖ {o_N}`. -/
def κS : OpenPartialHomeomorph (UN e) (UN e) := opensPH (OS e) D.ΦSh

theorem κS_eq (z : UN e) (hz : ζ0 (z, (1 : S3)) ≠ e) :
    D.κS z = D.ρU (D.gS z hz)⁻¹ (D.RU z hz) :=
  opensPH_apply _ _ ⟨z, hz⟩

theorem hκS : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ D.κS D.κS.source :=
  contMDiffOn_opensPH (𝓡 (m + 1)) _ _ D.contMDiff_ΦS

theorem hκSs : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ D.κS.symm D.κS.target :=
  contMDiffOn_opensPH_symm (𝓡 (m + 1)) _ _ D.contMDiff_ΦS'

end PolarData

/-- **The star quotient** `P_θ/S³_⋆`, as a glued manifold. -/
abbrev QuotSpace (D : PolarData (m := m) e) := Glued D.κS

instance chartedSpace_quotSpace (D : PolarData (m := m) e) :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (QuotSpace D) :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  chartedSpaceGlued D.κS

/-- **`P_θ/S³_⋆` is a `C^∞` manifold of dimension `n`.** -/
instance isManifold_quotSpace (D : PolarData (m := m) e) :
    IsManifold (𝓡 (m + 1)) ∞ (QuotSpace D) :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  isManifold_glued (𝓡 (m + 1)) D.hκS D.hκSs

namespace PolarData

variable (D : PolarData (m := m) e)

/-- `Ψ(ζ, u) = ρ(u)⁻¹ ζ`. -/
def Ψ (a : M0 e) : UN e := D.ρU a.2⁻¹ a.1

theorem Ψ_mem {a : M0 e} (ha : ζ0 a ≠ e) : ζ0 (D.Ψ a, (1 : S3)) ≠ e := D.ρ_ne_e _ ha

/-- **`Ψ` intertwines the two transitions**: `κ_Σ ∘ Ψ = Ψ ∘ κ` on the overlap. -/
theorem κS_Ψ (a : M0 e) (ha : ζ0 a ≠ e) : D.κS (D.Ψ a) = D.Ψ (D.κP a) := by
  rw [D.κS_eq _ (D.Ψ_mem ha), D.κP_eq a ha]
  have hx : D.xS (D.Ψ a, 1) (D.Ψ_mem ha) = D.ρV a.2⁻¹ (D.xS a ha) :=
    Subtype.ext (Subtype.ext (pX_map (D.ρ a.2⁻¹).toLinearIsometry (D.ρ_e _) _))
  have hg : D.gS (D.Ψ a) (D.Ψ_mem ha) = a.2⁻¹ * D.θ (D.xS a ha) * a.2 := by
    rw [gS, hx, D.θ_ρV, inv_inv]
  apply Subtype.ext; apply Subtype.ext
  show D.ρ (D.gS (D.Ψ a) _)⁻¹ (reflE e (D.ρ a.2⁻¹ (ζ0 a))) =
    D.ρ (D.θ (D.xS a ha) * a.2)⁻¹ (reflE e (ζ0 a))
  rw [hg, show D.ρ a.2⁻¹ (ζ0 a) = (D.ρ a.2⁻¹).toLinearIsometry (ζ0 a) from rfl,
    reflE_map _ (D.ρ_e _)]
  show D.ρ (a.2⁻¹ * D.θ (D.xS a ha) * a.2)⁻¹ (D.ρ a.2⁻¹ (reflE e (ζ0 a))) = _
  rw [D.ρ_mul_apply]
  congr 2
  group

/-- **The orbit map** `P_θ → P_θ/S³_⋆`, induced by `Ψ`. -/
def orbitMap : PolarBundle D → QuotSpace D :=
  glueLift (fun a => ι₁ D.κS (D.Ψ a)) (fun b => ι₂ D.κS (D.Ψ b)) fun a ha => by
    show ι₂ D.κS (D.Ψ (D.κP a)) = ι₁ D.κS (D.Ψ a)
    rw [← D.κS_Ψ a ha, ι₂_apply (show D.Ψ a ∈ D.κS.source from D.Ψ_mem ha)]

@[simp] theorem orbitMap_ι₁ (a : M0 e) : D.orbitMap (ι₁ D.κP a) = ι₁ D.κS (D.Ψ a) := rfl
@[simp] theorem orbitMap_ι₂ (b : M0 e) : D.orbitMap (ι₂ D.κP b) = ι₂ D.κS (D.Ψ b) := rfl

theorem Ψ_one (z : UN e) : D.Ψ (z, 1) = z := by
  apply Subtype.ext; apply Subtype.ext
  show D.ρ (1 : S3)⁻¹ (ζU z) = ζU z
  rw [inv_one, map_one]; rfl

theorem Ψ_starM (q : S3) (a : M0 e) : D.Ψ (D.starM q a) = D.Ψ a := by
  apply Subtype.ext; apply Subtype.ext
  show D.ρ (q * a.2)⁻¹ (D.ρ q (ζ0 a)) = D.ρ a.2⁻¹ (ζ0 a)
  rw [D.ρ_mul_apply]; congr 2; group

/-- **`Ψ` is constant on star orbits.** -/
theorem orbitMap_star (q : S3) (p : PolarBundle D) : D.orbitMap (q • p) = D.orbitMap p := by
  induction p using glued_induction with
  | h₁ a => exact congrArg (ι₁ D.κS) (D.Ψ_starM q a)
  | h₂ b => exact congrArg (ι₂ D.κS) (D.Ψ_starM q b)

/-- The slice `{u = 1}`: `z ↦ [(z, 1)]` is a section over the first chart. -/
theorem orbitMap_section₁ (z : UN e) : D.orbitMap (ι₁ D.κP (z, 1)) = ι₁ D.κS z :=
  congrArg (ι₁ D.κS) (D.Ψ_one z)

theorem orbitMap_section₂ (z : UN e) : D.orbitMap (ι₂ D.κP (z, 1)) = ι₂ D.κS z :=
  congrArg (ι₂ D.κS) (D.Ψ_one z)

theorem orbitMap_surjective : Surjective D.orbitMap := by
  intro x
  induction x using glued_induction with
  | h₁ z => exact ⟨_, D.orbitMap_section₁ z⟩
  | h₂ z => exact ⟨_, D.orbitMap_section₂ z⟩

/-- `⟪·, e⟫` on the quotient (the height function). -/
def height : QuotSpace D → ℝ :=
  glueLift (fun z => ⟪ζU z, e⟫) (fun z => -⟪ζU z, e⟫) fun z hz => by
    rw [D.κS_eq z hz]
    show -⟪D.ρ _ (reflE e (ζU z)), e⟫ = _
    rw [D.inner_ρ_e, inner_reflE D.e_norm, neg_neg]

theorem height_orbitMap (p : PolarBundle D) : D.height (D.orbitMap p) = ⟪(D.proj p : W), e⟫ := by
  induction p using glued_induction with
  | h₁ a => exact D.inner_ρ_e _ _
  | h₂ b =>
    show -⟪D.ρ _ (ζ0 b), e⟫ = ⟪reflE e (ζ0 b), e⟫
    rw [D.inner_ρ_e, inner_reflE D.e_norm]

theorem Ψ_eq_starM {a a' : M0 e} (h : D.Ψ a = D.Ψ a') : a' = D.starM (a'.2 * a.2⁻¹) a := by
  have hw : D.ρ a.2⁻¹ (ζ0 a) = D.ρ a'.2⁻¹ (ζ0 a') := congrArg (fun z : UN e => ζU z) h
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (by show a'.2 = a'.2 * a.2⁻¹ * a.2; group)
  show ζ0 a' = D.ρ (a'.2 * a.2⁻¹) (ζ0 a)
  rw [← D.ρ_mul_apply, hw, D.ρ_mul_apply, mul_inv_cancel, map_one]; rfl

/-- **The fibres of the orbit map are exactly the star orbits.** -/
theorem orbitMap_eq_iff (p p' : PolarBundle D) :
    D.orbitMap p = D.orbitMap p' ↔ ∃ q : S3, p' = q • p := by
  constructor
  · intro h
    have hh : ⟪(D.proj p : W), e⟫ = ⟪(D.proj p' : W), e⟫ := by
      rw [← D.height_orbitMap, ← D.height_orbitMap, h]
    by_cases hN : (D.proj p : W) = -e
    · have hS : (D.proj p : W) ≠ e := by rw [hN]; exact (ne_neg_self_e D.e_norm).symm
      have hS' : (D.proj p' : W) ≠ e := by
        intro h'
        rw [h', hN, inner_neg_left, real_inner_self_eq_norm_sq, D.e_norm] at hh
        norm_num at hh
      obtain ⟨b, rfl⟩ := D.mem_range_ι₂ p hS
      obtain ⟨b', rfl⟩ := D.mem_range_ι₂ p' hS'
      exact ⟨_, congrArg (ι₂ D.κP) (D.Ψ_eq_starM (ι₂_injective D.κS h))⟩
    · have hN' : (D.proj p' : W) ≠ -e := by
        intro h'
        apply hN
        have h1 : ⟪(D.proj p : W), e⟫ = -1 := by
          rw [hh, h', inner_neg_left, real_inner_self_eq_norm_sq, D.e_norm]; norm_num
        by_contra hne
        exact inner_ne_neg_one D.e_norm (by simp) hne h1
      obtain ⟨a, rfl⟩ := D.mem_range_ι₁ p hN
      obtain ⟨a', rfl⟩ := D.mem_range_ι₁ p' hN'
      exact ⟨_, congrArg (ι₁ D.κP) (D.Ψ_eq_starM (ι₁_injective D.κS h))⟩
  · rintro ⟨q, rfl⟩
    exact (D.orbitMap_star q p).symm

/-! ### Smoothness and the universal property -/

theorem contMDiff_Ψ : ContMDiff (IP m) (𝓡 (m + 1)) ∞ D.Ψ := by
  refine (ContMDiff.subtypeVal_comp_iff (UN e) _).1 (contMDiff_sphere_of_coe ?_)
  exact (D.ρ_smooth.comp (contMDiff_invS3.comp contMDiff_snd)).clm_apply contMDiff_ζ0

/-- **The orbit map is smooth.** -/
theorem contMDiff_orbitMap : ContMDiff (IP m) (𝓡 (m + 1)) ∞ D.orbitMap := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  haveI := nonempty_M0 (e := e)
  exact contMDiff_glueLift (IP m) D.hκP D.hκPs _
    ((contMDiff_ι₁ (𝓡 (m + 1)) D.hκS D.hκSs).comp D.contMDiff_Ψ)
    ((contMDiff_ι₂ (𝓡 (m + 1)) D.hκS D.hκSs).comp D.contMDiff_Ψ)

theorem contMDiff_slice : ContMDiff (𝓡 (m + 1)) (IP m) ∞ fun z : UN e => ((z, 1) : M0 e) :=
  contMDiff_id.prodMk contMDiff_const

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N]

/-- **Universal property of the quotient manifold**: `f : P_θ/S³_⋆ → N` is smooth iff
`f ∘ orbitMap` is. -/
theorem contMDiff_iff_comp_orbitMap (f : QuotSpace D → N) :
    ContMDiff (𝓡 (m + 1)) I' ∞ f ↔ ContMDiff (IP m) I' ∞ (f ∘ D.orbitMap) := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  haveI := nonempty_M0 (e := e)
  constructor
  · intro hf; exact hf.comp D.contMDiff_orbitMap
  · intro hf
    refine contMDiff_of_comp_ι (𝓡 (m + 1)) D.hκS D.hκSs ?_ ?_
    · have := (hf.comp (contMDiff_ι₁ (IP m) D.hκP D.hκPs)).comp contMDiff_slice
      refine this.congr fun z => ?_
      simp only [comp_apply, D.orbitMap_section₁]
    · have := (hf.comp (contMDiff_ι₂ (IP m) D.hκP D.hκPs)).comp contMDiff_slice
      refine this.congr fun z => ?_
      simp only [comp_apply, D.orbitMap_section₂]

end PolarData

end Quotient

end

end ExoticSpheres8And10
