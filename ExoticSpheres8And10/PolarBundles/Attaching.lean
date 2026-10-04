/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.PolarBundles.StarQuotient

/-! # §2: `lem:attaching` for general polar data

[GG] `lem:attaching`. For any polar data `D` (any `n ≥ 1`, any smooth orthogonal `ρ`
fixing `e`, any smooth `θ` with `eq:equiv`):

* `t2_polarBundle`, `t2_quotSpace`: `P_θ` and `P_θ/S³_⋆` are Hausdorff.
* `orbitSpaceHomeo`: the topological orbit space `P_θ/S³_⋆` (quotient topology) is homeomorphic
  to the manifold `QuotSpace D`, via the map induced by `Ψ`.
* (2) `sigmaDiffeoV`: `σ(y) = ρ(θ(y))⁻¹y` is a `C^∞` diffeomorphism of `S(V)` with inverse
  `σ̂(y) = ρ(θ(y))y`.
  `markings`: the boundary markings satisfy `y_S = σ(y_N)`.
  `polarT_κS`, `polarX_κS`: in polar coordinates the transition of the quotient is
  `(t, y) ↦ (π − t, σ(y))`. It is independent of `t` in the angular part and reflects the radial
  coordinate, so on a collar of `t = a` it is constant in the collar direction with angular
  part `σ` ([GG]'s proof of (3)).
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Attaching

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

local notation "Sn" => sphere (0 : W) 1

local notation "SV" => sphere (0 : Vs e) 1

namespace PolarData

variable (D : PolarData (m := m) e)

theorem norm_ζU (z : UN e) : ‖ζU z‖ = 1 := mem_sphere_zero_iff_norm.1 (z : Sn).2

/-! ## Hausdorffness -/

theorem continuous_height : Continuous D.height :=
  continuous_glueLift _
    ((continuous_subtype_val.comp continuous_subtype_val).inner continuous_const)
    ((continuous_subtype_val.comp continuous_subtype_val).inner continuous_const).neg

/-- **`P_θ` is Hausdorff.** -/
instance t2_polarBundle : T2Space (PolarBundle D) :=
  t2Space_glued D.proj D.contMDiff_proj.continuous fun a ha b hb => by
    have ha' : ζ0 a = e := not_not.1 ha
    have hb' : ζ0 b = e := not_not.1 hb
    intro h
    have h1 : (D.proj (ι₁ D.κP a) : W) = (D.proj (ι₂ D.κP b) : W) := congrArg Subtype.val h
    rw [proj_ι₁, proj_ι₂, ha', hb', reflE_e D.e_norm] at h1
    exact ne_neg_self_e D.e_norm h1

/-- **`P_θ/S³_⋆` is Hausdorff.** -/
instance t2_quotSpace : T2Space (QuotSpace D) :=
  t2Space_glued D.height D.continuous_height fun a ha b hb => by
    have ha' : ζU a = e := not_not.1 ha
    have hb' : ζU b = e := not_not.1 hb
    show ⟪ζU a, e⟫ ≠ -⟪ζU b, e⟫
    rw [ha', hb', real_inner_self_eq_norm_sq, D.e_norm]
    norm_num

/-! ## The topological orbit space -/

/-- The orbit space `P_θ/S³_⋆` with the quotient topology. -/
abbrev OrbitSpace := MulAction.orbitRel.Quotient S3 (PolarBundle D)

/-- The map `P_θ/S³_⋆ → QuotSpace D` induced by `Ψ`. -/
def orbitSpaceToQuot : D.OrbitSpace → QuotSpace D :=
  Quotient.lift D.orbitMap fun p p' h => by
    obtain ⟨q, rfl⟩ := h
    exact D.orbitMap_star q p'

theorem orbit_of_orbitMap {p p' : PolarBundle D} (h : D.orbitMap p = D.orbitMap p') :
    Quotient.mk (MulAction.orbitRel S3 (PolarBundle D)) p' =
      Quotient.mk (MulAction.orbitRel S3 (PolarBundle D)) p := by
  obtain ⟨q, hq⟩ := (D.orbitMap_eq_iff p p').1 h
  exact Quotient.sound ⟨q, hq.symm⟩

/-- The inverse, through the slices `{u = 1}`. -/
def quotToOrbitSpace : QuotSpace D → D.OrbitSpace :=
  glueLift (fun z => Quotient.mk _ (ι₁ D.κP (z, 1))) (fun z => Quotient.mk _ (ι₂ D.κP (z, 1)))
    fun z hz => D.orbit_of_orbitMap (by
      rw [D.orbitMap_section₁, D.orbitMap_section₂, ι₂_apply hz])

theorem quotToOrbitSpace_spec (y : QuotSpace D) :
    ∃ p, D.quotToOrbitSpace y = Quotient.mk _ p ∧ D.orbitMap p = y := by
  induction y using glued_induction with
  | h₁ z => exact ⟨_, rfl, D.orbitMap_section₁ z⟩
  | h₂ z => exact ⟨_, rfl, D.orbitMap_section₂ z⟩

/-- **The topological orbit space is the quotient manifold**: `P_θ/S³_⋆ ≃ₜ QuotSpace D`. -/
def orbitSpaceHomeo : D.OrbitSpace ≃ₜ QuotSpace D where
  toFun := D.orbitSpaceToQuot
  invFun := D.quotToOrbitSpace
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h p =>
      obtain ⟨p', h1, h2⟩ := D.quotToOrbitSpace_spec (D.orbitMap p)
      rw [show D.orbitSpaceToQuot (Quotient.mk _ p) = D.orbitMap p from rfl, h1]
      exact (D.orbit_of_orbitMap h2).symm
  right_inv y := by
    obtain ⟨p, h1, h2⟩ := D.quotToOrbitSpace_spec y
    rw [h1]; exact h2
  continuous_toFun := D.contMDiff_orbitMap.continuous.quotient_lift _
  continuous_invFun := by
    refine continuous_glueLift _ ?_ ?_
    · exact continuous_quotient_mk'.comp ((continuous_ι₁ D.κP).comp
        (continuous_id.prodMk continuous_const))
    · exact continuous_quotient_mk'.comp ((continuous_ι₂ D.κP).comp
        (continuous_id.prodMk continuous_const))

theorem orbitSpaceHomeo_mk (p : PolarBundle D) :
    D.orbitSpaceHomeo (Quotient.mk _ p) = D.orbitMap p := rfl

/-! ## (2): the attaching map `σ` -/

/-- `σ(y) = ρ(θ(y))⁻¹ y` ([GG] `eq:sigma`). -/
def sigmaV (y : SV) : SV := D.ρV (D.θ y)⁻¹ y

/-- `σ̂(y) = ρ(θ(y)) y`. -/
def sigmaHatV (y : SV) : SV := D.ρV (D.θ y) y

theorem θ_sigmaV (y : SV) : D.θ (D.sigmaV y) = D.θ y := by
  rw [sigmaV, D.θ_ρV]; group

theorem θ_sigmaHatV (y : SV) : D.θ (D.sigmaHatV y) = D.θ y := by
  rw [sigmaHatV, D.θ_ρV]; group

theorem sigmaHatV_sigmaV (y : SV) : D.sigmaHatV (D.sigmaV y) = y := by
  apply Subtype.ext; apply Subtype.ext
  show D.ρ (D.θ (D.sigmaV y)) (D.ρ (D.θ y)⁻¹ ((y : Vs e) : W)) = ((y : Vs e) : W)
  rw [D.θ_sigmaV, D.ρ_mul_apply, mul_inv_cancel, map_one]; rfl

theorem sigmaV_sigmaHatV (y : SV) : D.sigmaV (D.sigmaHatV y) = y := by
  apply Subtype.ext; apply Subtype.ext
  show D.ρ (D.θ (D.sigmaHatV y))⁻¹ (D.ρ (D.θ y) ((y : Vs e) : W)) = ((y : Vs e) : W)
  rw [D.θ_sigmaHatV, D.ρ_mul_apply, inv_mul_cancel, map_one]; rfl

theorem contMDiff_coeSV : ContMDiff (𝓡 m) 𝓘(ℝ, W) ∞ fun y : SV => ((y : Vs e) : W) :=
  (Vs e).subtypeL.contDiff.contMDiff.comp contMDiff_coe_sphere

theorem contMDiff_sigma_gen (g : SV → S3) (hg : ContMDiff (𝓡 m) (𝓡 3) ∞ g) :
    ContMDiff (𝓡 m) (𝓡 m) ∞ fun y : SV => D.ρV (g y) y := by
  apply contMDiff_sphere_of_coe
  have h : (fun y : SV => ((D.ρV (g y) y : SV) : Vs e)) =
      fun y => (Vs e).orthogonalProjectionOnto (D.ρ (g y) ((y : Vs e) : W)) :=
    funext fun y => (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _).symm
  rw [h]
  exact (Vs e).orthogonalProjectionOnto.contDiff.contMDiff.comp
    ((D.ρ_smooth.comp hg).clm_apply (contMDiff_coeSV (e := e) (m := m)))

/-- **[GG] `lem:attaching` (2): `σ` is a diffeomorphism of `S(V)` with inverse `σ̂`**, for
general polar data (in particular for `ρ₁₀` as well as `ρ₈`). -/
def sigmaDiffeoV : Diffeomorph (𝓡 m) (𝓡 m) SV SV ∞ where
  toFun := D.sigmaV
  invFun := D.sigmaHatV
  left_inv := D.sigmaHatV_sigmaV
  right_inv := D.sigmaV_sigmaHatV
  contMDiff_toFun := D.contMDiff_sigma_gen _ (contMDiff_invS3.comp D.θ_smooth)
  contMDiff_invFun := D.contMDiff_sigma_gen _ D.θ_smooth

/-! ### The transition in polar coordinates, and the boundary markings -/

theorem xS_κS (z : UN e) (hz : ζ0 (z, (1 : S3)) ≠ e) (h') :
    D.xS (D.κS z, 1) h' = D.sigmaV (D.xS (z, 1) hz) := by
  have h1 : D.κS z = D.ρU (D.gS z hz)⁻¹ (D.RU z hz) := D.κS_eq z hz
  have key : ∀ (w : UN e) (hw : w = D.ρU (D.gS z hz)⁻¹ (D.RU z hz)) (hw' : ζ0 (w, (1 : S3)) ≠ e),
      D.xS (w, 1) hw' = D.sigmaV (D.xS (z, 1) hz) := by
    intro w hw hw'
    subst hw
    rw [D.xS_ρU_RU]; rfl
  exact key _ h1 h'

/-- **The boundary markings** ([GG] `lem:attaching` (2)): if `p = [(ζ, u_N)]_N = [(Rζ, u_S)]_S`,
then `y_S = σ(y_N)` for `y_α = ρ(u_α)⁻¹ x`. -/
theorem markings (a : M0 e) (ha : ζ0 a ≠ e) :
    D.xS (D.Ψ (D.κP a), 1) (by rw [← D.κS_Ψ a ha]; exact (D.κS.map_source (D.Ψ_mem ha) : _)) =
      D.sigmaV (D.xS (D.Ψ a, 1) (D.Ψ_mem ha)) := by
  have := D.xS_κS (D.Ψ a) (D.Ψ_mem ha) (by rw [D.κS_Ψ a ha]; exact
    (by rw [← D.κS_Ψ a ha]; exact (D.κS.map_source (D.Ψ_mem ha) : _)))
  rw [← this]
  congr 1
  exact Prod.ext (D.κS_Ψ a ha).symm rfl

/-- In polar coordinates the transition of the quotient reflects the radial coordinate. -/
theorem polarT_κS (z : UN e) (hz : ζ0 (z, (1 : S3)) ≠ e) :
    polarT e (ζU (D.κS z)) = π - polarT e (ζU z) := by
  rw [D.κS_eq z hz]
  show polarT e (D.ρ _ (reflE e (ζU z))) = _
  rw [show D.ρ (D.gS z hz)⁻¹ (reflE e (ζU z)) =
      (D.ρ (D.gS z hz)⁻¹).toLinearIsometry (reflE e (ζU z)) from rfl,
    polarT_map _ (D.ρ_e _), polarT, inner_reflE D.e_norm, arccos_neg]
  rfl

/-- **The angular part of the transition is `σ`**: `x(κ_Σ z) = σ(x(z))`, independently of `t`. -/
theorem polarX_κS (z : UN e) (hz : ζ0 (z, (1 : S3)) ≠ e) :
    polarX e (ζU (D.κS z)) = ((D.sigmaV (D.xS (z, 1) hz) : Vs e) : W) := by
  rw [← D.xS_κS z hz (D.κS.map_source hz), ← pX_eq_polarX D.e_norm (norm_ζU _)]
  rfl


/-! ## (1): the quotient disks -/

omit [Fact (finrank ℝ ↥(Vs e) = m + 1)] [Fact (finrank ℝ W = m + 1 + 1)] in
theorem Disk_inner {a : ℝ} (Y : Disk e a) : ⟪(Y : W), e⟫ = 0 := Y.2.1

omit [Fact (finrank ℝ ↥(Vs e) = m + 1)] [Fact (finrank ℝ W = m + 1 + 1)] in
theorem Disk_norm {a : ℝ} (Y : Disk e a) : ‖(Y : W)‖ ≤ a := Y.2.2

include D in
theorem polarT_reflE (ζ : W) : polarT e (reflE e ζ) = π - polarT e ζ := by
  rw [polarT, polarT, inner_reflE D.e_norm, arccos_neg]

theorem polarT_ρ (q : S3) (w : W) : polarT e (D.ρ q w) = polarT e w :=
  polarT_map (D.ρ q).toLinearIsometry (D.ρ_e q) w

theorem polarT_Ψ (a : M0 e) : polarT e (ζU (D.Ψ a)) = polarT e (ζ0 a) := D.polarT_ρ _ _

/-- A disk vector `Y ∈ V`, `‖Y‖ < π`, as the point `cos‖Y‖ e + sin‖Y‖ Y/‖Y‖` of `U_N`. -/
def diskPt (Y : W) (hY : ⟪Y, e⟫ = 0) (hYπ : ‖Y‖ < π) : UN e :=
  ⟨⟨expN e Y, by rw [mem_sphere_zero_iff_norm]; exact norm_expN D.e_norm hY⟩, by
    show expN e Y ≠ -e
    intro h
    have := polarT_expN D.e_norm hY hYπ
    rw [h, polarT_neg_e D.e_norm] at this; linarith⟩

theorem ζU_diskPt (Y : W) (hY hYπ) : ζU (D.diskPt Y hY hYπ) = expN e Y := rfl

theorem polarT_diskPt (Y : W) (hY hYπ) : polarT e (ζU (D.diskPt Y hY hYπ)) = ‖Y‖ :=
  polarT_expN D.e_norm hY hYπ

theorem diskPt_diskN (z : UN e) (h : ⟪diskN e (ζU z), e⟫ = 0) (h' : ‖diskN e (ζU z)‖ < π) :
    D.diskPt (diskN e (ζU z)) h h' = z :=
  Subtype.ext (Subtype.ext (expN_diskN D.e_norm (norm_ζU _) z.2))

include D in
theorem norm_diskN_ζU (z : UN e) : ‖diskN e (ζU z)‖ = polarT e (ζU z) :=
  norm_diskN D.e_norm (norm_ζU _) z.2

include D in
theorem polarT_lt_pi (z : UN e) : polarT e (ζU z) < π := by
  have hle : polarT e (ζU z) ≤ π := arccos_le_pi _
  refine lt_of_le_of_ne hle fun h => z.2 ?_
  have h1 : ⟪ζU z, e⟫ = -1 := by
    have := congrArg cos h
    rwa [cos_pi, cos_polarT D.e_norm (norm_ζU _)] at this
  by_contra hne
  exact inner_ne_neg_one D.e_norm (norm_ζU _) hne h1

theorem diskPt_injective {Y Y' : W} (hY hYπ hY' hYπ')
    (h : D.diskPt Y hY hYπ = D.diskPt Y' hY' hYπ') : Y = Y' := by
  have h1 : expN e Y = expN e Y' := congrArg (fun z : UN e => ζU z) h
  rw [← diskN_expN D.e_norm hY hYπ, h1, diskN_expN D.e_norm hY' hYπ']

/-- `D_N`: the image of `P_N = π_θ⁻¹{t ≤ a}` in the quotient. -/
def DN (a : ℝ) : Set (QuotSpace D) := D.orbitMap '' (D.proj ⁻¹' {ζ | polarT e ζ ≤ a})

/-- `D_S`: the image of `P_S = π_θ⁻¹{t ≥ a}` in the quotient. -/
def DS (a : ℝ) : Set (QuotSpace D) := D.orbitMap '' (D.proj ⁻¹' {ζ | a ≤ polarT e ζ})

/-- The disk map of the northern disk: `Y ↦ [(cos‖Y‖ e + sin‖Y‖ Y/‖Y‖, 1)]`. -/
def diskMapN {a : ℝ} (haπ : a < π) (Y : Disk e a) : QuotSpace D :=
  ι₁ D.κS (D.diskPt Y (Disk_inner Y) (lt_of_le_of_lt (Disk_norm Y) haπ))

/-- The disk map of the southern disk, in the coordinates `ζ_S = (π − t)x`. -/
def diskMapS {a : ℝ} (ha0 : 0 < a) (Y : Disk e (π - a)) : QuotSpace D :=
  ι₂ D.κS (D.diskPt Y (Disk_inner Y) (by linarith [(Disk_norm Y)]))

theorem DN_eq {a : ℝ} (haπ : a < π) : D.DN a = range (D.diskMapN haπ) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hN : (D.proj p : W) ≠ -e := by
      intro h; simp only [mem_preimage, mem_setOf_eq, h, polarT_neg_e D.e_norm] at hp; linarith
    obtain ⟨b, rfl⟩ := D.mem_range_ι₁ p hN
    have hb : polarT e (ζU (D.Ψ b)) ≤ a := by rw [D.polarT_Ψ]; exact hp
    refine ⟨⟨diskN e (ζU (D.Ψ b)), inner_diskN D.e_norm (norm_ζU _),
      by rw [norm_diskN_ζU D]; exact hb⟩, ?_⟩
    exact congrArg (ι₁ D.κS) (D.diskPt_diskN _ _ _)
  · rintro ⟨Y, rfl⟩
    refine ⟨ι₁ D.κP (D.diskPt Y (Disk_inner Y) (lt_of_le_of_lt (Disk_norm Y) haπ), 1), ?_, D.orbitMap_section₁ _⟩
    show polarT e (ζU (D.diskPt Y (Disk_inner Y) (lt_of_le_of_lt (Disk_norm Y) haπ))) ≤ a
    rw [D.polarT_diskPt]; exact (Disk_norm Y)

theorem DS_eq {a : ℝ} (ha0 : 0 < a) : D.DS a = range (D.diskMapS ha0) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hS : (D.proj p : W) ≠ e := by
      intro h; simp only [mem_preimage, mem_setOf_eq, h, polarT_e D.e_norm] at hp; linarith
    obtain ⟨b, rfl⟩ := D.mem_range_ι₂ p hS
    have hb : polarT e (ζU (D.Ψ b)) ≤ π - a := by
      rw [D.polarT_Ψ]
      have : a ≤ polarT e (reflE e (ζ0 b)) := hp
      rw [polarT_reflE D] at this; linarith
    refine ⟨⟨diskN e (ζU (D.Ψ b)), inner_diskN D.e_norm (norm_ζU _),
      by rw [norm_diskN_ζU D]; exact hb⟩, ?_⟩
    exact congrArg (ι₂ D.κS) (D.diskPt_diskN _ _ _)
  · rintro ⟨Y, rfl⟩
    refine ⟨ι₂ D.κP (D.diskPt Y (Disk_inner Y) (by linarith [(Disk_norm Y)]), 1), ?_, D.orbitMap_section₂ _⟩
    show a ≤ polarT e (reflE e (ζU (D.diskPt Y (Disk_inner Y) (by linarith [(Disk_norm Y)]))))
    rw [polarT_reflE D, D.polarT_diskPt]; linarith [(Disk_norm Y)]

theorem continuous_diskPt_comp {a : ℝ} (haπ : a < π) :
    Continuous fun Y : Disk e a => D.diskPt Y (Disk_inner Y) (lt_of_le_of_lt (Disk_norm Y) haπ) := by
  apply continuous_induced_rng.2; apply continuous_induced_rng.2
  exact continuous_expN.comp continuous_subtype_val

theorem diskMapN_injective {a : ℝ} (haπ : a < π) : Injective (D.diskMapN haπ) :=
  fun Y Y' h => Subtype.ext (D.diskPt_injective _ _ _ _ (ι₁_injective D.κS h))

theorem diskMapS_injective {a : ℝ} (ha0 : 0 < a) : Injective (D.diskMapS ha0) :=
  fun Y Y' h => Subtype.ext (D.diskPt_injective _ _ _ _ (ι₂_injective D.κS h))

/-- **[GG] `lem:attaching` (1), northern disk**: `D_N = P_N/S³_⋆` is homeomorphic to the closed
disk of radius `a` in `V` (via `ζ_N = t x`, i.e. `Ψ_N` followed by geodesic polar coordinates). -/
def DNHomeo {a : ℝ} (haπ : a < π) : Disk e a ≃ₜ D.DN a := by
  haveI : FiniteDimensional ℝ W := FiniteDimensional.of_fact_finrank_eq_succ (m + 1)
  haveI : CompactSpace (Disk e a) := isCompact_iff_compactSpace.1 (isCompact_Disk a)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun Y => ⟨D.diskMapN haπ Y, by rw [D.DN_eq haπ]; exact ⟨Y, rfl⟩⟩)
      ⟨fun Y Y' h => D.diskMapN_injective haπ (congrArg Subtype.val h), fun x => by
        obtain ⟨Y, hY⟩ := (Set.ext_iff.1 (D.DN_eq haπ) (x : QuotSpace D)).1 x.2
        exact ⟨Y, Subtype.ext hY⟩⟩)
    (((continuous_ι₁ D.κS).comp (D.continuous_diskPt_comp haπ)).subtype_mk
      fun Y => (Set.ext_iff.1 (D.DN_eq haπ) _).2 ⟨Y, rfl⟩)

/-- **[GG] `lem:attaching` (1), southern disk**: `D_S` is homeomorphic to the closed disk of radius
`π − a` in `V` (via `ζ_S = (π − t)x`). -/
def DSHomeo {a : ℝ} (ha0 : 0 < a) : Disk e (π - a) ≃ₜ D.DS a := by
  haveI : FiniteDimensional ℝ W := FiniteDimensional.of_fact_finrank_eq_succ (m + 1)
  haveI : CompactSpace (Disk e (π - a)) := isCompact_iff_compactSpace.1 (isCompact_Disk _)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun Y => ⟨D.diskMapS ha0 Y, by rw [D.DS_eq ha0]; exact ⟨Y, rfl⟩⟩)
      ⟨fun Y Y' h => D.diskMapS_injective ha0 (congrArg Subtype.val h), fun x => by
        obtain ⟨Y, hY⟩ := (Set.ext_iff.1 (D.DS_eq ha0) (x : QuotSpace D)).1 x.2
        exact ⟨Y, Subtype.ext hY⟩⟩)
    (((continuous_ι₂ D.κS).comp (by
      apply continuous_induced_rng.2; apply continuous_induced_rng.2
      exact continuous_expN.comp continuous_subtype_val :
        Continuous fun Y : Disk e (π - a) => D.diskPt Y (Disk_inner Y) (by linarith [(Disk_norm Y)]))).subtype_mk
      fun Y => (Set.ext_iff.1 (D.DS_eq ha0) _).2 ⟨Y, rfl⟩)

/-- **The slice meets every orbit exactly once** ([GG] `lem:attaching` (1), proof). -/
theorem slice_unique (a : M0 e) : ∃! z : UN e, ∃ q : S3, D.starM q a = (z, 1) := by
  refine ⟨D.Ψ a, ⟨a.2⁻¹, Prod.ext rfl (inv_mul_cancel _)⟩, ?_⟩
  rintro z ⟨q, hq⟩
  have h2 : q * a.2 = 1 := congrArg Prod.snd hq
  have hq' : q = a.2⁻¹ := eq_inv_of_mul_eq_one_left h2
  subst hq'
  exact (congrArg Prod.fst hq).symm


/-! ## (3): `P_θ/S³_⋆ ≅ 𝔻_N ∪_σ 𝔻_S` -/

/-- The unit vector `Y/‖Y‖ ∈ S(V)`. -/
def angS (Y : W) (hY : ⟪Y, e⟫ = 0) (hY0 : Y ≠ 0) : SV :=
  ⟨⟨‖Y‖⁻¹ • Y, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm,
      real_inner_smul_left, hY, mul_zero]⟩, by
    rw [mem_sphere_zero_iff_norm]
    show ‖‖Y‖⁻¹ • Y‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hY0)]⟩

/-- **The boundary identification** of `𝔻_N ∪_σ 𝔻_S`: `Y = a y_N ∈ ∂𝔻_N` is glued to
`(π − a) σ(y_N) ∈ ∂𝔻_S` ([GG] `eq:sigma`, in the disk coordinates `ζ_N = t x`,
`ζ_S = (π − t)x`). -/
def DiskRel {a : ℝ} (ha0 : 0 < a) :
    Disk e a ⊕ Disk e (π - a) → Disk e a ⊕ Disk e (π - a) → Prop
  | .inl Y, .inr Y' => ∃ h : ‖(Y : W)‖ = a,
      (Y' : W) = (π - a) • ((D.sigmaV (angS Y (Disk_inner Y) (fun h0 => by
        rw [h0, norm_zero] at h; linarith)) : Vs e) : W)
  | _, _ => False

/-- **The disk gluing `𝔻_N ∪_σ 𝔻_S`.** -/
abbrev DiskGluing {a : ℝ} (ha0 : 0 < a) := Quot (D.DiskRel ha0)

omit [Fact (finrank ℝ ↥(Vs e) = m + 1)] in
theorem polarX_expN {Y : W} (he : ‖e‖ = 1) (hY : ⟪Y, e⟫ = 0) (hY0 : Y ≠ 0) (hYπ : ‖Y‖ < π) :
    polarX e (expN e Y) = ‖Y‖⁻¹ • Y :=
  (polar_unique he (ζ := expN e Y) (x := ‖Y‖⁻¹ • Y) (norm_pos_iff.2 hY0) hYπ
    (by rw [real_inner_smul_left, hY, mul_zero]) rfl).2

theorem xS_diskPt (Y : W) (hY hYπ) (hY0 : Y ≠ 0) (h') :
    D.xS (D.diskPt Y hY hYπ, 1) h' = angS Y hY hY0 := by
  apply Subtype.ext; apply Subtype.ext
  show pX e (expN e Y) = ‖Y‖⁻¹ • Y
  rw [pX_eq_polarX D.e_norm (norm_expN D.e_norm hY), polarX_expN D.e_norm hY hY0 hYπ]

theorem diskPt_ne_e (Y : W) (hY hYπ) (hY0 : Y ≠ 0) : ζ0 (D.diskPt Y hY hYπ, (1 : S3)) ≠ e := by
  intro h
  have h1 := D.polarT_diskPt Y hY hYπ
  rw [show ζU (D.diskPt Y hY hYπ) = e from h, polarT_e D.e_norm] at h1
  exact hY0 (norm_eq_zero.1 h1.symm)

theorem ζU_ne_neg (z : UN e) : ζU z ≠ -e := z.2

/-- The key computation: the transition maps the boundary point `a y` of `𝔻_N` to the boundary
point `(π − a) σ(y)` of `𝔻_S`. -/
theorem κS_diskPt {Y : W} (hY : ⟪Y, e⟫ = 0) (hYπ : ‖Y‖ < π) (hY0 : Y ≠ 0) :
    ζU (D.κS (D.diskPt Y hY hYπ)) = cos (π - ‖Y‖) • e + sin (π - ‖Y‖) •
      ((D.sigmaV (angS Y hY hY0) : Vs e) : W) := by
  have hz := D.diskPt_ne_e Y hY hYπ hY0
  have hne : ζU (D.κS (D.diskPt Y hY hYπ)) ≠ e := D.κS.map_source hz
  have hd := polar_decomp D.e_norm (norm_ζU _) hne (ζU_ne_neg _)
  rw [D.polarT_κS _ hz, D.polarX_κS _ hz, D.polarT_diskPt,
    D.xS_diskPt Y hY hYπ hY0] at hd
  exact hd

theorem expN_of_sigma {a : ℝ} (ha0 : 0 < a) (haπ : a < π) (Y' : W) (v : SV)
    (hY' : Y' = (π - a) • ((v : Vs e) : W)) :
    expN e Y' = cos (π - a) • e + sin (π - a) • ((v : Vs e) : W) := by
  have hv : ‖((v : Vs e) : W)‖ = 1 := mem_sphere_zero_iff_norm.1 v.2
  have hn : ‖Y'‖ = π - a := by
    rw [hY', norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [expN, hn, hY', inv_smul_smul₀ (by linarith : π - a ≠ 0)]

theorem boundary_glue {a : ℝ} (ha0 : 0 < a) (haπ : a < π) (Y : Disk e a) (Y' : Disk e (π - a))
    (h : D.DiskRel ha0 (.inl Y) (.inr Y')) : D.diskMapN haπ Y = D.diskMapS ha0 Y' := by
  obtain ⟨hn, hY'⟩ := h
  have hY0 : (Y : W) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hn; linarith
  have hz := D.diskPt_ne_e Y (Disk_inner Y) (lt_of_le_of_lt (Disk_norm Y) haπ) hY0
  show ι₁ D.κS _ = ι₂ D.κS _
  rw [← ι₂_apply (show D.diskPt Y (Disk_inner Y) _ ∈ D.κS.source from hz)]
  congr 1
  apply Subtype.ext; apply Subtype.ext
  show ζU (D.κS (D.diskPt Y (Disk_inner Y) _)) = expN e Y'
  rw [D.κS_diskPt (Disk_inner Y) _ hY0, expN_of_sigma ha0 haπ _ _ hY', hn]

/-- The map `𝔻_N ∪_σ 𝔻_S → P_θ/S³_⋆`. -/
def diskGlueMap {a : ℝ} (ha0 : 0 < a) (haπ : a < π) : D.DiskGluing ha0 → QuotSpace D :=
  Quot.lift (Sum.elim (D.diskMapN haπ) (D.diskMapS ha0)) (by
    rintro (Y | Y) (Y' | Y') h
    · exact h.elim
    · exact D.boundary_glue ha0 haπ Y Y' h
    · exact h.elim
    · exact h.elim)

theorem diskGlueMap_injective {a : ℝ} (ha0 : 0 < a) (haπ : a < π) :
    Injective (D.diskGlueMap ha0 haπ) := by
  intro x y h
  induction x using Quot.ind with
  | mk x =>
  induction y using Quot.ind with
  | mk y =>
  -- the mixed case: the boundary identification
  have mixed : ∀ (Y : Disk e a) (Y' : Disk e (π - a)), D.diskMapN haπ Y = D.diskMapS ha0 Y' →
      D.DiskRel ha0 (.inl Y) (.inr Y') := by
    intro Y Y' hYY
    obtain ⟨hs, hκ⟩ := ι₁_eq_ι₂.1 hYY
    have hY0 : (Y : W) ≠ 0 := by
      intro h0
      apply hs
      show ζU (D.diskPt Y (Disk_inner Y) _) = e
      rw [ζU_diskPt, h0, expN_zero]
    have hYπ := lt_of_le_of_lt (Disk_norm Y) haπ
    have hs' : ζ0 (D.diskPt Y (Disk_inner Y) hYπ, (1 : S3)) ≠ e := hs
    have hY'π : ‖(Y' : W)‖ < π := by linarith [(Disk_norm Y')]
    have ht : π - ‖(Y : W)‖ = ‖(Y' : W)‖ := by
      have h1 := D.polarT_κS (D.diskPt Y (Disk_inner Y) hYπ) hs'
      rw [hκ, D.polarT_diskPt, D.polarT_diskPt] at h1
      linarith
    have hnY : ‖(Y : W)‖ = a := le_antisymm (Disk_norm Y) (by linarith [(Disk_norm Y')])
    refine ⟨hnY, ?_⟩
    have hY'0 : (Y' : W) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at ht; linarith
    have h2 := D.polarX_κS (D.diskPt Y (Disk_inner Y) hYπ) hs'
    rw [hκ, ζU_diskPt, polarX_expN D.e_norm (Disk_inner Y') hY'0 hY'π,
      D.xS_diskPt Y (Disk_inner Y) hYπ hY0] at h2
    have hn' : ‖(Y' : W)‖ = π - a := by rw [← ht, hnY]
    calc (Y' : W) = ‖(Y' : W)‖ • (‖(Y' : W)‖⁻¹ • (Y' : W)) :=
          (smul_inv_smul₀ (norm_ne_zero_iff.2 hY'0) _).symm
      _ = _ := by rw [h2, hn']
  rcases x with Y | Y <;> rcases y with Y' | Y'
  · exact congrArg (fun Y => Quot.mk _ (Sum.inl Y)) (D.diskMapN_injective haπ h)
  · exact Quot.sound (mixed Y Y' h)
  · exact (Quot.sound (mixed Y' Y h.symm)).symm
  · exact congrArg (fun Y => Quot.mk _ (Sum.inr Y)) (D.diskMapS_injective ha0 h)

theorem diskGlueMap_surjective {a : ℝ} (ha0 : 0 < a) (haπ : a < π) :
    Surjective (D.diskGlueMap ha0 haπ) := by
  intro x
  induction x using glued_induction with
  | h₁ z =>
    by_cases hz : polarT e (ζU z) ≤ a
    · refine ⟨Quot.mk _ (.inl ⟨diskN e (ζU z), inner_diskN D.e_norm (norm_ζU _),
        by rw [norm_diskN_ζU D]; exact hz⟩), ?_⟩
      exact congrArg (ι₁ D.κS) (D.diskPt_diskN _ _ _)
    · push_neg at hz
      have hs : ζ0 (z, (1 : S3)) ≠ e := by
        intro h
        have : polarT e (ζU z) = 0 := by rw [show ζU z = e from h, polarT_e D.e_norm]
        linarith
      have ht := D.polarT_κS z hs
      refine ⟨Quot.mk _ (.inr ⟨diskN e (ζU (D.κS z)), inner_diskN D.e_norm (norm_ζU _),
        by rw [norm_diskN_ζU D, ht]; linarith⟩), ?_⟩
      show ι₂ D.κS _ = ι₁ D.κS z
      rw [D.diskPt_diskN, ι₂_apply (show z ∈ D.κS.source from hs)]
  | h₂ z =>
    by_cases hz : polarT e (ζU z) ≤ π - a
    · refine ⟨Quot.mk _ (.inr ⟨diskN e (ζU z), inner_diskN D.e_norm (norm_ζU _),
        by rw [norm_diskN_ζU D]; exact hz⟩), ?_⟩
      exact congrArg (ι₂ D.κS) (D.diskPt_diskN _ _ _)
    · push_neg at hz
      have ht : z ∈ D.κS.target := by
        show ζU z ≠ e
        intro h
        have : polarT e (ζU z) = 0 := by rw [h, polarT_e D.e_norm]
        linarith
      set w := D.κS.symm z
      have hw : ζ0 (w, (1 : S3)) ≠ e := D.κS.map_target ht
      have hκw : D.κS w = z := D.κS.right_inv ht
      have htw := D.polarT_κS w hw
      rw [hκw] at htw
      refine ⟨Quot.mk _ (.inl ⟨diskN e (ζU w), inner_diskN D.e_norm (norm_ζU _),
        by rw [norm_diskN_ζU D]; linarith⟩), ?_⟩
      show ι₁ D.κS _ = ι₂ D.κS z
      rw [D.diskPt_diskN, ← hκw, ι₂_apply (show w ∈ D.κS.source from hw)]

/-- **[GG] `lem:attaching` (3)**: `P_θ/S³_⋆ ≅ 𝔻_N ∪_σ 𝔻_S` (as topological spaces; the quotient
manifold `QuotSpace D` carries the smooth structure of the collar gluing, `polarT_κS`,
`polarX_κS`). -/
def diskGluingHomeo {a : ℝ} (ha0 : 0 < a) (haπ : a < π) : D.DiskGluing ha0 ≃ₜ QuotSpace D := by
  haveI : FiniteDimensional ℝ W := FiniteDimensional.of_fact_finrank_eq_succ (m + 1)
  haveI : CompactSpace (Disk e a) := isCompact_iff_compactSpace.1 (isCompact_Disk a)
  haveI : CompactSpace (Disk e (π - a)) := isCompact_iff_compactSpace.1 (isCompact_Disk _)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (D.diskGlueMap ha0 haπ)
      ⟨D.diskGlueMap_injective ha0 haπ, D.diskGlueMap_surjective ha0 haπ⟩)
    (continuous_quot_lift _ (((continuous_ι₁ D.κS).comp (D.continuous_diskPt_comp haπ)).sumElim
      ((continuous_ι₂ D.κS).comp (by
        apply continuous_induced_rng.2; apply continuous_induced_rng.2
        exact continuous_expN.comp continuous_subtype_val :
          Continuous fun Y : Disk e (π - a) => D.diskPt Y (Disk_inner Y) (by linarith [(Disk_norm Y)])))))

/-- **[GG] `lem:attaching` (3), orbit-space form**: the topological star quotient of `P_θ` is
homeomorphic to `𝔻_N ∪_σ 𝔻_S`. -/
def orbitSpaceDiskGluing {a : ℝ} (ha0 : 0 < a) (haπ : a < π) :
    D.OrbitSpace ≃ₜ D.DiskGluing ha0 :=
  D.orbitSpaceHomeo.trans (D.diskGluingHomeo ha0 haπ).symm

end PolarData

end Attaching

end

end ExoticSpheres8And10
