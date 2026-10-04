/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.Sections

/-! # §3, `prop:polar` from equivariant sections: the normal form `P_θ ≅ E`

Given equivariant sections (`EquivSections`, the output of [GG]'s Steps 1–4), this file builds:

* `θ = g|_{S(V)}`, smooth and conjugation-equivariant (`thetaS`, `polarData`);
* `Φ : P_θ → E`, `Φ[(ζ, u)]_N = s'_N(ζ) u`, `Φ[(z', u)]_S = s'_S(Rz') u`;
* `normalForm`: `Φ` is a `C^∞` diffeomorphism, star-equivariant, equivariant for the principal
  actions, and covers the identity of `S^n` (a principal-bundle isomorphism).
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section NormalForm

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  {R : StarRep e} {E : Type*} [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] {B : StarBundle (m := m) R E}

local notation "Sn" => sphere (0 : W) 1

local notation "SV" => sphere (0 : Vs e) 1

namespace EquivSections

variable (S : EquivSections B)

/-- `S(V) ⊂ S^n`. -/
def incl (y : SV) : Sn := ⟨((y : Vs e) : W), by
  rw [mem_sphere_zero_iff_norm]; exact (mem_sphere_zero_iff_norm.1 y.2 : ‖(y : Vs e)‖ = 1)⟩

theorem inner_incl (y : SV) : ⟪((incl y : Sn) : W), e⟫ = 0 := by
  have := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (y : Vs e).2
  rw [real_inner_comm]; exact this

include S in
theorem incl_mem_Ov (y : SV) : incl y ∈ Ov e := by
  have hi := inner_incl y
  constructor
  · intro h; rw [h, real_inner_self_eq_norm_sq, R.e_norm] at hi; norm_num at hi
  · intro h; rw [h, inner_neg_left, real_inner_self_eq_norm_sq, R.e_norm] at hi; norm_num at hi

theorem contMDiff_incl : ContMDiff (𝓡 m) (𝓡 (m + 1)) ∞ (incl (e := e)) :=
  contMDiff_sphere_of_coe (by
    exact ((Vs e).subtypeL.contDiff.contMDiff.comp contMDiff_coe_sphere :
      ContMDiff (𝓡 m) 𝓘(ℝ, W) ∞ fun y : SV => ((y : Vs e) : W)))

/-- **`θ = g|_{S(V)}`.** -/
def thetaS (y : SV) : S3 := S.g (incl y)

theorem contMDiff_thetaS : ContMDiff (𝓡 m) (𝓡 3) ∞ S.thetaS :=
  S.contMDiffOn_g.comp_contMDiff contMDiff_incl S.incl_mem_Ov

theorem thetaS_equiv (q : S3) (y y' : SV) (h : ((y' : Vs e) : W) = R.ρ q ((y : Vs e) : W)) :
    S.thetaS y' = q * S.thetaS y * q⁻¹ := by
  have hy : incl y' = R.ρS q (incl y) := Subtype.ext h
  rw [thetaS, hy, S.g_equiv q _ (S.incl_mem_Ov y)]; rfl

/-- **The polar data produced by `prop:polar`.** -/
def polarData : PolarData (m := m) e where
  e_norm := R.e_norm
  ρ := R.ρ
  ρ_e := R.ρ_e
  ρ_smooth := R.ρ_smooth
  θ := S.thetaS
  θ_smooth := S.contMDiff_thetaS
  θ_equiv := S.thetaS_equiv

/-- The southern base point of copy-2 coordinates: `R z'`. -/
def reflS (z : UN e) : Sn :=
  ⟨reflE e (z : Sn), by
    rw [mem_sphere_zero_iff_norm, norm_reflE R.e_norm]; exact mem_sphere_zero_iff_norm.1 (z : Sn).2⟩

theorem reflS_mem (z : UN e) : reflS (R := R) z ∈ US e := reflE_ne R.e_norm z.2

theorem contMDiff_reflS : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ (reflS (R := R) (e := e)) :=
  contMDiff_sphere_of_coe (by
    exact (contDiff_reflE e).contMDiff.comp (contMDiff_coe_sphere.comp contMDiff_subtype_val))

/-- `Φ` on the first chart. -/
def Φ₁ (a : M0 e) : E := B.ract (S.sN' (a.1 : Sn)) a.2

/-- `Φ` on the second chart. -/
def Φ₂ (b : M0 e) : E := B.ract (S.sS' (reflS (R := R) b.1)) b.2

theorem incl_xS (a : M0 e) (ha : PolarData.ζ0 a ≠ e) :
    incl ((S.polarData).xS a ha) = R.XS (a.1 : Sn) := by
  apply Subtype.ext
  show pX e (PolarData.ζ0 a) = _
  rw [R.XS_val ⟨ha, a.1.2⟩]; rfl

theorem Φ_compat (a : M0 e) (ha : a ∈ (S.polarData).κP.source) :
    S.Φ₂ ((S.polarData).κP a) = S.Φ₁ a := by
  have ha' : PolarData.ζ0 a ≠ e := ha
  rw [(S.polarData).κP_eq a ha']
  have hO : (a.1 : Sn) ∈ Ov e := ⟨ha', a.1.2⟩
  have h1 : reflS (R := R) ((S.polarData).Rmap a ha') = (a.1 : Sn) :=
    Subtype.ext (reflE_reflE R.e_norm _)
  show B.ract (S.sS' (reflS ((S.polarData).Rmap a ha'))) (S.thetaS ((S.polarData).xS a ha') * a.2)
    = B.ract (S.sN' (a.1 : Sn)) a.2
  rw [h1, thetaS, incl_xS, ← B.ract_mul, ← S.sN'_eq hO]

/-- **`Φ : P_θ → E`.** -/
def Φ : PolarBundle S.polarData → E := glueLift S.Φ₁ S.Φ₂ S.Φ_compat

theorem Φ_ι₁ (a : M0 e) : S.Φ (ι₁ _ a) = S.Φ₁ a := rfl

theorem Φ_ι₂ (b : M0 e) : S.Φ (ι₂ _ b) = S.Φ₂ b := rfl

theorem contMDiff_Φ₁ : ContMDiff (IP m) (IP m) ∞ S.Φ₁ := by
  have h1 : ContMDiff (IP m) (IP m) ∞ fun a : M0 e => S.sN' (a.1 : Sn) :=
    S.contMDiffOn_sN'.comp_contMDiff (contMDiff_subtype_val.comp contMDiff_fst) fun a => a.1.2
  exact ContMDiff.comp (g := fun x : E × S3 => B.ract x.1 x.2)
    (f := fun a : M0 e => (S.sN' (a.1 : Sn), a.2)) B.ract_smooth (h1.prodMk contMDiff_snd)

theorem contMDiff_Φ₂ : ContMDiff (IP m) (IP m) ∞ S.Φ₂ := by
  have h1 : ContMDiff (IP m) (IP m) ∞ fun b : M0 e => S.sS' (reflS (R := R) b.1) :=
    S.contMDiffOn_sS'.comp_contMDiff (contMDiff_reflS.comp contMDiff_fst) fun b => reflS_mem b.1
  exact ContMDiff.comp (g := fun x : E × S3 => B.ract x.1 x.2)
    (f := fun b : M0 e => (S.sS' (reflS (R := R) b.1), b.2)) B.ract_smooth (h1.prodMk contMDiff_snd)

/-- **`Φ` is smooth.** -/
theorem contMDiff_Φ : ContMDiff (IP m) (IP m) ∞ S.Φ := by
  haveI := nontrivial_of_polarData S.polarData
  haveI := nonempty_M0 (e := e)
  exact contMDiff_glueLift (IP m) (S.polarData).hκP (S.polarData).hκPs _ S.contMDiff_Φ₁
    S.contMDiff_Φ₂

/-- **`Φ` covers the identity of `S^n`.** -/
theorem proj_Φ (x : PolarBundle S.polarData) : B.proj (S.Φ x) = (S.polarData).proj x := by
  induction x using glued_induction with
  | h₁ a =>
    rw [Φ_ι₁, Φ₁, B.proj_ract, S.proj_sN' a.1.2]; rfl
  | h₂ b =>
    rw [Φ_ι₂, Φ₂, B.proj_ract, S.proj_sS' (reflS_mem b.1)]; rfl

/-- **`Φ` is equivariant for the principal actions.** -/
theorem Φ_ract (x : PolarBundle S.polarData) (h : S3) :
    S.Φ ((S.polarData).ract x h) = B.ract (S.Φ x) h := by
  induction x using glued_induction with
  | h₁ a => exact (B.ract_mul _ _ _).symm
  | h₂ b => exact (B.ract_mul _ _ _).symm

/-- **`Φ` is equivariant for the star actions.** -/
theorem Φ_star (q : S3) (x : PolarBundle S.polarData) : S.Φ (q • x) = B.star q (S.Φ x) := by
  induction x using glued_induction with
  | h₁ a =>
    show B.ract (S.sN' (R.ρS q (a.1 : Sn))) (q * a.2) = B.star q (B.ract (S.sN' (a.1 : Sn)) a.2)
    rw [S.sN'_equiv q a.1.2, B.ract_mul, inv_mul_cancel_left, B.star_ract]
  | h₂ b =>
    have hr : reflS (R := R) (PolarData.ρU S.polarData q b.1) = R.ρS q (reflS (R := R) b.1) :=
      Subtype.ext (reflE_map (R.ρ q).toLinearIsometry (R.ρ_e q) _)
    show B.ract (S.sS' (reflS (PolarData.ρU S.polarData q b.1))) (q * b.2) =
      B.star q (B.ract (S.sS' (reflS b.1)) b.2)
    rw [hr, S.sS'_equiv q (reflS_mem b.1), B.ract_mul, inv_mul_cancel_left, B.star_ract]


/-! ### The inverse of `Φ` -/

/-- `R ζ` as a point of `U_N` (for `ζ ≠ o_N`). -/
def reflU (ζ : Sn) (h : (ζ : W) ≠ e) : UN e :=
  ⟨⟨reflE e ζ, by
    rw [mem_sphere_zero_iff_norm, norm_reflE R.e_norm]; exact mem_sphere_zero_iff_norm.1 ζ.2⟩,
    reflE_ne_neg R.e_norm h⟩

theorem reflS_reflU (ζ : Sn) (h : (ζ : W) ≠ e) : reflS (R := R) (reflU (R := R) ζ h) = ζ :=
  Subtype.ext (reflE_reflE R.e_norm _)

theorem reflU_reflS (z : UN e) (h) : reflU (R := R) (reflS (R := R) z) h = z :=
  Subtype.ext (Subtype.ext (reflE_reflE R.e_norm _))

/-- `Φ⁻¹` over `U_N`. -/
def ΦinvN (p : E) (hp : (B.proj p : W) ≠ -e) : PolarBundle S.polarData :=
  ι₁ _ (⟨B.proj p, hp⟩, B.divE (S.sN' (B.proj p)) p)

/-- `Φ⁻¹` over `U_S`. -/
def ΦinvS (p : E) (hp : (B.proj p : W) ≠ e) : PolarBundle S.polarData :=
  ι₂ _ (reflU (R := R) (B.proj p) hp, B.divE (S.sS' (B.proj p)) p)

theorem ne_e_of_not (he : ‖e‖ = 1) (ζ : Sn) (h : ¬ (ζ : W) ≠ -e) : (ζ : W) ≠ e := by
  push_neg at h; rw [h]; exact (ne_neg_self_e he).symm

open Classical in
/-- `Φ⁻¹`. -/
def Ψ (p : E) : PolarBundle S.polarData :=
  if h : (B.proj p : W) ≠ -e then S.ΦinvN p h else S.ΦinvS p (ne_e_of_not R.e_norm _ h)

theorem divE_sS'_eq (p : E) (ζ : Sn) (hO : ζ ∈ Ov e) (hp : B.proj p = ζ) :
    B.divE (S.sS' ζ) p = S.g (R.XS ζ) * B.divE (S.sN' ζ) p := by
  apply B.divE_unique
  rw [← B.ract_mul, ← S.sN'_eq hO]
  exact B.ract_divE _ _ (by rw [hp, S.proj_sN' hO.2])

theorem ΦinvN_eq_ΦinvS (p : E) (h1 : (B.proj p : W) ≠ -e) (h2 : (B.proj p : W) ≠ e) :
    S.ΦinvN p h1 = S.ΦinvS p h2 := by
  have hO : B.proj p ∈ Ov e := ⟨h2, h1⟩
  set a : M0 e := (⟨B.proj p, h1⟩, B.divE (S.sN' (B.proj p)) p)
  have ha : PolarData.ζ0 a ≠ e := h2
  rw [ΦinvN, ΦinvS, ← ι₂_apply (show a ∈ (S.polarData).κP.source from ha)]
  congr 1
  rw [(S.polarData).κP_eq a ha]
  refine Prod.ext (Subtype.ext (Subtype.ext rfl)) ?_
  show S.thetaS ((S.polarData).xS a ha) * B.divE (S.sN' (B.proj p)) p = B.divE (S.sS' (B.proj p)) p
  rw [thetaS, incl_xS, S.divE_sS'_eq p _ hO rfl]

theorem Ψ_eq_N (p : E) (h : (B.proj p : W) ≠ -e) : S.Ψ p = S.ΦinvN p h := by
  rw [Ψ, dif_pos h]

theorem Ψ_eq_S (p : E) (h : (B.proj p : W) ≠ e) : S.Ψ p = S.ΦinvS p h := by
  unfold Ψ
  split_ifs with h1
  · exact S.ΦinvN_eq_ΦinvS p h1 h
  · rfl

theorem Φ_Ψ (p : E) : S.Φ (S.Ψ p) = p := by
  unfold Ψ
  split_ifs with h
  · show B.ract (S.sN' (B.proj p)) (B.divE (S.sN' (B.proj p)) p) = p
    exact B.ract_divE _ _ (S.proj_sN' h).symm
  · have h2 := ne_e_of_not R.e_norm _ h
    show B.ract (S.sS' (reflS (R := R) (reflU (R := R) (B.proj p) h2))) (B.divE (S.sS' (B.proj p)) p) = p
    rw [reflS_reflU]
    exact B.ract_divE _ _ (S.proj_sS' h2).symm

theorem Ψ_Φ (x : PolarBundle S.polarData) : S.Ψ (S.Φ x) = x := by
  induction x using glued_induction with
  | h₁ a =>
    have hp : B.proj (S.Φ (ι₁ _ a)) = (a.1 : Sn) := by
      rw [Φ_ι₁, Φ₁, B.proj_ract, S.proj_sN' a.1.2]
    have h1 : (B.proj (S.Φ (ι₁ _ a)) : W) ≠ -e := by rw [hp]; exact a.1.2
    rw [S.Ψ_eq_N _ h1, ΦinvN]
    congr 1
    refine Prod.ext (Subtype.ext hp) ?_
    show B.divE (S.sN' (B.proj (S.Φ₁ a))) (S.Φ₁ a) = a.2
    rw [show B.proj (S.Φ₁ a) = (a.1 : Sn) from hp]
    exact B.divE_unique _ _ _ rfl
  | h₂ b =>
    have hp : B.proj (S.Φ (ι₂ _ b)) = reflS (R := R) b.1 := by
      rw [Φ_ι₂, Φ₂, B.proj_ract, S.proj_sS' (reflS_mem b.1)]
    have h2 : (B.proj (S.Φ (ι₂ _ b)) : W) ≠ e := by rw [hp]; exact reflS_mem b.1
    rw [S.Ψ_eq_S _ h2, ΦinvS]
    congr 1
    refine Prod.ext ?_ ?_
    · have : ∀ (ζ : Sn) (hζ : ζ = reflS (R := R) b.1) (h : (ζ : W) ≠ e),
          reflU (R := R) ζ h = b.1 := by
        intro ζ hζ h; subst hζ; exact reflU_reflS _ _
      exact this _ hp h2
    · show B.divE (S.sS' (B.proj (S.Φ₂ b))) (S.Φ₂ b) = b.2
      rw [show B.proj (S.Φ₂ b) = reflS (R := R) b.1 from hp]
      exact B.divE_unique _ _ _ rfl

/-! ### Smoothness of the inverse -/

/-- `π⁻¹(U_N)` and `π⁻¹(U_S)` as open subsets of `E`. -/
def EN : TopologicalSpace.Opens E :=
  ⟨{p | (B.proj p : W) ≠ -e}, isOpen_ne_fun
    (continuous_subtype_val.comp B.proj_smooth.continuous) continuous_const⟩

def ES : TopologicalSpace.Opens E :=
  ⟨{p | (B.proj p : W) ≠ e}, isOpen_ne_fun
    (continuous_subtype_val.comp B.proj_smooth.continuous) continuous_const⟩

theorem contMDiffAt_Ψ_N (p : E) (hp : (B.proj p : W) ≠ -e) :
    ContMDiffAt (IP m) (IP m) ∞ S.Ψ p := by
  haveI := nontrivial_of_polarData S.polarData
  haveI := nonempty_M0 (e := e)
  let U : TopologicalSpace.Opens E := EN (B := B)
  have hproj : ContMDiff (IP m) (𝓡 (m + 1)) ∞ fun q : U => (⟨B.proj q, q.2⟩ : UN e) :=
    (ContMDiff.subtypeVal_comp_iff (UN e) _).1 (B.proj_smooth.comp contMDiff_subtype_val)
  have hsec : ContMDiff (IP m) (IP m) ∞ fun q : U => S.sN' (B.proj q) :=
    S.contMDiffOn_sN'.comp_contMDiff (B.proj_smooth.comp contMDiff_subtype_val) fun q => q.2
  have hdiv : ContMDiff (IP m) (𝓡 3) ∞ fun q : U => B.divE (S.sN' (B.proj q)) q := by
    rw [← contMDiffOn_univ]
    exact B.contMDiffOn_divE isOpen_univ hsec.contMDiffOn contMDiff_subtype_val.contMDiffOn
      fun q _ => (S.proj_sN' q.2).symm
  have hF : ContMDiff (IP m) (IP m) ∞ fun q : U => S.Ψ q := by
    have := (contMDiff_ι₁ (IP m) (S.polarData).hκP (S.polarData).hκPs).comp (hproj.prodMk hdiv)
    refine this.congr fun q => ?_
    rw [comp_apply, S.Ψ_eq_N _ q.2]; rfl
  exact (contMDiffAt_subtype_iff (U := U) (x := ⟨p, hp⟩)).1 (hF ⟨p, hp⟩)

theorem contMDiffAt_Ψ_S (p : E) (hp : (B.proj p : W) ≠ e) :
    ContMDiffAt (IP m) (IP m) ∞ S.Ψ p := by
  haveI := nontrivial_of_polarData S.polarData
  haveI := nonempty_M0 (e := e)
  let U : TopologicalSpace.Opens E := ES (B := B)
  have hproj : ContMDiff (IP m) (𝓡 (m + 1)) ∞
      fun q : U => reflU (R := R) (B.proj q) q.2 := by
    refine (ContMDiff.subtypeVal_comp_iff (UN e) _).1 (contMDiff_sphere_of_coe ?_)
    exact (contDiff_reflE e).contMDiff.comp
      (contMDiff_coe_sphere.comp (B.proj_smooth.comp contMDiff_subtype_val))
  have hsec : ContMDiff (IP m) (IP m) ∞ fun q : U => S.sS' (B.proj q) :=
    S.contMDiffOn_sS'.comp_contMDiff (B.proj_smooth.comp contMDiff_subtype_val) fun q => q.2
  have hdiv : ContMDiff (IP m) (𝓡 3) ∞ fun q : U => B.divE (S.sS' (B.proj q)) q := by
    rw [← contMDiffOn_univ]
    exact B.contMDiffOn_divE isOpen_univ hsec.contMDiffOn contMDiff_subtype_val.contMDiffOn
      fun q _ => (S.proj_sS' q.2).symm
  have hF : ContMDiff (IP m) (IP m) ∞ fun q : U => S.Ψ q := by
    have := (contMDiff_ι₂ (IP m) (S.polarData).hκP (S.polarData).hκPs).comp (hproj.prodMk hdiv)
    refine this.congr fun q => ?_
    rw [comp_apply, S.Ψ_eq_S _ q.2]; rfl
  exact (contMDiffAt_subtype_iff (U := U) (x := ⟨p, hp⟩)).1 (hF ⟨p, hp⟩)

theorem contMDiff_Ψ : ContMDiff (IP m) (IP m) ∞ S.Ψ := by
  intro p
  by_cases h : (B.proj p : W) = -e
  · exact S.contMDiffAt_Ψ_S p (by rw [h]; exact (ne_neg_self_e R.e_norm).symm)
  · exact S.contMDiffAt_Ψ_N p h

/-- **[GG] `prop:polar`, the isomorphism `Φ : P_θ ≅ E`** as a `C^∞` diffeomorphism. -/
def normalFormDiffeo : Diffeomorph (IP m) (IP m) (PolarBundle S.polarData) E ∞ where
  toFun := S.Φ
  invFun := S.Ψ
  left_inv := S.Ψ_Φ
  right_inv := S.Φ_Ψ
  contMDiff_toFun := S.contMDiff_Φ
  contMDiff_invFun := S.contMDiff_Ψ

/-! ### The star quotients -/

/-- The star orbit relation on `E`. -/
def starSetoid (B : StarBundle (m := m) R E) : Setoid E where
  r p p' := ∃ q, B.star q p = p'
  iseqv := ⟨fun p => ⟨1, B.star_one p⟩,
    fun ⟨q, h⟩ => ⟨q⁻¹, by rw [← h, ← B.star_mul, inv_mul_cancel, B.star_one]⟩,
    fun ⟨q, h⟩ ⟨q', h'⟩ => ⟨q' * q, by rw [B.star_mul, h, h']⟩⟩

theorem Ψ_star (q : S3) (p : E) : S.Ψ (B.star q p) = q • S.Ψ p := by
  conv_lhs => rw [← S.Φ_Ψ p, ← S.Φ_star]
  exact S.Ψ_Φ _

/-- **[GG] `prop:polar`, "consequently"**: `E/S³_⋆ ≃ₜ P_θ/S³_⋆`. -/
def starQuotientHomeo : Quotient (starSetoid B) ≃ₜ (S.polarData).OrbitSpace where
  toFun := Quotient.lift (fun p => Quotient.mk _ (S.Ψ p)) fun p p' hpp => by
    obtain ⟨q, h⟩ := hpp
    rw [← h, S.Ψ_star]; exact (Quotient.sound (MulAction.mem_orbit (S.Ψ p) q)).symm
  invFun := Quotient.lift (fun x => Quotient.mk (starSetoid B) (S.Φ x)) fun x y hxy => by
    obtain ⟨q, h⟩ := hxy
    rw [← h, S.Φ_star]
    exact (Quotient.sound (s := starSetoid B) (a := S.Φ y) (b := B.star q (S.Φ y)) ⟨q, rfl⟩).symm
  left_inv p := by
    induction p using Quotient.inductionOn with
    | h p => exact congrArg (Quotient.mk _) (S.Φ_Ψ p)
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h x => exact congrArg (Quotient.mk _) (S.Ψ_Φ x)
  continuous_toFun := (continuous_quotient_mk'.comp S.contMDiff_Ψ.continuous).quotient_lift _
  continuous_invFun := (continuous_quotient_mk'.comp S.contMDiff_Φ.continuous).quotient_lift _

/-- `E/S³_⋆` is homeomorphic to the quotient manifold `QuotSpace` of `P_θ`. -/
def starQuotientManifold : Quotient (starSetoid B) ≃ₜ QuotSpace S.polarData :=
  S.starQuotientHomeo.trans (S.polarData).orbitSpaceHomeo

end EquivSections

end NormalForm

end

end ExoticSpheres8And10
