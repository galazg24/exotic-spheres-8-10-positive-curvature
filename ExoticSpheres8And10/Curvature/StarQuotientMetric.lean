/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Northern.Submersion

/-! # §4: the quotient by the star action, for any star-invariant metric

`S4_NorthSub` and `S4_NorthRiem` were written for [GG]'s northern metric `G_N`. This file repeats
their horizontal-lift construction and the O'Neill descent, for **any** metric `G` on `V × S³`.
The metric need only:
- have a smooth, symmetric, positive-definite slice form `Gs Y` at `(Y, 1)`;
- be invariant under the star action `q ⋆ (Y, u) = (ρ(q)Y, qu)`.

The southern filling uses it with `G = GH` (`S4_SouthQuot`).
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

namespace SQ

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Lift

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (Gs : V → V × E3 →L[ℝ] V × E3 →L[ℝ] ℝ)

theorem contDiff_Gs_apply' {Gs : V → V × E3 →L[ℝ] V × E3 →L[ℝ] ℝ} (hGsm : ContDiff ℝ ∞ Gs)
    {f g : V → V × E3} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun Y => Gs Y (f Y) (g Y) :=
  (hGsm.clm_apply hf).clm_apply hg

/-- The obstruction to horizontality: `u ↦ Σᵢ G(u, (K eᵢ, eᵢ)) eᵢ`. -/
def hz (Y : V) : V × E3 →L[ℝ] E3 :=
  ∑ i : Fin 3, ((Gs Y).flip (ιv ρV Y (bE i))).smulRight (bE i)

theorem hz_apply (Y : V) (u : V × E3) :
    hz ρV Gs Y u = ∑ i : Fin 3, Gs Y u (ιv ρV Y (bE i)) • bE i := by
  simp [hz, ContinuousLinearMap.smulRight_apply]

/-- `Φ_Y = (dπ, hz) : V × ℝ³ → V × ℝ³`; its kernel is `vertical ∩ vertical^⊥ = 0`. -/
def Φs (Y : V) : V × E3 →L[ℝ] V × E3 := (dπl ρV Y).prod (hz ρV Gs Y)

theorem hz_eq_zero_iff (Y : V) (u : V × E3) :
    hz ρV Gs Y u = 0 ↔ ∀ β, Gs Y u (ιv ρV Y β) = 0 := by
  constructor
  · intro h β
    have hc : ∀ i, Gs Y u (ιv ρV Y (bE i)) = 0 := by
      intro i
      have := congrArg (fun x : E3 => x i) h
      simpa [hz_apply, Pi.single_apply] using this
    exact forall_basis_eq_zero (ℓ := (Gs Y u).comp (ιv ρV Y)) hc β
  · intro h
    rw [hz_apply]
    simp [h]

variable {Gs}

theorem Φs_injective (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y : V) : Function.Injective (Φs ρV Gs Y) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  have h1 : dπl ρV Y u = 0 := congrArg Prod.fst hu
  have h2 : hz ρV Gs Y u = 0 := congrArg Prod.snd hu
  rw [hz_eq_zero_iff] at h2
  have hv : u = ιv ρV Y u.2 := by
    rw [dπl_apply, sub_eq_zero] at h1
    rw [ιv_apply, ← h1]
  -- `u = ιv u.2`, so `G(u, u) = G(u, ιv u.2) = 0`
  by_contra hne
  have hpos := hGpos Y u hne
  have h3 := h2 u.2
  rw [← hv] at h3
  linarith

/-- `Φ_Y` as a continuous linear equivalence. -/
def Φe (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y : V) : (V × E3) ≃L[ℝ] (V × E3) :=
  (LinearEquiv.ofInjectiveEndo (Φs ρV Gs Y).toLinearMap (Φs_injective ρV hGpos Y)).toContinuousLinearEquiv

theorem coe_Φe (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y : V) : (Φe ρV hGpos Y : V × E3 →L[ℝ] V × E3) = Φs ρV Gs Y := by
  ext u <;> rfl

theorem isInvertible_Φs (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y : V) : (Φs ρV Gs Y).IsInvertible :=
  ⟨Φe ρV hGpos Y, coe_Φe ρV hGpos Y⟩

variable (Gs)

/-- **The horizontal lift** at `(Y, 1)`: `c ↦ Φ_Y⁻¹(c, 0)`. -/
def hlift (Y : V) : V →L[ℝ] V × E3 :=
  (ContinuousLinearMap.inverse (Φs ρV Gs Y)).comp (ContinuousLinearMap.inl ℝ V E3)

variable {Gs}

theorem Φs_hlift (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y c : V) : Φs ρV Gs Y (hlift ρV Gs Y c) = (c, 0) := by
  simp only [hlift, ContinuousLinearMap.comp_apply, ← coe_Φe ρV hGpos Y,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.inl_apply]

theorem dπl_hlift (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y c : V) : dπl ρV Y (hlift ρV Gs Y c) = c :=
  congrArg Prod.fst (Φs_hlift ρV hGpos Y c)

theorem hlift_horizontal (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y c : V) (β : E3) :
    Gs Y (hlift ρV Gs Y c) (ιv ρV Y β) = 0 :=
  (hz_eq_zero_iff ρV Gs Y _).1 (congrArg Prod.snd (Φs_hlift ρV hGpos Y c)) β

/-- **Uniqueness of horizontal lifts.** -/
theorem eq_hlift (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y : V) {u : V × E3}
    (hu : ∀ β, Gs Y u (ιv ρV Y β) = 0) : u = hlift ρV Gs Y (dπl ρV Y u) := by
  apply Φs_injective ρV hGpos Y
  rw [Φs_hlift ρV hGpos]
  show (dπl ρV Y u, hz ρV Gs Y u) = _
  rw [(hz_eq_zero_iff ρV Gs Y u).2 hu]

variable (Gs)

/-- **The quotient metric on `V`**: `g_B(Y)(c, c') = G_{(Y,1)}(h c, h c')`. -/
def gB (Y : V) : V →L[ℝ] V →L[ℝ] ℝ := bil (Gs Y) (hlift ρV Gs Y)

variable {Gs}

theorem gB_symm (hGsym : ∀ Y u w, Gs Y u w = Gs Y w u) (Y c c' : V) :
    gB ρV Gs Y c c' = gB ρV Gs Y c' c := hGsym Y _ _

theorem gB_pos (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (Y : V) {c : V} (hc : c ≠ 0) : 0 < gB ρV Gs Y c c := by
  refine hGpos Y _ fun h => hc ?_
  rw [← dπl_hlift ρV hGpos Y c]
  exact (congrArg (dπl ρV Y) h).trans (map_zero _)

theorem contDiff_Φs (hGsm : ContDiff ℝ ∞ Gs) : ContDiff ℝ ∞ (Φs ρV Gs) := by
  rw [contDiff_clm_apply_iff]
  intro u
  have hK : ∀ β : E3, ContDiff ℝ ∞ fun Y : V => KY ρV Y β := fun β =>
    (dρ ρV β).contDiff
  refine ContDiff.prodMk ?_ ?_
  · exact contDiff_const.sub (hK u.2)
  · have e : (fun Y => hz ρV Gs Y u) =
        fun Y => ∑ i : Fin 3, Gs Y u (ιv ρV Y (bE i)) • bE i :=
      funext fun Y => hz_apply ρV Gs Y u
    show ContDiff ℝ ∞ fun Y => hz ρV Gs Y u
    rw [e]
    refine ContDiff.sum fun i _ => ?_
    have h := contDiff_Gs_apply' hGsm (contDiff_const (c := u))
      ((hK (bE i)).prodMk (contDiff_const (c := (bE i : E3))))
    exact h.smul contDiff_const

theorem contDiff_hlift_apply (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (hGsm : ContDiff ℝ ∞ Gs) (c : V) :
    ContDiff ℝ ∞ fun Y => hlift ρV Gs Y c := by
  have hinv : ContDiff ℝ ∞ fun Y => ContinuousLinearMap.inverse (Φs ρV Gs Y) := by
    rw [contDiff_iff_contDiffAt]
    intro Y
    exact (isInvertible_Φs ρV hGpos Y).contDiffAt_map_inverse.comp Y
      (contDiff_Φs ρV hGsm).contDiffAt
  exact hinv.clm_apply contDiff_const

theorem contDiff_gB (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (hGsm : ContDiff ℝ ∞ Gs) :
    ContDiff ℝ ∞ (gB ρV Gs) := by
  rw [contDiff_clm_apply_iff]
  intro c
  rw [contDiff_clm_apply_iff]
  intro c'
  exact contDiff_Gs_apply' hGsm (contDiff_hlift_apply ρV hGpos hGsm c)
    (contDiff_hlift_apply ρV hGpos hGsm c')

end Lift

/-! ### `πN` is a Riemannian submersion, for any star-invariant metric -/

section Riem

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))
  {Gs : V → V × E3 →L[ℝ] V × E3 →L[ℝ] ℝ}
  {G : Π p : V × S3, TangentSpace (IN V) p →L[ℝ] TangentSpace (IN V) p →L[ℝ] ℝ}

variable [Bundle.RiemannianBundle (TangentSpace (IN V) : V × S3 → Type)]
  [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, V) : V → Type)]

include hρ in
theorem isRiemannianSubmersionAtPoint_slice (hGsym : ∀ Y u w, Gs Y u w = Gs Y w u)
    (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u)
    (hsl : ∀ (Y : V) (u w : TangentSpace (IN V) (Y, (1 : S3))), G (Y, 1) u w = Gs Y u w)
    (hM : ∀ p u v, tangentMetric (IN V) (V × S3) p u v = G p u v)
    (hB : ∀ y a b, tangentMetric 𝓘(ℝ, V) V y a b = gB ρV Gs y a b) (Y : V) :
    IsRiemannianSubmersionAtPoint (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) := by
  have hvert : ∀ β, tsN (Y, 1) (ιv ρV Y β) ∈
      verticalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) := fun β => by
    rw [mem_verticalSpace_iff]
    show dπN ρV Y (KY ρV Y β, β) = 0
    rw [dπN_apply hρ, sub_self]
  have hhor : ∀ w ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1), ∀ β,
      Gs Y w (ιv ρV Y β) = 0 := by
    intro w hw β
    have := (Submodule.mem_orthogonal _ _).1 hw _ (hvert β)
    rw [inner_eq_tangentMetric, hM, hsl] at this
    exact (hGsym Y w (ιv ρV Y β)).trans this
  intro u hu v hv
  rw [inner_eq_tangentMetric, inner_eq_tangentMetric, hB, hM, hsl]
  show gB ρV Gs (πN ρV (Y, 1)) (dπN ρV Y u) (dπN ρV Y v) = _
  rw [πN_slice, dπN_eq hρ]
  calc gB ρV Gs Y (dπl ρV Y u) (dπl ρV Y v)
      = Gs Y (hlift ρV Gs Y (dπl ρV Y u)) (hlift ρV Gs Y (dπl ρV Y v)) := rfl
    _ = Gs Y u v := by
      rw [← eq_hlift ρV hGpos Y (hhor u hu), ← eq_hlift ρV hGpos Y (hhor v hv)]

include hρ in
theorem isRiemannianSubmersionAtPoint_all (hGsym : ∀ Y u w, Gs Y u w = Gs Y w u)
    (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u)
    (hsl : ∀ (Y : V) (u w : TangentSpace (IN V) (Y, (1 : S3))), G (Y, 1) u w = Gs Y u w)
    (hinv : ∀ q p (u v : TangentSpace (IN V) p),
      G (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u)
        (mfderiv (IN V) (IN V) (starN ρV q) p v) = G p u v)
    (hM : ∀ p u v, tangentMetric (IN V) (V × S3) p u v = G p u v)
    (hB : ∀ y a b, tangentMetric 𝓘(ℝ, V) V y a b = gB ρV Gs y a b) (p : V × S3) :
    IsRiemannianSubmersionAtPoint (IN V) 𝓘(ℝ, V) (πN ρV) p := by
  have hfφ : πN ρV ∘ starN ρV p.2⁻¹ = id ∘ πN ρV := funext fun x => πN_starN ρV _ x
  have hπ : ∀ x, MDifferentiableAt (IN V) 𝓘(ℝ, V) (πN ρV) x := fun x =>
    (contMDiff_πN hρ x).mdifferentiableAt (by simp)
  have hφ : MDifferentiableAt (IN V) (IN V) (starN ρV p.2⁻¹) p :=
    (contMDiff_starN hρ _ p).mdifferentiableAt (by simp)
  have hiso : ∀ u v : TangentSpace (IN V) p,
      inner ℝ (mfderiv (IN V) (IN V) (starN ρV p.2⁻¹) p u)
        (mfderiv (IN V) (IN V) (starN ρV p.2⁻¹) p v) = inner ℝ u v := fun u v => by
    rw [inner_eq_tangentMetric, inner_eq_tangentMetric, hM, hM]
    exact hinv _ p u v
  have hψiso : ∀ a b : TangentSpace 𝓘(ℝ, V) (πN ρV p),
      inner ℝ (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) id (πN ρV p) a)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) id (πN ρV p) b) = inner ℝ a b := fun a b => by
    rw [mfderiv_id]; rfl
  have hR : IsRiemannianSubmersionAtPoint (IN V) 𝓘(ℝ, V) (πN ρV) (starN ρV p.2⁻¹ p) := by
    have e : starN ρV p.2⁻¹ p = (ρV p.2⁻¹ p.1, 1) := by
      show (ρV p.2⁻¹ p.1, p.2⁻¹ * p.2) = _
      rw [inv_mul_cancel]
    rw [e]
    exact isRiemannianSubmersionAtPoint_slice hρ hGsym hGpos hsl hM hB _
  exact isRiemannianSubmersionAtPoint_of_isometry hfφ (hπ p) (hπ _) hφ mdifferentiableAt_id hiso
    hψiso hR

end Riem

/-! ### Positive curvature descends to `(V, g_B)` -/

section Descend

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))
  {Gs : V → V × E3 →L[ℝ] V × E3 →L[ℝ] ℝ}
  {G : Π p : V × S3, TangentSpace (IN V) p →L[ℝ] TangentSpace (IN V) p →L[ℝ] ℝ}

theorem isSymm_cmet_gB' (hGsym : ∀ Y u w, Gs Y u w = Gs Y w u) : IsSymm (cmet (gB ρV Gs)) :=
  fun y a b => gB_symm ρV hGsym y a b

theorem isPosDef_cmet_gB' (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) : IsPosDef (cmet (gB ρV Gs)) :=
  fun y a ha => gB_pos ρV hGpos y ha

include hρ in
/-- **O'Neill for the star quotient.** If `G` has positive curvature on the horizontal planes at
`(Y, 1)`, then the quotient metric `g_B` has positive curvature on every plane at `Y`. -/
theorem quot_sectionalCurvature_pos (hGsym : ∀ Y u w, Gs Y u w = Gs Y w u)
    (hGpos : ∀ Y u, u ≠ 0 → 0 < Gs Y u u) (hGsm : ContDiff ℝ ∞ Gs)
    (hsG : IsSymm G) (hpG : IsPosDef G) (hgG : IsContMDiffMetricSection (V × E3) 2 G)
    (hsl : ∀ (Y : V) (u w : TangentSpace (IN V) (Y, (1 : S3))), G (Y, 1) u w = Gs Y u w)
    (hinv : ∀ q p (u v : TangentSpace (IN V) p),
      G (starN ρV q p) (mfderiv (IN V) (IN V) (starN ρV q) p u)
        (mfderiv (IN V) (IN V) (starN ρV q) p v) = G p u v) (Y : V)
    (hup : ∀ u v : TangentSpace (IN V) (Y, (1 : S3)), (∀ β, Gs Y u (ιv ρV Y β) = 0) →
      (∀ β, Gs Y v (ιv ρV Y β) = 0) → LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hsG hpG hgG (Y, 1) u v)
    (a c : TangentSpace 𝓘(ℝ, V) Y) (hac : LinearIndependent ℝ ![a, c]) :
    0 < sectionalCurvatureAt (isSymm_cmet_gB' hGsym) (isPosDef_cmet_gB' hGpos)
      (isContMDiffMetricSection_cmet ((contDiff_gB ρV hGpos hGsm).of_le two_le_top_nat)) Y a c := by
  let instM : Bundle.RiemannianBundle (TangentSpace (IN V) : V × S3 → Type) :=
    ⟨(toContMDiffRiemannianMetric (n := 2) hsG hpG hgG).toRiemannianMetric⟩
  let instB : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, V) : V → Type) :=
    ⟨(toContMDiffRiemannianMetric (n := ∞) (isSymm_cmet_gB' (ρV := ρV) hGsym)
      (isPosDef_cmet_gB' hGpos)
      (isContMDiffMetricSection_cmet (contDiff_gB ρV hGpos hGsm))).toRiemannianMetric⟩
  have hM : ∀ p u v, tangentMetric (IN V) (V × S3) p u v = G p u v := fun _ _ _ => rfl
  have hB : ∀ y a b, tangentMetric 𝓘(ℝ, V) V y a b = gB ρV Gs y a b := fun _ _ _ => rfl
  have hriem := isRiemannianSubmersionAtPoint_all hρ hGsym hGpos hsl hinv hM hB
  have hf : ContMDiff (IN V) 𝓘(ℝ, V) ((3 : ℕ∞)) (πN ρV) :=
    (contMDiff_πN hρ).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgB : IsContMDiffMetricSection V ((2 : ℕ∞)) (tangentMetric 𝓘(ℝ, V) V) :=
    isContMDiffMetricSection_cmet ((contDiff_gB ρV hGpos hGsm).of_le two_le_top_nat)
  have hsB : IsSymm (tangentMetric 𝓘(ℝ, V) V) := isSymm_cmet_gB' hGsym
  have hpB : IsPosDef (tangentMetric 𝓘(ℝ, V) V) := isPosDef_cmet_gB' hGpos
  have hvert : ∀ β, tsN (Y, 1) (ιv ρV Y β) ∈
      verticalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) := fun β => by
    rw [mem_verticalSpace_iff]
    show dπN ρV Y (KY ρV Y β, β) = 0
    rw [dπN_apply hρ, sub_self]
  have hhor : ∀ w ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1), ∀ β,
      Gs Y w (ιv ρV Y β) = 0 := by
    intro w hw β
    have := (Submodule.mem_orthogonal _ _).1 hw _ (hvert β)
    rw [inner_eq_tangentMetric, hM, hsl] at this
    exact (hGsym Y w (ιv ρV Y β)).trans this
  have hup' : ∀ u v : TangentSpace (IN V) (Y, (1 : S3)),
      u ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) →
      v ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) → LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hsG hpG hgG (Y, 1) u v := fun u v hu hv hli =>
    hup u v (hhor u hu) (hhor v hv) hli
  exact pos_sectionalCurvatureAt_base_of_mem (f := πN ρV) hsG hpG hsB hpB hf hgG hgB
    (isSubmersionAtPoint_πN hρ) hriem Y (Y, 1) (πN_slice Y) hup' a c hac

end Descend

end

end SQ

end ExoticSpheres8And10
