/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Northern.QuotientSubmersion
import ExoticSpheres8And10.Curvature.ONeill
import ExoticSpheres8And10.Geometry.Coordinates

/-! # §4: the northern orbit map `(V × S³, G_N) → (V, g_B)` is a Riemannian submersion

* `isRiemannianSubmersionAtPoint_πN_slice`: at the slice points `(Y, 1)`, by the explicit
  horizontal lift of `S4_NorthSub`;
* `isRiemannianSubmersionAtPoint_πN`: at every point, by equivariance (`RiemannianGeometry`'s
  `isRiemannianSubmersionAtPoint_of_isometry` with `φ = u⁻¹ ⋆ ·`, `ψ = id`);
* `isSubmersionAtPoint_πN`, `surjective_πN`;
* `pos_sectionalCurvatureAt_base_of_mem`: O'Neill, needing positivity upstairs only on the
  horizontal planes at **one** point of the fibre;
* `northQuot_sectionalCurvature_pos`: **positive curvature of `g_B` at `Y`** from positive
  curvature of `G_N` on the horizontal planes at `(Y, 1)`. Instance-free statement.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### O'Neill with positivity at one point of the fibre -/

section General

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]

/-- **O'Neill, pointwise.** If `K_M > 0` on the horizontal planes at one point `p` over `b`, then
`K_B > 0` on every plane at `b`. -/
theorem pos_sectionalCurvatureAt_base_of_mem {f : M → B}
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z) (b : B) (p : M) (hp : f p = b)
    (hM : ∀ u v : TangentSpace I p, u ∈ horizontalSpace I J f p →
      v ∈ horizontalSpace I J f p → LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hsymmM hposM hgM p u v)
    (a c : TangentSpace J b) (hac : LinearIndependent ℝ ![a, c]) :
    0 < sectionalCurvatureAt hsymmB hposB hgB b a c := by
  subst hp
  have hu := horizontalLift_mem (hsub p) a
  have hv := horizontalLift_mem (hsub p) c
  have hua : mfderiv I J f p (horizontalLift (hsub p) a) = a := horizontalLift_spec (hsub p) a
  have hvc : mfderiv I J f p (horizontalLift (hsub p) c) = c := horizontalLift_spec (hsub p) c
  have hli : LinearIndependent ℝ ![horizontalLift (hsub p) a, horizontalLift (hsub p) c] := by
    have hcomp : (mfderiv I J f p : TangentSpace I p →L[ℝ] TangentSpace J (f p)).toLinearMap ∘
        ![horizontalLift (hsub p) a, horizontalLift (hsub p) c] = ![a, c] := by
      ext i
      fin_cases i
      · exact hua
      · exact hvc
    exact LinearIndependent.of_comp _ (by rw [hcomp]; exact hac)
  have := pos_sectionalCurvatureAt_of_pos_of_mem_horizontalSpace hsymmM hposM hsymmB hposB hf
    hgM hgB hsub hriem hu hv hli (hM _ _ hu hv hli)
  rwa [hua, hvc] at this

end General

/-! ### The northern orbit map -/

section North

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))
  {δ : ℝ} {rt : V → ℝ}

/-- A vector of `V × ℝ³` as a tangent vector at `p` (an identity cast). -/
def tsN (p : V × S3) (x : V × E3) : TangentSpace (IN V) p := x

include hρ in
theorem dπN_eq (Y : V) : dπN ρV Y = dπl ρV Y := by
  refine ContinuousLinearMap.ext fun u => ?_
  exact dπN_apply hρ Y u.1 u.2

theorem πN_slice (Y : V) : πN ρV (Y, 1) = Y := by
  show ρV 1⁻¹ Y = Y
  rw [inv_one, ρV_one_apply]

include hρ in
theorem isSubmersionAtPoint_πN (p : V × S3) : IsSubmersionAtPoint (IN V) 𝓘(ℝ, V) (πN ρV) p := by
  have hs : ContMDiff 𝓘(ℝ, V) (IN V) ∞ fun y : V => (ρV p.2 y, p.2) :=
    (((ρV p.2 : V ≃L[ℝ] V) : V →L[ℝ] V).contDiff.contMDiff).prodMk contMDiff_const
  refine isSubmersionAtPoint_of_section (s := fun y : V => (ρV p.2 y, p.2))
    ((contMDiff_πN hρ p).mdifferentiableAt (by simp)) ((hs _).mdifferentiableAt (by simp)) ?_ ?_
  · show (ρV p.2 (ρV p.2⁻¹ p.1), p.2) = p
    rw [show ρV p.2 (ρV p.2⁻¹ p.1) = (ρV p.2 * ρV p.2⁻¹) p.1 from rfl, ← map_mul,
      mul_inv_cancel, map_one]
    rfl
  · refine Eventually.of_forall fun y => ?_
    show ρV p.2⁻¹ (ρV p.2 y) = y
    rw [show ρV p.2⁻¹ (ρV p.2 y) = (ρV p.2⁻¹ * ρV p.2) y from rfl, ← map_mul, inv_mul_cancel,
      map_one]
    rfl

theorem surjective_πN : Surjective (πN ρV) := fun y => ⟨(y, 1), πN_slice y⟩

variable [Bundle.RiemannianBundle (TangentSpace (IN V) : V × S3 → Type)]
  [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, V) : V → Type)]

include hρ in
/-- **`πN` is a Riemannian submersion at the slice points.** -/
theorem isRiemannianSubmersionAtPoint_πN_slice (hrt0 : ∀ Y, rt Y ≠ 0)
    (hM : ∀ p u v, tangentMetric (IN V) (V × S3) p u v = northMetric δ rt p u v)
    (hB : ∀ y a b, tangentMetric 𝓘(ℝ, V) V y a b = gB ρV δ rt y a b) (Y : V) :
    IsRiemannianSubmersionAtPoint (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) := by
  have hvert : ∀ β, tsN (Y, 1) (ιv ρV Y β) ∈
      verticalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) := fun β => by
    rw [mem_verticalSpace_iff]
    show dπN ρV Y (KY ρV Y β, β) = 0
    rw [dπN_apply hρ, sub_self]
  have hhor : ∀ w ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1), ∀ β,
      Gs δ rt Y w (ιv ρV Y β) = 0 := by
    intro w hw β
    have := (Submodule.mem_orthogonal _ _).1 hw _ (hvert β)
    rw [inner_eq_tangentMetric, hM, northMetric_slice] at this
    exact (Gs_symm δ rt Y w (ιv ρV Y β)).trans this
  intro u hu v hv
  rw [inner_eq_tangentMetric, inner_eq_tangentMetric, hB, hM, northMetric_slice]
  show gB ρV δ rt (πN ρV (Y, 1)) (dπN ρV Y u) (dπN ρV Y v) = _
  rw [πN_slice, dπN_eq hρ]
  calc gB ρV δ rt Y (dπl ρV Y u) (dπl ρV Y v)
      = Gs δ rt Y (hlift ρV δ rt Y (dπl ρV Y u)) (hlift ρV δ rt Y (dπl ρV Y v)) := rfl
    _ = Gs δ rt Y u v := by
      rw [← eq_hlift ρV δ hrt0 Y (hhor u hu), ← eq_hlift ρV δ hrt0 Y (hhor v hv)]

include hρ in
/-- **`πN` is a Riemannian submersion at every point**, by equivariance. -/
theorem isRiemannianSubmersionAtPoint_πN (hrt0 : ∀ Y, rt Y ≠ 0)
    (hrtρ : ∀ q Y, rt (ρV q Y) = rt Y)
    (hM : ∀ p u v, tangentMetric (IN V) (V × S3) p u v = northMetric δ rt p u v)
    (hB : ∀ y a b, tangentMetric 𝓘(ℝ, V) V y a b = gB ρV δ rt y a b) (p : V × S3) :
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
    exact northMetric_starN hρ hrtρ _ p u v
  have hψiso : ∀ a b : TangentSpace 𝓘(ℝ, V) (πN ρV p),
      inner ℝ (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) id (πN ρV p) a)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) id (πN ρV p) b) = inner ℝ a b := fun a b => by
    rw [mfderiv_id]; rfl
  have hR : IsRiemannianSubmersionAtPoint (IN V) 𝓘(ℝ, V) (πN ρV) (starN ρV p.2⁻¹ p) := by
    have e : starN ρV p.2⁻¹ p = (ρV p.2⁻¹ p.1, 1) := by
      show (ρV p.2⁻¹ p.1, p.2⁻¹ * p.2) = _
      rw [inv_mul_cancel]
    rw [e]
    exact isRiemannianSubmersionAtPoint_πN_slice hρ hrt0 hM hB _
  exact isRiemannianSubmersionAtPoint_of_isometry hfφ (hπ p) (hπ _) hφ mdifferentiableAt_id hiso
    hψiso hR

end North

/-! ### Positive curvature descends to `(V, g_B)` -/

section Descend

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))
  {δ : ℝ} {rt : V → ℝ}

theorem isSymm_cmet_gB : IsSymm (cmet (gB ρV δ rt)) := fun y a b => gB_symm ρV δ y a b

theorem isPosDef_cmet_gB (hrt0 : ∀ Y, rt Y ≠ 0) : IsPosDef (cmet (gB ρV δ rt)) :=
  fun y a ha => gB_pos ρV δ hrt0 y ha

theorem two_le_top_nat : ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top

include hρ in
/-- **Positive curvature of the northern quotient metric.** If [GG]'s northern metric `G_N` has
positive curvature on the horizontal planes at `(Y, 1)` (horizontal: `G_N`-orthogonal to the
star orbit, `G(u, (K_Y β, β)) = 0`), then `g_B` has positive curvature at `Y`. -/
theorem northQuot_sectionalCurvature_pos (hrt0 : ∀ Y, rt Y ≠ 0) (hrt : ContDiff ℝ ∞ rt)
    (hrtρ : ∀ q Y, rt (ρV q Y) = rt Y) (Y : V)
    (hup : ∀ u v : TangentSpace (IN V) (Y, (1 : S3)), (∀ β, Gs δ rt Y u (ιv ρV Y β) = 0) →
      (∀ β, Gs δ rt Y v (ιv ρV Y β) = 0) → LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt (isSymm_northMetric δ rt) (isPosDef_northMetric δ hrt0)
        (isContMDiffMetricSection_northMetric hrt 2) (Y, 1) u v)
    (a c : TangentSpace 𝓘(ℝ, V) Y) (hac : LinearIndependent ℝ ![a, c]) :
    0 < sectionalCurvatureAt isSymm_cmet_gB (isPosDef_cmet_gB hrt0)
      (isContMDiffMetricSection_cmet ((contDiff_gB ρV δ hrt0 hrt).of_le two_le_top_nat)) Y a c := by
  let instM : Bundle.RiemannianBundle (TangentSpace (IN V) : V × S3 → Type) :=
    ⟨(toContMDiffRiemannianMetric (n := ∞) (isSymm_northMetric δ rt) (isPosDef_northMetric δ hrt0)
      (isContMDiffMetricSection_northMetric hrt ⊤)).toRiemannianMetric⟩
  let instB : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, V) : V → Type) :=
    ⟨(toContMDiffRiemannianMetric (n := ∞) (isSymm_cmet_gB (ρV := ρV) (δ := δ) (rt := rt))
      (isPosDef_cmet_gB hrt0)
      (isContMDiffMetricSection_cmet (contDiff_gB ρV δ hrt0 hrt))).toRiemannianMetric⟩
  have hM : ∀ p u v, tangentMetric (IN V) (V × S3) p u v = northMetric δ rt p u v :=
    fun _ _ _ => rfl
  have hB : ∀ y a b, tangentMetric 𝓘(ℝ, V) V y a b = gB ρV δ rt y a b := fun _ _ _ => rfl
  have hriem := isRiemannianSubmersionAtPoint_πN hρ hrt0 hrtρ hM hB
  have hf : ContMDiff (IN V) 𝓘(ℝ, V) ((3 : ℕ∞)) (πN ρV) :=
    (contMDiff_πN hρ).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgB : IsContMDiffMetricSection V ((2 : ℕ∞)) (tangentMetric 𝓘(ℝ, V) V) :=
    isContMDiffMetricSection_cmet ((contDiff_gB ρV δ hrt0 hrt).of_le two_le_top_nat)
  have hgM : IsContMDiffMetricSection (V × E3) ((2 : ℕ∞)) (tangentMetric (IN V) (V × S3)) :=
    isContMDiffMetricSection_northMetric hrt 2
  have hsB : IsSymm (tangentMetric 𝓘(ℝ, V) V) := isSymm_cmet_gB
  have hpB : IsPosDef (tangentMetric 𝓘(ℝ, V) V) := isPosDef_cmet_gB hrt0
  have hsM : IsSymm (tangentMetric (IN V) (V × S3)) := isSymm_northMetric δ rt
  have hpM : IsPosDef (tangentMetric (IN V) (V × S3)) := isPosDef_northMetric δ hrt0
  have hvert : ∀ β, tsN (Y, 1) (ιv ρV Y β) ∈
      verticalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) := fun β => by
    rw [mem_verticalSpace_iff]
    show dπN ρV Y (KY ρV Y β, β) = 0
    rw [dπN_apply hρ, sub_self]
  have hhor : ∀ w ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1), ∀ β,
      Gs δ rt Y w (ιv ρV Y β) = 0 := by
    intro w hw β
    have := (Submodule.mem_orthogonal _ _).1 hw _ (hvert β)
    rw [inner_eq_tangentMetric, hM, northMetric_slice] at this
    exact (Gs_symm δ rt Y w (ιv ρV Y β)).trans this
  have hup' : ∀ u v : TangentSpace (IN V) (Y, (1 : S3)),
      u ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) →
      v ∈ horizontalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) → LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hsM hpM hgM (Y, 1) u v := fun u v hu hv hli =>
    hup u v (hhor u hu) (hhor v hv) hli
  have key := pos_sectionalCurvatureAt_base_of_mem (f := πN ρV) hsM hpM hsB hpB hf hgM hgB
    (isSubmersionAtPoint_πN hρ) hriem Y (Y, 1) (πN_slice Y) hup' a c hac
  exact key

end Descend

end

end ExoticSpheres8And10
