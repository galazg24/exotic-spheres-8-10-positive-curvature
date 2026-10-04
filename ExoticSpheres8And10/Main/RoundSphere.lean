/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Gluing.Charts
import ExoticSpheres8And10.Geometry.Naturality
import ExoticSpheres8And10.Geometry.Stereographic
import ExoticSpheres8And10.Geometry.RoundMetric
import ExoticSpheres8And10.Main.ScalarCurvature

/-! # The round sphere has positive sectional curvature

`Sph n = Metric.sphere (0 : ℝ^{n+1}) 1` with Mathlib's smooth structure, and its **round metric**
`roundMetric n`, the metric induced by the inclusion `Sph n ⊆ ℝ^{n+1}` (pullback of the
Euclidean inner product).

* The inverse stereographic projection `sInv e : e^⊥ → Sph n` is smooth with invertible
  differential.
* It pulls the round metric back to `HR = (1 + ‖y‖²/4)⁻² ⟪·,·⟫` (`inner_dst_dst`).
* `HR` has sectional curvature `1` everywhere (`fibreRm_round_all`).
* Naturality of sectional curvature (`sectionalCurvatureAt_pullback`) then gives
  `sec = 1 > 0` at every point other than `−e`. Using both poles covers the sphere.

**`hasPosCurvMetric_sphere n`** and **`hasPosScalMetric_sphere n`** (`n ≥ 2`): the round sphere
carries a smooth metric of positive sectional, hence positive scalar, curvature.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section RoundSphere

variable (n : ℕ)

instance fact_finrank_euclidean_succ : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The unit sphere `Sⁿ ⊆ ℝ^{n+1}`, with Mathlib's smooth structure. -/
abbrev Sph : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

instance isManifold_Sph : IsManifold (𝓡 n) ∞ (Sph n) := IsManifold.of_le le_top

/-- **The round metric**: the metric induced by `Sⁿ ⊆ ℝ^{n+1}`. -/
def roundMetric : Π x : Sph n, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  pullMet (I := 𝓡 n) (fun _ : EuclideanSpace ℝ (Fin (n + 1)) => innerSL ℝ)
    (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1)))

theorem roundMetric_apply (x : Sph n) (u v : TangentSpace (𝓡 n) x) :
    roundMetric n x u v = (innerSL ℝ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
      (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) Subtype.val x u)
      (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) Subtype.val x v) := rfl

theorem isSymm_roundMetric : IsSymm (roundMetric n) :=
  isSymm_pullMet fun _ a b => by
    rw [innerSL_apply_apply, innerSL_apply_apply]; exact real_inner_comm b a

theorem isPosDef_roundMetric : IsPosDef (roundMetric n) := fun x v hv => by
  set w : EuclideanSpace ℝ (Fin (n + 1)) :=
    mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) Subtype.val x v with hw
  have hw0 : w ≠ 0 := fun h0 => hv (mfderiv_coe_sphere_injective x (h0.trans (map_zero _).symm))
  rw [roundMetric_apply, ← hw, innerSL_apply_apply]
  exact real_inner_self_pos.2 hw0

theorem isContMDiffMetricSection_roundMetric :
    IsContMDiffMetricSection (EuclideanSpace ℝ (Fin n)) ∞ (roundMetric n) :=
  isContMDiffMetricSection_pullMet contDiff_const contMDiff_coe_sphere

variable {n}

/-- The inverse stereographic projection from `−e`, `e^⊥ → Sⁿ`. -/
def sInv {e : EuclideanSpace ℝ (Fin (n + 1))} (he : ‖e‖ = 1) (y : Vs e) : Sph n :=
  ⟨stereoE e y, by rw [mem_sphere_zero_iff_norm]; exact norm_stereo he (inner_Vs_e y)⟩

variable {e : EuclideanSpace ℝ (Fin (n + 1))} (he : ‖e‖ = 1)

theorem contMDiff_sInv : ContMDiff 𝓘(ℝ, Vs e) (𝓡 n) ∞ (sInv he) :=
  ContMDiff.codRestrict_sphere (f := fun y : Vs e => stereoE e (y : EuclideanSpace ℝ (Fin (n + 1))))
    ((contDiff_stereo e).comp (Vs e).subtypeL.contDiff).contMDiff _

omit he in
theorem hasFDerivAt_stereo_coe (y : Vs e) :
    HasFDerivAt (fun y : Vs e => stereoE e (y : EuclideanSpace ℝ (Fin (n + 1))))
      ((dstL e (y : EuclideanSpace ℝ (Fin (n + 1)))).comp (Vs e).subtypeL) y :=
  (hasFDerivAt_stereo e _).comp y (Vs e).subtypeL.hasFDerivAt

/-- `d(ι ∘ sInv) = dst`. -/
theorem mfderiv_val_sInv (y a : Vs e) :
    mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) Subtype.val (sInv he y)
        (mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y a) =
      dst e (y : EuclideanSpace ℝ (Fin (n + 1))) a := by
  have h1 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) Subtype.val (sInv he y) :=
    (contMDiff_coe_sphere (m := ∞) (n := n) (sInv he y)).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y :=
    (contMDiff_sInv he y).mdifferentiableAt (by simp)
  have hc := mfderiv_comp y h1 h2
  have hd : mfderiv 𝓘(ℝ, Vs e) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (Subtype.val ∘ sInv he) y =
      (dstL e (y : EuclideanSpace ℝ (Fin (n + 1)))).comp (Vs e).subtypeL :=
    (hasFDerivAt_stereo_coe y).hasMFDerivAt.mfderiv
  rw [hd] at hc
  have := congrArg (fun L => L a) hc
  exact this.symm

/-- **The round metric pulls back to `HR`.** -/
theorem roundMetric_sInv (y a b : Vs e) :
    roundMetric n (sInv he y) (mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y a)
        (mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y b) = HR y a b := by
  rw [roundMetric_apply, mfderiv_val_sInv, mfderiv_val_sInv, HR_apply, innerSL_apply_apply,
    inner_dst_dst he (inner_Vs_e y) _ _ (inner_Vs_e a) (inner_Vs_e b)]
  rfl

theorem finrank_Vs (he : ‖e‖ = 1) : finrank ℝ (Vs e) = n :=
  Submodule.finrank_orthogonal_span_singleton (fun h => by rw [h, norm_zero] at he; simp at he)

theorem isInvertible_mfderiv_sInv (y : Vs e) :
    (mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y).IsInvertible := by
  set L := mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y
  let L' : Vs e →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (L : TangentSpace 𝓘(ℝ, Vs e) y →ₗ[ℝ] TangentSpace (𝓡 n) (sInv he y))
  have hinj : Injective L' := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 := roundMetric_sInv he y a a
    have ha' : mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y a = 0 := ha
    simp only [ha', map_zero, ContinuousLinearMap.zero_apply, HR_apply] at h1
    have hψ := ψR_pos (y : Vs e)
    have : ⟪a, a⟫ = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hψ.ne'
      · exact h
    exact inner_self_eq_zero.1 this
  have hdim : finrank ℝ (Vs e) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_Vs he, finrank_euclideanSpace_fin]
  exact ⟨(LinearMap.linearEquivOfInjective L' hinj hdim).toContinuousLinearEquiv, by ext1 a; rfl⟩

/-! ### The curvature of `HR` -/

section HRCurv

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

theorem fderiv_ΓR_apply_apply (y u v w : K) :
    fderiv ℝ (fun z => ΓR z v w) y u = fderiv ℝ ΓR y u v w := by
  have hd : HasFDerivAt (ΓR (K := K)) (fderiv ℝ ΓR y) y :=
    ((contDiff_ΓR (K := K)).differentiable (by simp) y).hasFDerivAt
  have h1 := (hd.clm_apply (hasFDerivAt_const v y)).clm_apply (hasFDerivAt_const w y)
  rw [h1.fderiv]
  simp

theorem contDiff2_HR : ContDiff ℝ ((2 : ℕ∞) : ℕ∞ω) (HR (K := K)) :=
  (contDiff_HR (K := K)).of_le two_le_top_nat

/-- **`HR` has sectional curvature `1`**: `Rm(a,b,b,a) = gramDet(a,b)`. -/
theorem riemannTensorAt_HR (y a b : K) :
    riemannTensorAt (isSymm_HR (K := K)) (isPosDef_HR (K := K)).isNondegenerate
        (isContMDiffMetricSection_cmet (contDiff2_HR (K := K)))
        y a b b a =
      HR y a a * HR y b b - HR y a b ^ 2 := by
  have hΓc : ∀ u w : K, ContDiffAt ℝ 1 (fun z => ΓR z u w) y := fun u w =>
    (((contDiff_ΓR (K := K)).clm_apply contDiff_const).clm_apply contDiff_const).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  refine (riemannTensorAt_cmet (G := HR) isSymm_HR isPosDef_HR.isNondegenerate contDiff2_HR
    (Γ := fun z v w => ΓR z v w) HR_ΓR y a b b a (hΓc a b) (hΓc b b)).trans ?_
  rw [fderiv_ΓR_apply_apply, fderiv_ΓR_apply_apply]
  exact fibreRm_round_all y a b

/-- **`HR` has sectional curvature `1`.** -/
theorem sectionalCurvatureAt_HR {y a b : K}
    (hab : LinearIndependent ℝ ![a, b]) :
    sectionalCurvatureAt (isSymm_HR (K := K)) (isPosDef_HR (K := K))
      (isContMDiffMetricSection_cmet (contDiff2_HR (K := K))) y a b = 1 := by
  unfold sectionalCurvatureAt
  rw [riemannTensorAt_HR]
  exact div_self (gramDet_pos (isSymm_HR (K := K)) (isPosDef_HR (K := K)) hab).ne'

end HRCurv

/-! ### Positive curvature -/

theorem sec_pos_at_sInv (y : Vs e) (u v : TangentSpace (𝓡 n) (sInv he y))
    (huv : LinearIndependent ℝ ![u, v]) :
    0 < sectionalCurvatureAt (isSymm_roundMetric n) (isPosDef_roundMetric n)
      (IsContMDiffMetricSection.of_le' (isContMDiffMetricSection_roundMetric n) two_le_infty_ω)
      (sInv he y) u v := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_sInv he y
  set a : Vs e := L.symm u
  set b : Vs e := L.symm v
  have hLa : mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y a = u := by
    rw [← hL]; exact L.apply_symm_apply u
  have hLb : mfderiv 𝓘(ℝ, Vs e) (𝓡 n) (sInv he) y b = v := by
    rw [← hL]; exact L.apply_symm_apply v
  let L' : Vs e →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((L : TangentSpace 𝓘(ℝ, Vs e) y →L[ℝ] TangentSpace (𝓡 n) (sInv he y)) :
      TangentSpace 𝓘(ℝ, Vs e) y →ₗ[ℝ] TangentSpace (𝓡 n) (sInv he y))
  have hab : LinearIndependent ℝ ![a, b] := by
    refine LinearIndependent.of_comp L' ?_
    have : L' ∘ ![a, b] = ![u, v] := by
      funext i; fin_cases i
      · show L (L.symm u) = u; exact L.apply_symm_apply u
      · show L (L.symm v) = v; exact L.apply_symm_apply v
    rw [this]; exact huv
  have hpull := sectionalCurvatureAt_pullback (f := sInv he) (contMDiff_sInv he)
    (isInvertible_mfderiv_sInv he) (fun z c d => (roundMetric_sInv he z c d).symm)
    (isSymm_HR (K := Vs e)) (isPosDef_HR (K := Vs e))
    (isContMDiffMetricSection_cmet (contDiff2_HR (K := Vs e)))
    (isSymm_roundMetric n) (isPosDef_roundMetric n)
    (IsContMDiffMetricSection.of_le' (isContMDiffMetricSection_roundMetric n) two_le_infty_ω) y a b
  rw [hLa, hLb] at hpull
  exact lt_of_lt_of_eq one_pos ((sectionalCurvatureAt_HR (K := Vs e) hab).symm.trans hpull)

omit he in
/-- Every point other than `−e` is `sInv e y`. -/
theorem exists_sInv (he : ‖e‖ = 1) (x : Sph n) (hx : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ -e) :
    ∃ y : Vs e, sInv he y = x := by
  have hxn : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  refine ⟨⟨(2 : ℝ) • stereo e x, stereo_mem_Vs he _⟩, Subtype.ext ?_⟩
  show stereoE e ((2 : ℝ) • stereo e (x : EuclideanSpace ℝ (Fin (n + 1)))) = x
  have h := stereoInv_stereo he hxn (inner_ne_neg_one he hxn hx)
  set v := stereo e (x : EuclideanSpace ℝ (Fin (n + 1)))
  rw [← h]
  have hn : ‖(2 : ℝ) • v‖ ^ 2 = 4 * ‖v‖ ^ 2 := by rw [norm_smul, Real.norm_two]; ring
  have hD : (1 : ℝ) + ‖v‖ ^ 2 ≠ 0 := by positivity
  have hD4 : (4 : ℝ) + 4 * ‖v‖ ^ 2 ≠ 0 := by positivity
  rw [stereoE, stereoInv, hn]
  simp only [smul_add, smul_smul]
  congr 1 <;> congr 1 <;> (field_simp; try ring)

/-- **The round sphere has positive sectional curvature.** -/
theorem hasPosCurvMetric_sphere (n : ℕ) : HasPosCurvMetric (𝓡 n) (Sph n) := by
  refine ⟨roundMetric n, isSymm_roundMetric n, isPosDef_roundMetric n,
    isContMDiffMetricSection_roundMetric n, fun x u v huv => ?_⟩
  set e0 : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hne0 : ‖-e0‖ = 1 := by rw [norm_neg]; exact he0
  by_cases hx : (x : EuclideanSpace ℝ (Fin (n + 1))) = -e0
  · have hx' : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ - -e0 := by
      rw [hx, neg_neg]
      intro h
      have h1 := congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w 0) h
      simp [e0] at h1
      norm_num at h1
    obtain ⟨y, rfl⟩ := exists_sInv hne0 x hx'
    exact sec_pos_at_sInv hne0 y u v huv
  · obtain ⟨y, rfl⟩ := exists_sInv he0 x hx
    exact sec_pos_at_sInv he0 y u v huv

/-- **The round sphere has positive scalar curvature** (`n ≥ 2`). -/
theorem hasPosScalMetric_sphere {n : ℕ} (hn : 2 ≤ n) : HasPosScalMetric (𝓡 n) (Sph n) :=
  HasPosCurvMetric.hasPosScalMetric (𝓡 n) (Sph n) (by rw [finrank_euclideanSpace_fin]; exact hn)
    (hasPosCurvMetric_sphere n)

end RoundSphere

end

end ExoticSpheres8And10
