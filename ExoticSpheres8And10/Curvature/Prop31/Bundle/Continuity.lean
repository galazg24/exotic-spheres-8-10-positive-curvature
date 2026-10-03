/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Intrinsic

/-! # The intrinsic curvature norms are continuous

`curvNormSq` and `dcurvNormSq` are continuous on `P`: near any `y₀` they agree with the frame
expression in one fixed frame (`curvNormSq_eq`, `dcurvNormSq_eq`), which is continuous. So on a
compact `P` they are bounded, which gives the constants `M₀`, `M₁` of [HLY] Prop. 3.1.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Cont

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P]
  [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)
  {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)

theorem continuousAt_fsum {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι)
    {F : ι → X → ℝ} {x : X} (hF : ∀ i, ContinuousAt (F i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, F i y) x :=
  tendsto_finset_sum s fun i _ => hF i

namespace S3Connection

include hsg hpg hgs in
theorem continuous_curvNormSq : Continuous (C.curvNormSq g) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  obtain ⟨hb, hUo, he, hor⟩ := frameAt_spec hsg hpg hgs (Pb.proj y₀)
  set U := (frameAt g (Pb.proj y₀)).1
  set e := (frameAt g (Pb.proj y₀)).2
  set b₀ := Pb.proj y₀
  have hW : IsOpen (Pb.proj ⁻¹' (U ∩ Pb.nbhd b₀)) :=
    (hUo.inter (Pb.nbhd_open b₀)).preimage Pb.proj_smooth.continuous
  have hev : (fun y => Prop31Algebra.OmSq (C.ΩP e b₀ y)) =ᶠ[𝓝 y₀] C.curvNormSq g := by
    filter_upwards [hW.mem_nhds ⟨hb, Pb.mem_nbhd b₀⟩] with y hy
    exact C.curvNormSq_eq hsg hpg hgs hUo he hor hy.2 hy.1
  refine ContinuousAt.congr ?_ hev
  have hΩ : ∀ i j a, ContinuousAt (fun y => C.tΩ b₀ e i j a y) y₀ := fun i j a =>
    (C.contMDiffAt_tΩ b₀ (hUo.inter (Pb.nbhd_open b₀)) (fun b' hb' => hb'.2)
      (fun i b' hb' => he i b' hb'.1) ⟨hb, Pb.mem_nbhd b₀⟩ i j a).continuousAt
  simp only [Prop31Algebra.OmSq, ΩP]
  exact continuousAt_fsum _ fun i => continuousAt_fsum _ fun j => continuousAt_fsum _ fun a =>
    (hΩ i j a).pow 2

include hsg hpg hgs in
theorem continuous_dcurvNormSq : Continuous (C.dcurvNormSq g) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  obtain ⟨hb, hUo, he, hor⟩ := frameAt_spec hsg hpg hgs (Pb.proj y₀)
  set U := (frameAt g (Pb.proj y₀)).1
  set e := (frameAt g (Pb.proj y₀)).2
  set b₀ := Pb.proj y₀
  have hUo' : IsOpen (U ∩ Pb.nbhd b₀) := hUo.inter (Pb.nbhd_open b₀)
  have hW : IsOpen (Pb.proj ⁻¹' (U ∩ Pb.nbhd b₀)) := hUo'.preimage Pb.proj_smooth.continuous
  have hy₀ : y₀ ∈ Pb.proj ⁻¹' (U ∩ Pb.nbhd b₀) := ⟨hb, Pb.mem_nbhd b₀⟩
  have hev : (fun y => ∑ k, ∑ i, ∑ j, ∑ c, C.DΩP g e (fun _ => (1 : ℝ)) b₀ y k i j c ^ 2)
      =ᶠ[𝓝 y₀] C.dcurvNormSq g := by
    filter_upwards [hW.mem_nhds hy₀] with y hy
    exact C.dcurvNormSq_eq hsg hpg hgs hUo he hor hy.2 hy.1 _
  refine ContinuousAt.congr ?_ hev
  have he' : ∀ i, ∀ b ∈ U ∩ Pb.nbhd b₀, ContMDiffAt I I.tangent ∞ (T% (e i)) b :=
    fun i b hb' => he i b hb'.1
  have hΩs : ∀ i j a, ∀ y ∈ Pb.proj ⁻¹' (U ∩ Pb.nbhd b₀),
      ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞ (C.tΩ b₀ e i j a) y := fun i j a y hy =>
    C.contMDiffAt_tΩ b₀ hUo' (fun b' hb' => hb'.2) he' hy i j a
  have hΩ : ∀ i j a, ContinuousAt (fun y => C.tΩ b₀ e i j a y) y₀ := fun i j a =>
    (hΩs i j a y₀ hy₀).continuousAt
  have hdΩ : ∀ k i j a, ContinuousAt (fun y => C.dΩP e (fun _ => (1 : ℝ)) b₀ y k i j a) y₀ :=
    fun k i j a =>
      (S3Connection.contMDiffAt_mvfderiv_field
        (Filter.mem_of_superset (hW.mem_nhds hy₀) fun y hy => hΩs i j a y hy)
        (C.contMDiffAt_hlift b₀ hy₀.2 (he k _ hb))).continuousAt
  have hcB : ∀ i j k, ContinuousAt (fun y => tcB (Pb := Pb) g e i j k y) y₀ := fun i j k =>
    ((contMDiffAt_cBb hgs hUo' he' ⟨hb, Pb.mem_nbhd b₀⟩ i j k).comp y₀
      (Pb.proj_smooth y₀)).continuousAt
  have hΓ : ∀ i j k, ContinuousAt (fun y => ΓBf (tcB (Pb := Pb) g e) i j k y) y₀ :=
    fun i j k => (((hcB i j k).sub (hcB i k j)).sub (hcB j k i)).div_const 2
  have hD : ∀ k i j a, ContinuousAt (fun y => C.DΩP g e (fun _ => (1 : ℝ)) b₀ y k i j a) y₀ :=
    fun k i j a => by
      simp only [DΩP, DΩf]
      exact ((hdΩ k i j a).sub (continuousAt_fsum _ fun l => (hΓ k i l).mul (hΩ l j a))).sub
        (continuousAt_fsum _ fun l => (hΓ k j l).mul (hΩ i l a))
  exact continuousAt_fsum _ fun k => continuousAt_fsum _ fun i => continuousAt_fsum _ fun j =>
    continuousAt_fsum _ fun a => (hD k i j a).pow 2

include hsg hpg hgs in
/-- On a compact `P`, `|Ω|` and `|DΩ|` are bounded. -/
theorem exists_curv_bounds [CompactSpace P] :
    ∃ M0 M1 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ (∀ y, C.curvNormSq g y ≤ 2 * M0 ^ 2) ∧
      (∀ y, C.dcurvNormSq g y ≤ 2 * M1 ^ 2) := by
  obtain ⟨C0, hC0⟩ := isCompact_univ.exists_bound_of_continuousOn
    (C.continuous_curvNormSq hsg hpg hgs).continuousOn
  obtain ⟨C1, hC1⟩ := isCompact_univ.exists_bound_of_continuousOn
    (C.continuous_dcurvNormSq hsg hpg hgs).continuousOn
  refine ⟨√(max C0 0), √(max C1 0), Real.sqrt_nonneg _, Real.sqrt_nonneg _, fun y => ?_,
    fun y => ?_⟩
  · have h := hC0 y (mem_univ y)
    rw [Real.norm_eq_abs] at h
    rw [Real.sq_sqrt (le_max_right _ _)]
    have := (le_abs_self _).trans (h.trans (le_max_left C0 0))
    linarith [le_max_right C0 0]
  · have h := hC1 y (mem_univ y)
    rw [Real.norm_eq_abs] at h
    rw [Real.sq_sqrt (le_max_right _ _)]
    have := (le_abs_self _).trans (h.trans (le_max_left C1 0))
    linarith [le_max_right C1 0]

end S3Connection

end Cont

end

end ExoticSpheres8And10
