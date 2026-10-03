/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.ONeillPositiveCurvature
import ExoticSpheres8And10.PolarBundles.StarQuotient

/-! # §4: O'Neill's formula for the star quotients

[D] §4 twice concludes positive curvature of a quotient from positive curvature upstairs. In the
south: "The star action is free and isometric, so the quotient map `(P_S, G_S) → (D_S, g_S)` is a
Riemannian submersion. O'Neill's formula therefore gives `sec_{g_S} > 0`." In the north:
"every star-horizontal two-plane has positive sectional-curvature numerator … O'Neill's formula
gives a metric `g_N` on `D_N` with `sec_{g_N} > 0`."

O'Neill's horizontal curvature formula, `K_M(u,v) ≤ K_B(dπu, dπv)` on horizontal planes, is
proved in the library `RiemannianGeometry` (see `NOTICE`). There it is `pos_sectionalCurvatureAt_of_pos_of_mem_horizontalSpace`,
one plane at a time. This file supplies the two remaining steps.

* `isSubmersionAtPoint_of_section`: a map with a smooth local section through `p` is a
  submersion at `p`;
* `pos_sectionalCurvatureAt_base`: **positivity of the base.** If `f` is a surjective
  Riemannian submersion and `K_M > 0` on every horizontal 2-plane, then `K_B > 0` on every
  2-plane. Every independent pair downstairs is the image of an independent horizontal pair;
  `RiemannianGeometry` records this step as missing;
* `orbitMap_isSubmersion`: the star quotient map `P_θ → P_θ/S³_⋆` is a submersion everywhere,
  through the local sections `y ↦ u ⋆ ι(chart(y), 1)`;
* `quotSpace_pos_sectionalCurvature`: **[D]'s O'Neill step for the star quotient.** For any
  metrics on `P_θ` and on `P_θ/S³_⋆` making `orbitMap` a Riemannian submersion, positive
  curvature on star-horizontal planes gives positive sectional curvature of the quotient.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Set Function Filter Topology Module Quaternion

open scoped Manifold ContDiff

noncomputable section

section General

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

/-- **A map with a differentiable local section through `p` is a submersion at `p`.** -/
theorem isSubmersionAtPoint_of_section {f : M → B} {s : B → M} {p : M}
    (hf : MDifferentiableAt I J f p) (hs : MDifferentiableAt J I s (f p)) (hsp : s (f p) = p)
    (hfs : f ∘ s =ᶠ[𝓝 (f p)] id) : IsSubmersionAtPoint I J f p := by
  have hf' : MDifferentiableAt I J f (s (f p)) := by rw [hsp]; exact hf
  have h1 := mfderiv_comp (f p) hf' hs
  rw [hfs.mfderiv_eq, mfderiv_id] at h1
  have key : Surjective (mfderiv I J f (s (f p))) := fun v =>
    ⟨mfderiv J I s (f p) v, by
      have := congrArg (fun L => L v) h1
      exact this.symm⟩
  unfold IsSubmersionAtPoint
  rw [hsp] at key
  exact key

variable [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]

/-- **Positive curvature descends through a surjective Riemannian submersion.** If `K_M > 0` on
every horizontal 2-plane, then `K_B > 0` on every 2-plane of `B`. -/
theorem pos_sectionalCurvatureAt_base {f : M → B}
    (hsymmM : IsSymm (tangentMetric I M)) (hposM : IsPosDef (tangentMetric I M))
    (hsymmB : IsSymm (tangentMetric J B)) (hposB : IsPosDef (tangentMetric J B))
    (hf : ContMDiff I J ((3 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((2 : ℕ∞)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((2 : ℕ∞)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z) (hsurj : Surjective f)
    (hM : ∀ (p : M) (u v : TangentSpace I p), u ∈ horizontalSpace I J f p →
      v ∈ horizontalSpace I J f p → LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hsymmM hposM hgM p u v)
    (b : B) (a c : TangentSpace J b) (hac : LinearIndependent ℝ ![a, c]) :
    0 < sectionalCurvatureAt hsymmB hposB hgB b a c := by
  obtain ⟨p, rfl⟩ := hsurj b
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
    hgM hgB hsub hriem hu hv hli (hM p _ _ hu hv hli)
  rwa [hua, hvc] at this

end General

/-! ### The star quotient map is a submersion -/

section Star

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

local notation "S3" => Metric.sphere (0 : ℍ[ℝ]) 1

namespace PolarData

variable (D : PolarData (m := m) e)

theorem starM_Ψ (a : M0 e) : D.starM a.2 (D.Ψ a, 1) = a := by
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (mul_one _)
  show D.ρ a.2 (D.ρ a.2⁻¹ ((a.1 : Metric.sphere (0 : W) 1) : W)) = _
  rw [D.ρ_mul_apply, mul_inv_cancel, map_one]; rfl

/-- **The star quotient map is a submersion at every point.** -/
theorem orbitMap_isSubmersion (p : PolarBundle D) :
    IsSubmersionAtPoint (IP m) (𝓡 (m + 1)) D.orbitMap p := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  haveI := nonempty_M0 (e := e)
  have hfm : MDifferentiableAt (IP m) (𝓡 (m + 1)) D.orbitMap p :=
    (D.contMDiff_orbitMap p).mdifferentiableAt (by simp)
  have hstar : ∀ u : S3, ContMDiff (IP m) (IP m) ∞ fun x : PolarBundle D => u • x := fun u =>
    D.contMDiff_star.comp (contMDiff_const.prodMk contMDiff_id)
  rcases ι_cover D.κP p with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · -- `p = ι₁ a`, section `y ↦ a.2 ⋆ ι₁(chart₁ y, 1)`
    set s : QuotSpace D → PolarBundle D := fun y => a.2 • ι₁ D.κP (chart₁ D.κS y, (1 : S3))
    have hy : D.orbitMap (ι₁ D.κP a) ∈ range (ι₁ D.κS) := ⟨_, rfl⟩
    have hs : MDifferentiableAt (𝓡 (m + 1)) (IP m) s (D.orbitMap (ι₁ D.κP a)) := by
      have h1 := contMDiffAt_chart₁ (𝓡 (m + 1)) D.hκS D.hκSs hy
      have h2 : ContMDiffAt (𝓡 (m + 1)) (IP m) ∞
          (fun y => ((chart₁ D.κS y, (1 : S3)) : M0 e)) (D.orbitMap (ι₁ D.κP a)) :=
        h1.prodMk contMDiffAt_const
      exact (((hstar a.2).contMDiffAt.comp _
        ((contMDiff_ι₁ (IP m) D.hκP D.hκPs).contMDiffAt.comp _ h2))).mdifferentiableAt
        (by simp)
    refine isSubmersionAtPoint_of_section hfm hs ?_ ?_
    · show a.2 • ι₁ D.κP (chart₁ D.κS (ι₁ D.κS (D.Ψ a)), (1 : S3)) = ι₁ D.κP a
      rw [chart₁_ι₁]
      show D.star a.2 (ι₁ D.κP (D.Ψ a, 1)) = _
      rw [star_ι₁, D.starM_Ψ]
    · filter_upwards [(isOpenEmbedding_ι₁ D.κS).isOpen_range.mem_nhds hy] with y hy'
      show D.orbitMap (a.2 • ι₁ D.κP (chart₁ D.κS y, (1 : S3))) = y
      rw [D.orbitMap_star, orbitMap_ι₁, D.Ψ_one, ι₁_chart₁ D.κS hy']
  · -- `p = ι₂ b`, section `y ↦ b.2 ⋆ ι₂(chart₂ y, 1)`
    set s : QuotSpace D → PolarBundle D := fun y => b.2 • ι₂ D.κP (chart₂ D.κS y, (1 : S3))
    have hy : D.orbitMap (ι₂ D.κP b) ∈ range (ι₂ D.κS) := ⟨_, rfl⟩
    have hs : MDifferentiableAt (𝓡 (m + 1)) (IP m) s (D.orbitMap (ι₂ D.κP b)) := by
      have h1 := contMDiffAt_chart₂ (𝓡 (m + 1)) D.hκS D.hκSs hy
      have h2 : ContMDiffAt (𝓡 (m + 1)) (IP m) ∞
          (fun y => ((chart₂ D.κS y, (1 : S3)) : M0 e)) (D.orbitMap (ι₂ D.κP b)) :=
        h1.prodMk contMDiffAt_const
      exact (((hstar b.2).contMDiffAt.comp _
        ((contMDiff_ι₂ (IP m) D.hκP D.hκPs).contMDiffAt.comp _ h2))).mdifferentiableAt
        (by simp)
    refine isSubmersionAtPoint_of_section hfm hs ?_ ?_
    · show b.2 • ι₂ D.κP (chart₂ D.κS (ι₂ D.κS (D.Ψ b)), (1 : S3)) = ι₂ D.κP b
      rw [chart₂_ι₂]
      show D.star b.2 (ι₂ D.κP (D.Ψ b, 1)) = _
      rw [star_ι₂, D.starM_Ψ]
    · filter_upwards [(isOpenEmbedding_ι₂ D.κS).isOpen_range.mem_nhds hy] with y hy'
      show D.orbitMap (b.2 • ι₂ D.κP (chart₂ D.κS y, (1 : S3))) = y
      rw [D.orbitMap_star, orbitMap_ι₂, D.Ψ_one, ι₂_chart₂ D.κS hy']

variable [Bundle.RiemannianBundle (TangentSpace (IP m) : PolarBundle D → Type _)]
  [Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : QuotSpace D → Type _)]

/-- **[D]'s O'Neill step for the star quotient.** Let `P_θ` and `P_θ/S³_⋆` carry `C²`
Riemannian metrics for which the star quotient map is a Riemannian submersion (the quotient
metric of a free isometric star action). If the sectional curvature of `P_θ` is positive on every
star-horizontal 2-plane, then `P_θ/S³_⋆` has positive sectional curvature on every 2-plane. -/
theorem quotSpace_pos_sectionalCurvature
    (hsymmP : IsSymm (tangentMetric (IP m) (PolarBundle D)))
    (hposP : IsPosDef (tangentMetric (IP m) (PolarBundle D)))
    (hsymmQ : IsSymm (tangentMetric (𝓡 (m + 1)) (QuotSpace D)))
    (hposQ : IsPosDef (tangentMetric (𝓡 (m + 1)) (QuotSpace D)))
    (hgP : IsContMDiffMetricSection (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin 3))
      ((2 : ℕ∞)) (tangentMetric (IP m) (PolarBundle D)))
    (hgQ : IsContMDiffMetricSection (EuclideanSpace ℝ (Fin (m + 1))) ((2 : ℕ∞))
      (tangentMetric (𝓡 (m + 1)) (QuotSpace D)))
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint (IP m) (𝓡 (m + 1)) D.orbitMap z)
    (hP : ∀ (p : PolarBundle D) (u v : TangentSpace (IP m) p),
      u ∈ horizontalSpace (IP m) (𝓡 (m + 1)) D.orbitMap p →
      v ∈ horizontalSpace (IP m) (𝓡 (m + 1)) D.orbitMap p → LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hsymmP hposP hgP p u v)
    (y : QuotSpace D) (a c : TangentSpace (𝓡 (m + 1)) y) (hac : LinearIndependent ℝ ![a, c]) :
    0 < sectionalCurvatureAt hsymmQ hposQ hgQ y a c :=
  pos_sectionalCurvatureAt_base hsymmP hposP hsymmQ hposQ
    (D.contMDiff_orbitMap.of_le (by exact_mod_cast le_top)) hgP hgQ D.orbitMap_isSubmersion hriem
    D.orbitMap_surjective hP y a c hac

end PolarData

end Star

end

end ExoticSpheres8And10
