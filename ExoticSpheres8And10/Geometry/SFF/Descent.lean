/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.SFF.Warped
import RiemannianGeometry.ONeillLemmaOne

/-! # O'Neill: the second fundamental form of a quotient boundary

For a Riemannian submersion `f : M → B` and `h : B → ℝ`:

* `gradAt_comp_submersion`: `grad_M (h ∘ f) = (grad_B h)ᴴ`;
* `unitNormal_comp_submersion`: `ν_M (h ∘ f) = (ν_B h)ᴴ`;
* **`sff_submersion`**: `sff_B h (Y, Y) = sff_M (h ∘ f)(Yᴴ, Yᴴ)`.

This is [D]'s "The second fundamental form of a quotient boundary is the source second
fundamental form restricted to star-horizontal lifts". It follows from O'Neill's Lemma 1(3), that
`𝓗∇_{Y₁ᴴ}Y₂ᴴ = (∇*_{Y₁}Y₂)ᴴ` (`RiemannianGeometry` `horizontalProjection_leviCivita_horizontalLiftField`), and
from Lemma 1(1).
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff

noncomputable section

section Descend

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [Bundle.RiemannianBundle (TangentSpace J : B → Type _)]
  {f : M → B}

theorem isNondegenerate_tangentMetric' : IsNondegenerate (tangentMetric I M) :=
  fun p => tangentMetric_nondegenerate I M p

theorem gradAt_comp_submersion {h : B → ℝ} {z : M} (hh : MDiffAt h (f z)) (hf : MDiffAt f z) :
    gradAt isNondegenerate_tangentMetric' (h ∘ f) z =
      horizontalLiftField I J f (gradAt isNondegenerate_tangentMetric' h) z := by
  symm
  refine eq_gradAt _ _ z fun w => ?_
  rw [horizontalLiftField, mfderivAdjoint_spec (tangentMetric_nondegenerate I M z), g_gradAt,
    mvfderiv_comp' hh hf]

theorem unitNormal_comp_submersion {h : B → ℝ} {z : M} (hsub : IsSubmersionAtPoint I J f z)
    (hriem : IsRiemannianSubmersionAtPoint I J f z) (hh : MDiffAt h (f z)) (hf : MDiffAt f z) :
    unitNormal isNondegenerate_tangentMetric' (h ∘ f) z =
      horizontalLiftField I J f (unitNormal isNondegenerate_tangentMetric' h) z := by
  simp only [unitNormal]
  rw [gradAt_comp_submersion hh hf, tangentMetric_horizontalLiftField_apply hsub hriem]
  simp only [horizontalLiftField, unitNormal, map_smul]

/-- **The second fundamental form descends**: for a base field `Y₁` with `Y₁(f p) = Y`,
`sff_B h (Y, Y) = sff_M (h ∘ f)(Yᴴ, Yᴴ)`. -/
theorem sff_submersion {n : ℕ∞} (hn : minSmoothness ℝ 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hf : ContMDiff I J ((n + 1 : ℕ∞)) f)
    (hgM : IsContMDiffMetricSection E ((n : ℕ∞ω)) (tangentMetric I M))
    (hgB : IsContMDiffMetricSection E' ((n : ℕ∞ω)) (tangentMetric J B))
    (hsub : ∀ z, IsSubmersionAtPoint I J f z)
    (hriem : ∀ z, IsRiemannianSubmersionAtPoint I J f z) {h : B → ℝ}
    (hh : ∀ z, MDiffAt h (f z)) {p : M} {Y₁ : Π q : B, TangentSpace J q}
    (hY₁ : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω)) (T% Y₁) q)
    (hν : ∀ᶠ q in 𝓝 (f p), ContMDiffAt J J.tangent ((n : ℕ∞ω))
      (T% (unitNormal (isNondegenerate_tangentMetric' (I := J) (M := B)) h)) q) :
    sff isNondegenerate_tangentMetric' h (f p) (Y₁ (f p)) (Y₁ (f p)) =
      sff isNondegenerate_tangentMetric' (h ∘ f) p (horizontalLiftField I J f Y₁ p)
        (horizontalLiftField I J f Y₁ p) := by
  have hfd : ∀ z, MDiffAt f z := fun z => (hf z).mdifferentiableAt (by simp)
  have eν : unitNormal isNondegenerate_tangentMetric' (h ∘ f) =
      horizontalLiftField I J f (unitNormal isNondegenerate_tangentMetric' h) :=
    funext fun z => unitNormal_comp_submersion (hsub z) (hriem z) (hh z) (hfd z)
  unfold sff
  rw [eν]
  set L := leviCivita (tangentMetric I M)
    (horizontalLiftField I J f (unitNormal isNondegenerate_tangentMetric' h)) p
    (horizontalLiftField I J f Y₁ p)
  have hd : horizontalProjection I J f p L + verticalProjection I J f p L = L :=
    horizontalProjection_add_verticalProjection L
  have h3 := horizontalProjection_leviCivita_horizontalLiftField hn hn' hf hgM hgB
    (Eventually.of_forall hsub) (Eventually.of_forall hriem) hY₁ hν
  rw [← hd, map_add, ContinuousLinearMap.add_apply, h3,
    isSymm_tangentMetric p (verticalProjection I J f p L),
    tangentMetric_eq_zero_of_mem_horizontalSpace_of_mem_verticalSpace
      (horizontalLiftField_mem p) (verticalProjection_mem L), add_zero,
    tangentMetric_horizontalLiftField_apply (hsub p) (hriem p)]

end Descend

end

end ExoticSpheres8And10
