/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.GaugeSFF

/-! # Infrastructure: metrics pulled back along charts into a vector space

For a smooth `ψ : M → F` with invertible differential, and a smooth field `G` of symmetric
positive definite forms on `F`, the pullback `ψ^*G` is a smooth Riemannian metric on `M`. Its
curvature and second fundamental forms are those of `G`.

* `pullMet G ψ`, `pullMet_apply`;
* `isSymm_pullMet`, `isPosDef_pullMet`, `isContMDiffMetricSection_pullMet`;
* `sectionalCurvatureAt_pullMet`, `sff_pullMet`;
* `mfderiv_opens_val`: the inclusion of an open subset has differential the identity. So
  tangent vectors of `U` and of `M` at the same point are the same vectors of the model.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section OpensVal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem hasMFDerivAt_opens_val (s : TopologicalSpace.Opens M) (y : s) :
    HasMFDerivAt I I (Subtype.val : s → M) y (ContinuousLinearMap.id ℝ E) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have key : ∀ z ∈ (extChartAt I y).target, writtenInExtChartAt I I y Subtype.val z = z := by
    intro z hz
    simp only [extChartAt, OpenPartialHomeomorph.extend_target, mem_inter_iff, mem_preimage,
      mem_range] at hz
    obtain ⟨hz2, w, rfl⟩ := hz
    have h1 : (Subtype.val ∘ (chartAt H y).symm) (I.symm (I w)) =
        (chartAt H y.val).symm (I.symm (I w)) :=
      (chartAt H y.val).subtypeRestr_symm_apply ⟨y⟩ hz2
    simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, comp_apply] at h1 ⊢
    rw [h1, OpenPartialHomeomorph.right_inv _ hz2.1, I.left_inv]
  refine (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq ?_ (key _ (mem_extChartAt_target y))
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) y] with z hz
  exact key z hz

theorem mfderiv_opens_val (s : TopologicalSpace.Opens M) (y : s) :
    mfderiv I I (Subtype.val : s → M) y = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_opens_val s y).mfderiv

end OpensVal

section Pull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

/-- The pullback `ψ^*G`. -/
def pullMet (G : F → F →L[ℝ] F →L[ℝ] ℝ) (ψ : M → F) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
  letI : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  (((G (ψ x)).comp (mfderiv I 𝓘(ℝ, F) ψ x)).flip.comp (mfderiv I 𝓘(ℝ, F) ψ x)).flip

theorem pullMet_apply (G : F → F →L[ℝ] F →L[ℝ] ℝ) (ψ : M → F) (x : M) (v w : TangentSpace I x) :
    pullMet G ψ x v w = G (ψ x) (mfderiv I 𝓘(ℝ, F) ψ x v) (mfderiv I 𝓘(ℝ, F) ψ x w) := rfl

variable {G : F → F →L[ℝ] F →L[ℝ] ℝ} {ψ : M → F}

theorem isSymm_pullMet (hs : ∀ y a b, G y a b = G y b a) : IsSymm (I := I) (pullMet G ψ) :=
  fun x v w => hs _ _ _

theorem isPosDef_pullMet (hp : ∀ y a, a ≠ 0 → 0 < G y a a)
    (hψi : ∀ x, (mfderiv I 𝓘(ℝ, F) ψ x).IsInvertible) : IsPosDef (I := I) (pullMet G ψ) :=
  fun x v hv => by
    rw [pullMet_apply]
    refine hp _ _ fun h0 => hv ?_
    obtain ⟨L, hL⟩ := hψi x
    have : L v = 0 := by rw [← hL] at h0; exact h0
    simpa using congrArg L.symm this

theorem isContMDiffMetricSection_pullMet (hG : ContDiff ℝ ∞ G) (hψ : ContMDiff I 𝓘(ℝ, F) ∞ ψ) :
    IsContMDiffMetricSection E (⊤ : ℕ∞) (pullMet (I := I) G ψ) := by
  refine isContMDiffMetricSection_of_scalars _ fun x V W hV hW => ?_
  have hmn : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ∞ := by simp
  have hV' := contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x) hψ.contMDiffOn
    hmn hV
  have hW' := contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x) hψ.contMDiffOn
    hmn hW
  exact ((hG.contMDiff.comp hψ) x).clm_apply hV' |>.clm_apply hW'

end Pull

end

end ExoticSpheres8And10
