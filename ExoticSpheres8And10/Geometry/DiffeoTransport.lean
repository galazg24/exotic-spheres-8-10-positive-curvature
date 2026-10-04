/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.Naturality
import ExoticSpheres8And10.Geometry.Pullback
import ExoticSpheres8And10.Geometry.SFF.LevelSets

/-! # Positive sectional curvature is invariant under diffeomorphisms

For a `C^∞` diffeomorphism `φ : M → N` and a smooth metric `g` on `N`, the pullback
`φ^* g = g(dφ ·, dφ ·)` is a smooth metric on `M` with the same sectional curvatures
(`sectionalCurvatureAt_pullback`). Hence a smooth metric of positive sectional curvature on `N`
gives one on `M`:

* **`HasPosCurvMetric.of_diffeomorph`**: `M ≃ₘ N → HasPosCurvMetric N → HasPosCurvMetric M`.

This is the step that carries a metric built on one smooth model of a manifold to every smooth
manifold diffeomorphic to it. A homeomorphism would not do: the differential `dφ` is what pulls
the metric back.

* `pullbackForm φ g`, `pullbackForm_apply`: the pullback of a field of bilinear forms;
* `isSymm_pullbackForm`, `isPosDef_pullbackForm`, `isContMDiffMetricSection_pullbackForm`;
* `mpullback_symm_apply_self`: pulling a vector field back along `φ⁻¹` is pushing it forward
  along `φ`, `(φ⁻¹)^* V (φ y) = dφ_y (V y)`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section Transport

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- The pullback `φ^* g` of a field of bilinear forms along `φ : M → N`. -/
def pullbackForm (φ : M → N) (g : Π y : N, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
  letI : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  letI : NormedAddCommGroup (TangentSpace I (φ x)) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I (φ x)) := inferInstanceAs (NormedSpace ℝ E)
  (((g (φ x)).comp (mfderiv I I φ x)).flip.comp (mfderiv I I φ x)).flip

theorem pullbackForm_apply (φ : M → N)
    (g : Π y : N, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (x : M)
    (u v : TangentSpace I x) :
    pullbackForm φ g x u v = g (φ x) (mfderiv I I φ x u) (mfderiv I I φ x v) := rfl

variable {φ : M → N} {g : Π y : N, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}

theorem isSymm_pullbackForm (hs : IsSymm g) : IsSymm (pullbackForm φ g) := fun x u v => by
  rw [pullbackForm_apply, pullbackForm_apply]; exact hs _ _ _

theorem isPosDef_pullbackForm (hp : IsPosDef g) (hφ : ∀ x, (mfderiv I I φ x).IsInvertible) :
    IsPosDef (pullbackForm φ g) := fun x v hv => by
  rw [pullbackForm_apply]
  refine hp _ _ fun h0 => hv ?_
  obtain ⟨L, hL⟩ := hφ x
  have : L v = 0 := by rw [← hL] at h0; exact h0
  simpa using congrArg L.symm this

theorem infty_ne_zero_ω : (∞ : ℕ∞ω) ≠ 0 := by simp

/-- **Pulling back along `φ⁻¹` is pushing forward along `φ`**: `(φ⁻¹)^* V (φ y) = dφ_y (V y)`. -/
theorem mpullback_symm_apply_self (φ : M ≃ₘ^∞⟮I, I⟯ N) (V : Π x : M, TangentSpace I x) (y : M) :
    mpullback I I φ.symm V (φ y) = mfderiv I I φ y (V y) := by
  set A := mfderiv I I φ.symm (φ y)
  have hA : A.IsInvertible := ⟨φ.symm.mfderivToContinuousLinearEquiv infty_ne_zero_ω (φ y), rfl⟩
  have hchain : A (mfderiv I I φ y (V y)) = V y := by
    have h := mfderiv_comp y ((φ.symm.mdifferentiable infty_ne_zero_ω) (φ y))
      ((φ.mdifferentiable infty_ne_zero_ω) y)
    have hid : (φ.symm ∘ φ : M → M) = id := funext φ.symm_apply_apply
    rw [hid, mfderiv_id] at h
    exact (congrArg (fun L => L (V y)) h).symm
  have hV : V (φ.symm (φ y)) = A (mfderiv I I φ y (V y)) := by
    rw [hchain]; exact congrArg (fun z => (V z : E)) (φ.symm_apply_apply y)
  rw [mpullback_apply]
  show A.inverse (V (φ.symm (φ y))) = _
  rw [hV, hA.inverse_apply_self]

/-- **The pullback of a smooth metric along a diffeomorphism is smooth.** -/
theorem isContMDiffMetricSection_pullbackForm (φ : M ≃ₘ^∞⟮I, I⟯ N)
    (hg : IsContMDiffMetricSection E ∞ g) :
    IsContMDiffMetricSection E ∞ (pullbackForm φ g) := by
  refine isContMDiffMetricSection_of_scalars (m := ⊤) _ fun x V W hV hW => ?_
  have hinv : (mfderiv I I φ.symm (φ x)).IsInvertible :=
    ⟨φ.symm.mfderivToContinuousLinearEquiv infty_ne_zero_ω (φ x), rfl⟩
  have hmn : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ∞ := by simp
  have hVx : CMDiffAt ((⊤ : ℕ∞) : ℕ∞ω) (T% V) (φ.symm (φ x)) := by
    rw [φ.symm_apply_apply]; exact hV
  have hWx : CMDiffAt ((⊤ : ℕ∞) : ℕ∞ω) (T% W) (φ.symm (φ x)) := by
    rw [φ.symm_apply_apply]; exact hW
  have hV' := ContMDiffAt.mpullback_vectorField_preimage (n := ∞) hVx φ.symm.contMDiffAt hinv hmn
  have hW' := ContMDiffAt.mpullback_vectorField_preimage (n := ∞) hWx φ.symm.contMDiffAt hinv hmn
  have hpair := (contMDiffAt_pairing (hg (φ x)) hV' hW').comp x φ.contMDiffAt
  refine hpair.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [comp_apply, pullbackForm_apply]
  rw [mpullback_symm_apply_self, mpullback_symm_apply_self]

/-- **Positive sectional curvature transports along diffeomorphisms**: if `N` carries a smooth
metric of positive sectional curvature, so does every manifold `M` diffeomorphic to `N` (the
pullback metric). -/
theorem HasPosCurvMetric.of_diffeomorph (φ : M ≃ₘ^∞⟮I, I⟯ N) (h : HasPosCurvMetric I N) :
    HasPosCurvMetric I M := by
  obtain ⟨g, hs, hp, hg, hpos⟩ := h
  have hfi : ∀ x, (mfderiv I I φ x).IsInvertible :=
    fun x => ⟨φ.mfderivToContinuousLinearEquiv infty_ne_zero_ω x, rfl⟩
  have hsM := isSymm_pullbackForm (φ := (φ : M → N)) hs
  have hpM := isPosDef_pullbackForm (φ := (φ : M → N)) hp hfi
  have hgM := isContMDiffMetricSection_pullbackForm φ hg
  refine ⟨pullbackForm φ g, hsM, hpM, hgM, fun x u v huv => ?_⟩
  rw [sectionalCurvatureAt_pullback φ.contMDiff hfi (fun _ _ _ => rfl) hsM hpM
    (IsContMDiffMetricSection.of_le' hgM two_le_infty_ω) hs hp
    (IsContMDiffMetricSection.of_le' hg two_le_infty_ω) x u v]
  refine hpos _ _ _ ?_
  set L := φ.mfderivToContinuousLinearEquiv infty_ne_zero_ω x
  have h := huv.map' L.toLinearEquiv.toLinearMap L.toLinearEquiv.ker
  have heq : (L.toLinearEquiv.toLinearMap ∘ ![u, v]) =
      ![mfderiv I I φ x u, mfderiv I I φ x v] := by
    funext i; fin_cases i <;> rfl
  rw [heq] at h; exact h

end Transport

end

end ExoticSpheres8And10
