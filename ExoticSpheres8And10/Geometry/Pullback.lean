/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.HomBundleForms
import RiemannianGeometry.MLieBracketDerivation
import Mathlib

/-! # Infrastructure: metrics built from weighted pullbacks along smooth maps

A field of bilinear forms `x ↦ c(x) · q(df_x ·, df_x ·)`, with `c : M → ℝ` and `f : M → F`
smooth and `q` a constant form on a vector space `F`, is a smooth metric section. So is any
finite sum of such terms. Every metric of [GG] §4 is of this kind in suitable coordinates.

* `pullTerm c q f`: the term; `pullTerm_apply`;
* `contMDiffAt_pullTerm_apply`: its pairing with `C^m` fields is `C^m`;
* `isContMDiffMetricSection_of_scalars`: `RiemannianGeometry`'s double frame test, globalised, so a field of
  forms whose pairings with smooth fields are smooth is a smooth metric section.
-/

open RiemannianGeometry Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section Pull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The weighted pullback `c(x) · q(df_x v, df_x w)`. -/
def pullTerm (c : M → ℝ) (q : F →L[ℝ] F →L[ℝ] ℝ) (f : M → F) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
  letI : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  c x • (((q.comp (mvfderiv I f x)).flip).comp (mvfderiv I f x)).flip

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem pullTerm_apply (c : M → ℝ) (q : F →L[ℝ] F →L[ℝ] ℝ) (f : M → F) (x : M)
    (v w : TangentSpace I x) :
    pullTerm c q f x v w = c x * q (mvfderiv I f x v) (mvfderiv I f x w) := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Pairings of a weighted pullback with `C^m` fields are `C^m`. -/
theorem contMDiffAt_pullTerm_apply {m : ℕ∞} {c : M → ℝ} (q : F →L[ℝ] F →L[ℝ] ℝ) {f : M → F}
    (hc : ContMDiff I 𝓘(ℝ) ∞ c) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    {V W : Π y : M, TangentSpace I y} {x : M}
    (hV : CMDiffAt ((m : ℕ∞ω)) (T% V) x) (hW : CMDiffAt ((m : ℕ∞ω)) (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) ((m : ℕ∞ω)) (fun y ↦ pullTerm c q f y (V y) (W y)) x := by
  have hmn : ((m : ℕ∞ω)) + 1 ≤ ∞ := by
    exact_mod_cast (WithTop.coe_le_coe.mpr le_top : ((m + 1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))
  have hV' : ContMDiffAt I 𝓘(ℝ, F) ((m : ℕ∞ω)) (fun y ↦ mvfderiv I f y (V y)) x :=
    contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x) hf.contMDiffOn hmn hV
  have hW' : ContMDiffAt I 𝓘(ℝ, F) ((m : ℕ∞ω)) (fun y ↦ mvfderiv I f y (W y)) x :=
    contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x) hf.contMDiffOn hmn hW
  have h := ((hc x).of_le (by exact_mod_cast le_top)).mul
    ((contMDiffAt_const (c := q)).clm_apply hV' |>.clm_apply hW')
  exact h

omit [CompleteSpace E] in
/-- **The frame test, globalised.** A field of forms is a `C^m` metric section as soon as its
pairings with `C^m` fields near each point are `C^m`. -/
theorem isContMDiffMetricSection_of_scalars {m : ℕ∞}
    (K : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hK : ∀ (x : M) (V W : Π y : M, TangentSpace I y), CMDiffAt ((m : ℕ∞ω)) (T% V) x →
      CMDiffAt ((m : ℕ∞ω)) (T% W) x → ContMDiffAt I 𝓘(ℝ) ((m : ℕ∞ω)) (fun y ↦ K y (V y) (W y)) x) :
    IsContMDiffMetricSection E m K := by
  intro x
  have hxe : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  refine contMDiffAt_hom_hom_of_contMDiffAt_frame (Module.finBasis ℝ E)
    (trivializationAt E (TangentSpace I) x) hxe K fun i j ↦ hK x _ _ ?_ ?_
  · exact contMDiffAt_localFrame_of_mem (I := I) (n := (m : ℕ∞ω))
      (e := trivializationAt E (TangentSpace I) x) (b := Module.finBasis ℝ E) i hxe
  · exact contMDiffAt_localFrame_of_mem (I := I) (n := (m : ℕ∞ω))
      (e := trivializationAt E (TangentSpace I) x) (b := Module.finBasis ℝ E) j hxe

end Pull

end

end ExoticSpheres8And10
