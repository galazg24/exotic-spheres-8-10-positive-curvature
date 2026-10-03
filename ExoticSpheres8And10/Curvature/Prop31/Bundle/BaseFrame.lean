/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Blocks

/-! # Smooth orthonormal frames near every point of the base

Gram–Schmidt for smooth sections of the tangent bundle with respect to a smooth Riemannian
metric `g`:

  `u_k = s_k − Σ_{j<k} g(s_k, e_j) e_j`,   `e_k = u_k / √g(u_k, u_k)`.

Applied to the local frame of a tangent-bundle trivialisation (Mathlib's
`Trivialization.localFrame`), this gives, near every point of `B`, a smooth `g`-orthonormal
frame. `B` may have boundary or corners: the construction uses only manifold calculus.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff

noncomputable section

section GS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B] {n : ℕ}

variable (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
  (s : Fin n → Π b : B, TangentSpace I b)

/-- **Gram–Schmidt**, normalised. -/
def gsE (k : Fin n) (x : B) : TangentSpace I x :=
  (√(g x (s k x - ∑ j : Fin n, (if h : j < k then g x (s k x) (gsE j x) • gsE j x else 0))
      (s k x - ∑ j : Fin n, (if h : j < k then g x (s k x) (gsE j x) • gsE j x else 0))))⁻¹ •
    (s k x - ∑ j : Fin n, (if h : j < k then g x (s k x) (gsE j x) • gsE j x else 0))
termination_by k.val
decreasing_by all_goals exact h

/-- The unnormalised vector `u_k`. -/
def gsU (k : Fin n) (x : B) : TangentSpace I x :=
  s k x - ∑ j ∈ Finset.univ.filter (· < k), g x (s k x) (gsE g s j x) • gsE g s j x

theorem gsU_eq_dite (k : Fin n) (x : B) :
    gsU g s k x =
      s k x - ∑ j : Fin n, (if h : j < k then g x (s k x) (gsE g s j x) • gsE g s j x else 0) := by
  simp only [gsU, dite_eq_ite, Finset.sum_filter]

theorem gsE_eq (k : Fin n) (x : B) :
    gsE g s k x = (√(g x (gsU g s k x) (gsU g s k x)))⁻¹ • gsU g s k x := by
  rw [gsE, gsU_eq_dite]

theorem gsE_fun (k : Fin n) :
    gsE g s k = fun x => (√(g x (gsU g s k x) (gsU g s k x)))⁻¹ • gsU g s k x :=
  funext fun x => gsE_eq g s k x

variable {g s}

/-! ### Pointwise: orthonormality and the flag -/

section Pointwise

variable {x : B} (hsym : ∀ u v : TangentSpace I x, g x u v = g x v u)
  (hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < g x v v)
  (hli : LinearIndependent ℝ (fun i => s i x))

include hsym hpos hli in
/-- The Gram–Schmidt invariant at `x`, by strong induction. -/
theorem gs_invariant (k : Fin n) :
    0 < g x (gsU g s k x) (gsU g s k x) ∧ g x (gsE g s k x) (gsE g s k x) = 1 ∧
      (∀ j < k, g x (gsE g s k x) (gsE g s j x) = 0) ∧
      gsE g s k x ∈ Submodule.span ℝ ((fun i => s i x) '' Iic k) := by
  induction k using WellFoundedLT.induction
  rename_i k IH
  have horth : ∀ j < k, ∀ m < k,
      g x (gsE g s j x) (gsE g s m x) = if j = m then 1 else 0 := by
    intro j hj m hm
    rcases lt_trichotomy j m with h | h | h
    · rw [hsym, (IH m hm).2.2.1 j h, if_neg (ne_of_lt h)]
    · subst h; rw [(IH j hj).2.1, if_pos rfl]
    · rw [(IH j hj).2.2.1 m h, if_neg (ne_of_gt h)]
  have hperp : ∀ m < k, g x (gsU g s k x) (gsE g s m x) = 0 := by
    intro m hm
    have hsum : ∑ j ∈ Finset.univ.filter (· < k),
        g x (s k x) (gsE g s j x) * g x (gsE g s j x) (gsE g s m x) =
          g x (s k x) (gsE g s m x) := by
      rw [Finset.sum_congr rfl fun j hj => by rw [horth j (Finset.mem_filter.1 hj).2 m hm]]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_filter,
        Finset.mem_univ, true_and, if_pos hm]
    simp only [gsU, map_sub, map_sum, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hsum, sub_self]
  have hmem : ∀ j < k, gsE g s j x ∈ Submodule.span ℝ ((fun i => s i x) '' Iio k) :=
    fun j hj => Submodule.span_mono (image_mono (Iic_subset_Iio.2 hj)) (IH j hj).2.2.2
  have hne : gsU g s k x ≠ 0 := by
    intro h0
    have hsk : s k x =
        ∑ j ∈ Finset.univ.filter (· < k), g x (s k x) (gsE g s j x) • gsE g s j x :=
      sub_eq_zero.1 h0
    have hin : s k x ∈ Submodule.span ℝ ((fun i => s i x) '' Iio k) := by
      rw [hsk]
      exact Submodule.sum_mem _ fun j hj =>
        Submodule.smul_mem _ _ (hmem j (Finset.mem_filter.1 hj).2)
    exact hli.notMem_span_image (s := Iio k) (x := k) (lt_irrefl k) hin
  have hu := hpos _ hne
  refine ⟨hu, ?_, ?_, ?_⟩
  · rw [gsE_eq]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hu.le, inv_mul_cancel₀ hu.ne']
  · intro m hm
    rw [gsE_eq]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hperp m hm, mul_zero]
  · rw [gsE_eq]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact Submodule.subset_span (mem_image_of_mem (fun i => s i x) (Set.mem_Iic.2 le_rfl))
    · exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
        (Submodule.span_mono (image_mono (Iic_subset_Iic.2 (Finset.mem_filter.1 hj).2.le))
          (IH j (Finset.mem_filter.1 hj).2).2.2.2)

include hsym hpos hli in
/-- **The Gram–Schmidt frame is orthonormal** at `x`. -/
theorem gs_orthonormal (i j : Fin n) : g x (gsE g s i x) (gsE g s j x) = kron i j := by
  rcases lt_trichotomy i j with h | h | h
  · rw [hsym, (gs_invariant hsym hpos hli j).2.2.1 i h, kron, if_neg (ne_of_lt h)]
  · subst h; rw [(gs_invariant hsym hpos hli i).2.1, kron, if_pos rfl]
  · rw [(gs_invariant hsym hpos hli i).2.2.1 j h, kron, if_neg (ne_of_gt h)]

end Pointwise

/-! ### Smoothness -/

variable [IsManifold I ∞ B]

/-- **The Gram–Schmidt frame is smooth** wherever the input frame is smooth and independent. -/
theorem contMDiffAt_gsE {U : Set B} (hgs : IsContMDiffMetricSection E ∞ g) (hsg : IsSymm g)
    (hpg : IsPosDef g) (hs : ∀ i, ∀ x ∈ U, ContMDiffAt I I.tangent ∞ (T% (s i)) x)
    (hli : ∀ x ∈ U, LinearIndependent ℝ (fun i => s i x)) (k : Fin n) :
    ∀ x ∈ U, ContMDiffAt I I.tangent ∞ (T% (gsE g s k)) x := by
  induction k using WellFoundedLT.induction
  rename_i k IH
  intro x hx
  have hu : ContMDiffAt I I.tangent ∞ (T% (gsU g s k)) x :=
    (hs k x hx).sub_section (ContMDiffAt.sum_section
      (t := fun j y => g y (s k y) (gsE g s j y) • gsE g s j y) fun j hj =>
        (contMDiffAt_pairing (hgs x) (hs k x hx) (IH j (Finset.mem_filter.1 hj).2 x hx)).smul_section
          (IH j (Finset.mem_filter.1 hj).2 x hx))
  have hq : ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g y (gsU g s k y) (gsU g s k y)) x :=
    contMDiffAt_pairing (hgs x) hu hu
  have hpos' := (gs_invariant (hsg x) (hpg x) (hli x hx) k).1
  have hsq : ContMDiffAt I 𝓘(ℝ) ∞ (fun y => √(g y (gsU g s k y) (gsU g s k y))) x :=
    (Real.contDiffAt_sqrt hpos'.ne').contMDiffAt.comp x hq
  have hinv := hsq.inv₀ (Real.sqrt_pos.2 hpos').ne'
  rw [gsE_fun]
  exact hinv.smul_section hu

end GS

/-! ## Orthonormal frames near every point -/

section Exists

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] {n : ℕ}
  {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}

/-- **Every point of `B` has a neighbourhood with a smooth `g`-orthonormal frame.** Boundary
points included. -/
theorem exists_orthonormal_frame_near (hsg : IsSymm g) (hpg : IsPosDef g)
    (hgs : IsContMDiffMetricSection E ∞ g) (hn : finrank ℝ E = n) (b : B) :
    ∃ U : Set B, IsOpen U ∧ b ∈ U ∧ ∃ e : Fin n → Π x : B, TangentSpace I x,
      (∀ i, ∀ x ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) x) ∧
      (∀ x ∈ U, ∀ i j, g x (e i x) (e j x) = kron i j) := by
  let T := trivializationAt E (TangentSpace I) b
  let bE := Module.finBasisOfFinrankEq ℝ E hn
  have hfr := T.isLocalFrameOn_localFrame_baseSet I ∞ bE
  refine ⟨T.baseSet, T.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' b,
    gsE g (T.localFrame bE), ?_, ?_⟩
  · exact fun i => contMDiffAt_gsE hgs hsg hpg
      (fun i x hx => hfr.contMDiffAt T.open_baseSet hx i) (fun x hx => hfr.linearIndependent hx) i
  · exact fun x hx i j => gs_orthonormal (hsg x) (hpg x) (hfr.linearIndependent hx) i j

end Exists

end

end ExoticSpheres8And10
