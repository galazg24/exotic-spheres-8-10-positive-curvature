/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.FrameCalculus

/-! # Infrastructure: frame fields from families of maps, and orthonormal frames span

* `contMDiff_mfderivField`: if `Φ : M → N → M` is smooth (uncurried) with `Φ p n₀ = p`, the
  field `p ↦ dΦ_p(n₀) ζ` is a smooth section of `TM`. Fundamental fields of group actions
  (`Φ p q = p · q`) and translation fields (`Φ p t = p + t`) are of this form. The proof is the
  pattern of `RiemannianGeometry`'s `contMDiffAt_orbitField`.
* `span_of_orthonormal`: a `g`-orthonormal family of `dim E` fields is a frame, so every tangent
  vector is `Σ_γ g(w, F_γ) F_γ`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section Fields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The field `p ↦ dΦ_p(n₀) ζ`. -/
def mfderivField (Φ : M → N → M) (n₀ : N) (ζ : TangentSpace J n₀) :
    Π p : M, TangentSpace I p := fun p => mfderiv J I (Φ p) n₀ ζ

set_option maxHeartbeats 2000000 in
theorem contMDiff_mfderivField (Φ : M → N → M) (hΦ : ContMDiff (I.prod J) I ∞ (uncurry Φ))
    (n₀ : N) (hn : ∀ p, Φ p n₀ = p) (ζ : TangentSpace J n₀) :
    ContMDiff I I.tangent ((2 : ℕ∞) : ℕ∞ω) (T% (mfderivField (I := I) Φ n₀ ζ)) := by
  intro y₀
  have hg : ContMDiffAt I J ((2 : ℕ∞) : ℕ∞ω) (fun _ : M => n₀) y₀ := contMDiffAt_const
  have hϕ := ContMDiffAt.mfderiv (I := J) (I' := I) (n := ∞) (m := ((2 : ℕ∞) : ℕ∞ω)) Φ
    (fun _ => n₀) hΦ.contMDiffAt hg (by exact_mod_cast le_top)
  have hv : ContMDiffAt I J.tangent ((2 : ℕ∞) : ℕ∞ω)
      (fun _ : M => ((⟨n₀, ζ⟩ : TangentBundle J N))) y₀ := contMDiffAt_const
  have hb₂ : ContMDiffAt I I ((2 : ℕ∞) : ℕ∞ω) (fun y : M => Φ y n₀) y₀ := by
    rw [show (fun y : M => Φ y n₀) = id from funext hn]
    exact contMDiffAt_id
  have hres := ContMDiffAt.clm_apply_of_inCoordinates (F₁ := E') (E₁ := TangentSpace J)
    (F₂ := E) (E₂ := TangentSpace I) (b₁ := fun _ : M => n₀) (b₂ := fun y : M => Φ y n₀)
    (ϕ := fun y : M => mfderiv J I (Φ y) n₀) (v := fun _ : M => ζ) hϕ hv hb₂
  refine hres.congr_of_eventuallyEq (Eventually.of_forall fun m => ?_)
  exact congrArg (fun z : M => (⟨z, mfderivField (I := I) Φ n₀ ζ m⟩ : TangentBundle I M))
    (hn m).symm

end Fields

section Span

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Π y : M, TangentSpace I y}

/-- **An orthonormal family of `dim E` fields is a frame.** -/
theorem span_of_orthonormal (hp : IsPosDef g) (horth : ∀ α β y, g y (F α y) (F β y) = kron α β)
    (hcard : Fintype.card ι = Module.finrank ℝ E) (y : M) (w : TangentSpace I y) :
    w = ∑ γ, g y w (F γ y) • F γ y := by
  have : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  have hli : LinearIndependent ℝ fun γ => F γ y := by
    rw [Fintype.linearIndependent_iff]
    intro a ha δ
    have := congrArg (fun v => g y v (F δ y)) ha
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      horth, smul_eq_mul, map_zero, ContinuousLinearMap.zero_apply] at this
    rw [sum_smul_kron (V := ℝ) a δ] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range fun γ => F γ y) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, hcard]
    rfl
  set v := w - ∑ γ, g y w (F γ y) • F γ y with hv
  have horthv : ∀ δ, g y v (F δ y) = 0 := fun δ => by
    simp only [hv, map_sub, map_sum, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, horth, smul_eq_mul]
    rw [sum_smul_kron (V := ℝ) (fun γ => g y w (F γ y)) δ, sub_self]
  have hmem : v ∈ Submodule.span ℝ (Set.range fun γ => F γ y) := by rw [hspan]; trivial
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  have hvv : g y v v = 0 := by
    conv_lhs => arg 2; rw [← hb]
    simp only [map_sum, map_smul, smul_eq_mul, horthv, mul_zero, Finset.sum_const_zero]
  by_contra hne
  have h0 : v ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  exact absurd hvv (hp y v h0).ne'

end Span

end

end ExoticSpheres8And10
