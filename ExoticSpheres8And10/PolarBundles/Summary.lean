/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.PolarBundles.Attaching
import ExoticSpheres8And10.ActionField.Bound

/-! # §2: conventions, the star-bundle properties of `P_θ`, and a model of the hypotheses

* `bracket_orthonormal`: with the Euclidean inner product `Q` on `Im ℍ`, `[u, v] = 2u × v`
  (`commutator_eq_two_qcross`, A1), and `¼‖[u,v]‖² = 1` for an orthonormal pair. This is the
  Lie-algebraic value of the sectional curvature of the bi-invariant metric; the formula
  `K = ¼‖[u,v]‖²` itself is standard and imported.
* `polarBundle_isStarBundle`: `P_θ` with the star action and the principal action satisfies every
  clause of [D] `def:starbundle` (3) and the special `S³`-`S³` bundle definition, as proved in
  `S2_PolarBundle`.
* `trivialPolarData`: the hypotheses of `PolarData` are satisfiable in every dimension `n = m + 1`
  (trivial representation, `θ ≡ 1`), and all constructions are instantiated there.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

/-- **[D] §2, conventions**: for an orthonormal pair `u, v` in `Im ℍ` (inner product `Q`),
`[u, v] = 2 u × v` and `¼‖[u, v]‖² = 1`. -/
theorem bracket_orthonormal (u v : ℍ[ℝ]) (hu : u.re = 0) (hv : v.re = 0) (hu1 : ‖u‖ = 1)
    (hv1 : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) :
    u * v - v * u = (2 : ℝ) • qcross u v ∧ ‖u * v - v * u‖ ^ 2 / 4 = 1 := by
  have h1 : u * v - v * u = (2 : ℝ) • qcross u v := by
    rw [commutator_eq_two_qcross, qcross_im]
  refine ⟨h1, ?_⟩
  rw [h1, norm_smul, mul_pow, Real.norm_two, norm_qcross_sq u v hu hv, hu1, hv1,
    qdot_eq_inner u v hu, huv]
  norm_num

section Summary

variable {m : ℕ} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

/-- **`P_θ` is a star bundle** ([D] `def:starbundle` (3), special `S³`-`S³` bundle): a smooth
Hausdorff manifold with a smooth free right `S³`-action, transitive on the fibres of a smooth
projection to `S^n`, with a smooth free left `S³`-action commuting with it and covering `ρ`, and
trivialised over `U_N` and `U_S` by the two product charts. -/
theorem polarBundle_isStarBundle (D : PolarData (m := m) e) :
    -- smooth actions and projection
    ContMDiff ((𝓡 3).prod (IP m)) (IP m) ∞ (fun x : S3 × PolarBundle D => x.1 • x.2) ∧
    ContMDiff ((𝓡 3).prod (IP m)) (IP m) ∞ (fun x : S3 × PolarBundle D => D.ract x.2 x.1) ∧
    ContMDiff (IP m) (𝓡 (m + 1)) ∞ D.proj ∧
    -- principal action: free, transitive on fibres, preserving fibres
    (∀ p h, D.ract p h = p → h = 1) ∧
    (∀ p p', D.proj p = D.proj p' → ∃ h, p' = D.ract p h) ∧
    (∀ p h, D.proj (D.ract p h) = D.proj p) ∧
    -- star action: free, commuting, covering ρ
    (∀ (q : S3) (p : PolarBundle D), q • p = p → q = 1) ∧
    (∀ (q h : S3) (p : PolarBundle D), q • D.ract p h = D.ract (q • p) h) ∧
    (∀ (q : S3) (p : PolarBundle D), D.proj (q • p) = D.ρS q (D.proj p)) ∧
    -- local trivialisations over `U_N` and `U_S`
    (∀ p : PolarBundle D, (D.proj p : W) ≠ -e → p ∈ range (ι₁ D.κP)) ∧
    (∀ p : PolarBundle D, (D.proj p : W) ≠ e → p ∈ range (ι₂ D.κP)) ∧
    Topology.IsOpenEmbedding (ι₁ D.κP) ∧ Topology.IsOpenEmbedding (ι₂ D.κP) ∧
    T2Space (PolarBundle D) :=
  ⟨D.contMDiff_star, D.contMDiff_ract, D.contMDiff_proj, D.ract_free, D.ract_transitive,
    D.proj_ract, D.star_free, D.star_ract, D.proj_star, D.mem_range_ι₁, D.mem_range_ι₂,
    isOpenEmbedding_ι₁ D.κP, isOpenEmbedding_ι₂ D.κP, inferInstance⟩

end Summary

/-! ## Non-vacuity: a model of `PolarData` in every dimension -/

section Model

variable (m : ℕ)

/-- `W = ℝ^{m+2}`. -/
abbrev Wm := EuclideanSpace ℝ (Fin (m + 2))

instance fact_finrank_Wm : Fact (finrank ℝ (Wm m) = (m + 1) + 1) := ⟨by simp⟩

/-- `e = (1, 0, …, 0)`. -/
def e0 : Wm m := EuclideanSpace.single 0 1

theorem norm_e0 : ‖e0 m‖ = 1 := by simp [e0]

instance fact_finrank_Vs_e0 : Fact (finrank ℝ (Vs (e0 m)) = m + 1) :=
  ⟨Submodule.finrank_orthogonal_span_singleton (fun h => by
    have := norm_e0 m; rw [h, norm_zero] at this; exact zero_ne_one this)⟩

/-- **A model of polar data**: the trivial representation and `θ ≡ 1`. -/
def trivialPolarData : PolarData (m := m) (e0 m) where
  e_norm := norm_e0 m
  ρ := 1
  ρ_e _ := rfl
  ρ_smooth := by
    show ContMDiff (𝓡 3) 𝓘(ℝ, Wm m →L[ℝ] Wm m) ∞
      fun _ : S3 => (((1 : Wm m ≃ₗᵢ[ℝ] Wm m) : Wm m ≃L[ℝ] Wm m) : Wm m →L[ℝ] Wm m)
    exact contMDiff_const
  θ := fun _ => 1
  θ_smooth := contMDiff_const
  θ_equiv q _ _ _ := by simp

/-- All constructions are instantiated for the model (here with `a = π/2`). -/
example : IsManifold (IP m) ∞ (PolarBundle (trivialPolarData m)) := inferInstance

example : IsManifold (𝓡 (m + 1)) ∞ (QuotSpace (trivialPolarData m)) := inferInstance

example : (trivialPolarData m).OrbitSpace ≃ₜ (trivialPolarData m).DiskGluing (a := π / 2)
    (by positivity) :=
  (trivialPolarData m).orbitSpaceDiskGluing (by positivity) (by linarith [pi_pos])

example : Diffeomorph (𝓡 m) (𝓡 m) (sphere (0 : Vs (e0 m)) 1) (sphere (0 : Vs (e0 m)) 1) ∞ :=
  (trivialPolarData m).sigmaDiffeoV

end Model

end

end ExoticSpheres8And10
