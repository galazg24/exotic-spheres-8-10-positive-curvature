/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import Mathlib

/-! # Smooth disk gluing `𝔻(a) ∪_σ 𝔻(b)` with product collars, and its uniqueness

[D] (proof of `lem:attaching` (3)): "the induced identification on a product collar of the
common boundary is constant in the collar direction and has angular part `σ`. Thus the quotient
is the smooth disk gluing `D_N ∪_σ D_S`."

A **model** of this gluing, `DiskGluingModel I a b ε σ Y`, on a manifold `Y` consists of two
smooth charts from open balls of a real inner product space `V`:
* `ψ_N : B(a + ε) → Y` and `ψ_S : B(b + ε) → Y`, each a diffeomorphism onto an open set;
* the two images cover `Y`;
* they overlap exactly on the collars `a − ε < ‖y‖` and `b − ε < ‖y‖`;
* on the overlap `ψ_N = ψ_S ∘ τ`, where `τ(y) = (a + b − ‖y‖) σ(y/‖y‖)`. This is the product
  collar: the radial reflection `r ↦ a + b − r`, constant in the collar direction, with angular
  part `σ`. On the boundary sphere it is `a u ↦ b σ(u)`.

Then `Y ⊇ ψ_N(𝔻(a)), ψ_S(𝔻(b))`, the two closed disks, glued along their boundaries by `σ`.

* **`DiskGluingModel.glueDiffeo`**: any two models with the same `a, b, ε, σ` are diffeomorphic,
  by a diffeomorphism that intertwines the charts.
* **`DiskGluingModel.shrink`**: a model of collar width `ε` restricts to one of any width
  `0 < ε' ≤ ε`.
* **`diskGluing_unique`**: models of any two widths are diffeomorphic.

So "the smooth disk gluing `𝔻(a) ∪_σ 𝔻(b)`" is well defined up to diffeomorphism, independent of
the collar width, and no general collar-uniqueness theorem is needed.
-/

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section DiskGluing

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `y/‖y‖ ∈ S(V)`. -/
def normS (y : V) (hy : y ≠ 0) : Metric.sphere (0 : V) 1 :=
  ⟨‖y‖⁻¹ • y, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]⟩

open Classical in
/-- The product-collar gluing map `τ(y) = (a + b − ‖y‖) σ(y/‖y‖)` (and `τ(0) = 0`). -/
def collarTau (a b : ℝ) (σ : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1) (y : V) : V :=
  if hy : y = 0 then 0 else (a + b - ‖y‖) • (σ (normS y hy) : V)

theorem collarTau_of_ne {a b : ℝ} {σ : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1} {y : V}
    (hy : y ≠ 0) : collarTau a b σ y = (a + b - ‖y‖) • (σ (normS y hy) : V) := by
  rw [collarTau, dif_neg hy]

theorem norm_collarTau {a b : ℝ} {σ : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1} {y : V}
    (hy : y ≠ 0) (h : ‖y‖ ≤ a + b) : ‖collarTau a b σ y‖ = a + b - ‖y‖ := by
  rw [collarTau_of_ne hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    mem_sphere_zero_iff_norm.1 (σ _).2, mul_one]

/-- On the boundary sphere, `τ(a u) = b σ(u)`. -/
theorem collarTau_boundary {a b : ℝ} (ha : 0 < a)
    {σ : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1} (u : Metric.sphere (0 : V) 1) :
    collarTau a b σ (a • (u : V)) = b • (σ u : V) := by
  have hu : ‖(u : V)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
  have hau : ‖a • (u : V)‖ = a := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  have h0 : a • (u : V) ≠ 0 := fun h => by rw [h, norm_zero] at hau; exact ha.ne' hau.symm
  rw [collarTau_of_ne h0, hau, show a + b - a = b by ring]
  congr 3
  apply Subtype.ext
  show ‖a • (u : V)‖⁻¹ • (a • (u : V)) = u
  rw [hau, inv_smul_smul₀ ha.ne']

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners ℝ E' H')

/-- **A smooth disk gluing `𝔻(a) ∪_σ 𝔻(b)` with product collars of width `ε`**, on `Y`. -/
structure DiskGluingModel (a b ε : ℝ) (σ : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1)
    (Y : Type*) [TopologicalSpace Y] [ChartedSpace H' Y] where
  ε_pos : 0 < ε
  ε_le_a : ε ≤ a
  ε_le_b : ε ≤ b
  ψN : OpenPartialHomeomorph V Y
  ψS : OpenPartialHomeomorph V Y
  source_N : ψN.source = Metric.ball 0 (a + ε)
  source_S : ψS.source = Metric.ball 0 (b + ε)
  smooth_N : ContMDiffOn 𝓘(ℝ, V) I' ∞ ψN ψN.source
  smooth_N_symm : ContMDiffOn I' 𝓘(ℝ, V) ∞ ψN.symm ψN.target
  smooth_S : ContMDiffOn 𝓘(ℝ, V) I' ∞ ψS ψS.source
  smooth_S_symm : ContMDiffOn I' 𝓘(ℝ, V) ∞ ψS.symm ψS.target
  cover : ψN.target ∪ ψS.target = univ
  overlap_N : ∀ y ∈ ψN.source, (ψN y ∈ ψS.target ↔ a - ε < ‖y‖)
  overlap_S : ∀ y ∈ ψS.source, (ψS y ∈ ψN.target ↔ b - ε < ‖y‖)
  glue : ∀ y ∈ ψN.source, a - ε < ‖y‖ → ψN y = ψS (collarTau a b σ y)

variable {I'} {a b ε : ℝ} {σ : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1}
  {Y Y' : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace Y']
  [ChartedSpace H' Y']

namespace DiskGluingModel

theorem restrOpen_target' (e : OpenPartialHomeomorph V Y) {s : Set V} (hs : IsOpen s) :
    (e.restrOpen s hs).target = e.target ∩ e.symm ⁻¹' s := rfl

variable (M : DiskGluingModel I' a b ε σ Y)

theorem mem_cover (x : Y) : x ∈ M.ψN.target ∨ x ∈ M.ψS.target := by
  have : x ∈ M.ψN.target ∪ M.ψS.target := by rw [M.cover]; exact mem_univ x
  exact this

include M in
theorem ne_zero_of_overlap {y : V} (h : a - ε < ‖y‖) : y ≠ 0 := fun h0 => by
  rw [h0, norm_zero] at h; linarith [M.ε_le_a]

theorem norm_tau_of_overlap {y : V} (hy : y ∈ M.ψN.source) (h : a - ε < ‖y‖) :
    ‖collarTau a b σ y‖ = a + b - ‖y‖ := by
  rw [M.source_N, mem_ball_zero_iff] at hy
  exact norm_collarTau (M.ne_zero_of_overlap h) (by linarith [M.ε_le_b])

theorem tau_mem_source_S {y : V} (hy : y ∈ M.ψN.source) (h : a - ε < ‖y‖) :
    collarTau a b σ y ∈ M.ψS.source := by
  have hn := M.norm_tau_of_overlap hy h
  rw [M.source_S, mem_ball_zero_iff, hn]
  linarith

/-- On the overlap, `ψ_S⁻¹ = τ ∘ ψ_N⁻¹`. -/
theorem symm_S_of_overlap {x : Y} (hN : x ∈ M.ψN.target) (hS : x ∈ M.ψS.target) :
    a - ε < ‖M.ψN.symm x‖ ∧ M.ψS.symm x = collarTau a b σ (M.ψN.symm x) := by
  have hy := M.ψN.map_target hN
  have hx : M.ψN (M.ψN.symm x) = x := M.ψN.right_inv hN
  have h1 : a - ε < ‖M.ψN.symm x‖ := (M.overlap_N _ hy).1 (by rw [hx]; exact hS)
  refine ⟨h1, ?_⟩
  have h2 := M.glue _ hy h1
  rw [hx] at h2
  conv_lhs => rw [h2]
  exact M.ψS.left_inv (M.tau_mem_source_S hy h1)

variable (M' : DiskGluingModel I' a b ε σ Y')

open Classical in
/-- The map `Y → Y'`: `ψ'_N ∘ ψ_N⁻¹` on the northern chart, `ψ'_S ∘ ψ_S⁻¹` on the southern one. -/
def glueMap : Y → Y' := fun x =>
  if x ∈ M.ψN.target then M'.ψN (M.ψN.symm x) else M'.ψS (M.ψS.symm x)

theorem glueMap_of_N {x : Y} (hx : x ∈ M.ψN.target) : glueMap M M' x = M'.ψN (M.ψN.symm x) := by
  simp only [glueMap]; rw [if_pos hx]

theorem symm_N_mem_source' {x : Y} (hx : x ∈ M.ψN.target) : M.ψN.symm x ∈ M'.ψN.source := by
  rw [M'.source_N, ← M.source_N]; exact M.ψN.map_target hx

theorem symm_S_mem_source' {x : Y} (hx : x ∈ M.ψS.target) : M.ψS.symm x ∈ M'.ψS.source := by
  rw [M'.source_S, ← M.source_S]; exact M.ψS.map_target hx

theorem glueMap_of_S {x : Y} (hx : x ∈ M.ψS.target) : glueMap M M' x = M'.ψS (M.ψS.symm x) := by
  by_cases hN : x ∈ M.ψN.target
  · rw [glueMap_of_N M M' hN]
    obtain ⟨h1, h2⟩ := M.symm_S_of_overlap hN hx
    rw [h2, M'.glue _ (symm_N_mem_source' M M' hN) h1]
  · simp only [glueMap]; rw [if_neg hN]

/-- The map intertwines the northern charts. -/
theorem glueMap_ψN {y : V} (hy : y ∈ M.ψN.source) : glueMap M M' (M.ψN y) = M'.ψN y := by
  rw [glueMap_of_N M M' (M.ψN.map_source hy), M.ψN.left_inv hy]

/-- The map intertwines the southern charts. -/
theorem glueMap_ψS {y : V} (hy : y ∈ M.ψS.source) : glueMap M M' (M.ψS y) = M'.ψS y := by
  rw [glueMap_of_S M M' (M.ψS.map_source hy), M.ψS.left_inv hy]

variable [IsManifold I' ∞ Y] [IsManifold I' ∞ Y']

theorem contMDiff_glueMap : ContMDiff I' I' ∞ (glueMap M M') := by
  intro x
  rcases M.mem_cover x with hN | hS
  · have hev : glueMap M M' =ᶠ[𝓝 x] M'.ψN ∘ M.ψN.symm := by
      filter_upwards [M.ψN.open_target.mem_nhds hN] with z hz using glueMap_of_N M M' hz
    have hs := symm_N_mem_source' M M' hN
    exact ((M'.smooth_N.contMDiffAt (M'.ψN.open_source.mem_nhds hs)).comp x
      (M.smooth_N_symm.contMDiffAt (M.ψN.open_target.mem_nhds hN))).congr_of_eventuallyEq hev
  · have hev : glueMap M M' =ᶠ[𝓝 x] M'.ψS ∘ M.ψS.symm := by
      filter_upwards [M.ψS.open_target.mem_nhds hS] with z hz using glueMap_of_S M M' hz
    have hs := symm_S_mem_source' M M' hS
    exact ((M'.smooth_S.contMDiffAt (M'.ψS.open_source.mem_nhds hs)).comp x
      (M.smooth_S_symm.contMDiffAt (M.ψS.open_target.mem_nhds hS))).congr_of_eventuallyEq hev

theorem glueMap_glueMap (x : Y) : glueMap M' M (glueMap M M' x) = x := by
  rcases M.mem_cover x with hN | hS
  · have hs := symm_N_mem_source' M M' hN
    rw [glueMap_of_N M M' hN, glueMap_ψN M' M hs, M.ψN.right_inv hN]
  · have hs := symm_S_mem_source' M M' hS
    rw [glueMap_of_S M M' hS, glueMap_ψS M' M hs, M.ψS.right_inv hS]

/-- **Uniqueness of the smooth disk gluing**: two models with the same data are diffeomorphic,
by a diffeomorphism intertwining the northern and the southern charts. -/
def glueDiffeo : Y ≃ₘ^∞⟮I', I'⟯ Y' where
  toFun := glueMap M M'
  invFun := glueMap M' M
  left_inv := glueMap_glueMap M M'
  right_inv := glueMap_glueMap M' M
  contMDiff_toFun := contMDiff_glueMap M M'
  contMDiff_invFun := contMDiff_glueMap M' M

theorem glueDiffeo_ψN {y : V} (hy : y ∈ M.ψN.source) : glueDiffeo M M' (M.ψN y) = M'.ψN y :=
  glueMap_ψN M M' hy

theorem glueDiffeo_ψS {y : V} (hy : y ∈ M.ψS.source) : glueDiffeo M M' (M.ψS y) = M'.ψS y :=
  glueMap_ψS M M' hy

end DiskGluingModel

/-! ### Independence of the collar width -/

namespace DiskGluingModel

variable (M : DiskGluingModel I' a b ε σ Y)

/-- On the overlap, a southern preimage determines the northern one: `y = τ(w)`. -/
theorem eq_tau_of_S_mem_N {y : V} (hy : y ∈ M.ψS.source) (hN : M.ψS y ∈ M.ψN.target) :
    a - ε < ‖M.ψN.symm (M.ψS y)‖ ∧ y = collarTau a b σ (M.ψN.symm (M.ψS y)) := by
  obtain ⟨h1, h2⟩ := M.symm_S_of_overlap hN (M.ψS.map_source hy)
  rw [M.ψS.left_inv hy] at h2
  exact ⟨h1, h2⟩

/-- **Shrinking the collar**: a model of width `ε` restricts to a model of width `ε'`. -/
def shrink (ε' : ℝ) (h0 : 0 < ε') (hle : ε' ≤ ε) : DiskGluingModel I' a b ε' σ Y where
  ε_pos := h0
  ε_le_a := hle.trans M.ε_le_a
  ε_le_b := hle.trans M.ε_le_b
  ψN := M.ψN.restrOpen (Metric.ball 0 (a + ε')) Metric.isOpen_ball
  ψS := M.ψS.restrOpen (Metric.ball 0 (b + ε')) Metric.isOpen_ball
  source_N := by
    rw [OpenPartialHomeomorph.restrOpen_source, M.source_N]
    exact inter_eq_right.2 (Metric.ball_subset_ball (by linarith))
  source_S := by
    rw [OpenPartialHomeomorph.restrOpen_source, M.source_S]
    exact inter_eq_right.2 (Metric.ball_subset_ball (by linarith))
  smooth_N := M.smooth_N.mono inter_subset_left
  smooth_N_symm := M.smooth_N_symm.mono inter_subset_left
  smooth_S := M.smooth_S.mono inter_subset_left
  smooth_S_symm := M.smooth_S_symm.mono inter_subset_left
  cover := by
    refine eq_univ_of_forall fun x => ?_
    rcases M.mem_cover x with hN | hS
    · set y := M.ψN.symm x
      have hy : y ∈ M.ψN.source := M.ψN.map_target hN
      by_cases hr : ‖y‖ < a + ε'
      · exact Or.inl ⟨hN, mem_ball_zero_iff.2 hr⟩
      · push_neg at hr
        have hov : a - ε < ‖y‖ := by linarith [M.ε_pos]
        have hτ := M.norm_tau_of_overlap hy hov
        have hx : x = M.ψS (collarTau a b σ y) := by
          rw [← M.glue _ hy hov, M.ψN.right_inv hN]
        have hτs := M.tau_mem_source_S hy hov
        refine Or.inr ⟨by rw [hx]; exact M.ψS.map_source hτs, ?_⟩
        show M.ψS.symm x ∈ Metric.ball 0 (b + ε')
        rw [hx, M.ψS.left_inv hτs, mem_ball_zero_iff, hτ]
        linarith
    · set y := M.ψS.symm x
      have hy : y ∈ M.ψS.source := M.ψS.map_target hS
      by_cases hr : ‖y‖ < b + ε'
      · exact Or.inr ⟨hS, mem_ball_zero_iff.2 hr⟩
      · push_neg at hr
        have hN : x ∈ M.ψN.target := by
          have := (M.overlap_S y hy).2 (by linarith [M.ε_pos])
          rwa [M.ψS.right_inv hS] at this
        set w := M.ψN.symm x
        have hw : w ∈ M.ψN.source := M.ψN.map_target hN
        obtain ⟨h1, h2⟩ := M.symm_S_of_overlap hN hS
        have hn : ‖y‖ = a + b - ‖w‖ := by
          show ‖M.ψS.symm x‖ = _; rw [h2]; exact M.norm_tau_of_overlap hw h1
        refine Or.inl ⟨hN, ?_⟩
        show w ∈ Metric.ball 0 (a + ε')
        rw [M.source_N, mem_ball_zero_iff] at hw
        rw [mem_ball_zero_iff]
        linarith
  overlap_N := by
    intro y hy
    have hy' : y ∈ M.ψN.source := hy.1
    have hyr : ‖y‖ < a + ε' := mem_ball_zero_iff.1 hy.2
    show M.ψN y ∈ M.ψS.target ∩ M.ψS.symm ⁻¹' Metric.ball 0 (b + ε') ↔ _
    constructor
    · rintro ⟨hS, hb⟩
      have hov : a - ε < ‖y‖ := (M.overlap_N y hy').1 hS
      rw [mem_preimage, M.glue y hy' hov, M.ψS.left_inv (M.tau_mem_source_S hy' hov),
        mem_ball_zero_iff, M.norm_tau_of_overlap hy' hov] at hb
      linarith
    · intro h
      have hov : a - ε < ‖y‖ := by linarith
      refine ⟨(M.overlap_N y hy').2 hov, ?_⟩
      rw [mem_preimage, M.glue y hy' hov, M.ψS.left_inv (M.tau_mem_source_S hy' hov),
        mem_ball_zero_iff, M.norm_tau_of_overlap hy' hov]
      linarith
  overlap_S := by
    intro y hy
    have hy' : y ∈ M.ψS.source := hy.1
    have hyr : ‖y‖ < b + ε' := mem_ball_zero_iff.1 hy.2
    show M.ψS y ∈ M.ψN.target ∩ M.ψN.symm ⁻¹' Metric.ball 0 (a + ε') ↔ _
    constructor
    · rintro ⟨hN, ha⟩
      obtain ⟨h1, h2⟩ := M.eq_tau_of_S_mem_N hy' hN
      have hw := M.ψN.map_target hN
      have hn : ‖y‖ = a + b - ‖M.ψN.symm (M.ψS y)‖ := by
        conv_lhs => rw [h2]
        exact M.norm_tau_of_overlap hw h1
      rw [mem_preimage, mem_ball_zero_iff] at ha
      linarith
    · intro h
      have hN : M.ψS y ∈ M.ψN.target := (M.overlap_S y hy').2 (by linarith)
      obtain ⟨h1, h2⟩ := M.eq_tau_of_S_mem_N hy' hN
      have hw := M.ψN.map_target hN
      have hn : ‖y‖ = a + b - ‖M.ψN.symm (M.ψS y)‖ := by
        conv_lhs => rw [h2]
        exact M.norm_tau_of_overlap hw h1
      refine ⟨hN, ?_⟩
      rw [mem_preimage, mem_ball_zero_iff]
      linarith
  glue := fun y hy h => M.glue y hy.1 (by linarith)

end DiskGluingModel

variable [IsManifold I' ∞ Y] [IsManifold I' ∞ Y']

/-- **The smooth disk gluing is unique up to diffeomorphism, for any collar widths.** -/
theorem diskGluing_unique {ε' : ℝ} (M : DiskGluingModel I' a b ε σ Y)
    (M' : DiskGluingModel I' a b ε' σ Y') : Nonempty (Y ≃ₘ^∞⟮I', I'⟯ Y') :=
  ⟨DiskGluingModel.glueDiffeo (M.shrink (min ε ε') (lt_min M.ε_pos M'.ε_pos) (min_le_left _ _))
    (M'.shrink (min ε ε') (lt_min M.ε_pos M'.ε_pos) (min_le_right _ _))⟩

end DiskGluing

end

end ExoticSpheres8And10
