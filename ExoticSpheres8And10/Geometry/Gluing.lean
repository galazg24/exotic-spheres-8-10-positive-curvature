/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import Mathlib

/-! # Infrastructure: gluing two copies of a manifold along a partial diffeomorphism

Mathlib has no gluing of manifolds. [GG] §2 builds the polar bundle `P_θ` by gluing two product
charts along `u_S = θ(x) u_N`, and its star quotient by gluing two disks. Both are instances of
the following construction.

Let `M` be a `C^∞` manifold (model `I`), and `κ : M ⇀ M` an open partial homeomorphism that is
`C^∞` with `C^∞` inverse. `Glued κ` is `M ⊔ M` modulo `inl a ∼ inr (κ a)` for `a ∈ κ.source`,
with the quotient topology.

* `isOpenEmbedding_ι₁`, `isOpenEmbedding_ι₂`: both copies embed as open sets, and they cover.
* `ι₁_eq_ι₂`: the only identifications are `ι₁ a = ι₂ (κ a)`.
* A charted space over `M` (two charts, `ι₁⁻¹` and `ι₂⁻¹`), and over `H` by composition;
  `isManifold_glued`: `Glued κ` is a `C^∞` manifold.
* `contMDiff_ι₁`, `contMDiff_ι₂`: the inclusions are smooth.
* `contMDiff_glued_iff`: a map out of `Glued κ` is smooth iff both restrictions are.
* `glueLift`, `glueMap`: maps that are compatible with `κ` descend.

Hausdorffness is not part of Mathlib's `IsManifold` and is not needed here.
-/

namespace ExoticSpheres8And10

open Set Topology Function

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ## The groupoid of smooth partial diffeomorphisms of `M` -/

/-- The pregroupoid of `C^∞` maps of `M`. -/
def smoothPregroupoid (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Pregroupoid M where
  property f s := ContMDiffOn I I ∞ f s
  comp {_ _ _ _} hf hg _ _ _ := hg.comp' hf
  id_mem := contMDiffOn_id
  locality {_ _} _ h := contMDiffOn_of_locally_contMDiffOn h
  congr {_ _ _} _ hfg hf := hf.congr hfg

/-- The groupoid of `C^∞` partial diffeomorphisms of `M`. -/
def smoothGroupoid (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : StructureGroupoid M :=
  (smoothPregroupoid I M).groupoid

theorem mem_smoothGroupoid {e : OpenPartialHomeomorph M M} :
    e ∈ smoothGroupoid I M ↔ ContMDiffOn I I ∞ e e.source ∧ ContMDiffOn I I ∞ e.symm e.target :=
  mem_groupoid_of_pregroupoid

/-! ## The glued space -/

variable (κ : OpenPartialHomeomorph M M)

/-- `inl a ∼ inr (κ a)` for `a ∈ κ.source`. -/
def GlueRel : M ⊕ M → M ⊕ M → Prop
  | .inl a, .inl a' => a = a'
  | .inr b, .inr b' => b = b'
  | .inl a, .inr b => a ∈ κ.source ∧ κ a = b
  | .inr b, .inl a => a ∈ κ.source ∧ κ a = b

/-- The gluing relation is an equivalence relation. -/
def glueSetoid : Setoid (M ⊕ M) where
  r := GlueRel κ
  iseqv := {
    refl := fun x => by cases x <;> exact rfl
    symm := fun {x y} h => by
      cases x <;> cases y <;> simp only [GlueRel] at h ⊢ <;> first | exact h.symm | exact h
    trans := fun {x y z} h1 h2 => by
      cases x <;> cases y <;> cases z <;> simp only [GlueRel] at h1 h2 ⊢
      · exact h1.trans h2
      · exact h1 ▸ h2
      · exact κ.injOn h1.1 h2.1 (h1.2.trans h2.2.symm)
      · exact ⟨h1.1, h1.2.trans h2⟩
      · exact ⟨h2 ▸ h1.1, by rw [← h2]; exact h1.2⟩
      · exact h1.2.symm.trans h2.2
      · exact ⟨h2.1, h2.2.trans h1.symm⟩
      · exact h1.trans h2 }

/-- The glued space `(M ⊔ M)/(a ∼ κ a)`. -/
def Glued := Quotient (glueSetoid κ)

instance : TopologicalSpace (Glued κ) := instTopologicalSpaceQuotient

/-- The first copy. -/
def ι₁ (a : M) : Glued κ := Quotient.mk _ (.inl a)

/-- The second copy. -/
def ι₂ (b : M) : Glued κ := Quotient.mk _ (.inr b)

variable {κ}

theorem ι₁_eq_ι₂ {a b : M} : ι₁ κ a = ι₂ κ b ↔ a ∈ κ.source ∧ κ a = b :=
  Quotient.eq (r := glueSetoid κ)

theorem ι₂_apply {a : M} (ha : a ∈ κ.source) : ι₂ κ (κ a) = ι₁ κ a :=
  (ι₁_eq_ι₂.2 ⟨ha, rfl⟩).symm

theorem ι₂_symm {b : M} (hb : b ∈ κ.target) : ι₁ κ (κ.symm b) = ι₂ κ b := by
  rw [← ι₂_apply (κ.map_target hb), κ.right_inv hb]

variable (κ)

theorem ι₁_injective : Injective (ι₁ κ) := fun _ _ h => Quotient.exact h

theorem ι₂_injective : Injective (ι₂ κ) := fun _ _ h => Quotient.exact h

theorem ι_cover (x : Glued κ) : x ∈ range (ι₁ κ) ∨ x ∈ range (ι₂ κ) := by
  induction x using Quotient.inductionOn with
  | h s => cases s with
    | inl a => exact Or.inl ⟨a, rfl⟩
    | inr b => exact Or.inr ⟨b, rfl⟩

theorem glued_isOpen_iff {s : Set (Glued κ)} :
    IsOpen s ↔ IsOpen (ι₁ κ ⁻¹' s) ∧ IsOpen (ι₂ κ ⁻¹' s) := by
  show IsOpen (Quotient.mk (glueSetoid κ) ⁻¹' s) ↔ _
  exact isOpen_sum_iff

theorem continuous_ι₁ : Continuous (ι₁ κ) := continuous_quotient_mk'.comp continuous_inl

theorem continuous_ι₂ : Continuous (ι₂ κ) := continuous_quotient_mk'.comp continuous_inr

theorem preimage_ι₂_image_ι₁ (O : Set M) : ι₂ κ ⁻¹' (ι₁ κ '' O) = κ '' (κ.source ∩ O) := by
  ext b
  simp only [mem_preimage, mem_image, ι₁_eq_ι₂]
  constructor
  · rintro ⟨a, ha, hs, rfl⟩; exact ⟨a, ⟨hs, ha⟩, rfl⟩
  · rintro ⟨a, ⟨hs, ha⟩, rfl⟩; exact ⟨a, ha, hs, rfl⟩

theorem preimage_ι₁_image_ι₂ (O : Set M) : ι₁ κ ⁻¹' (ι₂ κ '' O) = κ.source ∩ κ ⁻¹' O := by
  ext a
  simp only [mem_preimage, mem_image, mem_inter_iff]
  constructor
  · rintro ⟨b, hb, h⟩
    obtain ⟨hs, rfl⟩ := ι₁_eq_ι₂.1 h.symm
    exact ⟨hs, hb⟩
  · rintro ⟨hs, hb⟩; exact ⟨κ a, hb, ι₂_apply hs⟩

theorem isOpenEmbedding_ι₁ : IsOpenEmbedding (ι₁ κ) := by
  refine .of_continuous_injective_isOpenMap (continuous_ι₁ κ) (ι₁_injective κ) fun O hO => ?_
  rw [glued_isOpen_iff, (ι₁_injective κ).preimage_image, preimage_ι₂_image_ι₁]
  exact ⟨hO, κ.isOpen_image_source_inter hO⟩

theorem isOpenEmbedding_ι₂ : IsOpenEmbedding (ι₂ κ) := by
  refine .of_continuous_injective_isOpenMap (continuous_ι₂ κ) (ι₂_injective κ) fun O hO => ?_
  rw [glued_isOpen_iff, (ι₂_injective κ).preimage_image, preimage_ι₁_image_ι₂]
  exact ⟨κ.isOpen_inter_preimage hO, hO⟩

/-! ## Charts -/

variable [Nonempty M]

/-- The chart `ι₁⁻¹ : Glued κ ⇀ M`. -/
noncomputable def chart₁ : OpenPartialHomeomorph (Glued κ) M :=
  ((isOpenEmbedding_ι₁ κ).toOpenPartialHomeomorph (ι₁ κ)).symm

/-- The chart `ι₂⁻¹ : Glued κ ⇀ M`. -/
noncomputable def chart₂ : OpenPartialHomeomorph (Glued κ) M :=
  ((isOpenEmbedding_ι₂ κ).toOpenPartialHomeomorph (ι₂ κ)).symm

theorem chart₁_source : (chart₁ κ).source = range (ι₁ κ) := by simp [chart₁]

theorem chart₂_source : (chart₂ κ).source = range (ι₂ κ) := by simp [chart₂]

theorem chart₁_symm_apply (a : M) : (chart₁ κ).symm a = ι₁ κ a := by simp [chart₁]

theorem chart₂_symm_apply (b : M) : (chart₂ κ).symm b = ι₂ κ b := by simp [chart₂]

theorem chart₁_ι₁ (a : M) : chart₁ κ (ι₁ κ a) = a :=
  (isOpenEmbedding_ι₁ κ).toOpenPartialHomeomorph_left_inv (ι₁ κ)

theorem chart₂_ι₂ (b : M) : chart₂ κ (ι₂ κ b) = b :=
  (isOpenEmbedding_ι₂ κ).toOpenPartialHomeomorph_left_inv (ι₂ κ)

theorem ι₁_chart₁ {x : Glued κ} (hx : x ∈ range (ι₁ κ)) : ι₁ κ (chart₁ κ x) = x :=
  (isOpenEmbedding_ι₁ κ).toOpenPartialHomeomorph_right_inv (ι₁ κ) hx

theorem ι₂_chart₂ {x : Glued κ} (hx : x ∈ range (ι₂ κ)) : ι₂ κ (chart₂ κ x) = x :=
  (isOpenEmbedding_ι₂ κ).toOpenPartialHomeomorph_right_inv (ι₂ κ) hx

open Classical in
/-- `Glued κ` is a charted space over `M`, with the two charts `ι₁⁻¹`, `ι₂⁻¹`. -/
noncomputable instance chartedSpaceOverM : ChartedSpace M (Glued κ) where
  atlas := {chart₁ κ, chart₂ κ}
  chartAt x := if x ∈ range (ι₁ κ) then chart₁ κ else chart₂ κ
  mem_chart_source x := by
    split_ifs with h
    · rw [chart₁_source]; exact h
    · rw [chart₂_source]; exact (ι_cover κ x).resolve_left h
  chart_mem_atlas x := by split_ifs <;> simp

/-- `Glued κ` is a charted space over `H`, by composing with the charts of `M`. -/
noncomputable instance (priority := 100) chartedSpaceGlued : ChartedSpace H (Glued κ) :=
  ChartedSpace.comp H M (Glued κ)

/-! ## Smooth structure -/

variable {κ}

variable [IsManifold I ∞ M] (hκ : ContMDiffOn I I ∞ κ κ.source)
  (hκs : ContMDiffOn I I ∞ κ.symm κ.target)

omit [IsManifold I ∞ M] in
theorem mem_trans_source {c c' : OpenPartialHomeomorph (Glued κ) M} {a : M} :
    a ∈ (c.symm ≫ₕ c').source ↔ a ∈ c.target ∧ c.symm a ∈ c'.source := by
  simp [OpenPartialHomeomorph.trans_source]

include hκ hκs in
theorem transitions_mem :
    ∀ c ∈ atlas M (Glued κ), ∀ c' ∈ atlas M (Glued κ), c.symm ≫ₕ c' ∈ smoothGroupoid I M := by
  have t₁ : (chart₁ κ).target = univ := by simp [chart₁]
  have t₂ : (chart₂ κ).target = univ := by simp [chart₂]
  -- the four transitions, as functions on their sources
  have h11 : ∀ a ∈ ((chart₁ κ).symm ≫ₕ chart₁ κ).source,
      ((chart₁ κ).symm ≫ₕ chart₁ κ) a = id a := fun a _ => by
    simp [chart₁_symm_apply, chart₁_ι₁]
  have h22 : ∀ a ∈ ((chart₂ κ).symm ≫ₕ chart₂ κ).source,
      ((chart₂ κ).symm ≫ₕ chart₂ κ) a = id a := fun a _ => by
    simp [chart₂_symm_apply, chart₂_ι₂]
  have s12 : ((chart₁ κ).symm ≫ₕ chart₂ κ).source ⊆ κ.source := fun a ha => by
    rw [mem_trans_source, chart₂_source, chart₁_symm_apply] at ha
    obtain ⟨b, hb⟩ := ha.2
    exact (ι₁_eq_ι₂.1 hb.symm).1
  have h12 : ∀ a ∈ ((chart₁ κ).symm ≫ₕ chart₂ κ).source,
      ((chart₁ κ).symm ≫ₕ chart₂ κ) a = κ a := fun a ha => by
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply, chart₁_symm_apply]
    rw [← ι₂_apply (s12 ha), chart₂_ι₂]
  have s21 : ((chart₂ κ).symm ≫ₕ chart₁ κ).source ⊆ κ.target := fun b hb => by
    rw [mem_trans_source, chart₁_source, chart₂_symm_apply] at hb
    obtain ⟨a, ha⟩ := hb.2
    obtain ⟨hs, rfl⟩ := ι₁_eq_ι₂.1 ha
    exact κ.map_source hs
  have h21 : ∀ b ∈ ((chart₂ κ).symm ≫ₕ chart₁ κ).source,
      ((chart₂ κ).symm ≫ₕ chart₁ κ) b = κ.symm b := fun b hb => by
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply, chart₂_symm_apply]
    rw [← ι₂_symm (s21 hb), chart₁_ι₁]
  have key : ∀ c c' : OpenPartialHomeomorph (Glued κ) M,
      ContMDiffOn I I ∞ (c.symm ≫ₕ c') (c.symm ≫ₕ c').source →
      ContMDiffOn I I ∞ (c'.symm ≫ₕ c) (c'.symm ≫ₕ c).source → c.symm ≫ₕ c' ∈ smoothGroupoid I M := by
    intro c c' h h'
    refine (mem_smoothGroupoid I (M := M)).2 ⟨h, ?_⟩
    have e : (c.symm ≫ₕ c').symm = c'.symm ≫ₕ c := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    rw [← OpenPartialHomeomorph.symm_source, e]
    exact h'
  have P11 : ContMDiffOn I I ∞ ((chart₁ κ).symm ≫ₕ chart₁ κ) ((chart₁ κ).symm ≫ₕ chart₁ κ).source :=
    contMDiffOn_id.congr h11
  have P22 : ContMDiffOn I I ∞ ((chart₂ κ).symm ≫ₕ chart₂ κ) ((chart₂ κ).symm ≫ₕ chart₂ κ).source :=
    contMDiffOn_id.congr h22
  have P12 : ContMDiffOn I I ∞ ((chart₁ κ).symm ≫ₕ chart₂ κ) ((chart₁ κ).symm ≫ₕ chart₂ κ).source :=
    (hκ.mono s12).congr h12
  have P21 : ContMDiffOn I I ∞ ((chart₂ κ).symm ≫ₕ chart₁ κ) ((chart₂ κ).symm ≫ₕ chart₁ κ).source :=
    (hκs.mono s21).congr h21
  intro c hc c' hc'
  change c ∈ ({chart₁ κ, chart₂ κ} : Set _) at hc
  change c' ∈ ({chart₁ κ, chart₂ κ} : Set _) at hc'
  simp only [mem_insert_iff, mem_singleton_iff] at hc hc'
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact key _ _ P11 P11
  · exact key _ _ P12 P21
  · exact key _ _ P21 P12
  · exact key _ _ P22 P22

include hκ hκs in
theorem hasGroupoid_smooth : HasGroupoid (Glued κ) (smoothGroupoid I M) :=
  ⟨fun he he' => transitions_mem I hκ hκs _ he _ he'⟩

include hκ hκs in
/-- **`Glued κ` is a `C^∞` manifold.** -/
theorem isManifold_glued : IsManifold I ∞ (Glued κ) :=
  haveI := hasGroupoid_smooth I hκ hκs
  { compatible := (StructureGroupoid.HasGroupoid.comp (G₁ := contDiffGroupoid ∞ I) (G₂ := smoothGroupoid I M)
      fun e he => (isLocalStructomorphOn_contDiffGroupoid_iff e).2
        ((mem_smoothGroupoid I (M := M)).1 he)).compatible }

omit [IsManifold I ∞ M] in
theorem chart₁_trans_mem (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) :
    chart₁ κ ≫ₕ c ∈ atlas H (Glued κ) :=
  mem_image2_of_mem (show chart₁ κ ∈ ({chart₁ κ, chart₂ κ} : Set _) by simp) hc

omit [IsManifold I ∞ M] in
theorem chart₂_trans_mem (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) :
    chart₂ κ ≫ₕ c ∈ atlas H (Glued κ) :=
  mem_image2_of_mem (show chart₂ κ ∈ ({chart₁ κ, chart₂ κ} : Set _) by simp) hc

include hκ hκs in
theorem contMDiff_ι₁ : haveI := isManifold_glued I hκ hκs; ContMDiff I I ∞ (ι₁ κ) := by
  haveI := isManifold_glued I hκ hκs
  intro a
  set c := chartAt H a
  have hmem : chart₁ κ ≫ₕ c ∈ IsManifold.maximalAtlas I ∞ (Glued κ) :=
    IsManifold.subset_maximalAtlas (chart₁_trans_mem c (chart_mem_atlas H a))
  have h1 := contMDiffOn_symm_of_mem_maximalAtlas hmem
  have h2 : ContMDiffOn I I ∞ (fun y => (chart₁ κ ≫ₕ c).symm (c y)) c.source :=
    h1.comp contMDiffOn_chart fun y hy => by
      rw [OpenPartialHomeomorph.trans_target]; exact ⟨c.map_source hy, by simp [chart₁]⟩
  have h3 : ContMDiffOn I I ∞ (ι₁ κ) c.source := h2.congr fun y hy => by
    simp only [OpenPartialHomeomorph.coe_trans_symm, comp_apply, c.left_inv hy, chart₁_symm_apply]
  exact h3.contMDiffAt (c.open_source.mem_nhds (mem_chart_source H a))

include hκ hκs in
theorem contMDiff_ι₂ : haveI := isManifold_glued I hκ hκs; ContMDiff I I ∞ (ι₂ κ) := by
  haveI := isManifold_glued I hκ hκs
  intro b
  set c := chartAt H b
  have hmem : chart₂ κ ≫ₕ c ∈ IsManifold.maximalAtlas I ∞ (Glued κ) :=
    IsManifold.subset_maximalAtlas (chart₂_trans_mem c (chart_mem_atlas H b))
  have h1 := contMDiffOn_symm_of_mem_maximalAtlas hmem
  have h2 : ContMDiffOn I I ∞ (fun y => (chart₂ κ ≫ₕ c).symm (c y)) c.source :=
    h1.comp contMDiffOn_chart fun y hy => by
      rw [OpenPartialHomeomorph.trans_target]; exact ⟨c.map_source hy, by simp [chart₂]⟩
  have h3 : ContMDiffOn I I ∞ (ι₂ κ) c.source := h2.congr fun y hy => by
    simp only [OpenPartialHomeomorph.coe_trans_symm, comp_apply, c.left_inv hy, chart₂_symm_apply]
  exact h3.contMDiffAt (c.open_source.mem_nhds (mem_chart_source H b))

include hκ hκs in
theorem contMDiffAt_chart₁ {x : Glued κ} (hx : x ∈ range (ι₁ κ)) :
    haveI := isManifold_glued I hκ hκs; ContMDiffAt I I ∞ (chart₁ κ) x := by
  haveI := isManifold_glued I hκ hκs
  set c := chartAt H (chart₁ κ x)
  have hmem : chart₁ κ ≫ₕ c ∈ IsManifold.maximalAtlas I ∞ (Glued κ) :=
    IsManifold.subset_maximalAtlas (chart₁_trans_mem c (chart_mem_atlas H _))
  have hxs : x ∈ (chart₁ κ ≫ₕ c).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by rw [chart₁_source]; exact hx, mem_chart_source H _⟩
  have h1 : ContMDiffAt I I ∞ (chart₁ κ ≫ₕ c) x :=
    (contMDiffOn_of_mem_maximalAtlas hmem).contMDiffAt
      ((chart₁ κ ≫ₕ c).open_source.mem_nhds hxs)
  have h2 : ContMDiffAt I I ∞ c.symm ((chart₁ κ ≫ₕ c) x) :=
    (contMDiffOn_chart_symm).contMDiffAt (c.open_target.mem_nhds (by
      have := (chart₁ κ ≫ₕ c).map_source hxs
      rw [OpenPartialHomeomorph.trans_target] at this; exact this.1))
  refine (h2.comp x h1).congr_of_eventuallyEq ?_
  filter_upwards [(chart₁ κ ≫ₕ c).open_source.mem_nhds hxs] with y hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  simp only [comp_apply, OpenPartialHomeomorph.coe_trans, c.left_inv hy.2]

include hκ hκs in
theorem contMDiffAt_chart₂ {x : Glued κ} (hx : x ∈ range (ι₂ κ)) :
    haveI := isManifold_glued I hκ hκs; ContMDiffAt I I ∞ (chart₂ κ) x := by
  haveI := isManifold_glued I hκ hκs
  set c := chartAt H (chart₂ κ x)
  have hmem : chart₂ κ ≫ₕ c ∈ IsManifold.maximalAtlas I ∞ (Glued κ) :=
    IsManifold.subset_maximalAtlas (chart₂_trans_mem c (chart_mem_atlas H _))
  have hxs : x ∈ (chart₂ κ ≫ₕ c).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by rw [chart₂_source]; exact hx, mem_chart_source H _⟩
  have h1 : ContMDiffAt I I ∞ (chart₂ κ ≫ₕ c) x :=
    (contMDiffOn_of_mem_maximalAtlas hmem).contMDiffAt
      ((chart₂ κ ≫ₕ c).open_source.mem_nhds hxs)
  have h2 : ContMDiffAt I I ∞ c.symm ((chart₂ κ ≫ₕ c) x) :=
    (contMDiffOn_chart_symm).contMDiffAt (c.open_target.mem_nhds (by
      have := (chart₂ κ ≫ₕ c).map_source hxs
      rw [OpenPartialHomeomorph.trans_target] at this; exact this.1))
  refine (h2.comp x h1).congr_of_eventuallyEq ?_
  filter_upwards [(chart₂ κ ≫ₕ c).open_source.mem_nhds hxs] with y hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  simp only [comp_apply, OpenPartialHomeomorph.coe_trans, c.left_inv hy.2]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

include hκ hκs in
/-- **A map out of `Glued κ` is smooth iff its restrictions to both copies are.** -/
theorem contMDiff_of_comp_ι {f : Glued κ → N} (h₁ : ContMDiff I I' ∞ (f ∘ ι₁ κ))
    (h₂ : ContMDiff I I' ∞ (f ∘ ι₂ κ)) :
    haveI := isManifold_glued I hκ hκs; ContMDiff I I' ∞ f := by
  haveI := isManifold_glued I hκ hκs
  intro x
  rcases ι_cover κ x with hx | hx
  · refine ((h₁ (chart₁ κ x)).comp x (contMDiffAt_chart₁ I hκ hκs hx)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpenEmbedding_ι₁ κ).isOpen_range.mem_nhds hx] with y hy
    simp only [comp_apply, ι₁_chart₁ κ hy]
  · refine ((h₂ (chart₂ κ x)).comp x (contMDiffAt_chart₂ I hκ hκs hx)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpenEmbedding_ι₂ κ).isOpen_range.mem_nhds hx] with y hy
    simp only [comp_apply, ι₂_chart₂ κ hy]

omit [Nonempty M] [IsManifold I ∞ M] in
/-- Maps compatible with `κ` descend to `Glued κ`. -/
def glueLift {X : Type*} (g₁ g₂ : M → X) (hg : ∀ a ∈ κ.source, g₂ (κ a) = g₁ a) : Glued κ → X :=
  Quotient.lift (Sum.elim g₁ g₂) (by
    rintro (a | b) (a' | b') h <;> change GlueRel κ _ _ at h <;> simp only [GlueRel] at h
    · exact congrArg g₁ h
    · simp only [Sum.elim_inl, Sum.elim_inr]; rw [← h.2, hg a h.1]
    · simp only [Sum.elim_inl, Sum.elim_inr]; rw [← h.2, hg a' h.1]
    · exact congrArg g₂ h)

omit [Nonempty M] [IsManifold I ∞ M] in
@[simp] theorem glueLift_ι₁ {X : Type*} (g₁ g₂ : M → X) (hg) (a : M) :
    glueLift g₁ g₂ hg (ι₁ κ a) = g₁ a := rfl

omit [Nonempty M] [IsManifold I ∞ M] in
@[simp] theorem glueLift_ι₂ {X : Type*} (g₁ g₂ : M → X) (hg) (b : M) :
    glueLift g₁ g₂ hg (ι₂ κ b) = g₂ b := rfl

omit [Nonempty M] [IsManifold I ∞ M] in
theorem continuous_glueLift {X : Type*} [TopologicalSpace X] {g₁ g₂ : M → X} (hg)
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) : Continuous (glueLift g₁ g₂ hg : Glued κ → X) :=
  (h₁.sumElim h₂).quotient_lift _

include hκ hκs in
theorem contMDiff_glueLift {g₁ g₂ : M → N} (hg) (h₁ : ContMDiff I I' ∞ g₁)
    (h₂ : ContMDiff I I' ∞ g₂) :
    haveI := isManifold_glued I hκ hκs; ContMDiff I I' ∞ (glueLift g₁ g₂ hg : Glued κ → N) :=
  contMDiff_of_comp_ι I hκ hκs h₁ h₂

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} {N' : Type*} [TopologicalSpace N']
  [ChartedSpace H'' N']

include hκ hκs in
/-- **Parametrised version:** a map `N × Glued κ → N'` is smooth iff both restrictions
`N × M → N'` are (used for the joint smoothness of group actions). -/
theorem contMDiff_prod_glued [IsManifold I' ∞ N] {f : N × Glued κ → N'}
    (h₁ : ContMDiff (I'.prod I) I'' ∞ fun p : N × M => f (p.1, ι₁ κ p.2))
    (h₂ : ContMDiff (I'.prod I) I'' ∞ fun p : N × M => f (p.1, ι₂ κ p.2)) :
    haveI := isManifold_glued I hκ hκs; ContMDiff (I'.prod I) I'' ∞ f := by
  haveI := isManifold_glued I hκ hκs
  rintro ⟨n, x⟩
  rcases ι_cover κ x with hx | hx
  · refine ((h₁ (n, chart₁ κ x)).comp (n, x)
      (contMDiffAt_id.prodMap (contMDiffAt_chart₁ I hκ hκs hx))).congr_of_eventuallyEq ?_
    filter_upwards [prod_mem_nhds Filter.univ_mem
      ((isOpenEmbedding_ι₁ κ).isOpen_range.mem_nhds hx)] with p hp
    simp only [comp_apply, Prod.map_fst, Prod.map_snd, id, ι₁_chart₁ κ hp.2]
  · refine ((h₂ (n, chart₂ κ x)).comp (n, x)
      (contMDiffAt_id.prodMap (contMDiffAt_chart₂ I hκ hκs hx))).congr_of_eventuallyEq ?_
    filter_upwards [prod_mem_nhds Filter.univ_mem
      ((isOpenEmbedding_ι₂ κ).isOpen_range.mem_nhds hx)] with p hp
    simp only [comp_apply, Prod.map_fst, Prod.map_snd, id, ι₂_chart₂ κ hp.2]

/-! ## Partial homeomorphisms from self-homeomorphisms of an open subset -/

section OpensPH

variable {X : Type*} [TopologicalSpace X]

open Classical in
/-- A homeomorphism `Φ` of an open set `U ⊆ X`, as an open partial homeomorphism of `X`
with source and target `U`. -/
noncomputable def opensPH (U : TopologicalSpace.Opens X) (Φ : U ≃ₜ U) :
    OpenPartialHomeomorph X X where
  toFun p := if hp : p ∈ U then (Φ ⟨p, hp⟩ : X) else p
  invFun p := if hp : p ∈ U then (Φ.symm ⟨p, hp⟩ : X) else p
  source := U
  target := U
  map_source' p hp := by
    have hp' : p ∈ U := hp; rw [dif_pos hp']; exact (Φ _).2
  map_target' p hp := by
    have hp' : p ∈ U := hp; rw [dif_pos hp']; exact (Φ.symm _).2
  left_inv' p hp := by
    have hp' : p ∈ U := hp; rw [dif_pos hp', dif_pos (Φ ⟨p, hp'⟩).2]; simp
  right_inv' p hp := by
    have hp' : p ∈ U := hp; rw [dif_pos hp', dif_pos (Φ.symm ⟨p, hp'⟩).2]; simp
  open_source := U.isOpen
  open_target := U.isOpen
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_subtype_val.comp Φ.continuous).congr fun x => by
      show (Φ x : X) = (if hp : (x : X) ∈ U then (Φ ⟨x, hp⟩ : X) else x)
      rw [dif_pos x.2]
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_subtype_val.comp Φ.symm.continuous).congr fun x => by
      show (Φ.symm x : X) = (if hp : (x : X) ∈ U then (Φ.symm ⟨x, hp⟩ : X) else x)
      rw [dif_pos x.2]

theorem opensPH_apply (U : TopologicalSpace.Opens X) (Φ : U ≃ₜ U) (x : U) :
    opensPH U Φ x = Φ x :=
  dif_pos x.2

theorem opensPH_symm_apply (U : TopologicalSpace.Opens X) (Φ : U ≃ₜ U) (x : U) :
    (opensPH U Φ).symm x = Φ.symm x :=
  dif_pos x.2

@[simp] theorem opensPH_source (U : TopologicalSpace.Opens X) (Φ : U ≃ₜ U) :
    (opensPH U Φ).source = U := rfl

@[simp] theorem opensPH_target (U : TopologicalSpace.Opens X) (Φ : U ≃ₜ U) :
    (opensPH U Φ).target = U := rfl

end OpensPH

omit [Nonempty M] [IsManifold I ∞ M] in
theorem contMDiffOn_opensPH (U : TopologicalSpace.Opens M) (Φ : U ≃ₜ U)
    (hΦ : ContMDiff I I ∞ fun x : U => (Φ x : M)) :
    ContMDiffOn I I ∞ (opensPH U Φ) (opensPH U Φ).source := by
  intro p hp
  have h : ContMDiffAt I I ∞ (fun x : U => opensPH U Φ x) ⟨p, hp⟩ :=
    (hΦ ⟨p, hp⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => opensPH_apply U Φ x)
  exact ((contMDiffAt_subtype_iff (U := U) (x := ⟨p, hp⟩)).1 h).contMDiffWithinAt

omit [Nonempty M] [IsManifold I ∞ M] in
theorem contMDiffOn_opensPH_symm (U : TopologicalSpace.Opens M) (Φ : U ≃ₜ U)
    (hΦ : ContMDiff I I ∞ fun x : U => (Φ.symm x : M)) :
    ContMDiffOn I I ∞ (opensPH U Φ).symm (opensPH U Φ).target := by
  intro p hp
  have h : ContMDiffAt I I ∞ (fun x : U => (opensPH U Φ).symm x) ⟨p, hp⟩ :=
    (hΦ ⟨p, hp⟩).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => opensPH_symm_apply U Φ x)
  exact ((contMDiffAt_subtype_iff (U := U) (x := ⟨p, hp⟩)).1 h).contMDiffWithinAt

omit [Nonempty M] [IsManifold I ∞ M] in
theorem glued_induction {P : Glued κ → Prop} (h₁ : ∀ a, P (ι₁ κ a)) (h₂ : ∀ b, P (ι₂ κ b))
    (x : Glued κ) : P x := by
  rcases ι_cover κ x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  exacts [h₁ a, h₂ b]

omit [Nonempty M] [IsManifold I ∞ M] in
/-- **Hausdorff criterion for `Glued κ`.** If `M` is Hausdorff and a continuous map to a
Hausdorff space separates the unglued points of the first copy from those of the second, then
`Glued κ` is Hausdorff. -/
theorem t2Space_glued [T2Space M] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : Glued κ → Y) (hf : Continuous f)
    (hsep : ∀ a ∉ κ.source, ∀ b ∉ κ.target, f (ι₁ κ a) ≠ f (ι₂ κ b)) : T2Space (Glued κ) := by
  have sep₁ : ∀ a a' : M, a ≠ a' → ∃ u v : Set (Glued κ), IsOpen u ∧ IsOpen v ∧
      ι₁ κ a ∈ u ∧ ι₁ κ a' ∈ v ∧ Disjoint u v := fun a a' h => by
    obtain ⟨u, v, hu, hv, hau, hav, huv⟩ := t2_separation h
    exact ⟨_, _, (isOpenEmbedding_ι₁ κ).isOpenMap u hu, (isOpenEmbedding_ι₁ κ).isOpenMap v hv,
      mem_image_of_mem _ hau, mem_image_of_mem _ hav,
      (disjoint_image_iff (ι₁_injective κ)).2 huv⟩
  have sep₂ : ∀ b b' : M, b ≠ b' → ∃ u v : Set (Glued κ), IsOpen u ∧ IsOpen v ∧
      ι₂ κ b ∈ u ∧ ι₂ κ b' ∈ v ∧ Disjoint u v := fun b b' h => by
    obtain ⟨u, v, hu, hv, hau, hav, huv⟩ := t2_separation h
    exact ⟨_, _, (isOpenEmbedding_ι₂ κ).isOpenMap u hu, (isOpenEmbedding_ι₂ κ).isOpenMap v hv,
      mem_image_of_mem _ hau, mem_image_of_mem _ hav,
      (disjoint_image_iff (ι₂_injective κ)).2 huv⟩
  have sepf : ∀ x y : Glued κ, f x ≠ f y → ∃ u v : Set (Glued κ), IsOpen u ∧ IsOpen v ∧
      x ∈ u ∧ y ∈ v ∧ Disjoint u v := fun x y h => by
    obtain ⟨u, v, hu, hv, hau, hav, huv⟩ := t2_separation h
    exact ⟨_, _, hu.preimage hf, hv.preimage hf, hau, hav, huv.preimage f⟩
  -- a point of the first copy outside the source is not in the second copy, and conversely
  have key : ∀ a b, ι₁ κ a ≠ ι₂ κ b → ∃ u v : Set (Glued κ), IsOpen u ∧ IsOpen v ∧
      ι₁ κ a ∈ u ∧ ι₂ κ b ∈ v ∧ Disjoint u v := fun a b hab => by
    by_cases ha : a ∈ κ.source
    · rw [← ι₂_apply ha] at hab ⊢
      exact sep₂ _ _ fun h => hab (congrArg _ h)
    · by_cases hb : b ∈ κ.target
      · rw [← ι₂_symm hb] at hab ⊢
        exact sep₁ _ _ fun h => hab (congrArg _ h)
      · exact sepf _ _ (hsep a ha b hb)
  refine ⟨fun x y hxy => ?_⟩
  induction x using glued_induction with
  | h₁ a =>
    induction y using glued_induction with
    | h₁ a' => exact sep₁ a a' fun h => hxy (congrArg _ h)
    | h₂ b => exact key a b hxy
  | h₂ b =>
    induction y using glued_induction with
    | h₁ a =>
      obtain ⟨u, v, hu, hv, h1, h2, h3⟩ := key a b (Ne.symm hxy)
      exact ⟨v, u, hv, hu, h2, h1, h3.symm⟩
    | h₂ b' => exact sep₂ b b' fun h => hxy (congrArg _ h)

end ExoticSpheres8And10
