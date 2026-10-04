/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.KoszulRegularity
import RiemannianGeometry.HomBundleFrame
import RiemannianGeometry.ManifoldOrder
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# The Koszul form as a smooth bilinear form on the tangent bundle

That is the last analytic ingredient of the Levi-Civita existence proof:
`ContMDiffCovariantDerivativeOn` demands a `C^m` section out, so a pointwise formula does not
suffice.

## Main results

* `tensorial_koszulRHS_direction`, `tensorial_koszulRHS_diffslot` — `κ` is tensorial in each
  tangent slot. In the differentiated slot this is *not* automatic: one of the six terms
  differentiates that slot, and the correction terms cancel **precisely because `g` is symmetric**.
* `IsKoszulTensorialAt`, `koszulSection`, `koszulSection_apply` — the bundling.
* `isKoszulTensorialAt_of_mdifferentiableAt` — the side conditions from differentiability alone.
* `contMDiffAt_hom_hom_of_eq_koszulRHS` — the **double frame test**, stated for any field of
  bilinear forms agreeing with `κ` on differentiable sections.
* `contMDiffAt_koszulSection` — the conclusion.

## Why `koszulSection` is defined by `dite`

`TensorialAt.mkHom₂` takes its two tensoriality facts as *arguments*. A definition carrying those
proofs is therefore not a section of a bundle at all, and smoothness cannot even be stated for it.
So the side conditions are packaged as a predicate `IsKoszulTensorialAt` and the definition is made
total, with junk value `0` where they fail — exactly the device `Trivialization.localFrame` uses for
points outside a base set. `koszulSection_eq_mkHom₂` says nothing is lost.

This is what keeps every hypothesis below **local**: a proof-carrying definition would have forced
the tensoriality data to be available globally before smoothness could be discussed.

## How the smoothness is proved

The frame test of `RiemannianGeometry.HomBundleFrame` — a hom-section is `C^n` once its values on the local
frame of a trivialisation are — applied **twice**: once in the inner slot, with target the trivial
line bundle, and once in the outer slot, with target `Hom(TM, ℝ)`. That reduces everything to the
scalars `y ↦ κ (s i) Y y (s j)`, which are `C^m` by `contMDiffAt_koszulRHS`. Two small steps are
easy to miss: the tensoriality side conditions cannot be discharged by the pairing lemmas of
`KoszulRegularity` (those need `C^n` with `n ≥ 1`, whereas `TensorialAt`'s fields supply only
`MDifferentiableAt` sections — the route is `MDifferentiableAt.clm_bundle_apply₂`), and lifting a
scalar to a section of the trivial line bundle is a step rather than a coercion.

## Conventions and hypotheses

`cov σ x v` is `(∇_v σ)(x)`: the **direction is the last argument**. The metric is supplied as data
`g : Π x, T_xM →L[ℝ] T_xM →L[ℝ] ℝ`, so everything here covers pseudo-Riemannian metrics; only
symmetry is used, never positive-definiteness. `[IsManifold I ∞ M]` is the manifold hypothesis, and
it suffices only because of the two instances in `RiemannianGeometry.ManifoldOrder`.
-/

noncomputable section

open Bundle VectorField Set Module Filter
open scoped RiemannianGeometry.ManifoldOrder
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Tensoriality of `koszulRHS`  -/

section Tensoriality

variable {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
  {X Y Z : Π y : M, TangentSpace I y}

omit [FiniteDimensional ℝ E] in
theorem tensorial_koszulRHS_diffslot {y : M}
    (hsymm : ∀ (z : M) (a b : TangentSpace I z), g z a b = g z b a)
    (hgd : ∀ {U W : Π z : M, TangentSpace I z}, MDiffAt (T% U) y → MDiffAt (T% W) y →
      MDiffAt (fun z ↦ g z (U z) (W z)) y)
    (hX : MDiffAt (T% X) y) (hY : MDiffAt (T% Y) y) :
    TensorialAt I E (koszulRHS g X Y y) y where
  add {Z Z'} hZ hZ' := by
    simp only [koszulRHS, Pi.add_apply, map_add,
      mvfderiv_fun_add (hgd hY hZ) (hgd hY hZ'),
      mvfderiv_fun_add (hgd hZ hX) (hgd hZ' hX),
      mlieBracket_add_right hZ hZ', add_apply]
    ring
  smul {f Z} hf hZ := by
    simp only [koszulRHS, Pi.smul_apply', map_smul, smul_eq_mul,
      mvfderiv_fun_mul hf (hgd hY hZ), mvfderiv_fun_mul hf (hgd hZ hX),
      mlieBracket_smul_right hf hZ, map_add, add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [hsymm y (Y y) (Z y)]
    ring

omit [FiniteDimensional ℝ E] in
theorem tensorial_koszulRHS_direction {y : M}
    (hsymm : ∀ (z : M) (a b : TangentSpace I z), g z a b = g z b a)
    (hgd : ∀ {U W : Π z : M, TangentSpace I z}, MDiffAt (T% U) y → MDiffAt (T% W) y →
      MDiffAt (fun z ↦ g z (U z) (W z)) y)
    (hY : MDiffAt (T% Y) y) (hZ : MDiffAt (T% Z) y) :
    TensorialAt I E (fun X ↦ koszulRHS g X Y y Z) y where
  add {X X'} hX hX' := by
    simp only [koszulRHS, Pi.add_apply, map_add,
      mvfderiv_fun_add (hgd hZ hX) (hgd hZ hX'),
      mvfderiv_fun_add (hgd hX hY) (hgd hX' hY),
      mlieBracket_add_left hX hX', add_apply]
    ring
  smul {f X} hf hX := by
    simp only [koszulRHS, Pi.smul_apply', map_smul, smul_eq_mul,
      mvfderiv_fun_mul hf (hgd hZ hX), mvfderiv_fun_mul hf (hgd hX hY),
      mlieBracket_smul_left hf hX, map_add, add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [hsymm y (Z y) (X y)]
    ring

end Tensoriality

/-! ## The bundled Koszul form, defined at every point of `M` -/

/-- The two pointwise tensoriality facts that `TensorialAt.mkHom₂` needs at `y` in order to
bundle the Koszul right-hand side into a continuous bilinear form on `T_y M`. -/
def IsKoszulTensorialAt (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (Y : Π y : M, TangentSpace I y) (y : M) : Prop :=
  (∀ Z : Π z : M, TangentSpace I z, MDiffAt (T% Z) y →
      TensorialAt I E (fun U ↦ koszulRHS g U Y y Z) y) ∧
  (∀ U : Π z : M, TangentSpace I z, MDiffAt (T% U) y →
      TensorialAt I E (koszulRHS g U Y y) y)

open Classical in
/-- The Koszul form, bundled as a section of `Hom(TM, Hom(TM, ℝ))` over **all** of `M`, with the
junk value `0` at the points where the tensoriality side conditions are not available. -/
def koszulSection (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (Y : Π y : M, TangentSpace I y) :
    Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
  fun y ↦ if h : IsKoszulTensorialAt g Y y then
      TensorialAt.mkHom₂ (fun U Z ↦ koszulRHS g U Y y Z) y h.1 h.2
    else 0

omit [CompleteSpace E] in
/-- Where the side conditions hold, `koszulSection` **is** the `TensorialAt.mkHom₂` bundling of
the Koszul right-hand side: no mathematical content is lost by the junk value. -/
theorem koszulSection_eq_mkHom₂ {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {Y : Π y : M, TangentSpace I y} {y : M} (h : IsKoszulTensorialAt g Y y) :
    koszulSection g Y y = TensorialAt.mkHom₂ (fun U Z ↦ koszulRHS g U Y y Z) y h.1 h.2 :=
  dif_pos h

omit [CompleteSpace E] in
theorem koszulSection_apply {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {Y : Π y : M, TangentSpace I y} {y : M} (h : IsKoszulTensorialAt g Y y)
    {U Z : Π z : M, TangentSpace I z} (hU : MDiffAt (T% U) y) (hZ : MDiffAt (T% Z) y) :
    koszulSection g Y y (U y) (Z y) = koszulRHS g U Y y Z := by
  rw [koszulSection_eq_mkHom₂ h]
  exact TensorialAt.mkHom₂_apply _ _ hU hZ

omit [CompleteSpace E] in
/-- `koszulSection` evaluated on *arbitrary* tangent vectors, through `FiberBundle.extend`. This is
the form in which the connection's identities are derived, since it quantifies over all of `T_yM`
rather than over differentiable sections. -/
theorem koszulSection_apply_extend
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {Y : Π y : M, TangentSpace I y} {y : M} (h : IsKoszulTensorialAt g Y y)
    (v w : TangentSpace I y) :
    koszulSection g Y y v w
      = koszulRHS g (FiberBundle.extend E v) Y y (FiberBundle.extend E w) := by
  rw [koszulSection_eq_mkHom₂ h]
  exact TensorialAt.mkHom₂_apply_eq_extend _ _ v w

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Differentiability of the pairing, from differentiability of the metric section.**

`y ↦ g y (U y) (W y)` is differentiable at `y` as soon as `g`, `U` and `W` are. Note this cannot be
obtained from the `contMDiff*_pairing` lemmas of `RiemannianGeometry.KoszulRegularity`: those need `C^n`
sections with `n ≥ 1`, while `TensorialAt`'s fields supply sections that are only
`MDifferentiableAt`, and differentiability cannot be upgraded. The route is
`MDifferentiableAt.clm_bundle_apply₂` with the target read as the trivial line bundle. -/
theorem mdiffAt_pairing
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ} {y : M}
    (hgm : MDiffAt (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun (z : M) ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z (g z)) y)
    {U W : Π z : M, TangentSpace I z} (hU : MDiffAt (T% U) y) (hW : MDiffAt (T% W) y) :
    MDiffAt (fun z ↦ g z (U z) (W z)) y := by
  have h : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun z ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z (g z (U z) (W z))) y :=
    MDifferentiableAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) hgm hU hW
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

omit [FiniteDimensional ℝ E] in
/-- The tensoriality side conditions hold at `y` as soon as `g` is symmetric, `g` is
`MDifferentiable` at `y` as a section, and `Y` is `MDifferentiable` at `y`. -/
theorem isKoszulTensorialAt_of_mdifferentiableAt
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {Y : Π y : M, TangentSpace I y} {y : M}
    (hsymm : ∀ (z : M) (a b : TangentSpace I z), g z a b = g z b a)
    (hgm : MDiffAt (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun (z : M) ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z (g z)) y)
    (hY : MDiffAt (T% Y) y) :
    IsKoszulTensorialAt g Y y :=
  ⟨fun _ hZ ↦ tensorial_koszulRHS_direction hsymm (mdiffAt_pairing hgm) hY hZ,
    fun _ hU ↦ tensorial_koszulRHS_diffslot hsymm (mdiffAt_pairing hgm) hU hY⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Sections of the trivial line bundle: a `C^n` scalar function is a `C^n` section. -/
theorem contMDiffAt_trivial_section {n : ℕ∞ω} {f : M → ℝ} {y : M}
    (hf : ContMDiffAt I 𝓘(ℝ) n f y) :
    ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) n
      (fun z ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z (f z)) y := by
  rw [Bundle.contMDiffAt_section]
  exact hf

/-! ## The double frame test -/

section FrameTest

variable {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
  {Y : Π y : M, TangentSpace I y}
  {Kf : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}

/-- **The double frame test**, relative to a chosen atlas trivialisation `e` and basis `b`.

Any field `Kf` of bilinear forms which agrees with `koszulRHS g · Y y ·` on `MDifferentiable`
sections, at every point of an open set `u`, is a `C^m` section of `Hom(TM, Hom(TM, ℝ))` at each
point of `u`, provided the metric-as-data `g` and the field `Y` are `C^(m+1)` on `u`. -/
theorem contMDiffAt_hom_hom_of_eq_koszulRHS_frame {m : ℕ∞} {u : Set M} {x : M}
    {ι : Type*} [Finite ι] (b : Basis ι ℝ E)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (hxe : x ∈ e.baseSet)
    (hu : IsOpen u) (hxu : x ∈ u)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m + 1 : ℕ∞))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) u)
    (hY : CMDiff[u] ((m + 1 : ℕ∞)) (T% Y))
    (hKf : ∀ y ∈ u, ∀ U Z : Π z : M, TangentSpace I z, MDiffAt (T% U) y → MDiffAt (T% Z) y →
      Kf y (U y) (Z y) = koszulRHS g U Y y Z) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)))
        y (Kf y)) x := by
  have hvopen : IsOpen (u ∩ e.baseSet) := hu.inter e.open_baseSet
  have hxv : x ∈ u ∩ e.baseSet := ⟨hxu, hxe⟩
  -- the local frame: `C^(m+1)` on `u ∩ e.baseSet`, and `MDifferentiable` on `e.baseSet`
  have hsO : ∀ i, CMDiff[u ∩ e.baseSet] ((m + 1 : ℕ∞)) (T% (e.localFrame b i)) := fun i ↦
    (e.contMDiffOn_localFrame_baseSet _ b i).mono inter_subset_right
  have hsA : ∀ (i : ι) (y : M), y ∈ e.baseSet → MDiffAt (T% (e.localFrame b i)) y := fun i y hy ↦
    (contMDiffAt_localFrame_of_mem (I := I) (n := 1) (e := e) (b := b) i hy).mdifferentiableAt
      (by simp)
  -- Step 1: the scalars `y ↦ Kf y (s i y) (s j y)` are `C^m` at `x`
  have hscal : ∀ i j, ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (Kf y (e.localFrame b i y) (e.localFrame b j y))) x := by
    intro i j
    refine contMDiffAt_trivial_section ?_
    refine (contMDiffAt_koszulRHS (g := g) (X := e.localFrame b i) (Y := Y)
      (Z := e.localFrame b j) hvopen hxv (hg.mono inter_subset_left)
      (hsO i) (hY.mono inter_subset_left) (hsO j)).congr_of_eventuallyEq ?_
    filter_upwards [hvopen.mem_nhds hxv] with y hy
    exact hKf y hy.1 _ _ (hsA i y hy.2) (hsA j y hy.2)
  -- Step 2: inner frame test, in the second tangent slot
  have hinner : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)) y
        (Kf y (e.localFrame b i y))) x := fun i ↦
    contMDiffAt_hom_bundle_of_contMDiffAt_localFrame (IB := I) (n := (m : ℕ∞ω))
      (E₂ := Bundle.Trivial M ℝ) (F₂ := ℝ) b e hxe
      (fun y ↦ (Kf y (e.localFrame b i y) : TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y))
      (hscal i)
  -- Step 3: outer frame test, in the first tangent slot
  exact contMDiffAt_hom_bundle_of_contMDiffAt_localFrame (IB := I) (n := (m : ℕ∞ω))
    (E₂ := fun y : M ↦ (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)) (F₂ := E →L[ℝ] ℝ)
    b e hxe
    (fun y ↦ (Kf y : TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)))
    hinner

/-- The double frame test with the canonical choices of trivialisation and basis. -/
theorem contMDiffAt_hom_hom_of_eq_koszulRHS {m : ℕ∞} {u : Set M} {x : M}
    (hu : IsOpen u) (hxu : x ∈ u)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m + 1 : ℕ∞))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) u)
    (hY : CMDiff[u] ((m + 1 : ℕ∞)) (T% Y))
    (hKf : ∀ y ∈ u, ∀ U Z : Π z : M, TangentSpace I z, MDiffAt (T% U) y → MDiffAt (T% Z) y →
      Kf y (U y) (Z y) = koszulRHS g U Y y Z) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)))
        y (Kf y)) x :=
  contMDiffAt_hom_hom_of_eq_koszulRHS_frame (Module.finBasis ℝ E)
    (trivializationAt E (TangentSpace I) x)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x) hu hxu hg hY hKf

end FrameTest

/-! ## The conclusion: the Koszul form is a `C^m` section -/

section Target

variable {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
  {Y : Π y : M, TangentSpace I y}

/-- **The target.**  The bundled Koszul form `koszulSection g Y` is a `C^m` section of
`Hom(TM, Hom(TM, ℝ))` at every point of an open set on which the symmetric metric-as-data `g`
and the field `Y` are `C^(m+1)`. -/
theorem contMDiffAt_koszulSection {m : ℕ∞} {u : Set M} {x : M}
    (hu : IsOpen u) (hxu : x ∈ u)
    (hsymm : ∀ (z : M) (a b : TangentSpace I z), g z a b = g z b a)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m + 1 : ℕ∞))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : M) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g y)) u)
    (hY : CMDiff[u] ((m + 1 : ℕ∞)) (T% Y)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)))
        y (koszulSection g Y y)) x := by
  have hone : (1 : ℕ∞ω) ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_add_self
  have hne : ((m + 1 : ℕ∞) : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one hone).ne'
  have hten : ∀ y ∈ u, IsKoszulTensorialAt g Y y := fun y hy ↦
    isKoszulTensorialAt_of_mdifferentiableAt hsymm
      (((hg y hy).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt hne)
      (((hY y hy).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt hne)
  exact contMDiffAt_hom_hom_of_eq_koszulRHS hu hxu hg hY
    (fun y hy _ _ hU hZ ↦ koszulSection_apply (hten y hy) hU hZ)

end Target

end RiemannianGeometry
