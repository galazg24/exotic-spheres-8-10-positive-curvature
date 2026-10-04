/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import RiemannianGeometry.LeviCivita
import RiemannianGeometry.HomBundleFrame
import RiemannianGeometry.Submersion
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The differential of a map and its fibrewise metric adjoint

For `f : M → B` between finite-dimensional real manifolds, this file packages `mfderiv I J f`
and, given metrics-as-data `gM` on `M` and `gB` on `B`, the fibrewise adjoint

  `A_p^* : T_{f p}B →L[ℝ] T_pM`,   `gM p (A_p^* w) u = gB (f p) w (A_p u)`,

together with the regularity of both.

## The bundle in which `df` lives — and why it is not a hom-bundle over one base

`mfderiv I J f p : TangentSpace I p →L[ℝ] TangentSpace J (f p)` has its **source fibre over `M`
at `p`** and its **target fibre over `B` at `f p`**. It is therefore *not* a section of a
hom-bundle over a single base: `Hom(E₁, E₂)` is defined for two bundles over the *same* base, and
the "base map" `b : M → B` of `ContMDiffAt.clm_bundle_comp` etc. does not help, since there both
`E₂ (b m)` and `E₃ (b m)` sit over the *same* point `b m`.

The would-be statement

    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E')) m
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E')
        (E := fun z : M ↦ (TangentSpace I z →L[ℝ] TangentSpace J (f z))) z (mfderiv I J f z)) p

does not even elaborate: there is no `TopologicalSpace (TotalSpace (E →L[ℝ] E')
fun z ↦ TangentSpace I z →L[ℝ] TangentSpace J (f z))`, because `fun z : M ↦ TangentSpace J (f z)`
carries no `FiberBundle` instance (that would be the pullback `f *ᵖ TangentSpace J`, which requires
a *bundled continuous* `f` — unavailable when `f` is only `C^(m+1)` on an open set).

This is exactly the situation Mathlib documents at `ContMDiffWithinAt.clm_apply_of_inCoordinates`
("the pullback bundles are smooth manifolds only when `b₁` and `b₂` are globally smooth, but we
want to apply this lemma with only local information") and which this project's
`ContMDiffWithinAt.clm_inverse_of_inCoordinates` follows. So the smoothness of `df` is stated
here, as there, through `ContinuousLinearMap.inCoordinates`.

## Main results

* `contMDiffAt_mfderiv_inCoordinates` — `df` is a `C^m` hom-section along `(id, f)`, read in
  coordinates, when `f` is `C^(m+1)` on an open set.
* `contMDiffAt_mfderiv_apply` — the usable consequence: `z ↦ (df_z (U z) : TB)` is `C^m` for a
  `C^m` vector field `U` on `M`.
* `mfderivCoadjoint`, `mfderivAdjoint` — the transpose of `df` composed with `gB`, and the
  adjoint itself.
* `mfderivAdjoint_spec` — **the public API**: `gM p (A_p^* w) u = gB (f p) w (A_p u)`.
* `contMDiffAt_mfderivCoadjoint`, `contMDiffAt_mfderivAdjoint_apply` — regularity: for a `C^m`
  field `W` along `f`, `z ↦ A_z^* (W z)` is a `C^m` section of `TM`.
* `contMDiffAt_mfderivAdjoint_inCoordinates` — the same as a hom-section statement: `z ↦ A_z^*`
  is `C^m` read in coordinates, the exact mirror of `contMDiffAt_mfderiv_inCoordinates`.
* `gM_mfderivAdjoint_apply_eq_zero`, `mfderivAdjoint_mem_verticalSpace_orthogonal` —
  horizontality: `A^* w` is `gM`-orthogonal to `ker (df)`.

## Regularity

`f` of class `C^(m+1)` on an open set gives `df` of class `C^m`, by
`ContMDiffWithinAt.mfderivWithin_const` with `hmn : m + 1 ≤ n`; this is the only place a
derivative is spent. Metrics of class `C^m` then give
the adjoint of class `C^m`: nothing below `contMDiffAt_mfderiv_inCoordinates` differentiates
anything — only fibrewise composition, inversion and application are used.
-/

noncomputable section

open Bundle Set ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  {f : M → B}

/-! ## Deliverable 1: the differential as a hom-section along `(id, f)` -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [CompleteSpace E'] [FiniteDimensional ℝ E'] in
/-- **The differential of a `C^(m+1)` map is a `C^m` hom-section**, read in coordinates.

`z ↦ mfderiv I J f z` is a family of continuous linear maps `T_zM →L[ℝ] T_{f z}B` between the
fibres of `TM` (over the base map `id`) and of `TB` (over the base map `f`). As the two base maps
differ, its regularity is expressed through `ContinuousLinearMap.inCoordinates`, exactly as in
`ContMDiffWithinAt.clm_apply_of_inCoordinates` and
`ContMDiffWithinAt.clm_inverse_of_inCoordinates`. See the module docstring.

This is where the one derivative is spent: `ContMDiffWithinAt.mfderivWithin_const` needs
`m + 1 ≤ n`. -/
theorem contMDiffAt_mfderiv_inCoordinates {m : ℕ∞} {u : Set M} {p : M}
    (hu : IsOpen u) (hpu : p ∈ u) (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ((m : ℕ∞ω))
      (fun z ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E'
        (TangentSpace J (M := B)) p z (f p) (f z) (mfderiv I J f z)) p := by
  have hmn : ((m : ℕ∞ω)) + 1 ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_rfl
  have h := (hf p hpu).mfderivWithin_const hmn hpu hu.uniqueMDiffOn
  refine (h.contMDiffAt (hu.mem_nhds hpu)).congr_of_eventuallyEq ?_
  filter_upwards [hu.mem_nhds hpu] with z hz
  have hfz : MDifferentiableAt I J f z :=
    ((hf z hz).contMDiffAt (hu.mem_nhds hz)).mdifferentiableAt (by
      simp only [ne_eq]
      push_cast
      exact (by positivity : (0 : ℕ∞ω) < (m : ℕ∞ω) + 1).ne')
  simp only [inTangentCoordinates, id_eq]
  rw [mfderivWithin_eq_mfderiv (hu.uniqueMDiffWithinAt hz) hfz]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [CompleteSpace E'] [FiniteDimensional ℝ E'] in
/-- **The differential applied to a `C^m` vector field is a `C^m` map into `TB`.**

The form in which the previous theorem is used: no `inCoordinates` survives. -/
theorem contMDiffAt_mfderiv_apply {m : ℕ∞} {u : Set M} {p : M}
    {U : Π z : M, TangentSpace I z}
    (hu : IsOpen u) (hpu : p ∈ u) (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hU : ContMDiffAt I I.tangent ((m : ℕ∞ω)) (fun z ↦ TotalSpace.mk' E z (U z)) p) :
    ContMDiffAt I J.tangent ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' E' (f z) (mfderiv I J f z (U z))) p := by
  have hml : ((m : ℕ∞ω)) ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((m : ℕ∞ω)) f p :=
    ((hf p hpu).contMDiffAt (hu.mem_nhds hpu)).of_le hml
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (contMDiffAt_mfderiv_inCoordinates hu hpu hf) hU hfp

/-! ## Deliverable 2: the fibrewise metric adjoint -/

/-- The transpose of `mfderiv I J f p` composed with the metric on the base:
`w ↦ gB (f p) w ∘L mfderiv I J f p`.

The four `letI`s transport the normed structure across the `TangentSpace` type synonym, which
derives only the topological and module instances; they are confined to the body, so the ambient
`Module` instances are the ones appearing in the type. -/
def mfderivCoadjoint
    (gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ)
    (f : M → B) (p : M) :
    TangentSpace J (f p) →L[ℝ] (TangentSpace I p →L[ℝ] ℝ) :=
  letI : NormedAddCommGroup (TangentSpace I p) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I p) := inferInstanceAs (NormedSpace ℝ E)
  letI : NormedAddCommGroup (TangentSpace J (f p)) := inferInstanceAs (NormedAddCommGroup E')
  letI : NormedSpace ℝ (TangentSpace J (f p)) := inferInstanceAs (NormedSpace ℝ E')
  ((gB (f p)).flip ∘L (mfderiv I J f p)).flip

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
@[simp]
theorem mfderivCoadjoint_apply
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ} {p : M}
    (w : TangentSpace J (f p)) (u : TangentSpace I p) :
    mfderivCoadjoint gB f p w u = gB (f p) w (mfderiv I J f p u) := rfl

/-- **The fibrewise metric adjoint** of `mfderiv I J f p`, built from the metric duals rather than
by choice: `A^* = (gM p)⁻¹ ∘L (Aᵀ ∘L gB (f p))`.

No hypothesis appears in the definition; where `gM p` fails to be invertible,
`ContinuousLinearMap.inverse` takes its junk value `0`. The characterising identity
`mfderivAdjoint_spec` supplies nondegeneracy, and is the only thing later work should use. -/
def mfderivAdjoint
    (gM : Π p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ)
    (f : M → B) (p : M) : TangentSpace J (f p) →L[ℝ] TangentSpace I p :=
  (ContinuousLinearMap.inverse (gM p)) ∘L (mfderivCoadjoint gB f p)

omit [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **The characterising identity, and the public API of the adjoint**:

  `gM p (A_p^* w) u = gB (f p) w (A_p u)`   for all `u`, `w`.

Only weak nondegeneracy of `gM` at `p` is used, through `isInvertible_g`; no symmetry, no
positive-definiteness, no differentiability. -/
theorem mfderivAdjoint_spec
    {gM : Π p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ}
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ}
    {p : M} (hnd : ∀ v : TangentSpace I p, (∀ w, gM p v w = 0) → v = 0)
    (w : TangentSpace J (f p)) (u : TangentSpace I p) :
    gM p (mfderivAdjoint gM gB f p w) u = gB (f p) w (mfderiv I J f p u) := by
  have hinv : (gM p).IsInvertible := isInvertible_g hnd
  rw [mfderivAdjoint, ContinuousLinearMap.comp_apply, hinv.self_apply_inverse,
    mfderivCoadjoint_apply]

omit [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- The adjoint is determined by its characterising identity. -/
theorem eq_mfderivAdjoint
    {gM : Π p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ}
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ}
    {p : M} (hnd : ∀ v : TangentSpace I p, (∀ w, gM p v w = 0) → v = 0)
    {T : TangentSpace J (f p) →L[ℝ] TangentSpace I p}
    (hT : ∀ w u, gM p (T w) u = gB (f p) w (mfderiv I J f p u)) :
    T = mfderivAdjoint gM gB f p := by
  ext w
  exact eq_of_g_eq hnd fun u ↦ (hT w u).trans (mfderivAdjoint_spec hnd w u).symm

/-! ### Regularity of the adjoint

Nothing here differentiates anything: only the fibrewise composition, inversion and application
lemmas of `RiemannianGeometry.HomBundleComp`, `RiemannianGeometry.HomBundleInverse`, `RiemannianGeometry.HomBundleFrame`
and Mathlib's `clm_bundle_apply` family are used. The single derivative loss is the one already
incurred by `contMDiffAt_mfderiv_inCoordinates`. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- Auxiliary: a section of the trivial line bundle along a base map is smooth exactly when the
underlying scalar function is. (The identity-base-map direction is
`RiemannianGeometry.contMDiffAt_trivial_section`.) -/
theorem contMDiffAt_scalar_of_trivialSection {n : ℕ∞ω} {c : M → B} {F : M → ℝ} {p : M}
    (h : ContMDiffAt I (J.prod 𝓘(ℝ, ℝ)) n
      (fun z ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (c z) (F z)) p) :
    ContMDiffAt I 𝓘(ℝ) n F p := by
  simp only [Bundle.contMDiffAt_totalSpace] at h
  exact h.2

omit [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ E'] in
/-- **The coadjoint applied to a `C^m` field along `f` is a `C^m` section of `T*M`.**

`z ↦ gB (f z) (W z) ∘L df_z` is a `C^m` section of `Hom(TM, ℝ)`. Proved by the frame test of
`RiemannianGeometry.HomBundleFrame`: on the local frame induced by `trivializationAt E (TangentSpace I) p`
its values are the scalars `gB (f z) (W z) (df_z (s_i z))`, which are `C^m` by
`ContMDiffAt.clm_bundle_apply₂` over the base map `f`. -/
theorem contMDiffAt_mfderivCoadjoint {m : ℕ∞} {u : Set M} {p : M}
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ}
    {W : Π z : M, TangentSpace J (f z)}
    (hu : IsOpen u) (hpu : p ∈ u)
    (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hgB : ContMDiffAt J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q (gB q)) (f p))
    (hW : ContMDiffAt I J.tangent ((m : ℕ∞ω)) (fun z ↦ TotalSpace.mk' E' (f z) (W z)) p) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] Bundle.Trivial M ℝ z) z
        (mfderivCoadjoint gB f z (W z))) p := by
  have hml : ((m : ℕ∞ω)) ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((m : ℕ∞ω)) f p :=
    ((hf p hpu).contMDiffAt (hu.mem_nhds hpu)).of_le hml
  have hgBf : ContMDiffAt I (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) (f z) (gB (f z))) p :=
    hgB.comp p hfp
  have hpe : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  refine contMDiffAt_hom_bundle_of_contMDiffAt_localFrame (Module.finBasis ℝ E)
    (trivializationAt E (TangentSpace I) p) hpe _ ?_
  intro i
  have hs : ContMDiffAt I I.tangent ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' E z
        ((trivializationAt E (TangentSpace I) p).localFrame (Module.finBasis ℝ E) i z)) p :=
    contMDiffAt_localFrame_of_mem (I := I) (n := (m : ℕ∞ω))
      (e := trivializationAt E (TangentSpace I) p) (b := Module.finBasis ℝ E) i hpe
  have hV := contMDiffAt_mfderiv_apply hu hpu hf hs
  have hprod : ContMDiffAt I (J.prod 𝓘(ℝ, ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (f z)
        (gB (f z) (W z) (mfderiv I J f z
          ((trivializationAt E (TangentSpace I) p).localFrame (Module.finBasis ℝ E) i z)))) p :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E') (F₂ := E') (F₃ := ℝ) hgBf hW hV
  exact contMDiffAt_trivial_section (contMDiffAt_scalar_of_trivialSection hprod)

omit [CompleteSpace E'] [FiniteDimensional ℝ E'] in
/-- **The adjoint applied to a `C^m` field along `f` is a `C^m` vector field on `M`.**

`f` of class `C^(m+1)`, `gM` and `gB` of class `C^m`, `W` of class `C^m` along `f`, `gM p`
nondegenerate: then `z ↦ A_z^* (W z)` is a `C^m` section of `TM` at `p`. No further derivative is
lost — the inverse metric enters through `ContMDiffAt.clm_bundle_inverse` and the application
through `ContMDiffAt.clm_bundle_apply`, neither of which differentiates. -/
theorem contMDiffAt_mfderivAdjoint_apply {m : ℕ∞} {u : Set M} {p : M}
    {gM : Π z : M, TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ}
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ}
    {W : Π z : M, TangentSpace J (f z)}
    (hu : IsOpen u) (hpu : p ∈ u)
    (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hgM : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z (gM z)) p)
    (hgB : ContMDiffAt J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q (gB q)) (f p))
    (hnd : ∀ v : TangentSpace I p, (∀ w, gM p v w = 0) → v = 0)
    (hW : ContMDiffAt I J.tangent ((m : ℕ∞ω)) (fun z ↦ TotalSpace.mk' E' (f z) (W z)) p) :
    ContMDiffAt I I.tangent ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' E z (mfderivAdjoint gM gB f z (W z))) p := by
  have hgM' : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ (TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] Bundle.Trivial M ℝ z)))
        z (gM z)) p := hgM
  exact (hgM'.clm_bundle_inverse (isInvertible_g hnd)).clm_bundle_apply
    (contMDiffAt_mfderivCoadjoint hu hpu hf hgB hW)

/-! ## Deliverable 3: horizontality of the adjoint

Stated purely in metric-as-data terms, as the brief permits: `A^* w` is `gM`-orthogonal to the
vertical space `ker (df_p)`. No fibrewise `InnerProductSpace` and no `RiemannianBundle` instance
is involved, so nothing has to be bound to a name. -/

omit [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **`A_p^* w` is horizontal**: it is `gM`-orthogonal to every vertical vector. -/
theorem gM_mfderivAdjoint_apply_eq_zero
    {gM : Π p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ}
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ}
    {p : M} (hnd : ∀ v : TangentSpace I p, (∀ w, gM p v w = 0) → v = 0)
    (w : TangentSpace J (f p)) {v : TangentSpace I p} (hv : mfderiv I J f p v = 0) :
    gM p (mfderivAdjoint gM gB f p w) v = 0 := by
  rw [mfderivAdjoint_spec hnd, hv, map_zero]

omit [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- The same, phrased through `verticalSpace`. -/
theorem mfderivAdjoint_mem_verticalSpace_orthogonal
    {gM : Π p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ}
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ}
    {p : M} (hnd : ∀ v : TangentSpace I p, (∀ w, gM p v w = 0) → v = 0)
    (w : TangentSpace J (f p)) :
    ∀ v ∈ verticalSpace I J f p, gM p (mfderivAdjoint gM gB f p w) v = 0 :=
  fun _ hv ↦ gM_mfderivAdjoint_apply_eq_zero hnd w (mem_verticalSpace_iff.mp hv)

omit [CompleteSpace E'] in
/-- **The adjoint is a `C^m` hom-section along `(f, id)`, read in coordinates.** -/
theorem contMDiffAt_mfderivAdjoint_inCoordinates {m : ℕ∞} {u : Set M} {p : M}
    {gM : Π z : M, TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ}
    {gB : Π q : B, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ}
    (hu : IsOpen u) (hpu : p ∈ u)
    (hf : ContMDiffOn I J ((m + 1 : ℕ∞)) f u)
    (hgM : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) z (gM z)) p)
    (hgB : ContMDiffAt J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ((m : ℕ∞ω))
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q : B ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q (gB q)) (f p))
    (hnd : ∀ v : TangentSpace I p, (∀ w, gM p v w = 0) → v = 0) :
    ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E) ((m : ℕ∞ω))
      (fun z ↦ ContinuousLinearMap.inCoordinates E' (TangentSpace J (M := B)) E
        (TangentSpace I (M := M)) (f p) (f z) p z (mfderivAdjoint gM gB f z)) p := by
  have hml : ((m : ℕ∞ω)) ≤ ((m + 1 : ℕ∞) : ℕ∞ω) := by push_cast; exact le_self_add
  have hfp : ContMDiffAt I J ((m : ℕ∞ω)) f p :=
    ((hf p hpu).contMDiffAt (hu.mem_nhds hpu)).of_le hml
  have hfpB : f p ∈ (trivializationAt E' (TangentSpace J) (f p)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (f p)
  have hpM : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have key : ∀ w : E', ContMDiffAt I 𝓘(ℝ, E) ((m : ℕ∞ω))
      (fun z ↦ ContinuousLinearMap.inCoordinates E' (TangentSpace J (M := B)) E
        (TangentSpace I (M := M)) (f p) (f z) p z (mfderivAdjoint gM gB f z) w) p := by
    intro w
    have hsymSec : ContMDiffAt J J.tangent ((m : ℕ∞ω))
        (fun q ↦ TotalSpace.mk' E' q
          ((trivializationAt E' (TangentSpace J) (f p)).symmL ℝ q w)) (f p) := by
      rw [Bundle.Trivialization.contMDiffAt_section_iff
        (trivializationAt E' (TangentSpace J) (f p)) hfpB]
      refine (contMDiffAt_const (c := w)).congr_of_eventuallyEq ?_
      filter_upwards [(trivializationAt E' (TangentSpace J) (f p)).open_baseSet.mem_nhds hfpB]
        with q hq
      rw [← (trivializationAt E' (TangentSpace J) (f p)).continuousLinearMapAt_apply_of_mem
          (R := ℝ) hq,
        (trivializationAt E' (TangentSpace J) (f p)).continuousLinearMapAt_symmL hq]
    have hW : ContMDiffAt I J.tangent ((m : ℕ∞ω))
        (fun z ↦ TotalSpace.mk' E' (f z)
          ((trivializationAt E' (TangentSpace J) (f p)).symmL ℝ (f z) w)) p :=
      hsymSec.comp p hfp
    have happ := contMDiffAt_mfderivAdjoint_apply hu hpu hf hgM hgB hnd hW
    rw [Bundle.contMDiffAt_totalSpace] at happ
    refine happ.2.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt E (TangentSpace I) p).open_baseSet.mem_nhds hpM] with z hz
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    rw [(trivializationAt E (TangentSpace I) p).continuousLinearMapAt_apply_of_mem (R := ℝ) hz]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ((Fin (Module.finrank ℝ E')) → E) →L[ℝ] (E' →L[ℝ] E),
      ∀ (v : Fin (Module.finrank ℝ E') → E) (w : E'),
        Ψ v w = ∑ i, (Module.finBasis ℝ E').repr w i • v i := by
    refine ⟨∑ i, (ContinuousLinearMap.smulRightL ℝ E' E
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E').coord i))).comp
      (ContinuousLinearMap.proj i), fun v w ↦ ?_⟩
    simp [Module.Basis.coord_apply]
  have main : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E) ((m : ℕ∞ω))
      (fun z ↦ Ψ (fun i ↦ ContinuousLinearMap.inCoordinates E' (TangentSpace J (M := B)) E
        (TangentSpace I (M := M)) (f p) (f z) p z (mfderivAdjoint gM gB f z)
          (Module.finBasis ℝ E' i))) p :=
    Ψ.contMDiffAt.comp p (contMDiffAt_pi_space.mpr fun i ↦ key _)
  refine main.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
  ext w
  rw [hΨ]
  conv_lhs => rw [show w = ∑ i, (Module.finBasis ℝ E').repr w i • (Module.finBasis ℝ E') i from
    ((Module.finBasis ℝ E').sum_repr w).symm]
  simp only [map_sum, map_smul]

end RiemannianGeometry
