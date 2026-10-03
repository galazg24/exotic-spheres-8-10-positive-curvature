/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import RiemannianGeometry.CurvatureSection
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Curvature depends only on the value of the section at the point

  `σ x = τ x → R(X, Y)σ x = R(X, Y)τ x`.

That is what makes `R(X, Y)` an endomorphism of the single fibre `V x`, and it is the last thing
needed before the curvature tensor can be bundled.

## Main results

* `curvature_sum_section` — curvature commutes with a finite sum of sections.
* `curvature_eq_sum_of_frame_expansion` — if `σ = ∑ i, c i • fr i` near `x` for an **arbitrary**
  local frame, then `R(X, Y)σ x = ∑ i, c i x • R(X, Y)(fr i) x`.
* `curvature_eq_of_eq_at` — the order-zero statement.

## Why germ locality is not enough, and what does the work

`curvature_congr_of_eventuallyEq` says `R(X, Y)σ x` depends only on the germ of `σ` at `x`. That is
strictly weaker than depending on `σ x`, and the standard witness is the covariant derivative
itself: `σ ↦ (∇_X σ) x` is germ-local — by the very same lemma,
`IsCovariantDerivativeOn.congr_of_eventuallyEq` — yet it depends on the 1-jet of `σ`, not on
`σ x`.

Running the local-frame argument on both operators shows exactly where they part company. Expand
`σ = ∑ᵢ cᵢ • sᵢ` near `x` in a local frame. For the covariant derivative, the Leibniz rule gives

  `∇_X(cᵢ • sᵢ)(x) = cᵢ(x) • ∇_X sᵢ(x) + (d cᵢ)ₓ(X x) • sᵢ(x)`

and summing leaves `∑ᵢ (d cᵢ)ₓ(X x) • sᵢ(x)` — a term in the **derivatives of the coefficients**,
which is precisely 1-jet dependence, and which does not vanish just because the `cᵢ(x)` do. For
curvature the corresponding step is

  `R(X, Y)(cᵢ • sᵢ)(x) = cᵢ(x) • R(X, Y)sᵢ(x)`

So the order-zero property of curvature in the section slot is not a formal consequence of germ
locality plus linearity — it is equivalent to the vanishing of `X(Yf) - Y(Xf) - [X,Y]f`.

`CovC2LocalMDiffAt F cov x` asks that `cov` send sections that are `C²` on a neighbourhood of `x`
to `Hom`-sections differentiable **at** `x`. It is needed because the frame sections and the partial
sums appearing in the argument are only defined and regular near `x`, so `MDiffAtCovSection` cannot
be assumed for each of them individually — and assuming it for each would make the statement depend
on the chosen frame, which is exactly what must not happen.

`C²` is the exact minimal order, not a safety margin: the conclusion asked for is
*differentiability* of `∇s`, one derivative is lost, and one derivative is all that is lost. The
predicate is therefore stated at that single strength rather than as a family — and the sections it
is applied to below (arbitrary local frames, `FiberBundle.extend` sections, and finite sums and
scalar multiples of those) are all `C^∞` or `C^n` in practice, so nothing is lost by pinning it.

## Frame independence

`curvature_eq_sum_of_frame_expansion` is stated for an arbitrary family `c`, `fr` with
`σ = ∑ i, c i • fr i` near `x`. No trivialization appears in it. `curvature_eq_of_eq_at` then
instantiates it once with Mathlib's `Trivialization.localFrame`, and its own statement mentions no
frame — so the conclusion cannot depend on the auxiliary choice.
-/

noncomputable section

open Bundle Set VectorField Filter Module
open scoped Manifold ContDiff Topology

namespace RiemannianGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X Y : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x} {x : M}

/-- **`cov` sends sections `C²` near `x` to `Hom`-sections differentiable at `x`.**
-/
abbrev CovC2LocalMDiffAt (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)) (x : M) : Prop :=
  ∀ s : Π y : M, V y,
    (∀ᶠ y in 𝓝 x, ContMDiffAt I (I.prod 𝓘(𝕜, F)) (2 : ℕ∞ω)
      (fun z ↦ (⟨z, s z⟩ : TotalSpace F V)) y) → MDiffAtCovSection F cov s x

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] [(x : M) → Module 𝕜 (V x)] [(x : M) → AddCommGroup (V x)]
  [IsManifold I 1 M] in
/-- Downgrade a `C²`-near-`x` section hypothesis to differentiability near `x`, which is what the
section-slot laws of `Foundations.CurvatureSection` consume. -/
theorem eventually_mdiffAt_of_eventually_contMDiffAt_two {s : Π y : M, V y}
    (h : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y) : ∀ᶠ y in 𝓝 x, MDiffAt (T% s) y :=
  h.mono fun _ hy ↦ hy.mdifferentiableAt (by simp)

theorem curvature_sum_section {ι : Type*} {t : Finset ι} {s : ι → Π y : M, V y}
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hs : ∀ i ∈ t, ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (s i)) y)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvature cov X Y (fun y ↦ ∑ i ∈ t, s i y) x = ∑ i ∈ t, curvature cov X Y (s i) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have h0 : (fun y ↦ ∑ i ∈ (∅ : Finset ι), s i y) = (0 : Π y : M, V y) := by
        funext y; simp
      rw [h0, Finset.sum_empty]
      exact curvature_zero_section hcov
  | insert a t ha ih =>
      have hsa : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (s a)) y :=
        hs a (Finset.mem_insert_self a t)
      have hst : ∀ i ∈ t, ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (s i)) y :=
        fun i hi ↦ hs i (Finset.mem_insert_of_mem hi)
      have hsum : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% fun z ↦ ∑ i ∈ t, s i z) y := by
        rw [← Filter.eventually_all_finset] at hst
        filter_upwards [hst] with y hy
        exact ContMDiffAt.sum_section fun i hi ↦ hy i hi
      have : (fun y ↦ ∑ i ∈ insert a t, s i y) = s a + fun y ↦ ∑ i ∈ t, s i y := by
        funext y; simp [Finset.sum_insert ha]
      rw [this, curvature_add_section_of_eventually hcov (hcovloc _ hsa) (hcovloc _ hsum)
        (eventually_mdiffAt_of_eventually_contMDiffAt_two hsa)
        (eventually_mdiffAt_of_eventually_contMDiffAt_two hsum) hX hY,
        ih hst, Finset.sum_insert ha]

section Expansion

variable [CompleteSpace E]

/-- **Curvature evaluated on a section expanded in an arbitrary local frame.**

If `s = ∑ i, c i • fr i` near `x`, with the coefficients `c i` of class `C^n` at `x` and the frame
sections `fr i` differentiable near `x`, then

  `R(X, Y)s x = ∑ i, c i x • R(X, Y)(fr i) x`.

Nothing about a trivialization appears: the frame is arbitrary. That is what makes the pointwise
statement independent of the auxiliary choices used to prove it.

Three ingredients, in order: germ locality replaces `s` by its expansion, `curvature_sum_section`
splits the finite sum, and `curvature_smul_section_of_eventually` pulls each coefficient out —
and that last step is the one that needs the bracket-derivation identity. -/
theorem curvature_eq_sum_of_frame_expansion {ι : Type*} [Fintype ι]
    {c : ι → M → 𝕜} {fr : ι → Π y : M, V y}
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hc : ∀ i, CMDiffAt (n : ℕ∞ω) (c i) x)
    (hfr : ∀ i, ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (fr i)) y)
    (hsd : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% σ) y)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hexp : ∀ᶠ y in 𝓝 x, σ y = ∑ i, c i y • fr i y) :
    curvature cov X Y σ x = ∑ i, c i x • curvature cov X Y (fr i) x := by
  classical
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h; rw [h] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  have : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  have hXd : MDiffAt (T% X) x := hX.self_of_nhds.mdifferentiableAt hne
  have hYd : MDiffAt (T% Y) x := hY.self_of_nhds.mdifferentiableAt hne
  have hcev : ∀ i, ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (c i) y := fun i ↦
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 (hc i)).mono fun _ h ↦ h.of_le h2n
  have hgd : ∀ i, ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (c i • fr i)) y := by
    intro i
    filter_upwards [hcev i, hfr i] with y hcy hfy
    exact ContMDiffAt.smul_section hcy hfy
  have hEd : ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% fun z ↦ ∑ i, (c i • fr i) z) y := by
    have hall : ∀ᶠ y in 𝓝 x, ∀ i ∈ Finset.univ, CMDiffAt (2 : ℕ∞ω) (T% (c i • fr i)) y := by
      rw [Filter.eventually_all_finset]
      exact fun i _ ↦ hgd i
    filter_upwards [hall] with y hy
    exact ContMDiffAt.sum_section fun i hi ↦ hy i hi
  have hexp' : ∀ᶠ y in 𝓝 x, σ y = (fun z ↦ ∑ i, (c i • fr i) z) y := by
    filter_upwards [hexp] with y hy
    simpa using hy
  rw [curvature_congr_of_eventuallyEq hcov
      (eventually_mdiffAt_of_eventually_contMDiffAt_two hsd)
      (eventually_mdiffAt_of_eventually_contMDiffAt_two hEd)
      (hcovloc _ hsd) (hcovloc _ hEd) hXd hYd hexp',
    curvature_sum_section (s := fun i ↦ c i • fr i) hcov hcovloc (fun i _ ↦ hgd i) hXd hYd]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact curvature_smul_section_of_eventually hcov (hcovloc _ (hfr i)) hn hn' (hc i)
    (eventually_mdiffAt_of_eventually_contMDiffAt_two (hfr i)) hX hY

end Expansion

section Frame

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 F]
  [ContMDiffVectorBundle (1 : ℕ∞ω) F V I]

/-- **The order-zero statement: curvature depends only on the value of the section at the point.**

Instantiates `curvature_eq_sum_of_frame_expansion` with Mathlib's local frame from the
trivialization at `x` and a basis of the model fibre, twice — once for each section — and then
compares the two sums coefficientwise using `Trivialization.localFrameCoeff_congr`, which says the
frame coefficients at `x` depend only on the section's value at `x`.

No frame appears in the statement, so the conclusion is independent of the auxiliary choices. -/
theorem curvature_eq_of_eq_at [ContMDiffVectorBundle (n : ℕ∞ω) F V I]
    (hcov : IsCovariantDerivativeOn F cov Set.univ) (hcovloc : CovC2LocalMDiffAt F cov x)
    (hn : minSmoothness 𝕜 2 ≤ n) (hn' : (n : ℕ∞ω) ≠ ∞)
    (hσ : CMDiffAt (n : ℕ∞ω) (T% σ) x) (hτ : CMDiffAt (n : ℕ∞ω) (T% τ) x)
    (hX : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% X) y)
    (hY : ∀ᶠ y in 𝓝 x, CMDiffAt (n : ℕ∞ω) (T% Y) y)
    (hστ : σ x = τ x) :
    curvature cov X Y σ x = curvature cov X Y τ x := by
  classical
  have h2n : (2 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_minSmoothness.trans hn
  have hne : (n : ℕ∞ω) ≠ 0 := by intro h; rw [h] at h2n; simp at h2n
  have h1n : (1 : ℕ∞ω) ≤ (n : ℕ∞ω) := le_trans (by norm_num) h2n
  have : IsManifold I (n : ℕ∞ω) M := IsManifold.of_le (n := (n : ℕ∞ω) + 1) le_self_add
  set e := trivializationAt F V x with he
  have : MemTrivializationAtlas e := by rw [he]; infer_instance
  have x_mem : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  set b := Basis.ofVectorSpace 𝕜 F with hb
  have hframe : ∀ i, ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% (e.localFrame b i)) y := by
    intro i
    filter_upwards [e.open_baseSet.mem_nhds x_mem] with y hy
    exact (contMDiffAt_localFrame_of_mem (n := (n : ℕ∞ω)) (e := e) b i hy).of_le h2n
  have hsd : ∀ s : Π y : M, V y, CMDiffAt (n : ℕ∞ω) (T% s) x →
      ∀ᶠ y in 𝓝 x, CMDiffAt (2 : ℕ∞ω) (T% s) y :=
    fun _ hs ↦ ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hs).mono fun _ h ↦ h.of_le h2n
  set cσ : Basis.ofVectorSpaceIndex 𝕜 F → M → 𝕜 :=
    fun i y ↦ Trivialization.localFrameCoeff I e b i y (σ y) with hcσ
  set cτ : Basis.ofVectorSpaceIndex 𝕜 F → M → 𝕜 :=
    fun i y ↦ Trivialization.localFrameCoeff I e b i y (τ y) with hcτ
  have hcσs : ∀ i, CMDiffAt (n : ℕ∞ω) (cσ i) x := by
    intro i; rw [hcσ]; exact contMDiffAt_localFrameCoeff b x_mem hσ i
  have hcτs : ∀ i, CMDiffAt (n : ℕ∞ω) (cτ i) x := by
    intro i; rw [hcτ]; exact contMDiffAt_localFrameCoeff b x_mem hτ i
  have kσ := curvature_eq_sum_of_frame_expansion (σ := σ) (c := cσ)
    (fr := fun i ↦ e.localFrame b i) hcov hcovloc hn hn' hcσs hframe (hsd σ hσ) hX hY
    (by
      filter_upwards [e.eventually_eq_localFrame_sum_coeff_smul (I := I) b x_mem] with y hy
      simp only [hcσ]; exact hy)
  have kτ := curvature_eq_sum_of_frame_expansion (σ := τ) (c := cτ)
    (fr := fun i ↦ e.localFrame b i) hcov hcovloc hn hn' hcτs hframe (hsd τ hτ) hX hY
    (by
      filter_upwards [e.eventually_eq_localFrame_sum_coeff_smul (I := I) b x_mem] with y hy
      simp only [hcτ]; exact hy)
  rw [kσ, kτ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcσ, hcτ]
  exact congrArg (fun t ↦ t • curvature cov X Y (e.localFrame b i) x)
    (Trivialization.localFrameCoeff_congr e b hστ)

end Frame

end RiemannianGeometry
