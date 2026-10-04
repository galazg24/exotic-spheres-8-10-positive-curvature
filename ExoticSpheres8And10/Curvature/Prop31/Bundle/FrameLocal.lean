/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.FrameCalculus
import RiemannianGeometry.RelatedVectorFields

/-! # Frame calculus with hypotheses on a neighbourhood only

`riemannTensorAt_frame_loc` is `riemannTensorAt_frame` with every hypothesis required only on
an open set `U ∋ x`: orthonormality, spanning, the bracket table and smoothness. Curvature is
local (`RiemannianGeometry`'s germ lemmas), so this is all the computation at `x` needs. It lets the frame live
over a trivialising neighbourhood of a principal bundle.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section FrameLoc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Π y : M, TangentSpace I y}
  {c : ι → ι → ι → M → ℝ} {U : Set M}

/-- **The Koszul formula in an orthonormal frame**, locally. -/
theorem g_leviCivita_frame_loc (hs : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    (hU : IsOpen U) (hFd : ∀ α, ∀ y ∈ U, MDiffAt (T% (F α)) y)
    (horth : ∀ α β, ∀ y ∈ U, g y (F α y) (F β y) = kron α β)
    (hbr : ∀ α β, ∀ y ∈ U, mlieBracket I (F α) (F β) y = ∑ γ, c α β γ y • F γ y)
    (α β γ : ι) {y : M} (hy : y ∈ U) :
    g y (leviCivita g (F β) y (F α y)) (F γ y) = frameΓ c α β γ y := by
  have hspec := leviCivita_spec hs hnd hgm (hFd α y hy) (hFd β y hy) (hFd γ y hy)
  rw [hspec]
  have hconst : ∀ a b : ι, mvfderiv I (fun z => g z (F a z) (F b z)) y = 0 := fun a b => by
    have e : (fun z => g z (F a z) (F b z)) =ᶠ[𝓝 y] fun _ => kron a b := by
      filter_upwards [hU.mem_nhds hy] with z hz using horth a b z hz
    rw [mvfderiv_congr_of_eventuallyEq e]
    ext v
    simp [mvfderiv, mfderiv_const]
  have hpair : ∀ a b d : ι, g y (mlieBracket I (F a) (F b) y) (F d y) = c a b d y :=
    fun a b d => by
      rw [hbr a b y hy, map_sum, ContinuousLinearMap.sum_apply]
      simp only [map_smul, ContinuousLinearMap.smul_apply, horth _ _ y hy, smul_eq_mul]
      exact sum_smul_kron (V := ℝ) (fun ε => c a b ε y) d
  simp only [koszulRHS, hconst, ContinuousLinearMap.zero_apply, hpair, frameΓ]
  ring

/-- **The connection in an orthonormal frame**, locally. -/
theorem leviCivita_frame_loc (hs : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    (hU : IsOpen U) (hFd : ∀ α, ∀ y ∈ U, MDiffAt (T% (F α)) y)
    (horth : ∀ α β, ∀ y ∈ U, g y (F α y) (F β y) = kron α β)
    (hspan : ∀ y ∈ U, ∀ (w : TangentSpace I y), w = ∑ γ, g y w (F γ y) • F γ y)
    (hbr : ∀ α β, ∀ y ∈ U, mlieBracket I (F α) (F β) y = ∑ γ, c α β γ y • F γ y)
    (α β : ι) {y : M} (hy : y ∈ U) :
    leviCivita g (F β) y (F α y) = ∑ γ, frameΓ c α β γ y • F γ y := by
  conv_lhs => rw [hspan y hy (leviCivita g (F β) y (F α y))]
  simp only [g_leviCivita_frame_loc hs hnd hgm hU hFd horth hbr _ _ _ hy]

/-- **The curvature in an orthonormal frame**, with hypotheses near `x` only. -/
theorem riemannTensorAt_frame_loc (hs : IsSymm g) (hp : IsPosDef g)
    (hg : IsContMDiffMetricSection E 2 g) (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hF : ∀ α, ∀ y ∈ U, CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% (F α)) y)
    (horth : ∀ α β, ∀ y ∈ U, g y (F α y) (F β y) = kron α β)
    (hspan : ∀ y ∈ U, ∀ (w : TangentSpace I y), w = ∑ γ, g y w (F γ y) • F γ y)
    (hbr : ∀ α β, ∀ y ∈ U, mlieBracket I (F α) (F β) y = ∑ γ, c α β γ y • F γ y)
    (hc : ∀ α β γ, ∀ y ∈ U, MDiffAt (c α β γ) y) (α β γ δ : ι) :
    riemannTensorAt hs hp.isNondegenerate hg x (F α x) (F β x) (F γ x) (F δ x) =
      mvfderiv I (frameΓ c β γ δ) x (F α x) - mvfderiv I (frameΓ c α γ δ) x (F β x) +
      ∑ ε, (frameΓ c β γ ε x * frameΓ c α ε δ x - frameΓ c α γ ε x * frameΓ c β ε δ x) -
      ∑ ε, c α β ε x * frameΓ c ε γ δ x := by
  have hnd := hp.isNondegenerate
  have hgm : IsMDiffMetric E g := hg.isMDiffMetric (by simp)
  have hFd : ∀ α, ∀ y ∈ U, MDiffAt (T% (F α)) y :=
    fun α y hy => (hF α y hy).mdifferentiableAt (by simp)
  have hΓd : ∀ α β γ, MDiffAt (frameΓ c α β γ) x := fun α β γ => by
    have e : frameΓ c α β γ = fun z => (c α β γ z - c α γ β z - c β γ α z) * (1 / 2 : ℝ) := by
      funext z; simp only [frameΓ]; ring
    rw [e]
    exact (((hc α β γ x hx).sub (hc α γ β x hx)).sub (hc β γ α x hx)).mul mdifferentiableAt_const
  have hfield : ∀ a b : ι, ∀ᶠ y in 𝓝 x, (fun y => leviCivita g (F b) y (F a y)) y =
      (∑ ε, frameΓ c a b ε • F ε) y := fun a b => by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [Finset.sum_apply]
    exact leviCivita_frame_loc hs hnd hgm hU hFd horth hspan hbr a b hy
  have hpair : ∀ (a : ι → ℝ) (δ : ι), g x (∑ ε, a ε • F ε x) (F δ x) = a δ :=
    fun a δ => by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      simp only [map_smul, ContinuousLinearMap.smul_apply, horth _ _ x hx, smul_eq_mul]
      exact sum_smul_kron (V := ℝ) a δ
  have hinner : ∀ a b : ι, g x (leviCivita g (fun y => leviCivita g (F γ) y (F b y)) x (F a x))
      (F δ x) = mvfderiv I (frameΓ c b γ δ) x (F a x) +
        ∑ ε, frameΓ c b γ ε x * frameΓ c a ε δ x := fun a b => by
    have hl := leviCivita_sum_smul hs hnd hgm Finset.univ (fun ε => frameΓ c b γ ε) F
      (fun ε => hΓd b γ ε) (fun ε => hFd ε x hx)
    rw [leviCivita_congr_of_eventuallyEq (hfield b γ), hl, ContinuousLinearMap.sum_apply, map_sum,
      ContinuousLinearMap.sum_apply]
    have hterm : ∀ ε : ι, g x ((frameΓ c b γ ε x • leviCivita g (F ε) x +
        (mvfderiv I (frameΓ c b γ ε) x).smulRight (F ε x)) (F a x)) (F δ x) =
        frameΓ c b γ ε x * frameΓ c a ε δ x +
          mvfderiv I (frameΓ c b γ ε) x (F a x) * kron ε δ := fun ε => by
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, map_add, map_smul, map_smul,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, g_leviCivita_frame_loc hs hnd hgm hU hFd horth hbr _ _ _ hx,
        horth _ _ x hx, smul_eq_mul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun ε _ => hterm ε, Finset.sum_add_distrib,
      sum_smul_kron (V := ℝ) (fun ε => mvfderiv I (frameΓ c b γ ε) x (F a x)) δ]
    ring
  have hbrk : g x (leviCivita g (F γ) x (mlieBracket I (F α) (F β) x)) (F δ x) =
      ∑ ε, c α β ε x * frameΓ c ε γ δ x := by
    rw [hbr α β x hx, map_sum, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      g_leviCivita_frame_loc hs hnd hgm hU hFd horth hbr _ _ _ hx]
  have hev : ∀ a, ∀ᶠ y in 𝓝 x, CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% (F a)) y := fun a => by
    filter_upwards [hU.mem_nhds hx] with y hy using hF a y hy
  have hR := riemannCurvatureAt_apply hs hnd hg (x := x) (hev α) (hev β) (hF γ x hx)
  rw [riemannTensorAt_apply, hR]
  have hcurv : g x (curvature (leviCivita g) (F α) (F β) (F γ) x) (F δ x) =
      g x (leviCivita g (fun y => leviCivita g (F γ) y (F β y)) x (F α x)) (F δ x) -
      g x (leviCivita g (fun y => leviCivita g (F γ) y (F α y)) x (F β x)) (F δ x) -
      g x (leviCivita g (F γ) x (mlieBracket I (F α) (F β) x)) (F δ x) := by
    simp only [curvature, map_sub, ContinuousLinearMap.sub_apply]
  rw [hcurv, hinner α β, hinner β α, hbrk, Finset.sum_sub_distrib]
  ring

end FrameLoc

end

end ExoticSpheres8And10
