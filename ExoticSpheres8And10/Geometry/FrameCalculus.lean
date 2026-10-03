/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.Germ

/-! # Infrastructure: frame calculus for `RiemannianGeometry`'s Levi-Civita connection and curvature

Let `F_α` (`α : ι`, a finite index type) be a smooth `g`-orthonormal frame with bracket coefficients
`[F_α, F_β] = Σ_γ c_αβ^γ F_γ`. Then:

* `g_leviCivita_frame`: `g(∇_{F_α} F_β, F_γ) = Γ_αβγ := ½(c_αβγ − c_αγβ − c_βγα)` (Koszul,
  with constant pairings);
* `leviCivita_frame`: `∇_{F_α} F_β = Σ_γ Γ_αβγ F_γ`;
* **`riemannTensorAt_frame`**: `Rm(F_α,F_β,F_γ,F_δ) = F_α(Γ_βγδ) − F_β(Γ_αγδ)
  + Σ_ε (Γ_βγε Γ_αεδ − Γ_αγε Γ_βεδ) − Σ_ε c_αβε Γ_εγδ`.

This is the computation behind every curvature formula of a connection metric
([HLY] §3.1, `eq:Koszul1`, `eq:Koszul2`): the curvature of a metric is determined by the bracket
structure of an orthonormal frame and its derivatives.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology

open scoped Manifold ContDiff

noncomputable section

section Frame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

/-- The Kronecker symbol. -/
def kron {ι : Type*} [DecidableEq ι] (a b : ι) : ℝ := if a = b then 1 else 0

/-- **The frame Christoffel coefficient** `Γ_αβγ = ½(c_αβγ − c_αγβ − c_βγα)`. -/
def frameΓ {ι : Type*} (c : ι → ι → ι → M → ℝ) (α β γ : ι) (y : M) : ℝ :=
  (c α β γ y - c α γ β y - c β γ α y) / 2

theorem sum_smul_kron {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (a : ι → ℝ) (δ : ι) : ∑ ε, a ε * kron ε δ = a δ := by
  simp [kron]

/-- A finite sum of differentiable scaled sections is differentiable. -/
theorem mdiffAt_sum_smul {κ : Type*} (s : Finset κ) {x : M} (f : κ → M → ℝ)
    (V : κ → Π y : M, TangentSpace I y) (hf : ∀ i, MDiffAt (f i) x)
    (hV : ∀ i, MDiffAt (T% (V i)) x) : MDiffAt (T% (∑ i ∈ s, f i • V i)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (contMDiff_zeroSection (n := 1) ℝ (TangentSpace I : M → Type _) x).mdifferentiableAt
      one_ne_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mdifferentiableAt_add_section ((hf a).smul_section (hV a)) ih

/-- **Leibniz for finite sums.** -/
theorem leviCivita_sum_smul (hs : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    {κ : Type*} (s : Finset κ) {x : M} (f : κ → M → ℝ) (V : κ → Π y : M, TangentSpace I y)
    (hf : ∀ i, MDiffAt (f i) x) (hV : ∀ i, MDiffAt (T% (V i)) x) :
    leviCivita g (∑ i ∈ s, f i • V i) x =
      ∑ i ∈ s, (f i x • leviCivita g (V i) x + (mvfderiv I (f i) x).smulRight (V i x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact leviCivita_zero_section
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      leviCivita_add_section hs hnd hgm ((hf a).smul_section (hV a)) (mdiffAt_sum_smul s f V hf hV),
      leviCivita_smul_section hs hnd hgm (hf a) (hV a), ih]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Π y : M, TangentSpace I y}
  {c : ι → ι → ι → M → ℝ}

/-- **The Koszul formula in an orthonormal frame.** -/
theorem g_leviCivita_frame (hs : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    (hFd : ∀ α y, MDiffAt (T% (F α)) y)
    (horth : ∀ α β y, g y (F α y) (F β y) = kron α β)
    (hbr : ∀ α β y, mlieBracket I (F α) (F β) y = ∑ γ, c α β γ y • F γ y)
    (α β γ : ι) (y : M) :
    g y (leviCivita g (F β) y (F α y)) (F γ y) = frameΓ c α β γ y := by
  have hspec := leviCivita_spec hs hnd hgm (hFd α y) (hFd β y) (hFd γ y)
  rw [hspec]
  have hconst : ∀ a b : ι, mvfderiv I (fun z => g z (F a z) (F b z)) y = 0 := fun a b => by
    have e : (fun z => g z (F a z) (F b z)) = fun _ => kron a b := funext fun z => horth a b z
    rw [e]
    ext v
    simp [mvfderiv, mfderiv_const]
  have hpair : ∀ a b d : ι, g y (mlieBracket I (F a) (F b) y) (F d y) = c a b d y :=
    fun a b d => by
      rw [hbr, map_sum, ContinuousLinearMap.sum_apply]
      simp only [map_smul, ContinuousLinearMap.smul_apply, horth, smul_eq_mul]
      exact sum_smul_kron (V := ℝ) (fun ε => c a b ε y) d
  simp only [koszulRHS, hconst, ContinuousLinearMap.zero_apply, hpair, frameΓ]
  ring

/-- **The connection in an orthonormal frame**: `∇_{F_α} F_β = Σ_γ Γ_αβγ F_γ`. -/
theorem leviCivita_frame (hs : IsSymm g) (hnd : IsNondegenerate g) (hgm : IsMDiffMetric E g)
    (hFd : ∀ α y, MDiffAt (T% (F α)) y)
    (horth : ∀ α β y, g y (F α y) (F β y) = kron α β)
    (hspan : ∀ y (w : TangentSpace I y), w = ∑ γ, g y w (F γ y) • F γ y)
    (hbr : ∀ α β y, mlieBracket I (F α) (F β) y = ∑ γ, c α β γ y • F γ y)
    (α β : ι) (y : M) :
    leviCivita g (F β) y (F α y) = ∑ γ, frameΓ c α β γ y • F γ y := by
  conv_lhs => rw [hspan y (leviCivita g (F β) y (F α y))]
  simp only [g_leviCivita_frame hs hnd hgm hFd horth hbr]

theorem mdiffAt_frameΓ (hc : ∀ α β γ y, MDiffAt (c α β γ) y) (α β γ : ι) (y : M) :
    MDiffAt (frameΓ c α β γ) y := by
  have e : frameΓ c α β γ = fun z => (c α β γ z - c α γ β z - c β γ α z) * (1 / 2 : ℝ) := by
    funext z; simp only [frameΓ]; ring
  rw [e]
  exact (((hc α β γ y).sub (hc α γ β y)).sub (hc β γ α y)).mul mdifferentiableAt_const

/-- **The curvature in an orthonormal frame.** -/
theorem riemannTensorAt_frame (hs : IsSymm g) (hp : IsPosDef g) (hg : IsContMDiffMetricSection E 2 g)
    (hF : ∀ α y, CMDiffAt ((2 : ℕ∞) : ℕ∞ω) (T% (F α)) y)
    (horth : ∀ α β y, g y (F α y) (F β y) = kron α β)
    (hspan : ∀ y (w : TangentSpace I y), w = ∑ γ, g y w (F γ y) • F γ y)
    (hbr : ∀ α β y, mlieBracket I (F α) (F β) y = ∑ γ, c α β γ y • F γ y)
    (hc : ∀ α β γ y, MDiffAt (c α β γ) y) (x : M) (α β γ δ : ι) :
    riemannTensorAt hs hp.isNondegenerate hg x (F α x) (F β x) (F γ x) (F δ x) =
      mvfderiv I (frameΓ c β γ δ) x (F α x) - mvfderiv I (frameΓ c α γ δ) x (F β x) +
      ∑ ε, (frameΓ c β γ ε x * frameΓ c α ε δ x - frameΓ c α γ ε x * frameΓ c β ε δ x) -
      ∑ ε, c α β ε x * frameΓ c ε γ δ x := by
  have hnd := hp.isNondegenerate
  have hgm : IsMDiffMetric E g := hg.isMDiffMetric (by simp)
  have hFd : ∀ α y, MDiffAt (T% (F α)) y := fun α y => (hF α y).mdifferentiableAt (by simp)
  have hΓd := mdiffAt_frameΓ hc
  have hfield : ∀ a b : ι, (fun y => leviCivita g (F b) y (F a y)) =
      ∑ ε, frameΓ c a b ε • F ε := fun a b => by
    funext y
    rw [Finset.sum_apply]
    exact leviCivita_frame hs hnd hgm hFd horth hspan hbr a b y
  have hpair : ∀ (a : ι → ℝ) (δ : ι), g x (∑ ε, a ε • F ε x) (F δ x) = a δ :=
    fun a δ => by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      simp only [map_smul, ContinuousLinearMap.smul_apply, horth, smul_eq_mul]
      exact sum_smul_kron (V := ℝ) a δ
  have hinner : ∀ a b : ι, g x (leviCivita g (fun y => leviCivita g (F γ) y (F b y)) x (F a x))
      (F δ x) = mvfderiv I (frameΓ c b γ δ) x (F a x) +
        ∑ ε, frameΓ c b γ ε x * frameΓ c a ε δ x := fun a b => by
    have hl := leviCivita_sum_smul hs hnd hgm Finset.univ (fun ε => frameΓ c b γ ε) F
      (fun ε => hΓd b γ ε x) (fun ε => hFd ε x)
    rw [hfield b γ, hl, ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.sum_apply]
    have hterm : ∀ ε : ι, g x ((frameΓ c b γ ε x • leviCivita g (F ε) x +
        (mvfderiv I (frameΓ c b γ ε) x).smulRight (F ε x)) (F a x)) (F δ x) =
        frameΓ c b γ ε x * frameΓ c a ε δ x +
          mvfderiv I (frameΓ c b γ ε) x (F a x) * kron ε δ := fun ε => by
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, map_add, map_smul, map_smul,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, g_leviCivita_frame hs hnd hgm hFd horth hbr, horth,
        smul_eq_mul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun ε _ => hterm ε, Finset.sum_add_distrib,
      sum_smul_kron (V := ℝ) (fun ε => mvfderiv I (frameΓ c b γ ε) x (F a x)) δ]
    ring
  have hbrk : g x (leviCivita g (F γ) x (mlieBracket I (F α) (F β) x)) (F δ x) =
      ∑ ε, c α β ε x * frameΓ c ε γ δ x := by
    rw [hbr, map_sum, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      g_leviCivita_frame hs hnd hgm hFd horth hbr]
  have hR := riemannCurvatureAt_apply hs hnd hg (x := x) (Eventually.of_forall (hF α))
    (Eventually.of_forall (hF β)) (hF γ x)
  rw [riemannTensorAt_apply, hR]
  have hcurv : g x (curvature (leviCivita g) (F α) (F β) (F γ) x) (F δ x) =
      g x (leviCivita g (fun y => leviCivita g (F γ) y (F β y)) x (F α x)) (F δ x) -
      g x (leviCivita g (fun y => leviCivita g (F γ) y (F α y)) x (F β x)) (F δ x) -
      g x (leviCivita g (F γ) x (mlieBracket I (F α) (F β) x)) (F δ x) := by
    simp only [curvature, map_sub, ContinuousLinearMap.sub_apply]
  rw [hcurv, hinner α β, hinner β α, hbrk, Finset.sum_sub_distrib]
  ring

end Frame

end

end ExoticSpheres8And10
