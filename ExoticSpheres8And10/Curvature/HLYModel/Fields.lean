/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.FrameFields
import ExoticSpheres8And10.Curvature.Northern.Chart

/-! # §4, HLY model: base-direction and fundamental fields on `K × S³`

On the trivial principal bundle `K × S³ → K` (right action `(x, u)·q = (x, uq)`):

* `Bw w`: the base-direction field `p ↦ (w, 0)`, the differential of `t ↦ (p.1 + t, p.2)` at `0`;
* `Rv ζ`: the fundamental field of the right action, the differential of `q ↦ (p.1, p.2 q)` at
  `1`. For `ζ ∈ ℝ³ = T₁S³` it reads ambiently as `u · ι(ζ)` ([HLY]'s `e^#`);
* both are smooth sections (`contMDiff_Bw`, `contMDiff_Rv`), and their ambient values are
  computed by the chain rule (`mvfderiv_fY_Bw`, `mvfderiv_fU_Bw`, `mvfderiv_fY_Rv`,
  `mvfderiv_fU_Rv`).
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The chain rule along a field `p ↦ dΦ_p(n₀) ζ`. -/
theorem mvfderiv_mfderivField {g : M → F} (Φ : M → N → M) (n₀ : N) (hn : ∀ p, Φ p n₀ = p)
    (hg : ∀ p, MDifferentiableAt I 𝓘(ℝ, F) g p) (hΦ : ∀ p, MDifferentiableAt J I (Φ p) n₀)
    (ζ : TangentSpace J n₀) (p : M) :
    mvfderiv I g p (mfderivField (I := I) Φ n₀ ζ p) = mvfderiv J (g ∘ Φ p) n₀ ζ := by
  have key : ∀ y (hy : Φ p n₀ = y),
      mvfderiv J (g ∘ Φ p) n₀ ζ = mvfderiv I g y (mfderiv J I (Φ p) n₀ ζ) := by
    intro y hy
    subst hy
    exact mvfderiv_comp' (hg _) (hΦ p) ζ
  exact (key p (hn p)).symm

end Chain

section Model

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- The right action map `q ↦ (p.1, p.2 q)`. -/
def Φv (p : K × S3) (q : S3) : K × S3 := (p.1, p.2 * q)

/-- The translation map `t ↦ (p.1 + t, p.2)`. -/
def Φb (p : K × S3) (t : K) : K × S3 := (p.1 + t, p.2)

theorem contMDiff_Φv : ContMDiff ((IN K).prod (𝓡 3)) (IN K) ∞ (uncurry (Φv (K := K))) := by
  have h1 : ContMDiff ((IN K).prod (𝓡 3)) 𝓘(ℝ, K) ∞ fun x : (K × S3) × S3 => x.1.1 :=
    contMDiff_fst.comp contMDiff_fst
  have h2 : ContMDiff ((IN K).prod (𝓡 3)) (𝓡 3) ∞ fun x : (K × S3) × S3 => x.1.2 * x.2 :=
    ContMDiff.comp (g := fun x : S3 × S3 => x.1 * x.2) (f := fun x : (K × S3) × S3 => (x.1.2, x.2))
      contMDiff_mulS3 ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  exact h1.prodMk h2

theorem contMDiff_Φb : ContMDiff ((IN K).prod 𝓘(ℝ, K)) (IN K) ∞ (uncurry (Φb (K := K))) := by
  have h1 : ContMDiff ((IN K).prod 𝓘(ℝ, K)) 𝓘(ℝ, K) ∞ fun x : (K × S3) × K => x.1.1 + x.2 :=
    (contMDiff_fst.comp contMDiff_fst).add contMDiff_snd
  have h2 : ContMDiff ((IN K).prod 𝓘(ℝ, K)) (𝓡 3) ∞ fun x : (K × S3) × K => x.1.2 :=
    contMDiff_snd.comp contMDiff_fst
  exact h1.prodMk h2

theorem mdifferentiableAt_Φv (p : K × S3) (q : S3) :
    MDifferentiableAt (𝓡 3) (IN K) (Φv p) q := by
  have : ContMDiff (𝓡 3) (IN K) ∞ (Φv p) :=
    contMDiff_Φv.comp (contMDiff_const.prodMk contMDiff_id)
  exact (this q).mdifferentiableAt (by simp)

theorem mdifferentiableAt_Φb (p : K × S3) (t : K) :
    MDifferentiableAt 𝓘(ℝ, K) (IN K) (Φb p) t := by
  have : ContMDiff 𝓘(ℝ, K) (IN K) ∞ (Φb p) :=
    contMDiff_Φb.comp (contMDiff_const.prodMk contMDiff_id)
  exact (this t).mdifferentiableAt (by simp)

/-- **The base-direction field** `(w, 0)`. -/
def Bw (w : K) : Π p : K × S3, TangentSpace (IN K) p :=
  mfderivField (I := IN K) (J := 𝓘(ℝ, K)) Φb 0 w

/-- **The fundamental field** of `ζ ∈ T₁S³` for the right action ([HLY]'s `ζ^#`). -/
def Rv (ζ : E3) : Π p : K × S3, TangentSpace (IN K) p :=
  mfderivField (I := IN K) (J := 𝓡 3) Φv 1 ζ

theorem contMDiff_Bw (w : K) : ContMDiff (IN K) (IN K).tangent ((2 : ℕ∞) : ℕ∞ω) (T% (Bw w)) :=
  contMDiff_mfderivField Φb contMDiff_Φb 0 (fun p => by simp [Φb]) w

theorem contMDiff_Rv (ζ : E3) : ContMDiff (IN K) (IN K).tangent ((2 : ℕ∞) : ℕ∞ω) (T% (Rv (K := K) ζ)) :=
  contMDiff_mfderivField Φv contMDiff_Φv 1 (fun p => by simp [Φv]) ζ

/-- `dι` at `1` is `ι3`. -/
theorem mvfderiv_val_one (ζ : E3) :
    mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) 1 ζ = ι3 ζ := by
  have hc : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ)
      (σ3 z30) := ((contMDiff_coe_sphere (m := 1)) _).mdifferentiableAt one_ne_zero
  have hs : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 3) σ3 z30 :=
    (contMDiff_σ3 z30).mdifferentiableAt (by simp)
  have key : ∀ y (hy : σ3 z30 = y), mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) y ζ = ι3 ζ := by
    intro y hy
    subst hy
    have h1 := mvfderiv_comp' (I := 𝓘(ℝ, E3)) hc hs ζ
    rw [mfderiv_σ3] at h1
    have h2 : mvfderiv 𝓘(ℝ, E3) (fun w => ((σ3 w : S3) : Quaternion ℝ)) z30 ζ = ι3 ζ := by
      have h3 := mvfderiv_vs (fun w => ((σ3 w : S3) : Quaternion ℝ)) z30 ζ
      rw [h3, (hasFDerivAt_val_σ3 z30).fderiv, ContinuousLinearMap.comp_apply, dstL_apply,
        z30_eq, map_zero, dst_zero]
    exact h1.symm.trans h2
  exact key 1 σ3_z30

theorem mvfderiv_fY_Bw (w : K) (p : K × S3) : mvfderiv (IN K) fY p (Bw w p) = w := by
  refine (mvfderiv_mfderivField (I := IN K) Φb 0 (fun p => by simp [Φb])
    (fun p => (contMDiff_fY p).mdifferentiableAt (by simp)) (fun p => mdifferentiableAt_Φb p 0)
    w p).trans ?_
  have e : (fY ∘ Φb p) = fun t : K => p.1 + t := rfl
  rw [e]
  have h := mvfderiv_vs (fun t : K => p.1 + t) (0 : K) w
  rw [fderiv_const_add, fderiv_id'] at h
  exact h

theorem mvfderiv_fU_Bw (w : K) (p : K × S3) : mvfderiv (IN K) fU p (Bw w p) = 0 := by
  refine (mvfderiv_mfderivField (I := IN K) Φb 0 (fun p => by simp [Φb])
    (fun p => (contMDiff_fU p).mdifferentiableAt (by simp)) (fun p => mdifferentiableAt_Φb p 0)
    w p).trans ?_
  have e : (fU ∘ Φb p) = fun _ : K => (p.2 : Quaternion ℝ) := rfl
  rw [e]
  have h := mvfderiv_vs (fun _ : K => (p.2 : Quaternion ℝ)) (0 : K) w
  exact h.trans (by simp)

theorem mvfderiv_fY_Rv (ζ : E3) (p : K × S3) : mvfderiv (IN K) fY p (Rv ζ p) = 0 := by
  refine (mvfderiv_mfderivField (I := IN K) Φv 1 (fun p => by simp [Φv])
    (fun p => (contMDiff_fY p).mdifferentiableAt (by simp)) (fun p => mdifferentiableAt_Φv p 1)
    ζ p).trans ?_
  have e : (fY ∘ Φv p) = fun _ : S3 => p.1 := rfl
  rw [e]
  simp [mvfderiv, mfderiv_const]
  rfl

theorem mvfderiv_fU_Rv (ζ : E3) (p : K × S3) :
    mvfderiv (IN K) fU p (Rv ζ p) = (p.2 : Quaternion ℝ) * ι3 ζ := by
  refine (mvfderiv_mfderivField (I := IN K) Φv 1 (fun p => by simp [Φv])
    (fun p => (contMDiff_fU p).mdifferentiableAt (by simp)) (fun p => mdifferentiableAt_Φv p 1)
    ζ p).trans ?_
  have e : (fU ∘ Φv p) = (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (p.2 : Quaternion ℝ)) ∘
      (Subtype.val : S3 → Quaternion ℝ) := rfl
  rw [e]
  exact (mvfderiv_clm_comp _ (((contMDiff_coe_sphere (m := 1)) 1).mdifferentiableAt one_ne_zero)
    ζ).trans ((congrArg _ (mvfderiv_val_one ζ)).trans rfl)

end Model

end

end ExoticSpheres8And10
