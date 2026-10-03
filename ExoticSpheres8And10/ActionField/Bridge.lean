/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.HLYGeneral
import ExoticSpheres8And10.Main.Representations

/-! # §5 ↔ §4: `lem:K` gives the hypothesis `‖K_y‖ ≤ 2` of `hly_general`

`hly_general` assumes `‖KY ρ y‖ ≤ 2`, where `KY ρ y = dρ₁(·)y` on `T₁S³ = ℝ³` in Mathlib's
chart at `1`. §5 proves [D]'s `‖K_y ξ‖ ≤ 2‖ξ‖` with `K_y ξ = d/dτ|₀ ρ(e^{τξ})y` and
`ξ ∈ Im ℍ`. They agree:
* `Dq_apply`: the chart identification `T₁S³ → ℍ` is the isometry `ι3` onto `Im ℍ`;
* `KY_eq_of_hasDerivAt`: `KY y b = K_y(ι3 b)`, by comparing the two derivatives of
  `τ ↦ ρ(e^{τ ι3 b}) y`;
* **`norm_KY_le`**: hence `‖KY y‖ ≤ 2` whenever `‖K_y ξ‖ ≤ 2‖ξ‖` for `‖y‖ ≤ 1`.
-/

open RiemannianGeometry Bundle VectorField NormedSpace

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The chart identification `T₁S³ → ℍ` is `ι3`.** -/
theorem Dq_apply (b : E3) : Dq b = ι3 b := by
  have hσ : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 3) σ3 z30 :=
    (contMDiff_σ3 z30).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ)
      (σ3 z30) :=
    ((contMDiff_coe_sphere (n := 3) : ContMDiff (𝓡 3) 𝓘(ℝ, Quaternion ℝ) ∞
      (Subtype.val : S3 → Quaternion ℝ)) _).mdifferentiableAt (by simp)
  have h := mfderiv_comp z30 hv hσ
  have hz : ι3 z30 = 0 := by rw [z30_eq, map_zero]
  have h2 : (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val ∘ σ3) z30 b : Quaternion ℝ) =
      ι3 b := by
    rw [mfderiv_eq_fderiv]
    exact (congrArg (fun L : E3 →L[ℝ] Quaternion ℝ => L b) (hasFDerivAt_val_σ3 z30).fderiv).trans
      (by show dst 1 (ι3 z30) (ι3 b) = ι3 b; rw [hz, dst_zero])
  have h3 : (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val ∘ σ3) z30 b : Quaternion ℝ) =
      mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) (σ3 z30)
        (mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 z30 b) := by rw [h]; rfl
  have h4 : (mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 z30 b : E3) = b := by rw [mfderiv_σ3]; rfl
  have hF : mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) (σ3 z30) b =
      mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) 1 b :=
    congrArg (fun q : S3 => (mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ)
      q b : Quaternion ℝ)) σ3_z30
  have h5 : mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) (σ3 z30)
      (mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 z30 b) =
      mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) (σ3 z30) b :=
    congrArg (fun w : E3 => (mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ)
      (Subtype.val : S3 → Quaternion ℝ) (σ3 z30) w : Quaternion ℝ)) h4
  show mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) 1 b = ι3 b
  exact hF.symm.trans (h5.symm.trans (h3.symm.trans h2))

theorem re_ι3 (b : E3) : (ι3 b).re = 0 := by
  have := inner_ι3_one b
  rwa [Quaternion.inner_def, star_one, mul_one] at this

/-- `τ ↦ e^{τξ}` as a `C¹` curve in `S³`. -/
theorem contMDiff_expS {ξ : Quaternion ℝ} (hξ : ξ.re = 0) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (expS hξ) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => exp (t • ξ)) (exp (t • ξ) * ξ) t :=
    fun t => hasDerivAt_exp_smul_const ξ t
  have hc : ContDiff ℝ 1 (fun t : ℝ => exp (t • ξ)) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt, ?_⟩
    have : deriv (fun t : ℝ => exp (t • ξ)) = fun t => exp (t • ξ) * ξ :=
      funext fun t => (hd t).deriv
    rw [this]
    exact (continuous_iff_continuousAt.2 fun t => (hd t).continuousAt).mul continuous_const
  exact hc.contMDiff.codRestrict_sphere fun t => (expS hξ t).2

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

/-- **`KY y b = K_y(ι3 b)`**: the derivative of `τ ↦ ρ(e^{τ ι3 b}) y`, computed through `dρ₁`. -/
theorem KY_eq_of_hasDerivAt {Kf : W → Quaternion ℝ → W} (y : Vs e) (b : E3)
    (hder : HasDerivAt (fun τ : ℝ => D.ρ (expS (re_ι3 b) τ) (y : W)) (Kf y (ι3 b)) 0) :
    ((KY D.ρVs y b : Vs e) : W) = Kf y (ι3 b) := by
  set γ := expS (re_ι3 b)
  have hγ0 : γ 0 = 1 := Subtype.ext (by simp [γ, expS])
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) γ 0 :=
    (contMDiff_expS (re_ι3 b) 0).mdifferentiableAt one_ne_zero
  -- `dγ₀(1) = b`
  have hv1 : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) (γ 0) :=
    ((contMDiff_coe_sphere (n := 3) : ContMDiff (𝓡 3) 𝓘(ℝ, Quaternion ℝ) ∞
      (Subtype.val : S3 → Quaternion ℝ)) _).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (0 : ℝ) hv1 hγd
  have hexp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Quaternion ℝ) (Subtype.val ∘ γ) 0 1 = ι3 b := by
    rw [mfderiv_eq_fderiv]
    have := (exp_curve (ι3 b)).2.1
    rw [show (Subtype.val ∘ γ) = fun τ : ℝ => exp (τ • ι3 b) from rfl, this.hasFDerivAt.fderiv]
    exact one_smul ℝ (ι3 b)
  have hdγ : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1 = b := by
    have h1' : mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) = ι3 b := by
      rw [← hexp, hc]; rfl
    have hF : mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) =
        Dq (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) :=
      congrArg (fun q : S3 => (mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ)
        (Subtype.val : S3 → Quaternion ℝ) q (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) : Quaternion ℝ)) hγ0
    have h5 : ι3 (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) = ι3 b :=
      (Dq_apply _).symm.trans (hF.symm.trans h1')
    exact ι3i.injective h5
  -- the derivative of `τ ↦ ρ(γ τ) y` through `dρ₁`
  have hρd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs) (γ 0) :=
    (D.contMDiff_ρVs _).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (0 : ℝ) hρd hγd
  have hF2 : ∀ w : E3, mfderiv (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs) (γ 0) w =
      mfderiv (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs) 1 w := fun w =>
    congrArg (fun q : S3 => (mfderiv (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs) q w :
      Vs e →L[ℝ] Vs e)) hγ0
  have hval : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs ∘ γ) 0 :
      ℝ →L[ℝ] (Vs e →L[ℝ] Vs e)) 1 = dρ D.ρVs b := by
    have e1 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs ∘ γ) 0 :
        ℝ →L[ℝ] (Vs e →L[ℝ] Vs e)) 1 =
        mfderiv (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs) (γ 0)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) := by rw [hcomp]; rfl
    have e2 : (mfderiv (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs) 1
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) : Vs e →L[ℝ] Vs e) = dρ D.ρVs b :=
      congrArg (fun w : E3 => (mfderiv (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs) 1 w :
        Vs e →L[ℝ] Vs e)) hdγ
    exact e1.trans ((hF2 _).trans e2)
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs ∘ γ) 0 :=
    hρd.comp 0 hγd
  obtain ⟨f', hf'⟩ : ∃ f' : ℝ →L[ℝ] (Vs e →L[ℝ] Vs e),
      f' = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Vs e →L[ℝ] Vs e) (ρhat D.ρVs ∘ γ) 0 := ⟨_, rfl⟩
  have hmf : HasFDerivAt (ρhat D.ρVs ∘ γ) f' 0 := hf' ▸ hmd.hasMFDerivAt.hasFDerivAt
  have hval' : f' 1 = dρ D.ρVs b := hf' ▸ hval
  have hd2 := (ContinuousLinearMap.apply ℝ (Vs e) y).hasFDerivAt.comp (0 : ℝ) hmf
  have hd3 := ((Vs e).subtypeL.hasFDerivAt.comp (0 : ℝ) hd2).hasDerivAt
  have hfun : ((Vs e).subtypeL ∘ (ContinuousLinearMap.apply ℝ (Vs e) y) ∘ (ρhat D.ρVs ∘ γ)) =
      fun τ : ℝ => D.ρ (γ τ) (y : W) := rfl
  rw [hfun] at hd3
  have huniq := hd3.unique hder
  rw [← huniq]
  show ((dρ D.ρVs b y : Vs e) : W) = ((f' 1 y : Vs e) : W)
  rw [hval']

/-- **`lem:K` gives the hypothesis of `hly_general`.** -/
theorem norm_KY_le {Kf : W → Quaternion ℝ → W}
    (hder : ∀ (ξ : Quaternion ℝ) (hξ : ξ.re = 0) (y : W),
      HasDerivAt (fun τ : ℝ => D.ρ (expS hξ τ) y) (Kf y ξ) 0)
    (hbd : ∀ y : W, ‖y‖ ≤ 1 → ∀ ξ, ‖Kf y ξ‖ ≤ 2 * ‖ξ‖) :
    ∀ y : Vs e, ‖y‖ = 1 → ‖KY D.ρVs y‖ ≤ 2 := by
  intro y hy
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun b => ?_
  have h := KY_eq_of_hasDerivAt D y b (hder _ (re_ι3 b) y)
  have h1 : ‖KY D.ρVs y b‖ = ‖Kf y (ι3 b)‖ := by
    rw [← h]; rfl
  rw [h1, ← norm_ι3 b]
  exact hbd y (le_of_eq hy) _

end

end ExoticSpheres8And10
