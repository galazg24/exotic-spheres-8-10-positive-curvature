/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Gluing.Transition

/-! # §4: the two charts on the overlap, and their differentials

* `ψ₂X : X → V`, the southern chart on all of `X` (meaningful on `U₂`); `ψ₂ = ψ₂X ∘ val`.
* `ψN = k ψ₁` with `k = 1/5`, the northern chart. On `X_N` it takes values in `|Y| ≤ F_a = 4/5`.
* **`ψ₂X_eq`**: on `U₁ ∖ {o_N}`, `ψ₂X = τ ∘ J ∘ ψN` with `J(Y) = (4k/|Y|²)Y`.
* **`mfderiv_ψ₂_eq`**: at a point of `U₁ ∩ U₂`,
  `dψ₂(v) = dτ_{J(ψN x)}(dJ_{ψN x}(dψN v))`, for the same model vector `v`.
* `fderiv_J`: `dJ_Y(c) = (4k/|Y|²)c` for `c ⊥ Y`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

section GlueX1

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

/-- `J(Y) = (4k/|Y|²) Y`. -/
def Jk (k : ℝ) (Y : Vs e) : Vs e := (4 * k / ‖Y‖ ^ 2) • Y

theorem fderiv_Jk (k : ℝ) {Y c : Vs e} (hY : Y ≠ 0) (hc : ⟪Y, c⟫ = 0) :
    fderiv ℝ (Jk k) Y c = (4 * k / ‖Y‖ ^ 2) • c := by
  have hs : ‖Y‖ ^ 2 ≠ 0 := by positivity
  have hμ : DifferentiableAt ℝ (fun s : ℝ => 4 * k / s) (‖Y‖ ^ 2) :=
    (differentiableAt_const _).div differentiableAt_id hs
  exact fderiv_radial hμ hc

theorem contDiffAt_Jk (k : ℝ) {Y : Vs e} (hY : Y ≠ 0) : ContDiffAt ℝ ∞ (Jk k) Y := by
  have hs : ‖Y‖ ^ 2 ≠ 0 := by positivity
  exact (contDiffAt_const.div (contDiff_norm_sq ℝ).contDiffAt hs).smul contDiffAt_id

namespace PolarData

/-- The southern chart on all of `X`. -/
def ψ₂X (x : QuotSpace D) : Vs e :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  stD (m := m) D.e_norm (chart₂ D.κS x)

theorem ψ₂_eq (x : D.U₂) : D.ψ₂ x = D.ψ₂X x.1 := rfl

theorem contMDiffAt_ψ₂X {x : QuotSpace D} (hx : x ∈ D.U₂) :
    ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞ D.ψ₂X x := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  exact ((stD (m := m) D.e_norm).contMDiff _).comp x
    (contMDiffAt_chart₂ (𝓡 (m + 1)) D.hκS D.hκSs hx)

/-- The differential of a function on `X`, restricted to an open set, is its differential. -/
theorem mfderiv_comp_val {U : TopologicalSpace.Opens (QuotSpace D)} {F : QuotSpace D → Vs e}
    (x : U) (hF : MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, Vs e) F x) :
    mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (F ∘ Subtype.val) x = mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) F x := by
  rw [mfderiv_comp x hF (hasMFDerivAt_opens_val U x).mdifferentiableAt, mfderiv_opens_val]
  rfl

theorem mfderiv_ψ₂ (x : D.U₂) :
    mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂ x = mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂X x :=
  D.mfderiv_comp_val x ((D.contMDiffAt_ψ₂X x.2).mdifferentiableAt (by simp))

theorem stD_ne_zero_iff (z : UN e) : stD (m := m) D.e_norm z ≠ 0 ↔ ζU z ≠ e := by
  constructor
  · intro h hz
    apply h
    refine Subtype.ext ?_
    show (2 : ℝ) • stereo e (ζU z) = 0
    rw [hz, stereo, real_inner_self_eq_norm_sq, D.e_norm]; simp
  · intro hz h
    have h1 := inner_ne_one_of_ne D.e_norm (by simp [ζU]) hz
    have h2 := inner_ζU_ne D.e_norm z
    have : ((stD (m := m) D.e_norm z : Vs e) : W) = 0 := by rw [h]; rfl
    have hn := congrArg (fun w => ‖w‖ ^ 2) this
    simp only [coe_stD, stereo, norm_smul, mul_pow, norm_sub_inner_sq D.e_norm
      (show ‖ζU z‖ = 1 by simp [ζU]), norm_zero] at hn
    have hlo := neg_one_lt_inner D.e_norm (show ‖ζU z‖ = 1 by simp [ζU]) h2
    have hhi := inner_lt_one D.e_norm (show ‖ζU z‖ = 1 by simp [ζU]) h1
    have : 0 < ‖(2 : ℝ)‖ ^ 2 * ‖(1 + ⟪ζU z, e⟫)⁻¹‖ ^ 2 * (1 - ⟪ζU z, e⟫ ^ 2) := by
      have h3 : (1 + ⟪ζU z, e⟫)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
      have h4 : 0 < 1 - ⟪ζU z, e⟫ ^ 2 := by nlinarith
      exact mul_pos (mul_pos (by norm_num) (pow_pos (norm_pos_iff.2 h3) 2)) h4
    linarith

/-- **The transition on the first copy**: `ψ₂X = τ ∘ inv ∘ ψ₁` away from `o_N`. -/
theorem ψ₂X_ι₁ (z : UN e) (hz : stD (m := m) D.e_norm z ≠ 0) :
    D.ψ₂X (ι₁ D.κS z) = D.τ (invV (stD (m := m) D.e_norm z)) := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  have hz' : ζU z ≠ e := (D.stD_ne_zero_iff z).1 hz
  have hsrc : z ∈ D.κS.source := hz'
  rw [← ι₂_apply hsrc]
  show stD (m := m) D.e_norm (chart₂ D.κS (ι₂ D.κS (D.κS z))) = _
  rw [chart₂_ι₂]
  exact D.stD_κS z hz'

theorem mem_U₂_of_ψ₁_ne (x : D.U₁) (hx : D.ψ₁ x ≠ 0) : x.1 ∈ D.U₂ := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  obtain ⟨_, z, rfl⟩ := x
  rw [ψ₁_mk] at hx
  have hsrc : z ∈ D.κS.source := (D.stD_ne_zero_iff z).1 hx
  exact ⟨D.κS z, ι₂_apply hsrc⟩

/-- The northern chart `ψN = k ψ₁`, `k ≠ 0`. -/
def ψN (k : ℝ) (hk : k ≠ 0) : D.U₁ ≃ₘ^∞⟮𝓡 (m + 1), 𝓘(ℝ, Vs e)⟯ Vs e :=
  D.ψ₁.trans (scaleE k hk).toDiffeomorph

theorem ψN_apply (k : ℝ) (hk : k ≠ 0) (x : D.U₁) : D.ψN k hk x = k • D.ψ₁ x := rfl

theorem isInvertible_ψN (k : ℝ) (hk : k ≠ 0) (x : D.U₁) :
    (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN k hk) x).IsInvertible :=
  ⟨(D.ψN k hk).mfderivToContinuousLinearEquiv (by simp) x, rfl⟩

/-- **The transition, in the northern chart**: `ψ₂X = τ ∘ J ∘ ψN` on `U₁ ∖ {o_N}`. -/
theorem ψ₂X_eq (k : ℝ) (hk : k ≠ 0) (x : D.U₁) (hx : D.ψ₁ x ≠ 0) :
    D.ψ₂X x.1 = D.τ (Jk k (D.ψN k hk x)) := by
  obtain ⟨_, z, rfl⟩ := x
  rw [ψ₁_mk] at hx
  rw [ψN_apply, ψ₁_mk]
  show D.ψ₂X (ι₁ D.κS z) = _
  rw [D.ψ₂X_ι₁ z hx]
  congr 1
  rw [Jk, invV, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, smul_smul]
  congr 1
  have : ‖stD (m := m) D.e_norm z‖ ≠ 0 := norm_ne_zero_iff.2 hx
  field_simp

/-- **The differentials on the overlap.** -/
theorem mfderiv_ψ₂_eq (k : ℝ) (hk : k ≠ 0) (x : D.U₁) (hx : D.ψ₁ x ≠ 0)
    (v : TangentSpace (𝓡 (m + 1)) x) :
    mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂ ⟨x.1, D.mem_U₂_of_ψ₁_ne x hx⟩ v =
      fderiv ℝ D.τ (Jk k (D.ψN k hk x))
        (fderiv ℝ (Jk k) (D.ψN k hk x) (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN k hk) x v)) := by
  have hY : D.ψN k hk x ≠ 0 := by rw [ψN_apply]; exact smul_ne_zero hk hx
  have hJ : Jk k (D.ψN k hk x) ≠ 0 := by
    rw [Jk]
    refine smul_ne_zero ?_ hY
    have : ‖D.ψN k hk x‖ ≠ 0 := norm_ne_zero_iff.2 hY
    positivity
  have hopen : IsOpen {x' : D.U₁ | D.ψ₁ x' ≠ 0} :=
    isOpen_ne_fun D.ψ₁.continuous continuous_const
  have hev : (D.ψ₂X ∘ Subtype.val : D.U₁ → Vs e) =ᶠ[𝓝 x] (D.τ ∘ Jk k) ∘ D.ψN k hk := by
    filter_upwards [hopen.mem_nhds hx] with x' hx'
    exact D.ψ₂X_eq k hk x' hx'
  have hTd : DifferentiableAt ℝ (D.τ ∘ Jk k) (D.ψN k hk x) :=
    ((D.contDiffAt_τ hJ).differentiableAt (by simp)).comp _
      ((contDiffAt_Jk k hY).differentiableAt (by simp))
  have hψd : MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN k hk) x :=
    ((D.ψN k hk).contMDiff x).mdifferentiableAt (by simp)
  have h1 : mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψ₂X ∘ Subtype.val) x =
      (fderiv ℝ (D.τ ∘ Jk k) (D.ψN k hk x)).comp
        (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN k hk) x) := by
    rw [hev.mfderiv_eq, mfderiv_comp x hTd.mdifferentiableAt hψd, mfderiv_eq_fderiv]
    rfl
  rw [D.mfderiv_comp_val x ((D.contMDiffAt_ψ₂X (D.mem_U₂_of_ψ₁_ne x hx)).mdifferentiableAt
    (by simp))] at h1
  rw [D.mfderiv_ψ₂]
  show mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂X x.1 v = _
  rw [h1]
  show fderiv ℝ (D.τ ∘ Jk k) (D.ψN k hk x)
      (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN k hk) x v) = _
  rw [fderiv_comp _ ((D.contDiffAt_τ hJ).differentiableAt (by simp))
      ((contDiffAt_Jk k hY).differentiableAt (by simp))]
  rfl

end PolarData

end GlueX1

end

end ExoticSpheres8And10
