/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Gluing.Overlap

/-! # §4: the cut of `X` along `Σ = {f = 3/5}` in the two charts

With `ρ₀ = 1`, [D]'s gluing sphere is `Σ = {cos t = −3/5}`. Here `f = −cos t` (`fX`) and
`c₀ = (4 − ρ₀²)/(4 + ρ₀²) = 3/5`.
* `subN`, `subS`: `{f ≤ 3/5} ⊆ U₁` and `{f ≥ 3/5} ⊆ U₂`.
* `fX_ψN`: on `U₁`, `f = φN(|ψN|²)` with `φN(s) = φL(25 s)`, `ψN = ψ₁/5`.
* `norm_ψN_le`, `norm_ψ₂_le`, `norm_ψN_eq`: `X_N` is `|ψN| ≤ 4/5 = F_a`; `X_S` is `|ψ₂| ≤ 1`;
  on `Σ`, `|ψN| = 4/5`.
* `regular`: `df ≠ 0` on `Σ`; `inner_ψN_of_df`: `ker df_x = (ψN x)^⊥` in the chart.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

section GlueX2

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

theorem k0_ne : (1 / 5 : ℝ) ≠ 0 := by norm_num

/-- `φN(s) = φL(25 s)`. -/
def φN (s : ℝ) : ℝ := φL (s / (1 / 5) ^ 2)

theorem φL_16 : φL 16 = 3 / 5 := by norm_num [φL]

theorem φL_1 : φL 1 = -3 / 5 := by norm_num [φL]

theorem φL_le_iff {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : φL s ≤ φL t ↔ s ≤ t :=
  φL_strictMonoOn.le_iff_le hs ht

namespace PolarData

theorem fX_ι₁ (z : UN e) : D.fX (ι₁ D.κS z) = -⟪ζU z, e⟫ := rfl

theorem fX_ι₂ (z : UN e) : D.fX (ι₂ D.κS z) = ⟪ζU z, e⟫ := by
  show - -⟪ζU z, e⟫ = _; ring

theorem ζU_eq_of_not_source {z : UN e} (hz : z ∉ D.κS.source) : ζU z = e := by
  by_contra h; exact hz h

theorem subN {x : QuotSpace D} (hx : D.fX x ≤ 3 / 5) : x ∈ D.U₁ := by
  haveI := nontrivial_of_polarData D
  induction x using glued_induction with
  | h₁ a => exact ⟨a, rfl⟩
  | h₂ b =>
    by_cases hb : b ∈ D.κS.target
    · exact ⟨_, ι₂_symm hb⟩
    · have : ζU b = e := by by_contra h; exact hb h
      rw [fX_ι₂, this, real_inner_self_eq_norm_sq, D.e_norm] at hx
      norm_num at hx

theorem subS {x : QuotSpace D} (hx : 3 / 5 ≤ D.fX x) : x ∈ D.U₂ := by
  haveI := nontrivial_of_polarData D
  induction x using glued_induction with
  | h₁ a =>
    by_cases ha : a ∈ D.κS.source
    · exact ⟨_, ι₂_apply ha⟩
    · have : ζU a = e := by by_contra h; exact ha h
      rw [fX_ι₁, this, real_inner_self_eq_norm_sq, D.e_norm] at hx
      norm_num at hx
  | h₂ b => exact ⟨b, rfl⟩

theorem fX_ψN : (fun x : D.U₁ => D.fX x) =
    φN ∘ (fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψN (1 / 5) k0_ne := by
  have h := D.fX_U₁
  funext x
  have hx := congrFun h x
  simp only [comp_apply] at hx ⊢
  rw [hx, φN, ψN_apply, norm_smul, mul_pow]
  congr 1
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
  field_simp

theorem norm_ψN_le (x : D.U₁) (hx : D.fX x ≤ 3 / 5) : ‖D.ψN (1 / 5) k0_ne x‖ ≤ 4 / 5 := by
  have h := congrFun D.fX_ψN x
  simp only [comp_apply] at h
  rw [h, φN, ← φL_16, φL_le_iff (by positivity) (by norm_num)] at hx
  have : ‖D.ψN (1 / 5) k0_ne x‖ ^ 2 ≤ (4 / 5) ^ 2 := by
    have := hx; rw [div_le_iff₀ (by norm_num)] at this; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 this

theorem norm_ψN_eq (x : D.U₁) (hx : D.fX x = 3 / 5) : ‖D.ψN (1 / 5) k0_ne x‖ = 4 / 5 := by
  have h := congrFun D.fX_ψN x
  simp only [comp_apply] at h
  rw [h, φN, ← φL_16] at hx
  have hinj := φL_strictMonoOn.injOn (by simp only [mem_Ici]; positivity)
    (show (0 : ℝ) ≤ 16 by norm_num) hx
  have : ‖D.ψN (1 / 5) k0_ne x‖ ^ 2 = (4 / 5) ^ 2 := by
    rw [div_eq_iff (by norm_num)] at hinj; linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1 this

theorem norm_ψ₂_le (x : D.U₂) (hx : 3 / 5 ≤ D.fX x) : ‖D.ψ₂ x‖ ≤ 1 := by
  have h := congrFun D.fX_U₂ x
  simp only [comp_apply] at h
  have h' : φL (‖D.ψ₂ x‖ ^ 2) ≤ φL 1 := by rw [← h, φL_1]; linarith
  rw [φL_le_iff (by positivity) (by norm_num)] at h'
  nlinarith [norm_nonneg (D.ψ₂ x)]

end PolarData

/-- `φN'(s) = 8·25/(25s + 4)²`. -/
def dφN (s : ℝ) : ℝ := 8 / (s / (1 / 5) ^ 2 + 4) ^ 2 * (1 / (1 / 5) ^ 2)

theorem dφN_pos {s : ℝ} (hs : 0 ≤ s) : 0 < dφN s := by
  unfold dφN; have : 0 < s / (1 / 5) ^ 2 + 4 := by positivity
  positivity

theorem hasDerivAt_φN {s : ℝ} (hs : 0 ≤ s) : HasDerivAt φN (dφN s) s := by
  have h := (hasDerivAt_φL (show 0 ≤ s / (1 / 5) ^ 2 by positivity)).comp s
    ((hasDerivAt_id s).div_const ((1 / 5) ^ 2))
  exact h

theorem hasFDerivAt_φN_normSq (Y : Vs e) :
    HasFDerivAt (φN ∘ fun y : Vs e => ‖y‖ ^ 2) (dφN (‖Y‖ ^ 2) • (2 • innerSL ℝ Y)) Y :=
  (hasDerivAt_φN (by positivity)).comp_hasFDerivAt Y (hasStrictFDerivAt_norm_sq Y).hasFDerivAt

namespace PolarData

theorem mvfderiv_fX (x : D.U₁) (v : TangentSpace (𝓡 (m + 1)) x) :
    mvfderiv (𝓡 (m + 1)) D.fX x.1 v =
      dφN (‖D.ψN (1 / 5) k0_ne x‖ ^ 2) *
        (2 * ⟪D.ψN (1 / 5) k0_ne x, mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x v⟫) := by
  have hf : MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) D.fX x.1 :=
    (D.contMDiff_fX _).mdifferentiableAt (by simp)
  have e1 : mvfderiv (𝓡 (m + 1)) D.fX x.1 v =
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (D.fX ∘ Subtype.val) x v := by
    rw [mfderiv_comp x hf (hasMFDerivAt_opens_val _ x).mdifferentiableAt, mfderiv_opens_val]
    rfl
  have e2 : (D.fX ∘ Subtype.val : D.U₁ → ℝ) =
      (φN ∘ fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψN (1 / 5) k0_ne := D.fX_ψN
  have hψd : MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x :=
    ((D.ψN (1 / 5) k0_ne).contMDiff x).mdifferentiableAt (by simp)
  have hT := hasFDerivAt_φN_normSq (D.ψN (1 / 5) k0_ne x)
  rw [e1, e2, mfderiv_comp x hT.differentiableAt.mdifferentiableAt hψd, mfderiv_eq_fderiv,
    hT.fderiv]
  show (dφN _ • (2 • innerSL ℝ _)) (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x v) = _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply, nsmul_eq_mul,
    Nat.cast_ofNat]
  rfl

/-- `ker df_x = (ψN x)^⊥` in the northern chart. -/
theorem inner_ψN_of_df (x : D.U₁) {v : TangentSpace (𝓡 (m + 1)) x}
    (hv : mvfderiv (𝓡 (m + 1)) D.fX x.1 v = 0) :
    ⟪D.ψN (1 / 5) k0_ne x, mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x v⟫ = 0 := by
  rw [mvfderiv_fX] at hv
  have := dφN_pos (s := ‖D.ψN (1 / 5) k0_ne x‖ ^ 2) (by positivity)
  rcases mul_eq_zero.1 hv with h | h
  · linarith
  · linarith

/-- **`Σ` is a regular level set.** -/
theorem regular {x : QuotSpace D} (hx : D.fX x = 3 / 5) : mvfderiv (𝓡 (m + 1)) D.fX x ≠ 0 := by
  intro h0
  set x₁ : D.U₁ := ⟨x, D.subN hx.le⟩
  have hinv := D.isInvertible_ψN (1 / 5) k0_ne x₁
  have hv : mvfderiv (𝓡 (m + 1)) D.fX x₁.1
      ((mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) (D.ψN (1 / 5) k0_ne) x₁).inverse
        (D.ψN (1 / 5) k0_ne x₁)) = 0 := by
    rw [show x₁.1 = x from rfl, h0]; rfl
  have h1 := D.inner_ψN_of_df x₁ hv
  have h3 := congrArg (fun w : Vs e => ⟪D.ψN (1 / 5) k0_ne x₁, w⟫)
    (hinv.self_apply_inverse (D.ψN (1 / 5) k0_ne x₁))
  have h4 : ⟪D.ψN (1 / 5) k0_ne x₁, D.ψN (1 / 5) k0_ne x₁⟫ = 0 := h3.symm.trans h1
  rw [real_inner_self_eq_norm_sq, D.norm_ψN_eq x₁ hx] at h4
  norm_num at h4

end PolarData

end GlueX2

end

end ExoticSpheres8And10
