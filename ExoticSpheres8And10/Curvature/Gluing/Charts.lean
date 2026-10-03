/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Geometry.PullbackMetric
import ExoticSpheres8And10.StarBundles.Stereographic

/-! # §4: the stereographic charts of the quotient `X = P_θ/S³_⋆`

`X = QuotSpace D` is two copies of `U_N = S^n ∖ {−e}`, glued along `κ_Σ`.
* `stD`: the (2-scaled) stereographic projection from `−e`, a diffeomorphism
  `U_N ≃ₘ V = e^⊥`, `z ↦ 2 stereo(ζ)`, with inverse `y ↦ stereoInv(y/2)`;
* `U₁ = range ι₁`, `U₂ = range ι₂` (open), and the diffeomorphisms `U_i ≃ₘ U_N`;
* `ψ₁`, `ψ₂ : U_i ≃ₘ V`;
* `⟪ζ, e⟫ = (4 − |y|²)/(4 + |y|²)` in these coordinates (`inner_e_stD`).
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Module PolarData

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

section Charts

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]

local notation "Sn" => Metric.sphere (0 : W) 1

theorem inner_Vs_e (y : Vs e) : ⟪(y : W), e⟫ = 0 := by
  have := (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).1 y.2
  rw [real_inner_comm]; exact this

theorem stereo_mem_Vs (he : ‖e‖ = 1) (ζ : W) : (2 : ℝ) • stereo e ζ ∈ Vs e := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_smul_right,
    real_inner_comm, inner_stereo he, mul_zero]

/-- The stereographic projection from `−e`, into `V = e^⊥`. -/
def stF (he : ‖e‖ = 1) (z : UN e) : Vs e := ⟨(2 : ℝ) • stereo e (ζU z), stereo_mem_Vs he _⟩

/-- Its inverse. -/
def stG (he : ‖e‖ = 1) (y : Vs e) : UN e :=
  ⟨⟨stereoInv e ((1 / 2 : ℝ) • (y : W)), by
      rw [mem_sphere_zero_iff_norm]
      exact norm_stereoInv he (by rw [real_inner_smul_left, inner_Vs_e, mul_zero])⟩,
    stereoInv_ne_neg he (by rw [real_inner_smul_left, inner_Vs_e, mul_zero])⟩

theorem inner_ζU_ne (he : ‖e‖ = 1) (z : UN e) : ⟪ζU z, e⟫ ≠ -1 :=
  inner_ne_neg_one he (by simp [ζU]) z.2

theorem stG_stF (he : ‖e‖ = 1) (z : UN e) : stG he (stF he z) = z := by
  refine Subtype.ext (Subtype.ext ?_)
  show stereoInv e ((1 / 2 : ℝ) • (2 : ℝ) • stereo e (ζU z)) = ζU z
  rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
  exact stereoInv_stereo he (by simp [ζU]) (inner_ζU_ne he z)

theorem stF_stG (he : ‖e‖ = 1) (y : Vs e) : stF he (stG he y) = y := by
  refine Subtype.ext ?_
  show (2 : ℝ) • stereo e (stereoInv e ((1 / 2 : ℝ) • (y : W))) = y
  rw [stereo_stereoInv he (by rw [real_inner_smul_left, inner_Vs_e, mul_zero]), smul_smul]
  norm_num

theorem contMDiff_ζU : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, W) ∞ (ζU (e := e)) :=
  (contMDiff_coe_sphere).comp contMDiff_subtype_val

theorem contMDiff_stF (he : ‖e‖ = 1) : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, Vs e) ∞ (stF he) := by
  have e1 : stF he = fun z => (Vs e).orthogonalProjectionOnto ((2 : ℝ) • stereo e (ζU z)) :=
    funext fun z => (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (stF he z)).symm
  rw [e1]
  intro z
  have h : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, W) ∞ (fun z : UN e => (2 : ℝ) • stereo e (ζU z)) z :=
    ((contDiffAt_stereo e (inner_ζU_ne he z)).const_smul (2 : ℝ)).comp_contMDiffAt
      (contMDiff_ζU z)
  exact ((Vs e).orthogonalProjectionOnto.contDiff.contMDiff _).comp z h

theorem contMDiff_stG (he : ‖e‖ = 1) : ContMDiff 𝓘(ℝ, Vs e) (𝓡 (m + 1)) ∞ (stG he) := by
  refine (ContMDiff.subtypeVal_comp_iff (UN e) _).1 (contMDiff_sphere_of_coe ?_)
  exact ((contDiff_stereoInv e).comp ((contDiff_const_smul (1 / 2 : ℝ)).comp
    (Vs e).subtypeL.contDiff)).contMDiff

/-- **The stereographic diffeomorphism** `U_N ≃ₘ e^⊥`. -/
def stD (he : ‖e‖ = 1) : UN e ≃ₘ^∞⟮𝓡 (m + 1), 𝓘(ℝ, Vs e)⟯ Vs e where
  toFun := stF he
  invFun := stG he
  left_inv := stG_stF he
  right_inv := stF_stG he
  contMDiff_toFun := contMDiff_stF he
  contMDiff_invFun := contMDiff_stG he

theorem coe_stD (he : ‖e‖ = 1) (z : UN e) : ((stD (m := m) he z : Vs e) : W) = (2 : ℝ) • stereo e (ζU z) :=
  rfl

/-- `⟪ζ, e⟫ = (4 − |y|²)/(4 + |y|²)` with `y = 2 stereo(ζ)`. -/
theorem inner_e_stD (he : ‖e‖ = 1) (z : UN e) :
    ⟪ζU z, e⟫ = (4 - ‖stD (m := m) he z‖ ^ 2) / (4 + ‖stD (m := m) he z‖ ^ 2) := by
  have hz : ζU z = stereoInv e ((1 / 2 : ℝ) • ((stD (m := m) he z : Vs e) : W)) :=
    congrArg (fun z' : UN e => ζU z') (stG_stF he z).symm
  have hv : ⟪(1 / 2 : ℝ) • ((stD (m := m) he z : Vs e) : W), e⟫ = 0 := by
    rw [real_inner_smul_left, inner_Vs_e, mul_zero]
  rw [hz, inner_stereoInv he hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
    Submodule.coe_norm]
  field_simp
  ring

end Charts

section Copies

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

namespace PolarData

/-- The first copy `U₁ = ι₁(U_N) ⊆ X`. -/
def U₁ : TopologicalSpace.Opens (QuotSpace D) :=
  ⟨range (ι₁ D.κS), (isOpenEmbedding_ι₁ D.κS).isOpen_range⟩

/-- The second copy `U₂ = ι₂(U_N) ⊆ X`. -/
def U₂ : TopologicalSpace.Opens (QuotSpace D) :=
  ⟨range (ι₂ D.κS), (isOpenEmbedding_ι₂ D.κS).isOpen_range⟩

/-- `U₁ ≃ₘ U_N`. -/
def ch₁ : D.U₁ ≃ₘ^∞⟮𝓡 (m + 1), 𝓡 (m + 1)⟯ UN e :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  { toFun x := chart₁ D.κS x.1
    invFun z := ⟨ι₁ D.κS z, z, rfl⟩
    left_inv x := Subtype.ext (ι₁_chart₁ D.κS x.2)
    right_inv z := chart₁_ι₁ D.κS z
    contMDiff_toFun x :=
      (contMDiffAt_chart₁ (𝓡 (m + 1)) D.hκS D.hκSs x.2).comp x (contMDiff_subtype_val x)
    contMDiff_invFun :=
      (ContMDiff.subtypeVal_comp_iff D.U₁ _).1 (contMDiff_ι₁ (𝓡 (m + 1)) D.hκS D.hκSs) }

/-- `U₂ ≃ₘ U_N`. -/
def ch₂ : D.U₂ ≃ₘ^∞⟮𝓡 (m + 1), 𝓡 (m + 1)⟯ UN e :=
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  { toFun x := chart₂ D.κS x.1
    invFun z := ⟨ι₂ D.κS z, z, rfl⟩
    left_inv x := Subtype.ext (ι₂_chart₂ D.κS x.2)
    right_inv z := chart₂_ι₂ D.κS z
    contMDiff_toFun x :=
      (contMDiffAt_chart₂ (𝓡 (m + 1)) D.hκS D.hκSs x.2).comp x (contMDiff_subtype_val x)
    contMDiff_invFun :=
      (ContMDiff.subtypeVal_comp_iff D.U₂ _).1 (contMDiff_ι₂ (𝓡 (m + 1)) D.hκS D.hκSs) }

theorem ch₁_ι₁ (z : UN e) : D.ch₁ ⟨ι₁ D.κS z, z, rfl⟩ = z := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  exact chart₁_ι₁ D.κS z

theorem ch₂_ι₂ (z : UN e) : D.ch₂ ⟨ι₂ D.κS z, z, rfl⟩ = z := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  exact chart₂_ι₂ D.κS z

/-- The northern stereographic chart `ψ₁ : U₁ ≃ₘ V`. -/
def ψ₁ : D.U₁ ≃ₘ^∞⟮𝓡 (m + 1), 𝓘(ℝ, Vs e)⟯ Vs e := D.ch₁.trans (stD D.e_norm)

/-- The southern stereographic chart `ψ₂ : U₂ ≃ₘ V`. -/
def ψ₂ : D.U₂ ≃ₘ^∞⟮𝓡 (m + 1), 𝓘(ℝ, Vs e)⟯ Vs e := D.ch₂.trans (stD D.e_norm)

theorem isInvertible_ψ₁ (x : D.U₁) : (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₁ x).IsInvertible :=
  ⟨D.ψ₁.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩

theorem isInvertible_ψ₂ (x : D.U₂) : (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, Vs e) D.ψ₂ x).IsInvertible :=
  ⟨D.ψ₂.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩

end PolarData

end Copies

section Level

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (finrank ℝ (Vs e) = m + 1)]
  (D : PolarData (m := m) e)

/-- The scaling `y ↦ k y` of `V`. -/
def scaleE (k : ℝ) (hk : k ≠ 0) : Vs e ≃L[ℝ] Vs e :=
  ContinuousLinearEquiv.equivOfInverse (k • ContinuousLinearMap.id ℝ (Vs e))
    (k⁻¹ • ContinuousLinearMap.id ℝ (Vs e)) (fun y => by simp [smul_smul, inv_mul_cancel₀ hk, mul_inv_cancel₀ hk])
    (fun y => by simp [smul_smul, inv_mul_cancel₀ hk, mul_inv_cancel₀ hk])

theorem scaleE_apply (k : ℝ) (hk : k ≠ 0) (y : Vs e) : scaleE k hk y = k • y := rfl

/-- `φ(s) = (s − 4)/(s + 4)`: the level function in stereographic coordinates. -/
def φL (s : ℝ) : ℝ := (s - 4) / (s + 4)

theorem hasDerivAt_φL {s : ℝ} (hs : 0 ≤ s) : HasDerivAt φL (8 / (s + 4) ^ 2) s := by
  have h4 : s + 4 ≠ 0 := by linarith
  have := ((hasDerivAt_id s).sub_const 4).div ((hasDerivAt_id s).add_const 4) h4
  simp only [id] at this
  have e1 : φL = (fun x => x - 4) / fun x => x + 4 := rfl
  rw [e1, show 8 / (s + 4) ^ 2 = (1 * (s + 4) - (s - 4) * 1) / (s + 4) ^ 2 by ring]
  exact this

theorem φL_strictMonoOn : StrictMonoOn φL (Ici 0) := fun a ha b hb hab => by
  simp only [mem_Ici] at ha hb
  unfold φL
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

namespace PolarData

theorem contMDiff_height : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ D.height := by
  haveI := nontrivial_of_polarData D
  haveI := nonempty_UN (e := e)
  have hi : ContDiff ℝ ∞ (fun w : W => ⟪w, e⟫) := contDiff_id.inner ℝ contDiff_const
  exact contMDiff_glueLift (𝓡 (m + 1)) D.hκS D.hκSs _ (hi.contMDiff.comp contMDiff_ζU)
    (hi.neg.contMDiff.comp contMDiff_ζU)

/-- [D]'s level function `f = −cos t` on `X`. -/
def fX (x : QuotSpace D) : ℝ := -D.height x

theorem contMDiff_fX : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ D.fX := D.contMDiff_height.neg

theorem ψ₁_mk (z : UN e) : D.ψ₁ ⟨ι₁ D.κS z, z, rfl⟩ = stD (m := m) D.e_norm z := by
  show stD (m := m) D.e_norm (D.ch₁ _) = _; rw [ch₁_ι₁]

theorem ψ₂_mk (z : UN e) : D.ψ₂ ⟨ι₂ D.κS z, z, rfl⟩ = stD (m := m) D.e_norm z := by
  show stD (m := m) D.e_norm (D.ch₂ _) = _; rw [ch₂_ι₂]

/-- On `U₁`: `f = φ(|ψ₁|²)`. -/
theorem fX_U₁ : (fun x : D.U₁ => D.fX x) = φL ∘ (fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₁ := by
  funext x
  obtain ⟨_, z, rfl⟩ := x
  show -⟪ζU z, e⟫ = φL (‖D.ψ₁ ⟨ι₁ D.κS z, z, rfl⟩‖ ^ 2)
  rw [ψ₁_mk, inner_e_stD (m := m) D.e_norm z, φL]
  have : (0 : ℝ) < 4 + ‖stD (m := m) D.e_norm z‖ ^ 2 := by positivity
  field_simp
  ring

/-- On `U₂`: `−f = φ(|ψ₂|²)`. -/
theorem fX_U₂ : (fun x : D.U₂ => -D.fX x) = φL ∘ (fun y : Vs e => ‖y‖ ^ 2) ∘ D.ψ₂ := by
  funext x
  obtain ⟨_, z, rfl⟩ := x
  show - -(-⟪ζU z, e⟫) = φL (‖D.ψ₂ ⟨ι₂ D.κS z, z, rfl⟩‖ ^ 2)
  rw [ψ₂_mk, inner_e_stD (m := m) D.e_norm z, φL]
  have : (0 : ℝ) < 4 + ‖stD (m := m) D.e_norm z‖ ^ 2 := by positivity
  field_simp
  ring

end PolarData

end Level

end

end ExoticSpheres8And10
