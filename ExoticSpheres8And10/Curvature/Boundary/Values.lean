/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Boundary.Matching
import ExoticSpheres8And10.Curvature.Northern.Cap

/-! # §4.4: the boundary values for [GG]'s two fillings

* `βN`, `Gs_eq_GsW`, `gB_eq_SQ`: [GG]'s northern metric is the warped product `GW (βN δ) r̃`, and
  the northern quotient metric of `S4_NorthSub` is the generic `SQ.gB`.
* `fderiv_radial`: for `n(y) = μ(|y|²)·y`, `Dn(c) = μ(|y|²)·c` when `c ⊥ y`.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section North

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- [GG]'s northern base metric `|dY|² + ψ(|Y|²)⟪Y, dY⟫²`. -/
def βN (δ : ℝ) (Y : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  ipL V + ψδ δ (‖Y‖ ^ 2) • bil mulL (innerSL ℝ Y)

theorem βN_apply (δ : ℝ) (Y a b : V) :
    βN δ Y a b = ⟪a, b⟫ + ψδ δ (‖Y‖ ^ 2) * (⟪Y, a⟫ * ⟪Y, b⟫) := by
  simp only [βN, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, bil_apply, ipL_apply,
    mulL_apply, innerSL_apply_apply, smul_eq_mul]

theorem Gs_eq_GsW (δ : ℝ) (rt : V → ℝ) : Gs δ rt = GsW (βN δ) rt := by
  funext Y
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun u' => ?_
  rw [Gs_apply, GsW_apply, βN_apply]

theorem gB_eq_SQ (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (δ : ℝ) (rt : V → ℝ) :
    gB ρV δ rt = SQ.gB ρV (GsW (βN δ) rt) := by
  rw [← Gs_eq_GsW]; rfl

theorem βN_symm (δ : ℝ) (Y a b : V) : βN δ Y a b = βN δ Y b a := by
  rw [βN_apply, βN_apply, real_inner_comm a b]; ring

theorem βN_nonneg (δ : ℝ) (Y a : V) : 0 ≤ βN δ Y a a := by
  rw [βN_apply]
  have := ψδ_nonneg δ (‖Y‖ ^ 2)
  have : 0 ≤ ⟪a, a⟫ := real_inner_self_nonneg
  nlinarith [sq_nonneg ⟪Y, a⟫]

theorem βN_pos (δ : ℝ) (Y a : V) (ha : a ≠ 0) : 0 < βN δ Y a a := by
  rw [βN_apply]
  have := ψδ_nonneg δ (‖Y‖ ^ 2)
  have := real_inner_self_pos.2 ha
  nlinarith [sq_nonneg ⟪Y, a⟫]

theorem contDiff_βN (δ : ℝ) : ContDiff ℝ ∞ (βN (V := V) δ) := by
  rw [contDiff_clm_apply_iff]
  intro a
  rw [contDiff_clm_apply_iff]
  intro b
  have e : (fun Y => βN δ Y a b) = fun Y : V => ⟪a, b⟫ + ψδ δ (‖Y‖ ^ 2) * (⟪Y, a⟫ * ⟪Y, b⟫) :=
    funext fun Y => βN_apply δ Y a b
  show ContDiff ℝ ∞ fun Y => βN δ Y a b
  rw [e]
  exact contDiff_const.add (((contDiff_ψδ δ).comp (contDiff_norm_sq ℝ)).mul
    ((contDiff_id.inner ℝ contDiff_const).mul (contDiff_id.inner ℝ contDiff_const)))

theorem βN_ρ (ρV : S3 →* (V ≃ₗᵢ[ℝ] V)) (δ : ℝ) (q : S3) (Y a b : V) :
    βN δ (ρV q Y) (ρV q a) (ρV q b) = βN δ Y a b := by
  simp only [βN_apply, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]

end North

section Radial

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The derivative of a radial field on tangential vectors**: for `n(y) = μ(|y|²)·y`,
`Dn_Y(c) = μ(|Y|²)·c` whenever `⟪Y, c⟫ = 0`. -/
theorem fderiv_radial {μ : ℝ → ℝ} {Y : V} (hμ : DifferentiableAt ℝ μ (‖Y‖ ^ 2)) {c : V}
    (hc : ⟪Y, c⟫ = 0) :
    fderiv ℝ (fun y : V => μ (‖y‖ ^ 2) • y) Y c = μ (‖Y‖ ^ 2) • c := by
  have hs := (hasStrictFDerivAt_norm_sq Y).hasFDerivAt
  have h := ((hμ.hasFDerivAt.comp Y hs).smul (hasFDerivAt_id Y))
  rw [(h.congr_of_eventuallyEq (f₁ := fun y : V => μ (‖y‖ ^ 2) • y)
    (Eventually.of_forall fun y => rfl)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.id_apply, hc, smul_zero, map_zero, zero_smul, add_zero, Function.comp_apply]

end Radial

section NorthNormal

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem fderiv_normSq_apply (y c : V) : fderiv ℝ (fun y : V => ‖y‖ ^ 2) y c = 2 * ⟪y, c⟫ := by
  rw [(hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv]
  simp [two_smul, two_mul]

/-- The `βN`-gradient of `|Y|²`: `vB = 2Y/(1 + ψ|Y|²)`. -/
def vBN (δ : ℝ) (y : V) : V := (2 / (1 + ψδ δ (‖y‖ ^ 2) * ‖y‖ ^ 2)) • y

theorem one_add_ψδ_pos (δ s : ℝ) (hs : 0 ≤ s) : 0 < 1 + ψδ δ s * s := by
  have := ψδ_nonneg δ s; positivity

theorem vBN_spec (δ : ℝ) (y c : V) : βN δ y (vBN δ y) c = fderiv ℝ (fun y : V => ‖y‖ ^ 2) y c := by
  rw [fderiv_normSq_apply, βN_apply, vBN, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have h := one_add_ψδ_pos δ (‖y‖ ^ 2) (by positivity)
  have h' : 1 + ‖y‖ ^ 2 * ψδ δ (‖y‖ ^ 2) ≠ 0 := by rw [mul_comm]; exact h.ne'
  field_simp

/-- The scalar of the northern unit normal: `ν_B = μN(|Y|²)·Y`. -/
def μN (δ s : ℝ) : ℝ := (√(4 * s / (1 + ψδ δ s * s)))⁻¹ * (2 / (1 + ψδ δ s * s))

theorem nuB_βN (δ : ℝ) : nuB (βN (V := V) δ) (vBN δ) = fun y => μN δ (‖y‖ ^ 2) • y := by
  funext y
  have h := one_add_ψδ_pos δ (‖y‖ ^ 2) (by positivity)
  have hb : βN δ y (vBN δ y) (vBN δ y) = 4 * ‖y‖ ^ 2 / (1 + ψδ δ (‖y‖ ^ 2) * ‖y‖ ^ 2) := by
    have h' : 1 + ‖y‖ ^ 2 * ψδ δ (‖y‖ ^ 2) ≠ 0 := by rw [mul_comm]; exact h.ne'
    simp only [βN_apply, vBN]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq]
    field_simp
    ring
  simp only [nuB]
  rw [hb]
  simp only [μN, vBN, smul_smul]

theorem μN_nonneg (δ s : ℝ) (hs : 0 ≤ s) : 0 ≤ μN δ s := by
  have := one_add_ψδ_pos δ s hs
  unfold μN; positivity

/-- **The northern base part is nonnegative on tangential vectors**. -/
theorem baseN_eq {δ : ℝ} {Y c : V} (hc : ⟪Y, c⟫ = 0)
    (hμ : DifferentiableAt ℝ (μN δ) (‖Y‖ ^ 2)) :
    βN δ Y (fderiv ℝ (nuB (βN δ) (vBN δ)) Y c) c +
      (1 / 2) * fderiv ℝ (βN δ) Y (nuB (βN δ) (vBN δ) Y) c c = μN δ (‖Y‖ ^ 2) * ⟪c, c⟫ := by
  rw [nuB_βN, fderiv_radial hμ hc]
  have hβd := ((contDiff_βN (V := V) δ).differentiable (by simp)) Y
  have h1 := fderiv_pair (G := βN δ) (A := fun _ => c) (B := fun _ => c) hβd
    (differentiableAt_const c) (differentiableAt_const c) (μN δ (‖Y‖ ^ 2) • Y)
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at h1
  rw [← h1]
  have e : (fun y : V => βN δ y c c) = fun y : V => ⟪c, c⟫ + ψδ δ (‖y‖ ^ 2) * (⟪y, c⟫ * ⟪y, c⟫) :=
    funext fun y => βN_apply δ y c c
  rw [e]
  have hψ := (((contDiff_ψδ δ).differentiable (by simp)) (‖Y‖ ^ 2)).hasFDerivAt.comp Y
    (hasStrictFDerivAt_norm_sq Y).hasFDerivAt
  have hi := hasFDerivAt_inner_right c Y
  have h2 := (hasFDerivAt_const ⟪c, c⟫ Y).add (hψ.mul (hi.mul hi))
  rw [(h2.congr_of_eventuallyEq (f₁ := fun y : V => ⟪c, c⟫ + ψδ δ (‖y‖ ^ 2) * (⟪y, c⟫ * ⟪y, c⟫))
    (Eventually.of_forall fun y => rfl)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.zero_apply,
    βN_apply, real_inner_smul_left, real_inner_smul_right, real_inner_comm Y c, hc,
    Function.comp_apply, Pi.mul_apply, mul_zero, zero_mul, add_zero]

end NorthNormal

section NorthFibre

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `e^{F²/2δ²} · μN(F²) · F = 1`: the `βN`-unit normal is `∂_s`. -/
theorem exp_μN_mul {δ Fa : ℝ} (hδ : δ ≠ 0) (hFa : 0 < Fa) :
    Real.exp (Fa ^ 2 / (2 * δ ^ 2)) * μN δ (Fa ^ 2) * Fa = 1 := by
  set E := 1 + ψδ δ (Fa ^ 2) * Fa ^ 2 with hE
  have hE' : E = Real.exp (Fa ^ 2 / δ ^ 2) := by
    rw [hE, mul_comm, mul_ψδ hδ]; ring
  have hEpos : 0 < E := by rw [hE']; exact Real.exp_pos _
  set X := Real.exp (Fa ^ 2 / (2 * δ ^ 2)) * μN δ (Fa ^ 2) * Fa
  have hX : 0 ≤ X := by
    have := μN_nonneg δ (Fa ^ 2) (by positivity)
    positivity
  have hq : 0 < 4 * Fa ^ 2 / E := by positivity
  have hX2 : X ^ 2 = 1 := by
    simp only [X, μN, ← hE]
    rw [mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hq.le, ← Real.exp_nat_mul]
    have : (↑(2 : ℕ) : ℝ) * (Fa ^ 2 / (2 * δ ^ 2)) = Fa ^ 2 / δ ^ 2 := by
      push_cast; field_simp
    rw [this, ← hE']
    field_simp
    ring
  have := (sq_eq_sq₀ hX zero_le_one).1 (by rw [hX2, one_pow])
  exact this

/-- **The northern fibre coefficient at the boundary**: `r̃ · Dr̃(ν) = r_a d` at `|Y| = F_a`. -/
theorem fibreN {ra d δ Fa : ℝ} (hδ : 0 < δ) (hFa : 0 < Fa) (hη : 1 / 2 ≤ Gδ δ Fa / δ) {Y : V}
    (hY : ‖Y‖ = Fa) :
    rD ra d δ Fa Y * fderiv ℝ (rD ra d δ Fa) Y (nuB (βN δ) (vBN δ) Y) = ra * d := by
  have hY0 : 0 < ‖Y‖ ^ 2 := by rw [hY]; positivity
  have e : rD (V := V) ra d δ Fa =
      fun Y => (fun t => rprof ra d δ (Gδ δ Fa) (Gδ δ (√t))) (‖Y‖ ^ 2) := by
    funext Y'; simp only [rD, Real.sqrt_sq (norm_nonneg _)]
  have hsq : √(‖Y‖ ^ 2) = Fa := by rw [Real.sqrt_sq (norm_nonneg _), hY]
  have h1 : HasDerivAt (fun t => rprof ra d δ (Gδ δ Fa) (Gδ δ (√t)))
      (d * etaCut (Gδ δ (√(‖Y‖ ^ 2)) / δ) *
        (Real.exp (√(‖Y‖ ^ 2) ^ 2 / (2 * δ ^ 2)) * (1 / (2 * √(‖Y‖ ^ 2))))) (‖Y‖ ^ 2) :=
    (hasDerivAt_rprof ra d δ (Gδ δ Fa) _).comp _ ((hasDerivAt_G δ _).comp _
      (Real.hasDerivAt_sqrt hY0.ne'))
  have h2 := h1.comp_hasFDerivAt Y (hasStrictFDerivAt_norm_sq Y).hasFDerivAt
  rw [e, (h2.congr_of_eventuallyEq
    (f₁ := fun Y => (fun t => rprof ra d δ (Gδ δ Fa) (Gδ δ (√t))) (‖Y‖ ^ 2))
    (Eventually.of_forall fun _ => rfl)).fderiv, nuB_βN]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply, two_smul,
    ContinuousLinearMap.add_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hsq, hY, rprof_end, etaCut_one hη]
  have hk := exp_μN_mul hδ.ne' hFa
  field_simp
  linear_combination (2 * ra * d) * hk

end NorthFibre

section South

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (Module.finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (Module.finrank ℝ (Vs e) = m + 1)]

namespace PolarData

/-- The `β0`-gradient of `|y|²`: `2y/ψR`. -/
def vBS (y : Vs e) : Vs e := (2 / ψR y) • y

theorem vBS_spec (y c : Vs e) : β0 y (vBS y) c = fderiv ℝ (fun y : Vs e => ‖y‖ ^ 2) y c := by
  rw [fderiv_normSq_apply, β0_apply, vBS, real_inner_smul_left]
  have := (ψR_pos y).ne'
  field_simp

/-- `ψR(y) = ψs(|y|²)`. -/
def ψs (s : ℝ) : ℝ := ((1 + s / 4) ^ 2)⁻¹

theorem ψR_eq_ψs (y : Vs e) : ψR y = ψs (‖y‖ ^ 2) := rfl

theorem ψs_pos (s : ℝ) (hs : 0 ≤ s) : 0 < ψs s := by unfold ψs; positivity

/-- The scalar of the southern unit normal. -/
def μS (s : ℝ) : ℝ := (√(4 * s / ψs s))⁻¹ * (2 / ψs s)

theorem nuB_β0 : nuB (β0 (e := e)) vBS = fun y => μS (‖y‖ ^ 2) • y := by
  funext y
  have h := ψs_pos (‖y‖ ^ 2) (by positivity)
  have hb : β0 y (vBS y) (vBS y) = 4 * ‖y‖ ^ 2 / ψs (‖y‖ ^ 2) := by
    rw [β0_apply, vBS, ψR_eq_ψs]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq]
    field_simp
    ring
  simp only [nuB]
  rw [hb]
  simp only [μS, vBS, ψR_eq_ψs, smul_smul]

theorem μS_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ μS s := by
  have := ψs_pos s hs
  unfold μS; positivity

theorem fderiv_ψR_apply (y n : Vs e) :
    fderiv ℝ (ψR (K := Vs e)) y n = -⟪y, n⟫ / (1 + ‖y‖ ^ 2 / 4) ^ 3 := by
  have hs := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hpos : 0 < 1 + ‖y‖ ^ 2 / 4 := by positivity
  have hq := (((hs.const_mul (1 / 4)).const_add 1).pow 2).congr_of_eventuallyEq
    (f₁ := fun x : Vs e => (1 + ‖x‖ ^ 2 / 4) ^ 2) (Eventually.of_forall fun x => by
      simp only [Function.comp_apply]; ring)
  have hinv := (hasDerivAt_inv (pow_pos hpos 2).ne').comp_hasFDerivAt y hq
  have e1 : ψR (K := Vs e) = (fun t => t⁻¹) ∘ fun x : Vs e => (1 + ‖x‖ ^ 2 / 4) ^ 2 := rfl
  rw [e1, hinv.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, two_smul, ContinuousLinearMap.add_apply, Function.comp_apply]
  field_simp
  ring

/-- **The southern base part** on tangential vectors. -/
theorem baseS_eq {Y c : Vs e} (hc : ⟪Y, c⟫ = 0) (hμ : DifferentiableAt ℝ μS (‖Y‖ ^ 2)) :
    β0 Y (fderiv ℝ (nuB β0 vBS) Y c) c + (1 / 2) * fderiv ℝ β0 Y (nuB β0 vBS Y) c c =
      μS (‖Y‖ ^ 2) * ⟪c, c⟫ * (ψs (‖Y‖ ^ 2) - (1 / 2) * ‖Y‖ ^ 2 / (1 + ‖Y‖ ^ 2 / 4) ^ 3) := by
  rw [nuB_β0, fderiv_radial hμ hc]
  have hβd : DifferentiableAt ℝ (β0 (e := e)) Y :=
    ((contDiff_ψR.smul contDiff_const).differentiable (by simp)) Y
  have h1 := fderiv_pair (G := β0 (e := e)) (A := fun _ => c) (B := fun _ => c) hβd
    (differentiableAt_const c) (differentiableAt_const c) (μS (‖Y‖ ^ 2) • Y)
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at h1
  rw [← h1]
  have e : (fun y : Vs e => β0 y c c) = fun y : Vs e => ψR y * ⟪c, c⟫ := funext fun y => β0_apply y c c
  rw [e, fderiv_mul_const ((contDiff_ψR.differentiable (by simp)) Y),
    ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_ψR_apply,
    β0_apply, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, ψR_eq_ψs]
  rw [real_inner_self_eq_norm_sq]
  ring

theorem baseS_factor_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ 4) :
    0 ≤ ψs s - (1 / 2) * s / (1 + s / 4) ^ 3 := by
  have hp : 0 < 1 + s / 4 := by positivity
  rw [ψs, sub_nonneg, div_le_iff₀ (pow_pos hp 3)]
  rw [show ((1 + s / 4) ^ 2)⁻¹ * (1 + s / 4) ^ 3 = 1 + s / 4 by field_simp]
  linarith

/-- **The southern fibre coefficient**: `r_S · Dr_S(ν) = −r_S²·2εA₀√s/(4+s)`. -/
theorem fibreS {ε A0 : ℝ} (hε : 0 < ε) {Y : Vs e} (hY : 0 < ‖Y‖) :
    rSy ε A0 Y * fderiv ℝ (rSy ε A0) Y (nuB β0 vBS Y) =
      -(rSy ε A0 Y ^ 2 * (2 * ε * A0 * ‖Y‖ / (4 + ‖Y‖ ^ 2))) := by
  rw [fderiv_rSy_apply, fderiv_φS_apply, nuB_β0]
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hs : 0 < ‖Y‖ ^ 2 := by positivity
  have hψ := ψs_pos (‖Y‖ ^ 2) hs.le
  have hd : (0 : ℝ) < 4 + ‖Y‖ ^ 2 := by positivity
  have hμ : μS (‖Y‖ ^ 2) * ‖Y‖ ^ 2 = ‖Y‖ * (1 + ‖Y‖ ^ 2 / 4) := by
    unfold μS ψs
    have h4 : 4 * ‖Y‖ ^ 2 / ((1 + ‖Y‖ ^ 2 / 4) ^ 2)⁻¹ = (2 * ‖Y‖ * (1 + ‖Y‖ ^ 2 / 4)) ^ 2 := by
      field_simp; ring
    rw [h4, Real.sqrt_sq (by positivity)]
    field_simp
  rw [hμ]
  field_simp
  ring

end PolarData

end South

section Model

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [Fact (Module.finrank ℝ W = (m + 1) + 1)] {e : W} [Fact (Module.finrank ℝ (Vs e) = m + 1)]

namespace PolarData

theorem differentiableAt_μN (δ : ℝ) {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ (μN δ) s := by
  have hq : DifferentiableAt ℝ (fun s => 1 + ψδ δ s * s) s :=
    (((contDiff_ψδ δ).differentiable (by simp) s).mul differentiableAt_id).const_add 1
  have hne := (one_add_ψδ_pos δ s hs.le).ne'
  have h4 : 0 < 4 * s / (1 + ψδ δ s * s) := div_pos (by positivity) (one_add_ψδ_pos δ s hs.le)
  exact (((((differentiableAt_const 4).mul differentiableAt_id).div hq hne).sqrt h4.ne').inv
    (Real.sqrt_pos.2 h4).ne').mul ((differentiableAt_const 2).div hq hne)

theorem differentiableAt_μS {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ μS s := by
  have hp : 0 < 1 + s / 4 := by positivity
  have hq : DifferentiableAt ℝ ψs s :=
    (((differentiableAt_const 1).add (differentiableAt_id.div_const 4)).pow 2).inv
      (pow_pos hp 2).ne'
  have hne := (ψs_pos s hs.le).ne'
  have h4 : 0 < 4 * s / ψs s := div_pos (by positivity) (ψs_pos s hs.le)
  exact (((((differentiableAt_const 4).mul differentiableAt_id).div hq hne).sqrt h4.ne').inv
    (Real.sqrt_pos.2 h4).ne').mul ((differentiableAt_const 2).div hq hne)

theorem contDiff_vBN {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (δ : ℝ) :
    ContDiff ℝ ∞ (vBN (V := V) δ) :=
  (contDiff_const.div (contDiff_const.add (((contDiff_ψδ δ).comp (contDiff_norm_sq ℝ)).mul
    (contDiff_norm_sq ℝ))) fun y => (one_add_ψδ_pos δ _ (by positivity)).ne').smul contDiff_id

theorem contDiff_vBS : ContDiff ℝ ∞ (vBS (e := e)) :=
  (contDiff_const.div contDiff_ψR fun y => (ψR_pos y).ne').smul contDiff_id

theorem contDiff_β0 : ContDiff ℝ ∞ (β0 (e := e)) := contDiff_ψR.smul contDiff_const

theorem β0_symm (y a b : Vs e) : β0 y a b = β0 y b a := by
  rw [β0_apply, β0_apply, real_inner_comm]

theorem β0_ρ (ρV : S3 →* (Vs e ≃ₗᵢ[ℝ] Vs e)) (q : S3) (y a b : Vs e) :
    β0 (ρV q y) (ρV q a) (ρV q b) = β0 y a b := by
  rw [β0_apply, β0_apply, ψR_ρ, LinearIsometryEquiv.inner_map_map]

theorem fderiv_normSq_ne {Y : Vs e} (hY : Y ≠ 0) : fderiv ℝ (fun y : Vs e => ‖y‖ ^ 2) Y ≠ 0 :=
    fun h => by
  have := congrArg (fun L : Vs e →L[ℝ] ℝ => L Y) h
  simp only [fderiv_normSq_apply, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at this
  exact hY (norm_eq_zero.1 (by nlinarith [norm_nonneg Y]))

/-- The boundary parameters of [GG] in terms of `ρ₀ = |y₀|`: the tangential scale of the chart
transition is `λ = ρ₀/F_a = 1 + ρ₀²/4`. -/
theorem norm_bdry {ρ0 Fa : ℝ} (hρ0 : 0 < ρ0) (hFa : Fa = 4 * ρ0 / (4 + ρ0 ^ 2)) {Y : Vs e}
    (hY : ‖Y‖ = Fa) : ‖(1 + ρ0 ^ 2 / 4) • Y‖ = ρ0 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hY, hFa]
  field_simp

/-- `β0(λY)(λa, λb) = βN(Y)(a, b)` for `a, b ⊥ Y`. -/
theorem bdry_β_match {δ ρ0 Fa : ℝ} (hρ0 : 0 < ρ0) (hFa : Fa = 4 * ρ0 / (4 + ρ0 ^ 2)) {Y : Vs e}
    (hY : ‖Y‖ = Fa) (a b : Vs e) (ha : ⟪Y, a⟫ = 0) (hb : ⟪Y, b⟫ = 0) :
    β0 ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • a) ((1 + ρ0 ^ 2 / 4) • b) = βN δ Y a b := by
  rw [β0_apply, βN_apply, ha, hb, real_inner_smul_left, real_inner_smul_right, ψR_eq_ψs,
    norm_bdry hρ0 hFa hY, ψs]
  have : (0 : ℝ) < 1 + ρ0 ^ 2 / 4 := by positivity
  field_simp
  ring

/-- `r_S(λY) = r̃(Y) = r_a` on the boundary. -/
theorem bdry_w_match {ε A0 ra d δ ρ0 Fa : ℝ} (hρ0 : 0 < ρ0) (hFa : Fa = 4 * ρ0 / (4 + ρ0 ^ 2))
    (hra : ra = √ε * Real.exp (ε / 2 * (A0 * (4 - ρ0 ^ 2) / (4 + ρ0 ^ 2)))) {Y : Vs e}
    (hY : ‖Y‖ = Fa) : rSy ε A0 ((1 + ρ0 ^ 2 / 4) • Y) = rD ra d δ Fa Y := by
  rw [rD, hY, rprof_end, rSy, φS, norm_bdry hρ0 hFa hY, hra]

variable {ρV : S3 →* (Vs e ≃ₗᵢ[ℝ] Vs e)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, Vs e →L[ℝ] Vs e) ∞ fun q : S3 => ((ρV q : Vs e ≃L[ℝ] Vs e) : Vs e →L[ℝ] Vs e))

include hρ in
/-- **The boundary metrics agree** (model charts): the southern product-connection quotient at
`λY`, on `λc`, equals the northern quotient at `Y`, on `c`. -/
theorem bdry_model_metric {ε A0 ra d δ ρ0 Fa : ℝ} (hε : 0 < ε) (hρ0 : 0 < ρ0)
    (hFa : Fa = 4 * ρ0 / (4 + ρ0 ^ 2))
    (hra : ra = √ε * Real.exp (ε / 2 * (A0 * (4 - ρ0 ^ 2) / (4 + ρ0 ^ 2))))
    (hw0N : ∀ Y : Vs e, rD ra d δ Fa Y ≠ 0) {Y : Vs e} (hY : ‖Y‖ = Fa) {c c' : Vs e} (hc : ⟪Y, c⟫ = 0)
    (hc' : ⟪Y, c'⟫ = 0) :
    SQ.gB ρV (GsW β0 (rSy ε A0)) ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • c)
        ((1 + ρ0 ^ 2 / 4) • c') = SQ.gB ρV (GsW (βN δ) (rD ra d δ Fa)) Y c c' :=
  gB_match hρ (βN_pos δ) (βN_nonneg δ) hw0N β0_pos β0_nonneg (fun y => (rSy_pos hε A0 y).ne')
    (bdry_β_match hρ0 hFa hY) (bdry_w_match hρ0 hFa hra hY) hc hc'

include hρ in
/-- **`B_N + B_S ≥ 0` on the boundary** (model charts). The northern quotient boundary at
`|Y| = F_a` with its outward normal, and the southern product-connection quotient boundary at
`|y| = ρ₀` with its outward normal, on the matched tangent vectors `c` and `λc`. The fibre terms
`r_a² q_s |ĉ₂|²` and `−r_a² q_s |ĉ₂|²` cancel, and both base parts are nonnegative. -/
theorem bdry_model_sff {ε A0 ra qs d δ ρ0 Fa : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hρ0 : 0 < ρ0)
    (hρ02 : ρ0 ≤ 2) (hFa : Fa = 4 * ρ0 / (4 + ρ0 ^ 2))
    (hra : ra = √ε * Real.exp (ε / 2 * (A0 * (4 - ρ0 ^ 2) / (4 + ρ0 ^ 2))))
    (hqs : qs = ε * A0 * Fa / 2) (hd : d = ra * qs) (hη : 1 / 2 ≤ Gδ δ Fa / δ)
    (hw0N : ∀ Y : Vs e, rD ra d δ Fa Y ≠ 0) {Y : Vs e} (hY : ‖Y‖ = Fa) {c : Vs e} (hc : ⟪Y, c⟫ = 0) :
    0 ≤ sff (SQ.isPosDef_cmet_gB' (ρV := ρV)
          (GsW_pos (w := rD ra d δ Fa) (βN_pos δ) (βN_nonneg δ) hw0N)).isNondegenerate
          (fun y : Vs e => ‖y‖ ^ 2) Y (toTSv Y c) (toTSv Y c) +
        sff (SQ.isPosDef_cmet_gB' (ρV := ρV)
          (GsW_pos (w := rSy ε A0) β0_pos β0_nonneg fun y => (rSy_pos hε A0 y).ne')).isNondegenerate
          (fun y : Vs e => ‖y‖ ^ 2) ((1 + ρ0 ^ 2 / 4) • Y)
          (toTSv ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • c))
          (toTSv ((1 + ρ0 ^ 2 / 4) • Y) ((1 + ρ0 ^ 2 / 4) • c)) := by
  have hFa0 : 0 < Fa := by rw [hFa]; positivity
  have hl : (0 : ℝ) < 1 + ρ0 ^ 2 / 4 := by positivity
  have hnY := norm_bdry hρ0 hFa hY
  have hY0 : Y ≠ 0 := fun h => by rw [h, norm_zero] at hY; linarith
  have hlY0 : (1 + ρ0 ^ 2 / 4) • Y ≠ 0 := smul_ne_zero hl.ne' hY0
  have hnρ : ∀ (q : S3) (y : Vs e), ‖ρV q y‖ ^ 2 = ‖y‖ ^ 2 := fun q y => by
    rw [LinearIsometryEquiv.norm_map]
  rw [sff_quot_GW hρ (contDiff_βN δ) (βN_symm δ) (βN_pos δ) (βN_nonneg δ) (contDiff_rD hδ) hw0N
      (βN_ρ ρV δ) (rD_invariant ra d δ Fa ρV) (contDiff_norm_sq ℝ) hnρ (fderiv_normSq_ne hY0)
      (contDiff_vBN δ) (vBN_spec δ) c,
    sff_quot_GW hρ contDiff_β0 β0_symm β0_pos β0_nonneg (contDiff_rSy ε A0)
      (fun y => (rSy_pos hε A0 y).ne') (β0_ρ ρV) (rSy_ρ ε A0) (contDiff_norm_sq ℝ) hnρ
      (fderiv_normSq_ne hlY0) contDiff_vBS vBS_spec ((1 + ρ0 ^ 2 / 4) • c),
    hlift_match hρ (βN_pos δ) (βN_nonneg δ) hw0N β0_pos β0_nonneg
      (fun y => (rSy_pos hε A0 y).ne') (bdry_β_match hρ0 hFa hY) (bdry_w_match hρ0 hFa hra hY) hc]
  set Zh := SQ.hlift ρV (GsW (βN δ) (rD ra d δ Fa)) Y c
  have hZ1 : ⟪Y, Zh.1⟫ = 0 := by
    have hdπ : Zh.1 - KY ρV Y Zh.2 = c :=
      SQ.dπl_hlift ρV (GsW_pos (w := rD ra d δ Fa) (βN_pos δ) (βN_nonneg δ) hw0N) Y c
    rw [sub_eq_iff_eq_add.1 hdπ, inner_add_right, hc, inner_Y_KY hρ, add_zero]
  have hZ1' : ⟪(1 + ρ0 ^ 2 / 4) • Y, (1 + ρ0 ^ 2 / 4) • Zh.1⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hZ1, mul_zero, mul_zero]
  have hs0 : 0 < ‖(1 + ρ0 ^ 2 / 4) • Y‖ := by rw [hnY]; exact hρ0
  rw [baseN_eq hZ1 (differentiableAt_μN δ (by rw [hY]; positivity)), fibreN hδ hFa0 hη hY,
    baseS_eq hZ1' (differentiableAt_μS (by positivity)), fibreS hε hs0]
  have hrS : rSy ε A0 ((1 + ρ0 ^ 2 / 4) • Y) = ra :=
    (bdry_w_match (d := d) (δ := δ) hρ0 hFa hra hY).trans (by rw [rD, hY, rprof_end])
  rw [hrS, hnY]
  dsimp only
  have hfib : ra * d - ra ^ 2 * (2 * ε * A0 * ρ0 / (4 + ρ0 ^ 2)) = 0 := by
    rw [hd, hqs, hFa]; field_simp; ring
  have hb1 := μN_nonneg δ (Fa ^ 2) (by positivity)
  have hb2 := μS_nonneg (ρ0 ^ 2) (by positivity)
  have hb3 := baseS_factor_nonneg (s := ρ0 ^ 2) (by positivity) (by nlinarith)
  have hi1 : 0 ≤ ⟪Zh.1, Zh.1⟫ := real_inner_self_nonneg
  have hi2 : 0 ≤ ⟪(1 + ρ0 ^ 2 / 4) • Zh.1, (1 + ρ0 ^ 2 / 4) • Zh.1⟫ := real_inner_self_nonneg
  have key : ∀ x : ℝ, ra * d * x + -(ra ^ 2 * (2 * ε * A0 * ρ0 / (4 + ρ0 ^ 2))) * x = 0 :=
    fun x => by linear_combination x * hfib
  rw [hY]
  calc (0 : ℝ) ≤ μN δ (Fa ^ 2) * ⟪Zh.1, Zh.1⟫ + μS (ρ0 ^ 2) *
        ⟪(1 + ρ0 ^ 2 / 4) • Zh.1, (1 + ρ0 ^ 2 / 4) • Zh.1⟫ *
          (ψs (ρ0 ^ 2) - 1 / 2 * ρ0 ^ 2 / (1 + ρ0 ^ 2 / 4) ^ 3) :=
        add_nonneg (mul_nonneg hb1 hi1) (mul_nonneg (mul_nonneg hb2 hi2) hb3)
    _ = _ := by linear_combination -(key ⟪Zh.2, Zh.2⟫)

/-- **Non-vacuity of `bdry_model_sff` and `bdry_model_metric`.** The parameters of
`northern_quotient_hyps_satisfiable` (`A0 = F_a = 1`, `a = π/2`) with `ρ₀ = 2`. -/
theorem bdry_model_hyps_satisfiable :
    ∃ ε A0 ra qs d δ ρ0 Fa : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < ρ0 ∧ ρ0 ≤ 2 ∧
      Fa = 4 * ρ0 / (4 + ρ0 ^ 2) ∧
      ra = √ε * Real.exp (ε / 2 * (A0 * (4 - ρ0 ^ 2) / (4 + ρ0 ^ 2))) ∧
      qs = ε * A0 * Fa / 2 ∧ d = ra * qs ∧ 1 / 2 ≤ Gδ δ Fa / δ ∧
      ∀ Y : Vs e, rD ra d δ Fa Y ≠ 0 := by
  obtain ⟨Cη, δ, ε, ra, qs, d, hC0, -, hδ, hδ3, hε, hra, hra2, hqs, hd, hql, -⟩ :=
    northern_quotient_hyps_satisfiable
  have hδ1 : δ ≤ 1 := by
    have h : 1 / (128 * 1 * 1 * (1 + Cη)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    by_contra hc
    push_neg at hc
    nlinarith [pow_lt_pow_left₀ hc zero_le_one (by norm_num : (3 : ℕ) ≠ 0)]
  have hra' : ra = √ε := by
    rw [Real.cos_pi_div_two, abs_zero, mul_zero, Real.exp_zero, mul_one] at hra2
    rw [← hra2, Real.sqrt_sq hra.le]
  refine ⟨ε, 1, ra, qs, d, δ, 2, 1, hε, hδ, by norm_num, le_rfl, by norm_num, ?_, by rw [hqs],
    hd, ?_, fun Y => (rD_pos hε one_pos one_pos hra (by rw [hqs]) hd hql Y).ne'⟩
  · rw [hra']; norm_num
  · rw [le_div_iff₀ hδ]
    have := le_G (δ := δ) zero_le_one
    linarith

end PolarData

end Model

end

end ExoticSpheres8And10
