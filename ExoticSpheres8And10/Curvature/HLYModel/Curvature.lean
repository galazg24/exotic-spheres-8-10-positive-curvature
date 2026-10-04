/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.HLYModel.Bracket

/-! # §4, HLY model: the curvature of the connection metric in the frame

* `lieBracket_eb_eq`, `cB_eq`: the round frame has
  `c^B_{ijk}(x) = ½(⟪x, b_i⟫ δ_{jk} − ⟪x, b_j⟫ δ_{ik})`, which vanishes at `0`;
* `contDiff_cA`: the bracket table is smooth;
* **`riemannTensorAt_Fr`**: `RiemannianGeometry`'s Riemann tensor of the connection metric on frame vectors is the
  ambient expression `RmA`, built from the table and its frame derivatives
  (`riemannTensorAt_frame` in the frame `X_i, E_a`).
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Curv

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

theorem hasFDerivAt_cfac (x : K) :
    HasFDerivAt (cfac (K := K)) ((1 / 2 : ℝ) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 4 : ℝ)).const_add 1
  have e : cfac (K := K) = fun y => 1 + 1 / 4 * ‖y‖ ^ 2 := by funext y; simp [cfac]; ring
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, innerSL_apply_apply,
    smul_eq_mul, two_smul]
  ring

theorem fderiv_eb_apply (i : Fin n) (x v : K) :
    fderiv ℝ (eb b i) x v = (⟪x, v⟫ / 2) • b i := by
  have h := (hasFDerivAt_cfac x).smul_const (b i)
  have e : eb b i = fun y => cfac y • b i := rfl
  rw [e, h.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  congr 1; ring

theorem lieBracket_eb_eq (i j : Fin n) (x : K) :
    lieBracket ℝ (eb b i) (eb b j) x =
      (cfac x / 2) • (⟪x, b i⟫ • b j - ⟪x, b j⟫ • b i) := by
  simp only [lieBracket_eq]
  rw [fderiv_eb_apply, fderiv_eb_apply]
  simp only [eb, real_inner_smul_right, smul_smul, smul_sub]
  congr 1 <;> congr 1 <;> ring

theorem cB_eq (i j k : Fin n) (x : K) :
    cB b i j k x = (⟪x, b i⟫ * kron j k - ⟪x, b j⟫ * kron i k) / 2 := by
  have hc := (cfac_pos x).ne'
  rw [cB, lieBracket_eb_eq, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, b.inner_eq_ite, b.inner_eq_ite]
  simp only [kron]
  field_simp

theorem contDiff_cB (i j k : Fin n) : ContDiff ℝ ∞ (cB b i j k) := by
  have e : cB b i j k = fun x => (⟪x, b i⟫ * kron j k - ⟪x, b j⟫ * kron i k) / 2 :=
    funext (cB_eq i j k)
  rw [e]
  exact (((contDiff_id.inner ℝ contDiff_const).mul contDiff_const).sub
    ((contDiff_id.inner ℝ contDiff_const).mul contDiff_const)).div_const 2

theorem contDiff_ϑf (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (i : Fin n) :
    ContDiff ℝ ∞ (ϑf b r i) := by
  unfold ϑf
  exact ((hr.fderiv_right (m := ∞) le_rfl).clm_apply (contDiff_eb i)).div hr hr0

theorem contDiff_curvA (hA : ContDiff ℝ ∞ A) (i j : Fin n) :
    ContDiff ℝ ∞ fun x => curvA A x (eb b i x) (eb b j x) := by
  unfold curvA
  have hdA := hA.fderiv_right (m := ∞) le_rfl
  have hi := contDiff_eb (b := b) i
  have hj := contDiff_eb (b := b) j
  exact (((hdA.clm_apply hi).clm_apply hj).sub ((hdA.clm_apply hj).clm_apply hi)).add
    ((hA.clm_apply hi).mul (hA.clm_apply hj)) |>.sub ((hA.clm_apply hj).mul (hA.clm_apply hi))

theorem contDiff_Ωc (hA : ContDiff ℝ ∞ A) (i j : Fin n) (a : Fin 3) :
    ContDiff ℝ ∞ (Ωc b A i j a) := by
  unfold Ωc
  exact (((contDiff_curvA hA i j).comp contDiff_fst).mul contDiff_snd).inner ℝ
    (contDiff_snd.mul contDiff_const)

theorem contDiff_cA (hA : ContDiff ℝ ∞ A) (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0)
    (α β γ : Fin n ⊕ Fin 3) : ContDiff ℝ ∞ (cA b A r α β γ) := by
  rcases α with i | a <;> rcases β with j | c <;> rcases γ with k | d <;>
    simp only [cA]
  · exact (contDiff_cB i j k).comp contDiff_fst
  · exact ((hr.comp contDiff_fst).neg).mul (contDiff_Ωc hA i j d)
  · exact contDiff_const
  · exact (((contDiff_ϑf hr hr0 i).comp contDiff_fst).neg).mul contDiff_const
  · exact contDiff_const
  · exact ((contDiff_ϑf hr hr0 j).comp contDiff_fst).mul contDiff_const
  · exact contDiff_const
  · exact ((hr.inv hr0).comp contDiff_fst).mul contDiff_const

theorem contDiff_frameΓA (hA : ContDiff ℝ ∞ A) (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0)
    (α β γ : Fin n ⊕ Fin 3) : ContDiff ℝ ∞ (frameΓ (cA b A r) α β γ) := by
  unfold frameΓ
  exact (((contDiff_cA hA hr hr0 α β γ).sub (contDiff_cA hA hr hr0 α γ β)).sub
    (contDiff_cA hA hr hr0 β γ α)).div_const 2

variable (b A r) in
/-- **The curvature in the frame, ambiently.** -/
def RmA (α β γ δ : Fin n ⊕ Fin 3) (z : K × Quaternion ℝ) : ℝ :=
  fderiv ℝ (frameΓ (cA b A r) β γ δ) z (Fa b A r α z) -
    fderiv ℝ (frameΓ (cA b A r) α γ δ) z (Fa b A r β z) +
    ∑ ε, (frameΓ (cA b A r) β γ ε z * frameΓ (cA b A r) α ε δ z -
      frameΓ (cA b A r) α γ ε z * frameΓ (cA b A r) β ε δ z) -
    ∑ ε, cA b A r α β ε z * frameΓ (cA b A r) ε γ δ z

theorem finrank_card (b : OrthonormalBasis (Fin n) ℝ K) :
    Fintype.card (Fin n ⊕ Fin 3) = Module.finrank ℝ (K × E3) := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Module.finrank_prod,
    finrank_euclideanSpace_fin, Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]

/-- **`RiemannianGeometry`'s Riemann tensor of the connection metric, on frame vectors.** -/
theorem riemannTensorAt_Fr (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (p : K × S3) (α β γ δ : Fin n ⊕ Fin 3) :
    riemannTensorAt isSymm_GH (isPosDef_GH (A := A) hr0).isNondegenerate
      (isContMDiffMetricSection_GH hA hr) p (Fr b A r α p) (Fr b A r β p) (Fr b A r γ p)
      (Fr b A r δ p) = RmA b A r α β γ δ (emb p) := by
  have hcm : ∀ α β γ y, MDifferentiableAt (IN K) 𝓘(ℝ) (fun q => cA b A r α β γ (emb q)) y :=
    fun α β γ y => (((contDiff_cA hA hr hr0 α β γ).contMDiff.comp contMDiff_emb) y).mdifferentiableAt
      (by simp)
  have hF : ∀ α y, ContMDiffAt (IN K) (IN K).tangent ((2 : ℕ∞) : ℕ∞ω)
      (fun q => (⟨q, Fr b A r α q⟩ : TangentBundle (IN K) (K × S3))) y :=
    fun α y => contMDiff_Fr hA hr hr0 α y
  have horth := GH_Fr (b := b) hAim hr0
  have hspan := span_of_orthonormal (isPosDef_GH (A := A) hr0) horth (finrank_card b)
  have hbr : ∀ α β y, mlieBracket (IN K) (Fr b A r α) (Fr b A r β) y =
      ∑ γ, (fun q => cA b A r α β γ (emb q)) y • Fr b A r γ y :=
    fun α β y => mlieBracket_Fr hA hAim hr hr0 α β y
  rw [riemannTensorAt_frame (c := fun α β γ q => cA b A r α β γ (emb q)) isSymm_GH
    (isPosDef_GH hr0) (isContMDiffMetricSection_GH hA hr) hF horth hspan hbr hcm p]
  have hd : ∀ (α β γ δ : Fin n ⊕ Fin 3), mvfderiv (IN K)
      (frameΓ (fun α β γ q => cA b A r α β γ (emb q)) β γ δ) p (Fr b A r α p) =
      fderiv ℝ (frameΓ (cA b A r) β γ δ) (emb p) (Fa b A r α (emb p)) := fun α β γ δ => by
    have e : frameΓ (fun α β γ q => cA b A r α β γ (emb q)) β γ δ =
        frameΓ (cA b A r) β γ δ ∘ emb := rfl
    rw [e, mvfderiv_comp' ((((contDiff_frameΓA hA hr hr0 β γ δ).contMDiff) (emb p)).mdifferentiableAt
      (by simp)) ((contMDiff_emb p).mdifferentiableAt (by simp)), mfderiv_emb_Fr hAim α p]
    exact mvfderiv_vs _ _ _
  rw [hd, hd]
  rfl

end Curv

end

end ExoticSpheres8And10
