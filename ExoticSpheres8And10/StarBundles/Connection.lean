/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.StarBundles.Stereographic
import ExoticSpheres8And10.Analysis.ODEParameters

/-! # §3, Step 1 (first half): a principal connection on `E|_{U_N}`

[D] Step 1: "Choose a smooth principal connection `ω₀` on `E`." Mathlib has no principal
connections. We work over `U_N ≅ V` (stereographic coordinates) with the local trivialisations
`σ_i(v) = sec_i(φ(v))` of the star bundle, pulled back to open sets `O_i ⊆ V`, and construct a
connection as a compatible family of `Im ℍ`-valued potentials `A_i : O_i → L(V, ℍ)`:

`A_j = Σ_k ψ_k g_{kj}⁻¹ dg_{kj}`, with `ψ` a smooth partition of unity on `V` subordinate to
`{O_k}` and `g_{kj}` the transition functions (`σ_j = σ_k g_{kj}`). Then

* `contDiffOn_A`: `A_j` is smooth on `O_j`;
* `A_re`: `A_j` is `Im ℍ`-valued;
* `A_compat`: on `O_i ∩ O_j`, `A_j = g_{ij}⁻¹ A_i g_{ij} + g_{ij}⁻¹ dg_{ij}` (the gauge law of
  [D] `eq:potentials`), so the local horizontal-lift equations `u' = −A(c')u` are compatible.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real Filter Topology

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Conn

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

local notation "V" => Vs e

/-! ### Stereographic coordinates on `U_N` -/

theorem inner_V (v : V) : ⟪(v : W), e⟫ = 0 := by
  have := Submodule.mem_orthogonal_singleton_iff_inner_right.1 v.2
  rwa [real_inner_comm] at this

namespace StarRep

variable (R)

/-- `φ : V → U_N ⊂ S^n`. -/
def phiN (v : V) : Sn :=
  ⟨stereoInv e v, by rw [mem_sphere_zero_iff_norm]; exact norm_stereoInv R.e_norm (inner_V v)⟩

theorem phiN_mem (v : V) : R.phiN v ∈ UN e := stereoInv_ne_neg R.e_norm (inner_V v)

theorem contMDiff_phiN : ContMDiff 𝓘(ℝ, V) (𝓡 (m + 1)) ∞ R.phiN :=
  contMDiff_sphere_of_coe (k := m + 1) ((contDiff_stereoInv e).comp (Vs e).subtypeL.contDiff).contMDiff

theorem continuous_phiN : Continuous R.phiN :=
  continuous_induced_rng.2 ((contDiff_stereoInv e).continuous.comp continuous_subtype_val)

theorem phiN_zero : R.phiN 0 = ⟨e, by simp [R.e_norm]⟩ := by
  apply Subtype.ext; simp [phiN, stereoInv]

end StarRep

/-! ### Pulled-back trivialisations -/

namespace StarBundle

/-- The chart domain `O_ζ₀ = φ⁻¹(nbhd ζ₀) ⊆ V`. -/
def O (ζ₀ : Sn) : Set V := R.phiN ⁻¹' B.nbhd ζ₀

theorem isOpen_O (ζ₀ : Sn) : IsOpen (B.O ζ₀) := (B.nbhd_open ζ₀).preimage R.continuous_phiN

theorem mem_O_self (v : V) : v ∈ B.O (R.phiN v) := B.mem_nbhd _

/-- The pulled-back local section `σ_ζ₀ = sec_ζ₀ ∘ φ`. -/
def σ (ζ₀ : Sn) (v : V) : E := B.sec ζ₀ (R.phiN v)

theorem contMDiffOn_σ (ζ₀ : Sn) : ContMDiffOn 𝓘(ℝ, V) (IP m) ∞ (B.σ ζ₀) (B.O ζ₀) :=
  (B.sec_smooth ζ₀).comp R.contMDiff_phiN.contMDiffOn fun _ h => h

theorem proj_σ (ζ₀ : Sn) {v : V} (hv : v ∈ B.O ζ₀) : B.proj (B.σ ζ₀ v) = R.phiN v :=
  B.proj_sec ζ₀ _ hv

/-- The transition `g_{ij} = σ_i⁻¹ σ_j`, as an `ℍ`-valued function. -/
def gV (i j : Sn) (v : V) : ℍ[ℝ] := (B.divE (B.σ i v) (B.σ j v) : ℍ[ℝ])

theorem norm_gV (i j : Sn) (v : V) : ‖B.gV i j v‖ = 1 := by simp [gV]

theorem σ_eq (i j : Sn) {v : V} (hi : v ∈ B.O i) (hj : v ∈ B.O j) :
    B.σ j v = B.ract (B.σ i v) (B.divE (B.σ i v) (B.σ j v)) :=
  (B.ract_divE _ _ (by rw [B.proj_σ i hi, B.proj_σ j hj])).symm

theorem contDiffOn_gV (i j : Sn) : ContDiffOn ℝ ∞ (B.gV i j) (B.O i ∩ B.O j) := by
  have h := B.contMDiffOn_divE ((B.isOpen_O i).inter (B.isOpen_O j))
    ((B.contMDiffOn_σ i).mono inter_subset_left) ((B.contMDiffOn_σ j).mono inter_subset_right)
    fun v hv => by rw [B.proj_σ i hv.1, B.proj_σ j hv.2]
  exact contMDiffOn_iff_contDiffOn.1 (contMDiff_coe_sphere.comp_contMDiffOn h)

/-- The cocycle identity `g_{kj} = g_{ki} g_{ij}`. -/
theorem gV_cocycle (i j k : Sn) {v : V} (hi : v ∈ B.O i) (hj : v ∈ B.O j) (hk : v ∈ B.O k) :
    B.gV k j v = B.gV k i v * B.gV i j v := by
  have : B.divE (B.σ k v) (B.σ j v) = B.divE (B.σ k v) (B.σ i v) * B.divE (B.σ i v) (B.σ j v) := by
    apply B.divE_unique
    rw [← B.ract_mul, ← B.σ_eq k i hk hi, ← B.σ_eq i j hi hj]
  simp only [gV, this]; rfl

/-! ### The Maurer–Cartan forms `g⁻¹ dg` -/

/-- `g_{ij}⁻¹ dg_{ij}`. -/
def mc (i j : Sn) (v : V) : V →L[ℝ] ℍ[ℝ] :=
  (ContinuousLinearMap.mul ℝ ℍ[ℝ] (Star.star (B.gV i j v))).comp (fderiv ℝ (B.gV i j) v)

theorem hasFDerivAt_gV (i j : Sn) {v : V} (h : v ∈ B.O i ∩ B.O j) :
    HasFDerivAt (B.gV i j) (fderiv ℝ (B.gV i j) v) v :=
  ((B.contDiffOn_gV i j).differentiableOn (by norm_num) v h).differentiableAt
    (((B.isOpen_O i).inter (B.isOpen_O j)).mem_nhds h) |>.hasFDerivAt

theorem contDiffOn_mc (i j : Sn) : ContDiffOn ℝ ∞ (B.mc i j) (B.O i ∩ B.O j) := by
  have hO := (B.isOpen_O i).inter (B.isOpen_O j)
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (B.gV i j) v) (B.O i ∩ B.O j) :=
    (B.contDiffOn_gV i j).fderiv_of_isOpen hO (by exact_mod_cast le_rfl)
  have h2 : ContDiffOn ℝ ∞ (fun v => ContinuousLinearMap.mul ℝ ℍ[ℝ] (Star.star (B.gV i j v)))
      (B.O i ∩ B.O j) :=
    (ContinuousLinearMap.mul ℝ ℍ[ℝ]).contDiff.comp_contDiffOn
      ((starL' ℝ : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]).contDiff.comp_contDiffOn (B.contDiffOn_gV i j))
  exact h2.clm_comp h1

/-- `g⁻¹dg` is imaginary, since `‖g‖ ≡ 1`. -/
theorem mc_re (i j : Sn) {v : V} (h : v ∈ B.O i ∩ B.O j) (w : V) : (B.mc i j v w).re = 0 := by
  have hO := (B.isOpen_O i).inter (B.isOpen_O j)
  have hd := (B.hasFDerivAt_gV i j h).inner ℝ (B.hasFDerivAt_gV i j h)
  have hconst : (fun x => ⟪B.gV i j x, B.gV i j x⟫) =ᶠ[𝓝 v] fun _ => (1 : ℝ) :=
    Eventually.of_forall fun x => by
      show ⟪B.gV i j x, B.gV i j x⟫ = 1
      rw [real_inner_self_eq_norm_sq, B.norm_gV, one_pow]
  have h0 := hd.congr_of_eventuallyEq hconst.symm |>.unique (hasFDerivAt_const (1 : ℝ) v)
  have hw := congrArg (fun L => L w) h0
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.zero_apply] at hw
  have hc := real_inner_comm (B.gV i j v) (fderiv ℝ (B.gV i j) v w)
  calc (Star.star (B.gV i j v) * fderiv ℝ (B.gV i j) v w).re
      = (fderiv ℝ (B.gV i j) v w * Star.star (B.gV i j v)).re := re_mul_comm _ _
    _ = ⟪fderiv ℝ (B.gV i j) v w, B.gV i j v⟫ := (Quaternion.inner_def _ _).symm
    _ = 0 := by linarith


/-! ### The connection potentials -/

theorem exists_pou : ∃ ψ : SmoothPartitionOfUnity Sn 𝓘(ℝ, V) V univ, ψ.IsSubordinate B.O :=
  SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, V)) isClosed_univ B.O B.isOpen_O
    fun v _ => mem_iUnion.2 ⟨_, B.mem_O_self v⟩

/-- A smooth partition of unity on `V` subordinate to the chart domains. -/
def pou : SmoothPartitionOfUnity Sn 𝓘(ℝ, V) V univ := B.exists_pou.choose

theorem pou_sub : B.pou.IsSubordinate B.O := B.exists_pou.choose_spec

theorem mem_O_of_mem_finsupport {k : Sn} {v : V} (hk : k ∈ B.pou.finsupport v) : v ∈ B.O k :=
  B.pou_sub k (subset_tsupport _ ((B.pou.mem_finsupport v).1 hk))

/-- **The connection potentials** `A_j = Σ_k ψ_k g_{kj}⁻¹ dg_{kj}`. -/
def A (j : Sn) (v : V) : V →L[ℝ] ℍ[ℝ] := ∑ᶠ k, B.pou k v • B.mc k j v

theorem A_eq_sum (j : Sn) (v : V) :
    B.A j v = ∑ k ∈ B.pou.finsupport v, B.pou k v • B.mc k j v :=
  (B.pou.sum_finsupport_smul_eq_finsum v (fun k v => B.mc k j v)).symm

theorem A_apply (j : Sn) (v w : V) :
    B.A j v w = ∑ k ∈ B.pou.finsupport v, B.pou k v • B.mc k j v w := by
  rw [A_eq_sum, ContinuousLinearMap.sum_apply]; rfl

theorem contDiffOn_A (j : Sn) : ContDiffOn ℝ ∞ (B.A j) (B.O j) := fun v hv =>
  (B.pou.contDiffAt_finsum fun k hk => (B.contDiffOn_mc k j).contDiffAt
    (((B.isOpen_O k).inter (B.isOpen_O j)).mem_nhds ⟨B.pou_sub k hk, hv⟩)).contDiffWithinAt

/-- The real part as an additive map. -/
def reHom : ℍ[ℝ] →+ ℝ where
  toFun q := q.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **`A_j` is `Im ℍ`-valued.** -/
theorem A_re (j : Sn) {v : V} (hv : v ∈ B.O j) (w : V) : (B.A j v w).re = 0 := by
  rw [A_apply]
  show reHom (∑ k ∈ B.pou.finsupport v, B.pou k v • B.mc k j v w) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  show (B.pou k v • B.mc k j v w).re = 0
  rw [Quaternion.re_smul, B.mc_re k j ⟨B.mem_O_of_mem_finsupport hk, hv⟩, smul_zero]

/-- The transformation of one Maurer–Cartan form under a change of chart. -/
theorem mc_trans (i j k : Sn) {v : V} (hi : v ∈ B.O i) (hj : v ∈ B.O j) (hk : v ∈ B.O k) (w : V) :
    B.mc k j v w = Star.star (B.gV i j v) * B.mc k i v w * B.gV i j v + B.mc i j v w := by
  have hO : IsOpen (B.O i ∩ B.O j ∩ B.O k) :=
    ((B.isOpen_O i).inter (B.isOpen_O j)).inter (B.isOpen_O k)
  have heq : B.gV k j =ᶠ[𝓝 v] fun x => B.gV k i x * B.gV i j x := by
    filter_upwards [hO.mem_nhds ⟨⟨hi, hj⟩, hk⟩] with x hx
    exact B.gV_cocycle i j k hx.1.1 hx.1.2 hx.2
  have hd := (B.hasFDerivAt_gV k i ⟨hk, hi⟩).mul' (B.hasFDerivAt_gV i j ⟨hi, hj⟩)
  have hfd := (hd.congr_of_eventuallyEq heq).fderiv
  have hunit : Star.star (B.gV k i v) * B.gV k i v = 1 := star_mul_of_norm_one (B.norm_gV _ _ _)
  simp only [mc, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', hfd,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, op_smul_eq_mul]
  rw [B.gV_cocycle i j k hi hj hk, StarMul.star_mul]
  have : Star.star (B.gV i j v) * Star.star (B.gV k i v) *
      (B.gV k i v * fderiv ℝ (B.gV i j) v w + fderiv ℝ (B.gV k i) v w * B.gV i j v) =
      Star.star (B.gV i j v) * (Star.star (B.gV k i v) * B.gV k i v) * fderiv ℝ (B.gV i j) v w +
      Star.star (B.gV i j v) * (Star.star (B.gV k i v) * fderiv ℝ (B.gV k i) v w) * B.gV i j v := by
    noncomm_ring
  rw [this, hunit, mul_one, add_comm]

/-- **The gauge law** ([D] `eq:potentials`): on `O_i ∩ O_j`,
`A_j = g_{ij}⁻¹ A_i g_{ij} + g_{ij}⁻¹ dg_{ij}`. -/
theorem A_compat (i j : Sn) {v : V} (hi : v ∈ B.O i) (hj : v ∈ B.O j) (w : V) :
    B.A j v w = Star.star (B.gV i j v) * B.A i v w * B.gV i j v +
      Star.star (B.gV i j v) * fderiv ℝ (B.gV i j) v w := by
  have h1 : ∑ k ∈ B.pou.finsupport v, B.pou k v • B.mc k j v w =
      ∑ k ∈ B.pou.finsupport v, (Star.star (B.gV i j v) * (B.pou k v • B.mc k i v w) *
        B.gV i j v + B.pou k v • B.mc i j v w) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [B.mc_trans i j k hi hj (B.mem_O_of_mem_finsupport hk), smul_add, mul_smul_comm,
      smul_mul_assoc]
  rw [A_apply, A_apply, h1, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.sum_smul, B.pou.sum_finsupport v (mem_univ v), one_smul]
  rfl

end StarBundle

end Conn

end

end ExoticSpheres8And10
