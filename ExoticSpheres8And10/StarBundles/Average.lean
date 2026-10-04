/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.RaySmooth
import ExoticSpheres8And10.Analysis.HaarS3

/-! # §3, Step 1 (second half): an invariant connection over `U_N`

[GG] Step 1 averages a principal connection over the star action with normalised Haar measure,
`ω = ∫ L_q^* ω₀ dq`, and checks `L_a^* ω = ω`.

The transport of Step 3 (`S3_RaySmooth`) with the partition-of-unity connection of
`S3_Connection` already gives a smooth section `s⁰ : V → E` over `U_N ≅ V` (stereographic
coordinates) with `s⁰(0) = s₀`, the model point of Step 2. In this global trivialisation a
connection is a single `Im ℍ`-valued potential, and we average the trivial one (`ω₀` = the flat
connection of `s⁰`):

* `hq q x ∈ S³`: the star action in the trivialisation, `q ⋆ s⁰(x) = s⁰(ρ(q)x) · h(q,x)`, with the
  cocycle law `hq_mul` and `hq_zero : h(q,0) = q`;
* `mu a x w = h(a,x)⁻¹ ∂_w h(a,·)(x)`: the potential of `L_a^* ω₀`, with its transformation law
  `mu_mul` (`L_a^* L_b^* = L_{ba}^*`);
* `Abar (x,w) = ∫ μ(q⁻¹, x, w) dq`: the averaged potential, smooth (`contDiff_Abar`), imaginary
  (`Abar_re`) and **invariant** (`Abar_inv`):
  `Ā(x,w) = h(a,x)⁻¹ Ā(ρ(a)x, ρ(a)w) h(a,x) + μ(a,x,w)`, i.e. `L_a^* ω = ω`.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real Filter Topology MeasureTheory

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Average

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

local notation "V" => Vs e

/-! ### The representation on `V` -/

namespace StarRep

variable (R)

theorem ρ_mem_V (q : S3) (x : V) : R.ρ q (x : W) ∈ V := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  calc ⟪e, R.ρ q x⟫ = ⟪R.ρ q e, R.ρ q x⟫ := by rw [R.ρ_e]
    _ = ⟪e, (x : W)⟫ := LinearIsometryEquiv.inner_map_map _ _ _
    _ = 0 := by rw [real_inner_comm]; exact inner_V x

/-- `ρ(q)` restricted to `V = e^⊥`. -/
def ρL (q : S3) : V →L[ℝ] V :=
  (((R.ρ q : W ≃L[ℝ] W) : W →L[ℝ] W).comp (Vs e).subtypeL).codRestrict (Vs e) (R.ρ_mem_V q)

@[simp] theorem coe_ρL (q : S3) (x : V) : ((R.ρL q x : V) : W) = R.ρ q x := rfl

theorem ρL_mul (a b : S3) (x : V) : R.ρL (a * b) x = R.ρL a (R.ρL b x) := by
  apply Subtype.ext; simp [map_mul]

theorem ρL_zero (q : S3) : R.ρL q 0 = 0 := map_zero _

theorem phiN_ρL (q : S3) (x : V) : R.phiN (R.ρL q x) = R.ρS q (R.phiN x) := by
  apply Subtype.ext
  exact stereoInv_map e (R.ρ q).toLinearIsometry (R.ρ_e q) x

theorem contMDiff_ρL :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ fun p : S3 × V => R.ρL p.1 p.2 := by
  have h1 : ContMDiff ((𝓡 3).prod 𝓘(ℝ, V)) 𝓘(ℝ, W) ∞
      fun p : S3 × V => ((R.ρ p.1 : W ≃L[ℝ] W) : W →L[ℝ] W) (p.2 : W) :=
    (R.ρ_smooth.comp contMDiff_fst).clm_apply
      ((Vs e).subtypeL.contDiff.contMDiff.comp contMDiff_snd)
  have h2 := (Vs e).orthogonalProjectionOnto.contDiff.contMDiff.comp h1
  refine h2.congr fun p => ?_
  show R.ρL p.1 p.2 = (Vs e).orthogonalProjectionOnto (R.ρL p.1 p.2 : W)
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

end StarRep

/-! ### Infrastructure: normalisation to `S³`, cutoff near `S³` -/

open Classical in
/-- The normalisation `ℍ → S³` (`0 ↦ 1`). -/
def nrmS (q : ℍ[ℝ]) : S3 :=
  if hq : q = 0 then 1 else ⟨‖q‖⁻¹ • q, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hq)]⟩

theorem nrmS_coe (a : S3) : nrmS (a : ℍ[ℝ]) = a := by
  have ha : (a : ℍ[ℝ]) ≠ 0 := ne_zero_of_mem_unit_sphere a
  apply Subtype.ext
  rw [nrmS, dif_neg ha]
  show ‖(a : ℍ[ℝ])‖⁻¹ • (a : ℍ[ℝ]) = a
  rw [mem_sphere_zero_iff_norm.1 a.2, inv_one, one_smul]

theorem contMDiffOn_nrmS : ContMDiffOn 𝓘(ℝ, ℍ[ℝ]) (𝓡 3) ∞ nrmS {q | q ≠ 0} := by
  have hs : IsOpen {q : ℍ[ℝ] | q ≠ 0} := isOpen_ne
  refine contMDiffOn_sphere_of_coe hs ?_
  have h : ContDiffOn ℝ ∞ (fun q : ℍ[ℝ] => ‖q‖⁻¹ • q) {q | q ≠ 0} := fun q hq =>
    (((contDiffAt_norm ℝ hq).inv (norm_ne_zero_iff.2 hq)).smul contDiffAt_id).contDiffWithinAt
  refine (contMDiffOn_iff_contDiffOn.2 h).congr fun q hq => ?_
  show ((nrmS q : S3) : ℍ[ℝ]) = ‖q‖⁻¹ • q
  rw [nrmS, dif_neg hq]

theorem exists_chiS : ∃ χ : ℍ[ℝ] → ℝ, ContDiff ℝ ∞ χ ∧ (∀ q ∈ sphere (0 : ℍ[ℝ]) 1, χ q = 1) ∧
    tsupport χ ⊆ {q | q ≠ 0} :=
  exists_cutoff (isCompact_sphere 0 1) isOpen_ne fun q hq h => by
    rw [h] at hq; simp at hq

/-- A cutoff equal to `1` on `S³` and supported away from `0`. -/
def chiS : ℍ[ℝ] → ℝ := exists_chiS.choose

theorem contDiff_chiS : ContDiff ℝ ∞ chiS := exists_chiS.choose_spec.1

theorem chiS_coe (a : S3) : chiS (a : ℍ[ℝ]) = 1 := exists_chiS.choose_spec.2.1 _ a.2

theorem tsupport_chiS : tsupport chiS ⊆ {q | q ≠ 0} := exists_chiS.choose_spec.2.2

/-- The real part as a continuous linear map. -/
def reL : ℍ[ℝ] →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (QuaternionAlgebra.reₗ _ _ _)

@[simp] theorem reL_apply (q : ℍ[ℝ]) : reL q = q.re := rfl

/-- `f⁻¹ df` is imaginary for a unit-quaternion-valued `f`. -/
theorem re_star_mul_fderiv {f : V → ℍ[ℝ]} {x : V} (hf : DifferentiableAt ℝ f x)
    (hn : ∀ y, ‖f y‖ = 1) (w : V) : (Star.star (f x) * fderiv ℝ f x w).re = 0 := by
  have hd := hf.hasFDerivAt.inner ℝ hf.hasFDerivAt
  have hconst : (fun y => ⟪f y, f y⟫) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Eventually.of_forall fun y => by
      show ⟪f y, f y⟫ = 1
      rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have h0 := hd.congr_of_eventuallyEq hconst.symm |>.unique (hasFDerivAt_const (1 : ℝ) x)
  have hw := congrArg (fun L => L w) h0
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.zero_apply] at hw
  have hc := real_inner_comm (f x) (fderiv ℝ f x w)
  calc (Star.star (f x) * fderiv ℝ f x w).re
      = (fderiv ℝ f x w * Star.star (f x)).re := re_mul_comm _ _
    _ = ⟪fderiv ℝ f x w, f x⟫ := (Quaternion.inner_def _ _).symm
    _ = 0 := by linarith

namespace StarBundle

variable [T2Space E]

/-! ### The section `s⁰` by transport from the model point -/

theorem exists_s0 : ∃ s₀ : E, B.proj s₀ = R.phiN 0 ∧ ∀ q, B.star q s₀ = B.ract s₀ q :=
  B.exists_model_point (R.phiN 0) fun q => by rw [← R.phiN_ρL, R.ρL_zero]

/-- The model point `s₀` of Step 2 over `o_N = φ(0)`. -/
def s0pt : E := B.exists_s0.choose

theorem proj_s0pt : B.proj B.s0pt = R.phiN 0 := B.exists_s0.choose_spec.1

theorem star_s0pt (q : S3) : B.star q B.s0pt = B.ract B.s0pt q := B.exists_s0.choose_spec.2 q

/-- **The section `s⁰`**: transport of `s₀` along rays for the partition-of-unity connection. -/
def s0 (v : V) : E := B.rayEnd B.s0pt B.proj_s0pt v

theorem contMDiff_s0 : ContMDiff 𝓘(ℝ, V) (IP m) ∞ B.s0 :=
  B.contMDiff_rayEnd B.s0pt B.proj_s0pt

theorem proj_s0 (v : V) : B.proj (B.s0 v) = R.phiN v := B.proj_rayEnd _ _ v

theorem s0_zero : B.s0 0 = B.s0pt := by
  refine B.rayEnd_eq B.proj_s0pt (Γ := fun _ => B.s0pt) ⟨fun τ _ => ?_, fun i τ _ _ => ?_⟩ rfl
  · rw [smul_zero]; exact B.proj_s0pt
  · simp only [map_zero, neg_zero, zero_mul]
    exact hasDerivWithinAt_const _ _ _

/-! ### The star action in the trivialisation `s⁰` -/

theorem proj_star_s0 (q : S3) (x : V) :
    B.proj (B.star q (B.s0 x)) = B.proj (B.s0 (R.ρL q x)) := by
  rw [B.proj_star, B.proj_s0, B.proj_s0, R.phiN_ρL]

/-- `q ⋆ s⁰(x) = s⁰(ρ(q)x) · h(q,x)`. -/
def hq (q : S3) (x : V) : S3 := B.divE (B.s0 (R.ρL q x)) (B.star q (B.s0 x))

theorem ract_hq (q : S3) (x : V) : B.ract (B.s0 (R.ρL q x)) (B.hq q x) = B.star q (B.s0 x) :=
  B.ract_divE _ _ (B.proj_star_s0 q x)

theorem hq_unique {q : S3} {x : V} {g : S3}
    (hg : B.ract (B.s0 (R.ρL q x)) g = B.star q (B.s0 x)) : B.hq q x = g :=
  B.divE_unique _ _ _ hg

/-- The cocycle law `h(ab, x) = h(a, ρ(b)x) h(b, x)`. -/
theorem hq_mul (a b : S3) (x : V) : B.hq (a * b) x = B.hq a (R.ρL b x) * B.hq b x := by
  apply B.hq_unique
  rw [← B.ract_mul, R.ρL_mul, B.ract_hq a (R.ρL b x), ← B.star_ract, B.ract_hq, B.star_mul]

theorem hq_zero (q : S3) : B.hq q 0 = q := by
  apply B.hq_unique
  rw [R.ρL_zero, B.s0_zero, B.star_s0pt]

theorem contMDiff_hq :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, V)) (𝓡 3) ∞ fun p : S3 × V => B.hq p.1 p.2 := by
  have hf : ContMDiff ((𝓡 3).prod 𝓘(ℝ, V)) (IP m) ∞ fun p : S3 × V => B.s0 (R.ρL p.1 p.2) :=
    B.contMDiff_s0.comp R.contMDiff_ρL
  have hf' : ContMDiff ((𝓡 3).prod 𝓘(ℝ, V)) (IP m) ∞ fun p : S3 × V => B.star p.1 (B.s0 p.2) :=
    ContMDiff.comp (g := fun x : S3 × E => B.star x.1 x.2) (f := fun p : S3 × V => (p.1, B.s0 p.2))
      B.star_smooth (contMDiff_fst.prodMk (B.contMDiff_s0.comp contMDiff_snd))
  exact contMDiffOn_univ.1 (B.contMDiffOn_divE isOpen_univ hf.contMDiffOn hf'.contMDiffOn
    fun p _ => B.proj_star_s0 p.1 p.2)

/-- The ambient extension `Ĥ(q, x) = χ(q) h(q/|q|, x) ∈ ℍ`, smooth on `ℍ × V`. -/
def Hh (q : ℍ[ℝ]) (x : V) : ℍ[ℝ] := chiS q • ((B.hq (nrmS q) x : S3) : ℍ[ℝ])

theorem Hh_coe (a : S3) (x : V) : B.Hh (a : ℍ[ℝ]) x = B.hq a x := by
  rw [Hh, chiS_coe, one_smul, nrmS_coe]

theorem contDiff_Hh : ContDiff ℝ ∞ fun p : ℍ[ℝ] × V => B.Hh p.1 p.2 := by
  have hΩ : IsOpen {p : ℍ[ℝ] × V | p.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hn : ContMDiffOn 𝓘(ℝ, ℍ[ℝ] × V) ((𝓡 3).prod 𝓘(ℝ, V)) ∞
      (fun p : ℍ[ℝ] × V => (nrmS p.1, p.2)) {p | p.1 ≠ 0} :=
    (contMDiffOn_nrmS.comp contDiff_fst.contMDiff.contMDiffOn fun _ hp => hp).prodMk
      contDiff_snd.contMDiff.contMDiffOn
  have h1 : ContMDiffOn 𝓘(ℝ, ℍ[ℝ] × V) 𝓘(ℝ, ℍ[ℝ]) ∞
      (fun p : ℍ[ℝ] × V => ((B.hq (nrmS p.1) p.2 : S3) : ℍ[ℝ])) {p | p.1 ≠ 0} :=
    contMDiff_coe_sphere.comp_contMDiffOn
      (ContMDiff.comp_contMDiffOn (g := fun p : S3 × V => B.hq p.1 p.2)
        (f := fun p : ℍ[ℝ] × V => (nrmS p.1, p.2)) B.contMDiff_hq hn)
  refine contDiff_cutoff_smul (χ := fun p : ℍ[ℝ] × V => chiS p.1) hΩ
    (contDiff_chiS.comp contDiff_fst) ?_ (contMDiffOn_iff_contDiffOn.1 h1)
  exact (tsupport_comp_subset_preimage chiS continuous_fst).trans fun p hp => tsupport_chiS hp

theorem contDiff_hq_coe (a : S3) : ContDiff ℝ ∞ fun y : V => ((B.hq a y : S3) : ℍ[ℝ]) := by
  have := B.contDiff_Hh.comp (contDiff_const (c := (a : ℍ[ℝ])).prodMk contDiff_id)
  have e : (fun y : V => ((B.hq a y : S3) : ℍ[ℝ])) =
      (fun p : ℍ[ℝ] × V => B.Hh p.1 p.2) ∘ fun y => ((a : ℍ[ℝ]), id y) :=
    funext fun y => (B.Hh_coe a y).symm
  rw [e]; exact this

theorem hasFDerivAt_hq (a : S3) (x : V) :
    HasFDerivAt (fun y : V => ((B.hq a y : S3) : ℍ[ℝ]))
      (fderiv ℝ (fun y : V => ((B.hq a y : S3) : ℍ[ℝ])) x) x :=
  ((B.contDiff_hq_coe a).differentiable (by simp)).differentiableAt.hasFDerivAt

/-! ### The Maurer–Cartan term and its transformation law -/

/-- The potential of `L_a^* ω₀`: `μ(a, x, w) = h(a,x)⁻¹ ∂_w h(a, ·)(x)`. -/
def mu (a : S3) (x w : V) : ℍ[ℝ] :=
  Star.star ((B.hq a x : S3) : ℍ[ℝ]) * fderiv ℝ (fun y : V => ((B.hq a y : S3) : ℍ[ℝ])) x w

theorem mu_re (a : S3) (x w : V) : (B.mu a x w).re = 0 :=
  re_star_mul_fderiv ((B.hasFDerivAt_hq a x).differentiableAt)
    (fun y => mem_sphere_zero_iff_norm.1 (B.hq a y).2) w

/-- **`L_a^* L_b^* ω₀ = L_{ba}^* ω₀`** in the trivialisation. -/
theorem mu_mul (b a : S3) (x w : V) :
    B.mu (b * a) x w = Star.star ((B.hq a x : S3) : ℍ[ℝ]) * B.mu b (R.ρL a x) (R.ρL a w) *
      ((B.hq a x : S3) : ℍ[ℝ]) + B.mu a x w := by
  set f : V → ℍ[ℝ] := fun y => ((B.hq b y : S3) : ℍ[ℝ])
  set g : V → ℍ[ℝ] := fun y => ((B.hq a y : S3) : ℍ[ℝ])
  have hfa : HasFDerivAt (fun y => f (R.ρL a y)) ((fderiv ℝ f (R.ρL a x)).comp (R.ρL a)) x :=
    (B.hasFDerivAt_hq b (R.ρL a x)).comp x (R.ρL a).hasFDerivAt
  have hd := hfa.mul' (B.hasFDerivAt_hq a x)
  have heq : (fun y : V => ((B.hq (b * a) y : S3) : ℍ[ℝ])) = fun y => f (R.ρL a y) * g y := by
    funext y; rw [B.hq_mul]; rfl
  have hfd : fderiv ℝ (fun y : V => ((B.hq (b * a) y : S3) : ℍ[ℝ])) x w =
      f (R.ρL a x) * fderiv ℝ g x w + fderiv ℝ f (R.ρL a x) (R.ρL a w) * g x := by
    rw [heq, show (fun y => f (R.ρL a y) * g y) =
      ((fun y => f (R.ρL a y)) * fun y => ((B.hq a y : S3) : ℍ[ℝ])) from rfl, hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      op_smul_eq_mul]
    rfl
  have hunit : Star.star (f (R.ρL a x)) * f (R.ρL a x) = 1 :=
    star_mul_of_norm_one (mem_sphere_zero_iff_norm.1 (B.hq b _).2)
  have hcoe : ((B.hq (b * a) x : S3) : ℍ[ℝ]) = f (R.ρL a x) * g x := by rw [B.hq_mul]; rfl
  rw [mu, hfd, hcoe, StarMul.star_mul]
  simp only [mu]
  change Star.star (g x) * Star.star (f (R.ρL a x)) *
      (f (R.ρL a x) * fderiv ℝ g x w + fderiv ℝ f (R.ρL a x) (R.ρL a w) * g x) =
    Star.star (g x) * (Star.star (f (R.ρL a x)) * fderiv ℝ f (R.ρL a x) (R.ρL a w)) * g x +
      Star.star (g x) * fderiv ℝ g x w
  have : Star.star (g x) * Star.star (f (R.ρL a x)) *
      (f (R.ρL a x) * fderiv ℝ g x w + fderiv ℝ f (R.ρL a x) (R.ρL a w) * g x) =
      Star.star (g x) * (Star.star (f (R.ρL a x)) * f (R.ρL a x)) * fderiv ℝ g x w +
      Star.star (g x) * (Star.star (f (R.ρL a x)) * fderiv ℝ f (R.ρL a x) (R.ρL a w)) * g x := by
    noncomm_ring
  rw [this, hunit, mul_one, add_comm]

/-! ### The averaged potential -/

/-- The ambient integrand `G(q, (x,w)) = Ĥ(q̄,x)* ∂_w Ĥ(q̄,·)(x)`; on `S³`, `G(a) = μ(a⁻¹)`. -/
def Gint (q : ℍ[ℝ]) (p : V × V) : ℍ[ℝ] :=
  Star.star (B.Hh (Star.star q) p.1) * fderiv ℝ (fun y => B.Hh (Star.star q) y) p.1 p.2

theorem contDiff_Gint : ContDiff ℝ ∞ fun z : ℍ[ℝ] × (V × V) => B.Gint z.1 z.2 := by
  have hst : ContDiff ℝ ∞ (Star.star : ℍ[ℝ] → ℍ[ℝ]) := (starL' ℝ : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]).contDiff
  have hH : ContDiff ℝ ∞ fun z : ℍ[ℝ] × (V × V) => B.Hh (Star.star z.1) z.2.1 :=
    B.contDiff_Hh.comp ((hst.comp contDiff_fst).prodMk (contDiff_fst.comp contDiff_snd))
  have hD : ContDiff ℝ ∞ fun z : ℍ[ℝ] × (V × V) =>
      fderiv ℝ (fun y => B.Hh (Star.star z.1) y) z.2.1 := by
    refine ContDiff.fderiv (m := ∞) (n := ∞) (f := fun z : ℍ[ℝ] × (V × V) => fun y => B.Hh (Star.star z.1) y)
      ?_ (contDiff_fst.comp contDiff_snd) (by simp)
    exact B.contDiff_Hh.comp ((hst.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd)
  exact (hst.comp hH).mul (hD.clm_apply (contDiff_snd.comp contDiff_snd))

theorem Gint_coe (a : S3) (x w : V) : B.Gint (a : ℍ[ℝ]) (x, w) = B.mu a⁻¹ x w := by
  have hst : Star.star (a : ℍ[ℝ]) = ((a⁻¹ : S3) : ℍ[ℝ]) := by
    rw [coe_inv_S3, inv_eq_star_of_norm_one (mem_sphere_zero_iff_norm.1 a.2)]
  have hf : (fun y => B.Hh (Star.star (a : ℍ[ℝ])) y) = fun y => ((B.hq a⁻¹ y : S3) : ℍ[ℝ]) := by
    funext y; rw [hst, B.Hh_coe]
  simp only [Gint, hf, mu]

theorem integrable_mu_inv (x w : V) : Integrable (fun q : S3 => B.mu q⁻¹ x w) haarS3 := by
  have := integrable_param haarS3 continuous_subtype_val B.contDiff_Gint.continuous (x, w)
  refine this.congr (Eventually.of_forall fun q => ?_)
  exact B.Gint_coe q x w

/-- **The averaged potential** `Ā(x, w) = ∫_{S³} μ(q⁻¹, x, w) dq`. -/
def Abar (p : V × V) : ℍ[ℝ] := ∫ q : S3, B.Gint (q : ℍ[ℝ]) p ∂haarS3

theorem contDiff_Abar : ContDiff ℝ ∞ B.Abar :=
  contDiff_integral_param_infty haarS3 continuous_subtype_val B.contDiff_Gint

theorem Abar_eq (x w : V) : B.Abar (x, w) = ∫ q : S3, B.mu q⁻¹ x w ∂haarS3 :=
  integral_congr_ae (Eventually.of_forall fun q => B.Gint_coe q x w)

theorem Abar_re (p : V × V) : (B.Abar p).re = 0 := by
  obtain ⟨x, w⟩ := p
  rw [Abar_eq, ← reL_apply, ← ContinuousLinearMap.integral_comp_comm _ (B.integrable_mu_inv x w)]
  simp only [reL_apply, mu_re, integral_zero]

/-- **Invariance of the averaged connection** ([GG] Step 1, `L_a^* ω = ω`). -/
theorem Abar_inv (a : S3) (x w : V) :
    B.Abar (x, w) = Star.star ((B.hq a x : S3) : ℍ[ℝ]) * B.Abar (R.ρL a x, R.ρL a w) *
      ((B.hq a x : S3) : ℍ[ℝ]) + B.mu a x w := by
  set h : ℍ[ℝ] := ((B.hq a x : S3) : ℍ[ℝ])
  set L := ContinuousLinearMap.mulLeftRight ℝ ℍ[ℝ] (Star.star h) h
  have hL : ∀ z, L z = Star.star h * z * h := fun z =>
    ContinuousLinearMap.mulLeftRight_apply ℝ ℍ[ℝ] _ _ z
  have hint := B.integrable_mu_inv (R.ρL a x) (R.ρL a w)
  have h1 : Star.star h * B.Abar (R.ρL a x, R.ρL a w) * h + B.mu a x w =
      ∫ q : S3, B.mu (q⁻¹ * a) x w ∂haarS3 := by
    rw [Abar_eq, ← hL, ← L.integral_comp_comm hint, ← integral_haarS3_const (B.mu a x w),
      ← integral_add (L.integrable_comp hint) (integrable_const _)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    show L (B.mu q⁻¹ (R.ρL a x) (R.ρL a w)) + B.mu a x w = B.mu (q⁻¹ * a) x w
    rw [hL, B.mu_mul]
  rw [h1, Abar_eq]
  have := integral_haarS3_mul_left (fun q : S3 => B.mu q⁻¹ x w) a⁻¹
  simp only [mul_inv_rev, inv_inv] at this
  exact this.symm

end StarBundle

end Average

end

end ExoticSpheres8And10
