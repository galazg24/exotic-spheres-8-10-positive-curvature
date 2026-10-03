/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Global

/-! # The frame formulas for `|Ω|²`, `|DΩ|²` and `Hess φ` are intrinsic

[D] defines `|Ω|² = Σ_{i<j,a}(Ω_{ij}^a)²` and `|DΩ|²` in an orthonormal frame, and uses
`Hess φ` as a tensor. This file proves that these frame expressions do not depend on the
choices made.

* **Hessian.** `hessF_expand_right`: `Hess φ(X, Y) = Σ_i g(Y, e_i) Hess φ(X, e_i)`. So
  `hessF g φ X Y b` depends only on `X b` and `Y b` (`hessF_pointwise`). In `X` this is by
  definition.
* **Curvature, intrinsically.**
  - `tΩ_eq_conn_bracket`: `Ω_{ij}^a(y) = −⟪ω_y([X_i, X_j]), q_a⟫`, where `X_i` is the
    horizontal lift of `e_i`.
  - The horizontal lift does not depend on the trivialisation (`hlift_gauge`), so neither does
    `Ω` (`tΩ_gauge`).
  - `tΩ_frame`: under a change of orthonormal frame `e'_k = Σ_l a_{kl} e_l`,
    `Ω'_{km} = Σ_{l,q} a_{kl} a_{mq} Ω_{lq}`. The horizontal terms of the bracket are killed by
    `ω`.
  - `OmSq_frame`: hence `Σ(Ω_{ij}^a)²` is the same in every orthonormal frame, since `a` is
    orthogonal.
* `DΩ` is treated in the companion section below.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Orthogonal-matrix algebra -/

section Orth

variable {n : ℕ} {a : Fin n → Fin n → ℝ} (hO : ∀ y y', ∑ x, a x y * a x y' = kron y y')

theorem sum3_rot {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℝ) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ y, ∑ z, ∑ x, F x y z := by
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun y _ => Finset.sum_comm

include hO in
theorem orth_collapse (x y : Fin n → ℝ) :
    ∑ l, (∑ p, x p * a l p) * (∑ q, a l q * y q) = ∑ p, x p * y p := by
  calc ∑ l, (∑ p, x p * a l p) * (∑ q, a l q * y q)
        = ∑ l, ∑ p, ∑ q, x p * y q * (a l p * a l q) :=
          Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_mul_sum]
            exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    _ = ∑ p, ∑ q, ∑ l, x p * y q * (a l p * a l q) := sum3_rot _
    _ = ∑ p, ∑ q, x p * y q * kron p q :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
            rw [← hO p q, Finset.mul_sum]
    _ = ∑ p, x p * y p := by
          simp only [kron, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
            if_true]

include hO in
theorem orth_sq (v : Fin n → ℝ) : ∑ k, (∑ m, a k m * v m) ^ 2 = ∑ m, v m ^ 2 := by
  calc ∑ k, (∑ m, a k m * v m) ^ 2 = ∑ l, (∑ p, v p * a l p) * (∑ q, a l q * v q) :=
        Finset.sum_congr rfl fun l _ => by
          rw [sq]; congr 1; exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    _ = ∑ p, v p * v p := orth_collapse hO v v
    _ = _ := Finset.sum_congr rfl fun p _ => (sq _).symm

include hO in
theorem orth_sq2 (Ω : Fin n → Fin n → ℝ) :
    ∑ k, ∑ m, (∑ l, ∑ q, a k l * a m q * Ω l q) ^ 2 = ∑ l, ∑ q, Ω l q ^ 2 := by
  have h1 : ∀ k m, ∑ l, ∑ q, a k l * a m q * Ω l q = ∑ l, a k l * ∑ q, a m q * Ω l q :=
    fun k m => Finset.sum_congr rfl fun l _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [orth_sq hO]
  rw [Finset.sum_comm]
  simp only [orth_sq hO]

include hO in
theorem orth_sq3 (T : Fin n → Fin n → Fin n → ℝ) :
    ∑ k, ∑ i, ∑ j, (∑ m, ∑ l, ∑ q, a k m * a i l * a j q * T m l q) ^ 2 =
      ∑ m, ∑ l, ∑ q, T m l q ^ 2 := by
  have h1 : ∀ k i j, ∑ m, ∑ l, ∑ q, a k m * a i l * a j q * T m l q =
      ∑ m, a k m * ∑ l, ∑ q, a i l * a j q * T m l q := fun k i j =>
    Finset.sum_congr rfl fun m _ => by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
  simp only [h1]
  rw [sum3_rot]
  simp only [orth_sq hO]
  rw [(sum3_rot (fun m i j => (∑ l, ∑ q, a i l * a j q * T m l q) ^ 2)).symm]
  simp only [orth_sq2 hO]

end Orth

/-! ## Brackets of finite combinations, read through a 1-form killing the fields -/

section BracketExpand

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]

theorem mlieBracket_sum_smul_left {ι : Type*} (s : Finset ι) {X : ι → Π x : M, TangentSpace J x}
    {f : ι → M → ℝ} {p : M} (hX : ∀ l, MDiffAt (T% (X l)) p) (hf : ∀ l, MDiffAt (f l) p)
    (W : Π x : M, TangentSpace J x) :
    mlieBracket J (∑ l ∈ s, f l • X l) W p = ∑ l ∈ s, mlieBracket J (f l • X l) W p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mlieBracket_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      mlieBracket_add_left ((hf a).smul_section (hX a)) (mdiffAt_sum_smul s f X hf hX), ih]

theorem mlieBracket_sum_smul_right {ι : Type*} (s : Finset ι) {X : ι → Π x : M, TangentSpace J x}
    {f : ι → M → ℝ} {p : M} (hX : ∀ l, MDiffAt (T% (X l)) p) (hf : ∀ l, MDiffAt (f l) p)
    (V : Π x : M, TangentSpace J x) :
    mlieBracket J V (∑ l ∈ s, f l • X l) p = ∑ l ∈ s, mlieBracket J V (f l • X l) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mlieBracket_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      mlieBracket_add_right ((hf a).smul_section (hX a)) (mdiffAt_sum_smul s f X hf hX), ih]

/-- **Tensoriality of a bracket read through a form that kills the fields.** -/
theorem clm_mlieBracket_expand {ι : Type*} [Fintype ι] {X : ι → Π x : M, TangentSpace J x}
    {f h : ι → M → ℝ} {p : M} (hX : ∀ l, MDiffAt (T% (X l)) p) (hf : ∀ l, MDiffAt (f l) p)
    (hh : ∀ l, MDiffAt (h l) p) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (θ : TangentSpace J p →L[ℝ] F) (hθ : ∀ l, θ (X l p) = 0) :
    θ (mlieBracket J (∑ l, f l • X l) (∑ m, h m • X m) p) =
      ∑ l, ∑ m, (f l p * h m p) • θ (mlieBracket J (X l) (X m) p) := by
  rw [mlieBracket_sum_smul_left _ hX hf, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mlieBracket_sum_smul_right _ hX hh, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mlieBracket_smul_left (hf l) (hX l), mlieBracket_smul_right (hh m) (hX m)]
  simp only [Pi.smul_apply', map_add, map_neg, map_smul, hθ, smul_zero, neg_zero, zero_add,
    smul_smul]

end BracketExpand

/-! ## The Hessian is a tensor -/

section HessTensor

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] {n : ℕ}

theorem mvfderiv_sum_mul {f h : Fin n → B → ℝ} {b : B}
    (hf : ∀ j, MDifferentiableAt I 𝓘(ℝ) (f j) b) (hh : ∀ j, MDifferentiableAt I 𝓘(ℝ) (h j) b)
    (v : TangentSpace I b) :
    mvfderiv I (fun z => ∑ j, f j z * h j z) b v =
      ∑ j, (f j b * mvfderiv I (h j) b v + h j b * mvfderiv I (f j) b v) := by
  classical
  have key : ∀ s : Finset (Fin n),
      MDifferentiableAt I 𝓘(ℝ) (fun z => ∑ j ∈ s, f j z * h j z) b ∧
      mvfderiv I (fun z => ∑ j ∈ s, f j z * h j z) b v =
        ∑ j ∈ s, (f j b * mvfderiv I (h j) b v + h j b * mvfderiv I (f j) b v) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨mdifferentiableAt_const, mvfderiv_const_real 0 b v⟩
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hd : MDifferentiableAt I 𝓘(ℝ) (fun z => f a z * h a z) b := (hf a).mul (hh a)
      refine ⟨hd.add ih.1, ?_⟩
      have hm := (hd.hasMFDerivAt.add ih.1.hasMFDerivAt).mfderiv
      have h2 : mvfderiv I (fun z => f a z * h a z + ∑ j ∈ s, f j z * h j z) b v =
          mvfderiv I (fun z => f a z * h a z) b v +
            mvfderiv I (fun z => ∑ j ∈ s, f j z * h j z) b v := congrArg (fun L => L v) hm
      rw [h2, ih.2, mvfderiv_mul_real (hf a) (hh a)]
  exact (key Finset.univ).2

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B} {φ : B → ℝ}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g) (hUo : IsOpen U)
  (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
  (horthB : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) (hn : finrank ℝ E = n)
  (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)

include hsg hpg hgs hUo he horthB hn hφ in
/-- **The Hessian is tensorial in its second slot**: `Hess φ(X, Y) = Σ_i g(Y, e_i) Hess φ(X, e_i)`. -/
theorem hessF_expand_right {b : B} (hb : b ∈ U) (X Y : Π x : B, TangentSpace I x)
    (hY : MDiffAt (T% Y) b) :
    hessF g φ X Y b = ∑ i, g b (Y b) (e i b) * hessF g φ X (e i) b := by
  have hgm : IsMDiffMetric E g :=
    (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω).isMDiffMetric (by simp)
  have hFd : ∀ i, MDiffAt (T% (e i)) b := fun i => (he i b hb).mdifferentiableAt (by simp)
  have hf : ∀ i, MDifferentiableAt I 𝓘(ℝ) (fun z => g z (Y z) (e i z)) b :=
    fun i => mdiffAt_pairing (hgm b) hY (hFd i)
  have hYe : ∀ z ∈ U, Y z = ∑ i, g z (Y z) (e i z) • e i z :=
    fun z hz => span_base_frame hpg horthB hn hz (Y z)
  have hev : ∀ᶠ z in 𝓝 b, Y z = (∑ i, (fun z => g z (Y z) (e i z)) • e i) z := by
    filter_upwards [hUo.mem_nhds hb] with z hz
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply']
    exact hYe z hz
  have h1fun : (fun z => mvfderiv I φ z (Y z)) =ᶠ[𝓝 b]
      fun z => ∑ i, g z (Y z) (e i z) * mvfderiv I φ z (e i z) := by
    filter_upwards [hUo.mem_nhds hb] with z hz
    conv_lhs => rw [hYe z hz]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hT1 : mvfderiv I (fun z => mvfderiv I φ z (Y z)) b (X b) =
      ∑ i, (g b (Y b) (e i b) * mvfderiv I (fun z => mvfderiv I φ z (e i z)) b (X b) +
        mvfderiv I φ b (e i b) * mvfderiv I (fun z => g z (Y z) (e i z)) b (X b)) := by
    rw [RiemannianGeometry.mvfderiv_congr_of_eventuallyEq h1fun,
      mvfderiv_sum_mul hf (fun i => mdiffAt_dφ_e he hφ hb i)]
  have hT2 : mvfderiv I φ b (leviCivita g Y b (X b)) =
      ∑ i, (g b (Y b) (e i b) * mvfderiv I φ b (leviCivita g (e i) b (X b)) +
        mvfderiv I (fun z => g z (Y z) (e i z)) b (X b) * mvfderiv I φ b (e i b)) := by
    rw [leviCivita_congr_of_eventuallyEq hev,
      leviCivita_sum_smul hsg hpg.isNondegenerate hgm Finset.univ _ e hf hFd,
      ContinuousLinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  unfold hessF
  rw [hT1, hT2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end HessTensor

/-! ## The curvature of a connection, intrinsically -/

section CurvIntrinsic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P]
  [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

namespace S3Connection

/-- **The horizontal lift does not depend on the trivialisation.** -/
theorem hlift_gauge {b₀ b₁ : B} {p : P} (h₀ : Pb.proj p ∈ Pb.nbhd b₀)
    (h₁ : Pb.proj p ∈ Pb.nbhd b₁) (e : Π b : B, TangentSpace I b) :
    C.hlift b₀ e p = C.hlift b₁ e p := by
  have h := C.eq_zero_of_proj_conn (v := C.hlift b₀ e p - C.hlift b₁ e p)
    (by rw [map_sub, C.mfderiv_proj_hlift b₀ h₀, C.mfderiv_proj_hlift b₁ h₁, sub_self])
    (by rw [map_sub, C.conn_hlift, C.conn_hlift, sub_self])
  exact sub_eq_zero.1 h

/-- `ω([X₁, X₂]) = −ū F(e₁, e₂) u` for horizontal lifts. -/
theorem conn_mlieBracket_hlift (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    {e₁ e₂ : Π b : B, TangentSpace I b}
    (he₁ : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e₁) q)
    (he₂ : ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% e₂) q) :
    C.conn p (mlieBracket (I.prod (𝓡 3)) (C.hlift b₀ e₁) (C.hlift b₀ e₂) p) =
      -(star (Pb.fU b₀ p) * C.curvF b₀ e₁ e₂ (Pb.proj p) * Pb.fU b₀ p) := by
  have hd₁ : MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) (C.potE b₀ e₁) (Pb.proj p) :=
    (C.contMDiffAt_potE b₀ hp he₁.self_of_nhds).mdifferentiableAt (by simp)
  have hd₂ : MDifferentiableAt I 𝓘(ℝ, Quaternion ℝ) (C.potE b₀ e₂) (Pb.proj p) :=
    (C.contMDiffAt_potE b₀ hp he₂.self_of_nhds).mdifferentiableAt (by simp)
  have hre : (star (Pb.fU b₀ p) * C.curvF b₀ e₁ e₂ (Pb.proj p) * Pb.fU b₀ p).re = 0 := by
    rw [re_star_mul_mul, C.re_curvF b₀ hd₁ hd₂, zero_mul]
  rw [C.mlieBracket_hlift b₀ hp he₁ he₂, map_sub, map_sum, C.conn_hlift, zero_sub]
  simp only [map_smul, C.vert, ι3_ζq]
  rw [sum_inner_qe hre]

/-- **`Ω_{ij}^a = −⟪ω([X_i, X_j]), q_a⟫`.** -/
theorem tΩ_eq_conn_bracket (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (e : Fin n → Π b : B, TangentSpace I b)
    (he : ∀ i, ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% (e i)) q)
    (i j : Fin n) (a : Fin 3) :
    C.tΩ b₀ e i j a p =
      -⟪C.conn p (mlieBracket (I.prod (𝓡 3)) (C.hlift b₀ (e i)) (C.hlift b₀ (e j)) p), qe a⟫ := by
  rw [C.conn_mlieBracket_hlift b₀ hp (he i) (he j), inner_neg_left, neg_neg]
  rfl

/-- **`Ω` does not depend on the trivialisation.** -/
theorem tΩ_gauge {b₀ b₁ : B} {p : P} (h₀ : Pb.proj p ∈ Pb.nbhd b₀)
    (h₁ : Pb.proj p ∈ Pb.nbhd b₁) (e : Fin n → Π b : B, TangentSpace I b)
    (he : ∀ i, ∀ᶠ q in 𝓝 (Pb.proj p), ContMDiffAt I I.tangent ∞ (T% (e i)) q)
    (i j : Fin n) (a : Fin 3) :
    C.tΩ b₀ e i j a p = C.tΩ b₁ e i j a p := by
  rw [C.tΩ_eq_conn_bracket b₀ h₀ e he, C.tΩ_eq_conn_bracket b₁ h₁ e he]
  have hW : IsOpen (Pb.proj ⁻¹' (Pb.nbhd b₀ ∩ Pb.nbhd b₁)) :=
    ((Pb.nbhd_open b₀).inter (Pb.nbhd_open b₁)).preimage Pb.proj_smooth.continuous
  have hev : ∀ k, C.hlift b₀ (e k) =ᶠ[𝓝 p] C.hlift b₁ (e k) := fun k => by
    filter_upwards [hW.mem_nhds ⟨h₀, h₁⟩] with q hq using C.hlift_gauge hq.1 hq.2 (e k)
  rw [(hev i).mlieBracket_vectorField_eq (hev j)]

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e e' : Fin n → Π b : B, TangentSpace I b} {U U' : Set B}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)
  (hUo : IsOpen U) (hU'o : IsOpen U')
  (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
  (he' : ∀ i, ∀ b ∈ U', ContMDiffAt I I.tangent ∞ (T% (e' i)) b)
  (hor : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j)
  (hor' : ∀ b ∈ U', ∀ i j, g b (e' i b) (e' j b) = kron i j) (hn : finrank ℝ E = n)

include hUo he in
theorem ev_smooth_of_mem {b : B} (hb : b ∈ U) (i : Fin n) :
    ∀ᶠ q in 𝓝 b, ContMDiffAt I I.tangent ∞ (T% (e i)) q := by
  filter_upwards [hUo.mem_nhds hb] with q hq using he i q hq

include hgs hpg hUo hU'o he he' hor hn in
/-- **Change of orthonormal frame**: `Ω'_{km} = Σ_{l,q} a_{kl} a_{mq} Ω_{lq}`, with
`a_{kl} = g(e'_k, e_l)`. -/
theorem tΩ_frame (b₀ : B) {p : P} (hp0 : Pb.proj p ∈ Pb.nbhd b₀) (hpU : Pb.proj p ∈ U)
    (hpU' : Pb.proj p ∈ U') (k m : Fin n) (a : Fin 3) :
    C.tΩ b₀ e' k m a p = ∑ l, ∑ q,
      g (Pb.proj p) (e' k (Pb.proj p)) (e l (Pb.proj p)) *
        g (Pb.proj p) (e' m (Pb.proj p)) (e q (Pb.proj p)) * C.tΩ b₀ e l q a p := by
  set A : Fin n → Fin n → P → ℝ := fun k l x =>
    g (Pb.proj x) (e' k (Pb.proj x)) (e l (Pb.proj x)) with hA
  have hW : IsOpen (Pb.proj ⁻¹' (U ∩ U' ∩ Pb.nbhd b₀)) :=
    ((hUo.inter hU'o).inter (Pb.nbhd_open b₀)).preimage Pb.proj_smooth.continuous
  have hev : ∀ k, C.hlift b₀ (e' k) =ᶠ[𝓝 p]
      (∑ l, A k l • C.hlift b₀ (e l) : Π x : P, TangentSpace (I.prod (𝓡 3)) x) := fun k => by
    filter_upwards [hW.mem_nhds ⟨⟨hpU, hpU'⟩, hp0⟩] with x hx
    simp only [Finset.sum_apply, Pi.smul_apply']
    exact C.hlift_linear b₀ Finset.univ x (e' k) e (fun l => A k l x)
      (span_base_frame hpg hor hn hx.1.1 (e' k (Pb.proj x)))
  have hXd : ∀ l, MDifferentiableAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent
      (T% (C.hlift b₀ (e l))) p := fun l =>
    (C.contMDiffAt_hlift b₀ hp0 (he l _ hpU)).mdifferentiableAt (by simp)
  have hAd : ∀ k l, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (A k l) p := fun k l =>
    ((contMDiffAt_pairing (hgs _) (he' k _ hpU') (he l _ hpU)).comp p
      (Pb.proj_smooth p)).mdifferentiableAt (by simp)
  rw [C.tΩ_eq_conn_bracket b₀ hp0 e' (fun i => ev_smooth_of_mem hU'o he' hpU' i),
    (hev k).mlieBracket_vectorField_eq (hev m),
    clm_mlieBracket_expand hXd (hAd k) (hAd m) (C.conn p) (fun l => C.conn_hlift b₀ p (e l)),
    sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [real_inner_smul_left, C.tΩ_eq_conn_bracket b₀ hp0 e (fun i => ev_smooth_of_mem hUo he hpU i)]
  ring

include hsg hpg hor hor' hn in
/-- The change-of-frame matrix `a_{kl} = g(e'_k, e_l)` is orthogonal. -/
theorem frame_change_orth {b : B} (hbU : b ∈ U) (hbU' : b ∈ U') (y y' : Fin n) :
    ∑ x, g b (e' x b) (e y b) * g b (e' x b) (e y' b) = kron y y' := by
  rw [← hor b hbU y y']
  conv_rhs => rw [span_base_frame hpg hor' hn hbU' (e y b)]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [hsg b (e y b) (e' x b), hsg b (e' x b) (e y' b)]

include hsg hgs hpg hUo hU'o he he' hor hor' hn in
/-- **`Σ(Ω_{ij}^a)²` is the same in every orthonormal frame.** -/
theorem OmSq_frame (b₀ : B) {p : P} (hp0 : Pb.proj p ∈ Pb.nbhd b₀) (hpU : Pb.proj p ∈ U)
    (hpU' : Pb.proj p ∈ U') : Prop31Algebra.OmSq (C.ΩP e' b₀ p) = Prop31Algebra.OmSq (C.ΩP e b₀ p) := by
  have hO := frame_change_orth hsg hpg hor hor' hn hpU hpU'
  simp only [Prop31Algebra.OmSq, ΩP]
  simp only [C.tΩ_frame hpg hgs hUo hU'o he he' hor hn b₀ hp0 hpU hpU']
  conv_lhs => rw [sum3_rot, sum3_rot]
  conv_rhs => rw [sum3_rot, sum3_rot]
  exact Finset.sum_congr rfl fun c _ => orth_sq2 hO (fun l q => C.tΩ b₀ e l q c p)

end S3Connection

end CurvIntrinsic

end

end ExoticSpheres8And10
