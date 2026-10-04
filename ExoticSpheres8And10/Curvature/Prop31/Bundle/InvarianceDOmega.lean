/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Invariance

/-! # `|DΩ|²` is intrinsic

For a change of orthonormal frame `e'_k = Σ_l a_{kl} e_l` (with `a` orthogonal), we prove
`(D_kΩ)'_{ij} = Σ_{m,l,q} a_{km} a_{il} a_{jq} (D_mΩ)_{lq}` (`DΩP_frame`). Hence
`Σ((D_kΩ)_{ij}^a)²` is the same in every orthonormal frame (`DΩsq_frame`). It does not depend
on the trivialisation either (`DΩP_gauge`).

Writing `Ω' = aΩaᵀ` and `Γ'_k = (aĜ + ȧ)aᵀ`:
* the derivative terms `ȧ = e'_k(a)` of `e'_k(Ω')` cancel against those of the Christoffel
  symbols `Γ'`;
* this is the matrix identity `DΩ_matrix`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace Matrix

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Matrix algebra -/

section MatrixAlg

variable {n : ℕ}

/-- The cancellation behind the tensoriality of `DΩ`. -/
theorem DΩ_matrix (a G Ω D da : Matrix (Fin n) (Fin n) ℝ) (hO : aᵀ * a = 1) :
    da * Ω * aᵀ + a * Ω * daᵀ + a * D * aᵀ - ((a * G + da) * aᵀ) * (a * Ω * aᵀ) -
      (a * Ω * aᵀ) * ((a * G + da) * aᵀ)ᵀ = a * (D - G * Ω - Ω * Gᵀ) * aᵀ := by
  have h2 : ∀ X : Matrix (Fin n) (Fin n) ℝ, aᵀ * (a * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hO, Matrix.one_mul]
  simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2]
  abel

theorem mat_entry3 (X Y Z : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (X * Y * Zᵀ) i j = ∑ l, ∑ q, X i l * Z j q * Y l q := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => by ring

end MatrixAlg

/-! ## Derivatives of finite sums of products -/

section SumDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mvfderiv_fsum {ι : Type*} (s : Finset ι) {f : ι → M → ℝ} {x : M}
    (hf : ∀ i, MDifferentiableAt J 𝓘(ℝ) (f i) x) (v : TangentSpace J x) :
    MDifferentiableAt J 𝓘(ℝ) (fun z => ∑ i ∈ s, f i z) x ∧
      mvfderiv J (fun z => ∑ i ∈ s, f i z) x v = ∑ i ∈ s, mvfderiv J (f i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨mdifferentiableAt_const, mvfderiv_const_real 0 x v⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine ⟨(hf a).add ih.1, ?_⟩
    have hm := ((hf a).hasMFDerivAt.add ih.1.hasMFDerivAt).mfderiv
    have h2 : mvfderiv J (fun z => f a z + ∑ i ∈ s, f i z) x v =
        mvfderiv J (f a) x v + mvfderiv J (fun z => ∑ i ∈ s, f i z) x v :=
      congrArg (fun L => L v) hm
    rw [h2, ih.2]

theorem mvfderiv_sum2_mul3 {n : ℕ} {f h : Fin n → M → ℝ} {w : Fin n → Fin n → M → ℝ} {x : M}
    (hf : ∀ l, MDifferentiableAt J 𝓘(ℝ) (f l) x) (hh : ∀ l, MDifferentiableAt J 𝓘(ℝ) (h l) x)
    (hw : ∀ l q, MDifferentiableAt J 𝓘(ℝ) (w l q) x) (v : TangentSpace J x) :
    mvfderiv J (fun z => ∑ l, ∑ q, f l z * h q z * w l q z) x v =
      ∑ l, ∑ q, (mvfderiv J (f l) x v * h q x * w l q x +
        f l x * mvfderiv J (h q) x v * w l q x + f l x * h q x * mvfderiv J (w l q) x v) := by
  have hprod : ∀ l q, MDifferentiableAt J 𝓘(ℝ) (fun z => f l z * h q z * w l q z) x :=
    fun l q => ((hf l).mul (hh q)).mul (hw l q)
  have hin : ∀ l, MDifferentiableAt J 𝓘(ℝ) (fun z => ∑ q, f l z * h q z * w l q z) x :=
    fun l => (mvfderiv_fsum Finset.univ (hprod l) v).1
  rw [(mvfderiv_fsum Finset.univ (f := fun l z => ∑ q, f l z * h q z * w l q z) hin v).2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(mvfderiv_fsum Finset.univ (f := fun q z => f l z * h q z * w l q z) (hprod l) v).2]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mvfderiv_mul_real (f := fun z => f l z * h q z) ((hf l).mul (hh q)) (hw l q),
    mvfderiv_mul_real (hf l) (hh q)]
  ring

end SumDeriv

/-! ## `DΩ` under a change of frame and of trivialisation -/

section DOm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P]
  [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

namespace S3Connection

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e e' : Fin n → Π b : B, TangentSpace I b} {U U' : Set B}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)
  (hUo : IsOpen U) (hU'o : IsOpen U')
  (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
  (he' : ∀ i, ∀ b ∈ U', ContMDiffAt I I.tangent ∞ (T% (e' i)) b)
  (hor : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j)
  (hor' : ∀ b ∈ U', ∀ i j, g b (e' i b) (e' j b) = kron i j) (hn : finrank ℝ E = n)

theorem DΩP_r (b₀ : B) (r r' : B → ℝ) (y : P) :
    C.DΩP g e r b₀ y = C.DΩP g e r' b₀ y := rfl

include hUo he in
/-- **`DΩ` does not depend on the trivialisation.** -/
theorem DΩP_gauge {b₀ b₁ : B} {y : P} (h₀ : Pb.proj y ∈ Pb.nbhd b₀)
    (h₁ : Pb.proj y ∈ Pb.nbhd b₁) (hyU : Pb.proj y ∈ U) (r : B → ℝ) :
    C.DΩP g e r b₀ y = C.DΩP g e r b₁ y := by
  have hW : IsOpen (Pb.proj ⁻¹' (Pb.nbhd b₀ ∩ Pb.nbhd b₁ ∩ U)) :=
    (((Pb.nbhd_open b₀).inter (Pb.nbhd_open b₁)).inter hUo).preimage Pb.proj_smooth.continuous
  have hev : ∀ i j c, C.tΩ b₀ e i j c =ᶠ[𝓝 y] C.tΩ b₁ e i j c := fun i j c => by
    filter_upwards [hW.mem_nhds ⟨⟨h₀, h₁⟩, hyU⟩] with q hq
    exact C.tΩ_gauge hq.1.1 hq.1.2 e (fun k => ev_smooth_of_mem hUo he hq.2 k) i j c
  funext k i j c
  simp only [DΩP, DΩf, dΩP]
  rw [RiemannianGeometry.mvfderiv_congr_of_eventuallyEq (hev i j c)]
  have hX : C.Fr b₀ e r (.inl k) y = C.Fr b₁ e r (.inl k) y := C.hlift_gauge h₀ h₁ (e k)
  have hval : ∀ l q, C.tΩ b₀ e l q c y = C.tΩ b₁ e l q c y := fun l q => (hev l q c).eq_of_nhds
  rw [hX]
  simp only [hval]

include hsg hpg hgs hUo hU'o he he' hor hor' hn in
/-- The Christoffel symbols of `e'`, in terms of those of `e`. -/
theorem ΓB_frame {b : B} (hbU : b ∈ U) (hbU' : b ∈ U') (k i l : Fin n) :
    ΓBf (cBb g e') k i l b =
      ∑ x, (g b (e' i b) (e x b) * ∑ m', g b (e' k b) (e m' b) *
          ∑ p, ΓBf (cBb g e) m' x p b * g b (e' l b) (e p b) +
        mvfderiv I (fun z => g z (e' i z) (e x z)) b (e' k b) * g b (e' l b) (e x b)) := by
  have hgm : IsMDiffMetric E g :=
    (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω).isMDiffMetric (by simp)
  have hFd : ∀ α, ∀ z ∈ U, MDiffAt (T% (e α)) z :=
    fun α z hz => (he α z hz).mdifferentiableAt (by simp)
  have hFd' : ∀ α, ∀ z ∈ U', MDiffAt (T% (e' α)) z :=
    fun α z hz => (he' α z hz).mdifferentiableAt (by simp)
  have hbr : ∀ α β, ∀ z ∈ U, mlieBracket I (e α) (e β) z = ∑ γ, cBb g e α β γ z • e γ z :=
    fun α β z hz => span_base_frame hpg hor hn hz _
  have hbr' : ∀ α β, ∀ z ∈ U', mlieBracket I (e' α) (e' β) z = ∑ γ, cBb g e' α β γ z • e' γ z :=
    fun α β z hz => span_base_frame hpg hor' hn hz _
  -- `Γ'_{kil} = g(∇_{e'_k} e'_i, e'_l)`
  have h1 : ΓBf (cBb g e') k i l b = g b (leviCivita g (e' i) b (e' k b)) (e' l b) :=
    (g_leviCivita_frame_loc hsg hpg.isNondegenerate hgm hU'o hFd' (fun α β z hz => hor' z hz α β)
      hbr' k i l hbU').symm
  -- `e'_i = Σ_x a_{ix} e_x` near `b`
  have hf : ∀ x, MDifferentiableAt I 𝓘(ℝ) (fun z => g z (e' i z) (e x z)) b :=
    fun x => mdiffAt_pairing (hgm b) (hFd' i b hbU') (hFd x b hbU)
  have hev : ∀ᶠ z in 𝓝 b, e' i z = (∑ x, (fun z => g z (e' i z) (e x z)) • e x) z := by
    filter_upwards [(hUo.inter hU'o).mem_nhds ⟨hbU, hbU'⟩] with z hz
    simp only [Finset.sum_apply, Pi.smul_apply']
    exact span_base_frame hpg hor hn hz.1 (e' i z)
  have hLC : ∀ x, leviCivita g (e x) b (e' k b) =
      ∑ m', g b (e' k b) (e m' b) • ∑ x', frameΓ (cBb g e) m' x x' b • e x' b := by
    intro x
    conv_lhs => rw [span_base_frame hpg hor hn hbU (e' k b)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [map_smul, leviCivita_frame_loc hsg hpg.isNondegenerate hgm hUo hFd
      (fun α β z hz => hor z hz α β) (fun z hz w => span_base_frame hpg hor hn hz w) hbr m' x hbU]
  rw [h1, leviCivita_congr_of_eventuallyEq hev,
    leviCivita_sum_smul hsg hpg.isNondegenerate hgm Finset.univ _ e hf (fun x => hFd x b hbU),
    ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, hLC x]
  have hsym : ∀ x', g b (e x' b) (e' l b) = g b (e' l b) (e x' b) := fun x' => hsg b _ _
  simp only [map_add, map_smul, map_sum, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul, hsym, frameΓ,
    ΓBf]


include hsg hpg hgs hUo hU'o he he' hor hor' hn in
/-- **`DΩ` is a tensor**: under `e'_k = Σ_l a_{kl} e_l`,
`(D_kΩ)'_{ij} = Σ_{m,l,q} a_{km} a_{il} a_{jq} (D_mΩ)_{lq}`. -/
theorem DΩP_frame (b₀ : B) {y : P} (hy0 : Pb.proj y ∈ Pb.nbhd b₀) (hyU : Pb.proj y ∈ U)
    (hyU' : Pb.proj y ∈ U') (r : B → ℝ) (k i j : Fin n) (c : Fin 3) :
    C.DΩP g e' r b₀ y k i j c = ∑ m, ∑ l, ∑ q,
      g (Pb.proj y) (e' k (Pb.proj y)) (e m (Pb.proj y)) *
        g (Pb.proj y) (e' i (Pb.proj y)) (e l (Pb.proj y)) *
          g (Pb.proj y) (e' j (Pb.proj y)) (e q (Pb.proj y)) * C.DΩP g e r b₀ y m l q c := by
  set b := Pb.proj y with hbdef
  set am : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun x z => g b (e' x b) (e z b) with ham
  set Ωm : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun l q => C.tΩ b₀ e l q c y with hΩm
  set Gm : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun x p => ∑ m', am k m' * ΓBf (cBb g e) m' x p b with hGm
  set dam : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun x z => mvfderiv I (fun w => g w (e' x w) (e z w)) b (e' k b) with hdam
  set Dm : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun l q => ∑ m, am k m * C.dΩP e r b₀ y m l q c with hDm
  have hO' := frame_change_orth hsg hpg hor hor' hn hyU hyU'
  have hO : amᵀ * am = 1 := by
    ext x z
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, ham, Matrix.of_apply]
    exact hO' x z
  -- (F1) `Ω' = aΩaᵀ`
  have hF1 : ∀ x z, C.tΩ b₀ e' x z c y = (am * Ωm * amᵀ) x z := fun x z => by
    rw [mat_entry3, C.tΩ_frame hpg hgs hUo hU'o he he' hor hn b₀ hy0 hyU hyU']
    rfl
  -- (F2) `Γ' = (aĜ + ȧ)aᵀ`
  have hF2 : ∀ x z, ΓBf (cBb g e') k x z b = ((am * Gm + dam) * amᵀ) x z := fun x z => by
    rw [ΓB_frame hsg hpg hgs hUo hU'o he he' hor hor' hn hyU hyU']
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, ham, hGm, hdam,
      Matrix.of_apply, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    conv_rhs => rw [sum3_rot]
    exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun p _ => by ring
  -- (F3) `e'_k(Ω') = ȧΩaᵀ + aΩȧᵀ + aDaᵀ`
  have hW : IsOpen (Pb.proj ⁻¹' (U ∩ U' ∩ Pb.nbhd b₀)) :=
    ((hUo.inter hU'o).inter (Pb.nbhd_open b₀)).preimage Pb.proj_smooth.continuous
  have hevΩ : ∀ x z, C.tΩ b₀ e' x z c =ᶠ[𝓝 y] fun p => ∑ l, ∑ q,
      g (Pb.proj p) (e' x (Pb.proj p)) (e l (Pb.proj p)) *
        g (Pb.proj p) (e' z (Pb.proj p)) (e q (Pb.proj p)) * C.tΩ b₀ e l q c p := fun x z => by
    filter_upwards [hW.mem_nhds ⟨⟨hyU, hyU'⟩, hy0⟩] with p hp
    exact C.tΩ_frame hpg hgs hUo hU'o he he' hor hn b₀ hp.2 hp.1.1 hp.1.2 x z c
  have hAd : ∀ x l, MDifferentiableAt I 𝓘(ℝ) (fun w => g w (e' x w) (e l w)) b := fun x l =>
    (contMDiffAt_pairing (hgs _) (he' x _ hyU') (he l _ hyU)).mdifferentiableAt (by simp)
  have hAdP : ∀ x l, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ)
      (fun p => g (Pb.proj p) (e' x (Pb.proj p)) (e l (Pb.proj p))) y := fun x l =>
    (hAd x l).comp y (Pb.mdiffAt_proj y)
  have hΩd : ∀ l q, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (C.tΩ b₀ e l q c) y := fun l q =>
    (C.contMDiffAt_tΩ b₀ (hUo.inter (Pb.nbhd_open b₀)) (fun b' hb' => hb'.2)
      (fun i b' hb' => he i b' hb'.1) ⟨hyU, hy0⟩ l q c).mdifferentiableAt (by simp)
  have hXk : C.Fr b₀ e' r (.inl k) y = ∑ m, am k m • C.hlift b₀ (e m) y :=
    C.hlift_linear b₀ Finset.univ y (e' k) e (fun m => am k m)
      (span_base_frame hpg hor hn hyU (e' k b))
  have hdA : ∀ x l, mvfderiv (I.prod (𝓡 3))
      (fun p => g (Pb.proj p) (e' x (Pb.proj p)) (e l (Pb.proj p))) y
        (C.Fr b₀ e' r (.inl k) y) = dam x l := fun x l => by
    rw [show (fun p => g (Pb.proj p) (e' x (Pb.proj p)) (e l (Pb.proj p))) =
      (fun w => g w (e' x w) (e l w)) ∘ Pb.proj from rfl, mvfderiv_comp_proj (hAd x l)]
    show mvfderiv I _ b (mfderiv (I.prod (𝓡 3)) I Pb.proj y (C.hlift b₀ (e' k) y)) = _
    rw [C.mfderiv_proj_hlift b₀ hy0]
    rfl
  have hdΩ : ∀ l q, mvfderiv (I.prod (𝓡 3)) (C.tΩ b₀ e l q c) y (C.Fr b₀ e' r (.inl k) y) =
      Dm l q := fun l q => by
    rw [hXk, map_sum]
    simp only [map_smul, smul_eq_mul, hDm, Matrix.of_apply]
    rfl
  have hF3 : ∀ x z, C.dΩP e' r b₀ y k x z c =
      (dam * Ωm * amᵀ + am * Ωm * damᵀ + am * Dm * amᵀ) x z := fun x z => by
    show mvfderiv (I.prod (𝓡 3)) (C.tΩ b₀ e' x z c) y (C.Fr b₀ e' r (.inl k) y) = _
    rw [RiemannianGeometry.mvfderiv_congr_of_eventuallyEq (hevΩ x z),
      mvfderiv_sum2_mul3 (f := fun l p => g (Pb.proj p) (e' x (Pb.proj p)) (e l (Pb.proj p)))
        (h := fun q p => g (Pb.proj p) (e' z (Pb.proj p)) (e q (Pb.proj p)))
        (w := fun l q p => C.tΩ b₀ e l q c p) (hAdP x) (hAdP z) hΩd]
    simp only [hdA, hdΩ, Matrix.add_apply, mat_entry3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [ham, hΩm, Matrix.of_apply]
    ring
  have hΩ' : (Matrix.of fun x z => C.tΩ b₀ e' x z c y) = am * Ωm * amᵀ := by
    ext x z; exact hF1 x z
  have hΓ' : (Matrix.of fun x z => ΓBf (cBb g e') k x z b) = (am * Gm + dam) * amᵀ := by
    ext x z; exact hF2 x z
  have hd' : (Matrix.of fun x z => C.dΩP e' r b₀ y k x z c) =
      dam * Ωm * amᵀ + am * Ωm * damᵀ + am * Dm * amᵀ := by
    ext x z; exact hF3 x z
  have hDΩ' : C.DΩP g e' r b₀ y k i j c =
      ((Matrix.of fun x z => C.dΩP e' r b₀ y k x z c) -
        (Matrix.of fun x z => ΓBf (cBb g e') k x z b) *
          (Matrix.of fun x z => C.tΩ b₀ e' x z c y) -
        (Matrix.of fun x z => C.tΩ b₀ e' x z c y) *
          (Matrix.of fun x z => ΓBf (cBb g e') k x z b)ᵀ) i j := by
    simp only [DΩP, DΩf, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply]
    congr 1
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hΓeq : ∀ m l p, ΓBf (tcB (Pb := Pb) g e) m l p y = ΓBf (cBb g e) m l p b :=
    fun _ _ _ => rfl
  have hinner : ∀ l q, (Dm - Gm * Ωm - Ωm * Gmᵀ) l q =
      ∑ m, am k m * C.DΩP g e r b₀ y m l q c := fun l q => by
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hDm,
      hGm, hΩm, DΩP, DΩf, hΓeq, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => by ring
  rw [hDΩ', hd', hΓ', hΩ', DΩ_matrix am Gm Ωm Dm dam hO, mat_entry3]
  simp only [hinner, Finset.mul_sum]
  conv_rhs => rw [sum3_rot]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun m _ => by simp only [ham, Matrix.of_apply]; ring

include hsg hpg hgs hUo hU'o he he' hor hor' hn in
/-- **`Σ((D_kΩ)_{ij}^a)²` is the same in every orthonormal frame.** -/
theorem DΩsq_frame (b₀ : B) {y : P} (hy0 : Pb.proj y ∈ Pb.nbhd b₀) (hyU : Pb.proj y ∈ U)
    (hyU' : Pb.proj y ∈ U') (r : B → ℝ) :
    ∑ k, ∑ i, ∑ j, ∑ c, C.DΩP g e' r b₀ y k i j c ^ 2 =
      ∑ k, ∑ i, ∑ j, ∑ c, C.DΩP g e r b₀ y k i j c ^ 2 := by
  have hO' := frame_change_orth hsg hpg hor hor' hn hyU hyU'
  have h4 : ∀ F : Fin n → Fin n → Fin n → Fin 3 → ℝ,
      ∑ k, ∑ i, ∑ j, ∑ c, F k i j c = ∑ c, ∑ k, ∑ i, ∑ j, F k i j c := fun F => by
    calc ∑ k, ∑ i, ∑ j, ∑ c, F k i j c = ∑ k, ∑ i, ∑ c, ∑ j, F k i j c :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ c, ∑ i, ∑ j, F k i j c := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [C.DΩP_frame hsg hpg hgs hUo hU'o he he' hor hor' hn b₀ hy0 hyU hyU' r]
  rw [h4, h4]
  exact Finset.sum_congr rfl fun c _ =>
    orth_sq3 hO' (fun m l q => C.DΩP g e r b₀ y m l q c)


end S3Connection

end DOm

end

end ExoticSpheres8And10
