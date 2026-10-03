/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Hessian
import ExoticSpheres8And10.Curvature.Prop31.Bundle.BaseFrame

/-! # [HLY] Prop. 3.1 globally: positive curvature of `G_ε` on a principal `S³`-bundle

`hly_prop31_global`. Let:
* `B` be a compact manifold with corners (boundary allowed) with a smooth Riemannian metric `g`
  of sectional curvature `≥ κ > 0`, in `RiemannianGeometry`'s sense;
* `P → B` be a principal `S³`-bundle with connection `ω`, whose curvature and covariant
  derivative satisfy `|Ω| ≤ M₀` and `|DΩ| ≤ M₁` (in every local gauge and orthonormal frame);
* `φ` be smooth with `−Hess φ ≥ Λ g` and `Λ ≥ 64 M₀² + 1024 κ⁻¹ (M₁+1)²`.

Then there is `ε₀ > 0` such that for `0 < ε < ε₀` the metric `G_ε = π^*g + ε e^{εφ} Q(ω,ω)` has
positive sectional curvature at every point of `P`, boundary included.

The proof is pointwise (`prop31_at_P`) at each `y`. It uses a smooth orthonormal frame near
`π y` (`exists_orthonormal_frame_near`), with uniform constants from compactness:
* `sup φ`;
* `sup |dφ|²`, which is continuous because the frame expression does not depend on the frame
  (`gradSq_frame_indep`).
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Grad

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] {n : ℕ}

/-- `|dφ|²` in the frame `e`. -/
def gradSq (φ : B → ℝ) (e : Fin n → Π b : B, TangentSpace I b) (x : B) : ℝ :=
  ∑ k, mvfderiv I φ x (e k x) ^ 2

/-- **`|dφ|²` does not depend on the orthonormal frame.** -/
theorem gradSq_frame_indep {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
    (hsg : IsSymm g) (hpg : IsPosDef g) (hn : finrank ℝ E = n) (φ : B → ℝ) {x : B}
    {e e' : Fin n → Π b : B, TangentSpace I b}
    (ho : ∀ i j, g x (e i x) (e j x) = kron i j) (ho' : ∀ i j, g x (e' i x) (e' j x) = kron i j) :
    gradSq φ e' x = gradSq φ e x := by
  have hcard : Fintype.card (Fin n) = finrank ℝ E := by rw [Fintype.card_fin, hn]
  have hsp : ∀ w : TangentSpace I x, w = ∑ l, g x w (e l x) • e l x :=
    fun w => span_of_orthonormal_at hpg ho hcard w
  have hsp' : ∀ w : TangentSpace I x, w = ∑ k, g x w (e' k x) • e' k x :=
    fun w => span_of_orthonormal_at hpg ho' hcard w
  have h1 : ∀ k, mvfderiv I φ x (e' k x) =
      ∑ l, g x (e' k x) (e l x) * mvfderiv I φ x (e l x) := by
    intro k
    conv_lhs => rw [hsp (e' k x)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have h2 : ∀ l m, ∑ k, g x (e' k x) (e l x) * g x (e' k x) (e m x) = kron l m := by
    intro l m
    rw [← ho l m]
    conv_rhs => rw [hsp' (e m x)]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => by
      rw [hsg x (e' k x) (e l x), hsg x (e' k x) (e m x)]; ring
  unfold gradSq
  simp only [h1]
  have h3 : ∑ k, (∑ l, g x (e' k x) (e l x) * mvfderiv I φ x (e l x)) ^ 2 =
      ∑ l, ∑ m, mvfderiv I φ x (e l x) * mvfderiv I φ x (e m x) *
        ∑ k, g x (e' k x) (e l x) * g x (e' k x) (e m x) := by
    have hsq : ∀ k, (∑ l, g x (e' k x) (e l x) * mvfderiv I φ x (e l x)) ^ 2 =
        ∑ l, ∑ m, g x (e' k x) (e l x) * mvfderiv I φ x (e l x) *
          (g x (e' k x) (e m x) * mvfderiv I φ x (e m x)) :=
      fun k => by rw [sq, Finset.sum_mul_sum]
    simp only [hsq, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h3]
  simp only [h2, kron, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sq]

end Grad

/-- **The ε-budget**: every condition of D2 on `ε` holds for all small `ε`. -/
theorem eps_budget {κ Λ M0 D0 Φ0 : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hM0 : 0 ≤ M0) (hD0 : 0 ≤ D0)
    (hΦ0 : 0 ≤ Φ0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ε * Φ0 ≤ Real.log 2 ∧ 2 * ε * M0 ≤ 1 ∧ ε * D0 * M0 ≤ 1 ∧ 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ κ ∧
        ε * D0 ^ 2 ≤ Λ / 4 ∧ 2 * ε ^ 3 * D0 ^ 2 ≤ 1 ∧ 32 * 4 ^ 2 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 ≤ Λ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have d1 : (0 : ℝ) < Φ0 + 1 := by linarith
  have d2 : (0 : ℝ) < 2 * M0 + 1 := by linarith
  have d3 : (0 : ℝ) < D0 * M0 + 1 := by nlinarith [mul_nonneg hD0 hM0]
  have d4 : (0 : ℝ) < 64 * 4 ^ 2 * M0 ^ 2 + 1 := by positivity
  have d5 : (0 : ℝ) < 4 * (D0 ^ 2 + 1) := by positivity
  have d6 : (0 : ℝ) < 2 * (D0 ^ 2 + 1) := by positivity
  have d7 : (0 : ℝ) < 32 * 4 ^ 2 * (D0 ^ 2 * M0 ^ 2 + 1) := by positivity
  refine ⟨min 1 (min (Real.log 2 / (Φ0 + 1)) (min (1 / (2 * M0 + 1)) (min (1 / (D0 * M0 + 1))
    (min (κ / (64 * 4 ^ 2 * M0 ^ 2 + 1)) (min (Λ / (4 * (D0 ^ 2 + 1)))
      (min (1 / (2 * (D0 ^ 2 + 1))) (Λ / (32 * 4 ^ 2 * (D0 ^ 2 * M0 ^ 2 + 1))))))))), ?_, ?_⟩
  · exact lt_min one_pos (lt_min (div_pos hl2 d1) (lt_min (div_pos one_pos d2)
      (lt_min (div_pos one_pos d3) (lt_min (div_pos hκ d4) (lt_min (div_pos hΛ d5)
        (lt_min (div_pos one_pos d6) (div_pos hΛ d7)))))))
  · intro ε hε hlt
    simp only [lt_min_iff] at hlt
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hlt
    rw [lt_div_iff₀ d1] at h2
    rw [lt_div_iff₀ d2] at h3
    rw [lt_div_iff₀ d3] at h4
    rw [lt_div_iff₀ d4] at h5
    rw [lt_div_iff₀ d5] at h6
    rw [lt_div_iff₀ d6] at h7
    rw [lt_div_iff₀ d7] at h8
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    have hε3 : ε ^ 3 ≤ ε := by nlinarith
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
    · nlinarith [mul_nonneg (sub_nonneg.2 hε3) (sq_nonneg D0)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hε3) (mul_nonneg (sq_nonneg D0) (sq_nonneg M0))]

section Global

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P]
  [IsManifold (I.prod (𝓡 3)) ∞ P] {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **[HLY] Prop. 3.1, global form** (see the module docstring). -/
theorem hly_prop31_global [CompactSpace B]
    {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
    (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)
    (hn : finrank ℝ E = n) {κ : ℝ} (hκ : 0 < κ)
    (hsec : ∀ (b : B) (u v : TangentSpace I b), LinearIndependent ℝ ![u, v] →
      κ ≤ sectionalCurvatureAt hsg hpg (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω) b u v)
    {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {φ : B → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {M0 M1 Λ : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hΩ : ∀ (b₀ : B) (U : Set B) (e : Fin n → Π b : B, TangentSpace I b), IsOpen U →
      U ⊆ Pb.nbhd b₀ → (∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) →
      (∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) →
      ∀ y : P, Pb.proj y ∈ U → Prop31Algebra.OmSq (C.ΩP e b₀ y) ≤ 2 * M0 ^ 2)
    (hDΩ : ∀ (b₀ : B) (U : Set B) (e : Fin n → Π b : B, TangentSpace I b), IsOpen U →
      U ⊆ Pb.nbhd b₀ → (∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) →
      (∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) →
      ∀ y : P, Pb.proj y ∈ U →
        ∑ i, ∑ j, ∑ k, ∑ a, C.DΩP g e (fun _ => 1) b₀ y i j k a ^ 2 ≤ 2 * M1 ^ 2)
    (hHess : ∀ (b : B) (X : Π x : B, TangentSpace I x), ContMDiffAt I I.tangent ∞ (T% X) b →
      Λ * g b (X b) (X b) ≤ -hessF g φ X X b)
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 ≤ Λ) :
    ∃ ε₀ > 0, ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      ∀ (y : P) (u v : TangentSpace (I.prod (𝓡 3)) y), LinearIndependent ℝ ![u, v] →
        0 < sectionalCurvatureAt (C.isSymm_connMetric hsg φ ε) (C.isPosDef_connMetric hpg φ hε)
          (IsContMDiffMetricSection.of_le' (C.isContMDiffMetricSection_connMetric hgs hφ ε)
            two_le_infty_ω) y u v := by
  classical
  choose Uf hUo hbU ef hes hor using fun b => exists_orthonormal_frame_near hsg hpg hgs hn b
  -- `sup |dφ|²`
  have hDc : Continuous fun x => gradSq φ (ef x) x := by
    refine continuous_iff_continuousAt.2 fun x0 => ?_
    have heq : (fun x => gradSq φ (ef x) x) =ᶠ[𝓝 x0] gradSq φ (ef x0) := by
      filter_upwards [(hUo x0).mem_nhds (hbU x0)] with x hx
      exact gradSq_frame_indep hsg hpg hn φ (hor x0 x hx) (hor x x (hbU x))
    have hk : ∀ k, ContMDiffAt I 𝓘(ℝ) ∞ (fun z => mvfderiv I φ z (ef x0 k z)) x0 := fun k =>
      S3Connection.contMDiffAt_mvfderiv_field (Eventually.of_forall fun b' => hφ b')
        (hes x0 k x0 (hbU x0))
    have hc : ContinuousAt (gradSq φ (ef x0)) x0 :=
      tendsto_finset_sum _ fun k _ => (hk k).continuousAt.pow 2
    exact hc.congr heq.symm
  obtain ⟨CD, hCD⟩ := isCompact_univ.exists_bound_of_continuousOn hDc.continuousOn
  obtain ⟨CΦ, hCΦ⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuous.continuousOn
  set D0 := √(max CD 0) with hD0def
  set Φ0 := max CΦ 0 with hΦ0def
  have hD0 : 0 ≤ D0 := Real.sqrt_nonneg _
  have hΦ0 : 0 ≤ Φ0 := le_max_right _ _
  have hDle : ∀ x, gradSq φ (ef x) x ≤ D0 ^ 2 := fun x => by
    rw [hD0def, Real.sq_sqrt (le_max_right _ _)]
    have := hCD x (mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hφle : ∀ x, φ x ≤ Φ0 := fun x => by
    have := hCΦ x (mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hΛpos : 0 < Λ := by
    have h1 : 0 < 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 :=
      mul_pos (div_pos (by norm_num) hκ) (pow_pos (by linarith) 2)
    nlinarith [sq_nonneg M0]
  obtain ⟨ε₀, hε₀, hbud⟩ := eps_budget hκ hΛpos hM0 hD0 hΦ0
  refine ⟨ε₀, hε₀, fun ε hε hεlt y u v huv => ?_⟩
  obtain ⟨hlog, hA2, hA3, hB2, hC1, hC2, hC3⟩ := hbud ε hε hεlt
  -- the frame near `b = π y`, in the gauge at `b`
  set b := Pb.proj y with hbdef
  set U' := Uf b ∩ Pb.nbhd b
  have hU'o : IsOpen U' := (hUo b).inter (Pb.nbhd_open b)
  have hU'n : U' ⊆ Pb.nbhd b := inter_subset_right
  have hyU : Pb.proj y ∈ U' := ⟨hbU b, Pb.mem_nbhd b⟩
  set e := ef b with hedef
  have he' : ∀ i, ∀ x ∈ U', ContMDiffAt I I.tangent ∞ (T% (e i)) x :=
    fun i x hx => hes b i x hx.1
  have hor' : ∀ x ∈ U', ∀ i j, g x (e i x) (e j x) = kron i j := fun x hx => hor b x hx.1
  have hsp' : ∀ x ∈ U', ∀ w : TangentSpace I x, w = ∑ k, g x w (e k x) • e k x :=
    fun x hx w => span_base_frame hpg hor' hn hx w
  have hr := contMDiff_rOf hφ ε
  have hrpos : ∀ b', 0 < rOf ε φ b' := fun b' => rOf_pos hε b'
  have hr2 : ∀ b', rOf ε φ b' ^ 2 = ε * Real.exp (ε * φ b') := fun b' => rOf_sq hε b'
  -- D2's data
  have hOm := hΩ b U' e hU'o hU'n he' hor' y hyU
  have hDOm : ∑ i, ∑ j, ∑ k, ∑ a, C.DΩP g e (rOf ε φ) b y i j k a ^ 2 ≤ 2 * M1 ^ 2 :=
    hDΩ b U' e hU'o hU'n he' hor' y hyU
  have hν := fun x => NB_quad_ge hsg hpg hgs hU'o he' hor' hn hφ hε hHess hyU (hDle b) x
  have hKB := KB_ge_of_sec hsg hpg hgs hU'o he' hor' hn hsec hyU
  have hr2' : rOf ε φ b ^ 2 ≤ 2 * ε := by
    rw [hr2]
    have h1 : ε * φ b ≤ Real.log 2 := (mul_le_mul_of_nonneg_left (hφle b) hε.le).trans hlog
    have h2 : Real.exp (ε * φ b) ≤ 2 := by
      calc Real.exp (ε * φ b) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 h1
        _ = 2 := Real.exp_log (by norm_num)
    nlinarith
  have htD : √(∑ k, S3Connection.ϑb (rOf ε φ) e k b ^ 2) ≤ ε * D0 / 2 := by
    simp only [ϑb_rOf hφ hε]
    have h1 : ∑ k, (ε / 2 * mvfderiv I φ b (e k b)) ^ 2 = (ε / 2) ^ 2 * gradSq φ e b := by
      unfold gradSq; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1]
    calc √((ε / 2) ^ 2 * gradSq φ e b) ≤ √((ε / 2) ^ 2 * D0 ^ 2) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hDle b) (sq_nonneg _))
      _ = ε * D0 / 2 := by
          rw [← mul_pow, Real.sqrt_sq (mul_nonneg (by linarith) hD0)]; ring
  have hfr := C.prop31_at_P hsg hpg hgs hφ hε hr hr2 b hU'o hU'n he' hor' hsp' hn hrpos hyU
    (ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4) κ M0 M1 Λ D0 hM0 hM1 hκ hOm hDOm hν hKB hΛ hr2' htD le_rfl
    hA2 hA3 hB2 hC1 hC2 hC3
  -- frame coefficients on `P`
  have horthP : ∀ α β, C.connMetric g φ ε y (C.Fr b e (rOf ε φ) α y)
      (C.Fr b e (rOf ε φ) β y) = kron α β :=
    fun α β => C.connMetric_Fr (fun b' => (hrpos b').ne') hr2 b hU'n hor' hyU α β
  have hcard : Fintype.card (Fin n ⊕ Fin 3) = Module.finrank ℝ (E × E3) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Module.finrank_prod,
      finrank_euclideanSpace_fin, hn]
  have hspP : ∀ w : TangentSpace (I.prod (𝓡 3)) y,
      w = ∑ α, C.connMetric g φ ε y w (C.Fr b e (rOf ε φ) α y) • C.Fr b e (rOf ε φ) α y :=
    fun w => span_of_orthonormal_at (C.isPosDef_connMetric hpg φ hε) horthP hcard w
  let cf : TangentSpace (I.prod (𝓡 3)) y → Prop31Algebra.Tv n := fun w =>
    (fun i => C.connMetric g φ ε y w (C.Fr b e (rOf ε φ) (.inl i) y),
      fun a => C.connMetric g φ ε y w (C.Fr b e (rOf ε φ) (.inr a) y))
  have hvec : ∀ w, C.vecFP e (rOf ε φ) b y (cf w) = w := by
    intro w
    unfold S3Connection.vecFP
    conv_rhs => rw [hspP w]
    refine Finset.sum_congr rfl fun α _ => ?_
    rcases α with i | a <;> rfl
  have hGv : ∀ v w : Prop31Algebra.Tv n, C.connMetric g φ ε y (C.vecFP e (rOf ε φ) b y v)
      (C.vecFP e (rOf ε φ) b y w) = Prop31Algebra.dot v.1 w.1 + Prop31Algebra.dot v.2 w.2 := by
    intro v w
    unfold S3Connection.vecFP
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, horthP, kron, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [Fintype.sum_sum_type]
    simp only [coef, Sum.elim_inl, Sum.elim_inr, Prop31Algebra.dot]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hgd := gramDet_pos (C.isSymm_connMetric hsg φ ε) (C.isPosDef_connMetric hpg φ hε) huv
  have hgram : gramDet (C.connMetric g φ ε) y u v =
      Prop31Algebra.totalGram (cf u).1 (cf v).1 (cf u).2 (cf v).2 := by
    conv_lhs => rw [← hvec u, ← hvec v]
    unfold gramDet
    rw [hGv, hGv, hGv]
    rfl
  have hRm := hfr (cf u).1 (cf v).1 (cf u).2 (cf v).2
  simp only [Prod.mk.eta, hvec] at hRm
  rw [sectionalCurvatureAt_def]
  refine div_pos ?_ hgd
  have hc : 0 < min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε)) :=
    lt_min (lt_min (by linarith) (by positivity)) (by positivity)
  rw [hgram] at hgd
  exact lt_of_lt_of_le (mul_pos hc hgd) hRm

end Global

end

end ExoticSpheres8And10
