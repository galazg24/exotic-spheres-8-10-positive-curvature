/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.HLYModel.Frame
import ExoticSpheres8And10.Curvature.Prop31.Blocks
import RiemannianGeometry.RelatedVectorFields

/-! # §4, HLY model: the bracket table of the orthonormal frame ([HLY] `eq:brackets`)

For the frame `X_i = FH i`, `E_a = FV a` of the connection metric on `K × S³`:

* `[X_i, X_j] = Σ_k c^B_{ijk} X_k − r Ω_{ij}^a E_a`, with `c^B` the structure functions of the
  round frame and `Ω_{ij}^a = ⟪F(e_i, e_j) u, u qe_a⟫ = ⟪ū F u, qe_a⟫`;
* `[X_i, E_a] = −ϑ_i E_a`, `ϑ_i = e_i(r)/r`;
* `[E_a, E_b] = r⁻¹ cst_{abc} E_c`.

`cA` is this table, as functions on the ambient `K × ℍ`. `mlieBracket_Fr` is the identity
`[F_α, F_β] = Σ_γ cA_{αβγ} F_γ` on `K × S³`. It comes from the ambient identities
(`S4_HLYAmbient`) through `RiemannianGeometry`'s naturality of brackets for related fields.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `qe a qe b − qe b qe a = Σ_c cst_{abc} qe c`. -/
theorem qe_comm (a c : Fin 3) : qe a * qe c - qe c * qe a = ∑ d, Prop31Algebra.cst a c d • qe d := by
  fin_cases a <;> fin_cases c <;>
    ext <;> simp [qe, Prop31Algebra.cst, Prop31Algebra.lc, Fin.sum_univ_three, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> norm_num

theorem inner_mul_left_unit' (q a c : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    ⟪q * a, q * c⟫ = ⟪a, c⟫ := by
  have hq' : ‖q‖ = 1 := by
    have h := Quaternion.normSq_eq_norm_mul_self q
    rw [hq] at h
    nlinarith [norm_nonneg q]
  exact inner_of_norm_pres (f := fun x => q * x) (fun x y => mul_add _ x y)
    (fun x => by rw [norm_mul, hq', one_mul]) a c

theorem mlieBracket_vs {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V W : Π z : F, TangentSpace 𝓘(ℝ, F) z) (z : F) :
    mlieBracket 𝓘(ℝ, F) V W z = lieBracket ℝ V W z := by
  have h1 : mlieBracketWithin 𝓘(ℝ, F) V W Set.univ = lieBracketWithin ℝ V W Set.univ :=
    mlieBracketWithin_eq_lieBracketWithin
  have h2 : lieBracketWithin ℝ V W Set.univ = lieBracket ℝ V W := lieBracketWithin_univ
  have h3 := congrFun (h1.trans h2) z
  rw [mlieBracketWithin_univ] at h3
  exact h3

section Table

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ K) (A : K → K →L[ℝ] Quaternion ℝ) (r : K → ℝ)

/-- The structure functions of the round frame: `[e_i, e_j] = Σ_k c^B_{ijk} e_k`. -/
def cB (i j k : Fin n) (x : K) : ℝ := ⟪lieBracket ℝ (eb b i) (eb b j) x, b k⟫ / cfac x

/-- `ϑ_i = e_i(r)/r`. -/
def ϑf (i : Fin n) (x : K) : ℝ := fderiv ℝ r x (eb b i x) / r x

/-- The curvature components `Ω_{ij}^a = ⟪F(e_i, e_j) u, u qe_a⟫`. -/
def Ωc (i j : Fin n) (a : Fin 3) (z : K × Quaternion ℝ) : ℝ :=
  ⟪curvA A z.1 (eb b i z.1) (eb b j z.1) * z.2, z.2 * qe a⟫

/-- **The bracket table**, ambiently. -/
def cA : Fin n ⊕ Fin 3 → Fin n ⊕ Fin 3 → Fin n ⊕ Fin 3 → K × Quaternion ℝ → ℝ
  | .inl i, .inl j, .inl k => fun z => cB b i j k z.1
  | .inl i, .inl j, .inr a => fun z => -(r z.1) * Ωc b A i j a z
  | .inl i, .inr a, .inr c => fun z => -(ϑf b r i z.1) * kron a c
  | .inr a, .inl i, .inr c => fun z => ϑf b r i z.1 * kron a c
  | .inr a, .inr c, .inr d => fun z => (r z.1)⁻¹ * Prop31Algebra.cst a c d
  | _, _, _ => fun _ => 0

variable {b A r}

theorem contDiff_eb (i : Fin n) : ContDiff ℝ ∞ (eb b i) :=
  (contDiff_const.add ((contDiff_norm_sq ℝ).div_const 4)).smul contDiff_const

theorem cfac_pos (x : K) : 0 < cfac x := by unfold cfac; positivity

/-- The round frame expansion `w = Σ_k (⟪w, b_k⟫ / cfac) e_k`. -/
theorem expand_eb (x w : K) : w = ∑ k, (⟪w, b k⟫ / cfac x) • eb b k x := by
  have hc := (cfac_pos x).ne'
  conv_lhs => rw [← b.sum_repr' w]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eb, smul_smul, div_mul_cancel₀ _ hc, real_inner_comm]

theorem lieBracket_eb (i j : Fin n) (x : K) :
    lieBracket ℝ (eb b i) (eb b j) x = ∑ k, cB b i j k x • eb b k x :=
  expand_eb x _

theorem hlA_sum {X : K → K} {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Y : ι → K → K)
    (z : K × Quaternion ℝ) (h : X z.1 = ∑ k ∈ s, c k • Y k z.1) :
    hlA A X z = ∑ k ∈ s, c k • hlA A (Y k) z := by
  refine Prod.ext ?_ ?_
  · simp [hlA, h, Prod.fst_sum]
  · simp only [hlA, Prod.snd_sum, Prod.smul_snd, h, map_sum, map_smul, neg_mul,
      Finset.sum_mul, smul_mul_assoc, ← Finset.sum_neg_distrib, smul_neg]

theorem vfA_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (e : ι → Quaternion ℝ)
    (z : K × Quaternion ℝ) : vfA r (∑ d ∈ s, c d • e d) z = ∑ d ∈ s, c d • vfA r (e d) z := by
  refine Prod.ext ?_ ?_
  · simp [vfA, Prod.fst_sum]
  · simp only [vfA, Prod.snd_sum, Prod.smul_snd, Finset.mul_sum, mul_smul_comm, Finset.smul_sum,
      smul_comm (r z.1)⁻¹]

theorem re_fderiv_A (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (x v w : K) :
    (fderiv ℝ A x v w).re = 0 := by
  have hre : (fun y : K => ⟪A y w, (1 : Quaternion ℝ)⟫) = fun _ => 0 := by
    funext y; rw [inner_quat, hAim]
    simp [Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
  have hd : HasFDerivAt (fun y : K => A y w) ((fderiv ℝ A x).flip w) x := by
    have := ((hA.differentiable (by simp)) x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using this
  have h1 : HasFDerivAt (fun y : K => ⟪A y w, (1 : Quaternion ℝ)⟫)
      ((ipL (Quaternion ℝ)).flip 1 |>.comp ((fderiv ℝ A x).flip w)) x :=
    (((ipL (Quaternion ℝ)).flip 1).hasFDerivAt).comp x hd
  rw [hre] at h1
  have h2 := congrArg (fun L : K →L[ℝ] ℝ => L v) (h1.unique (hasFDerivAt_const 0 x))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ipL_apply,
    ContinuousLinearMap.zero_apply] at h2
  rw [inner_quat] at h2
  simpa [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one] using h2

theorem re_curvA (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (x v w : K) :
    (curvA A x v w).re = 0 := by
  have hc : ∀ p q : Quaternion ℝ, (p * q - q * p).re = 0 := fun p q => by
    rw [Quaternion.re_sub, Quaternion.re_mul, Quaternion.re_mul]; ring
  have := hc (A x v) (A x w)
  simp only [curvA, Quaternion.re_add, Quaternion.re_sub, re_fderiv_A hA hAim] at this ⊢
  linarith

/-- **The ambient bracket identities, in the frame.** At `z = (x, u)` with `|u| = 1`. -/
theorem lieBracket_Fa (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (α β : Fin n ⊕ Fin 3) (z : K × Quaternion ℝ)
    (hz : Quaternion.normSq z.2 = 1) :
    lieBracket ℝ (Fa b A r α) (Fa b A r β) z = ∑ γ, cA b A r α β γ z • Fa b A r γ z := by
  have hu : star z.2 * z.2 = 1 := by rw [Quaternion.star_mul_self, hz]; rfl
  have hu' : z.2 * star z.2 = 1 := by rw [Quaternion.self_mul_star, hz]; rfl
  rw [Fintype.sum_sum_type]
  rcases α with i | a <;> rcases β with j | c
  · -- [X_i, X_j]
    show lieBracket ℝ (hlA A (eb b i)) (hlA A (eb b j)) z = _
    rw [lieBracket_hlA hA (contDiff_eb i) (contDiff_eb j)]
    simp only [Fa, Sum.elim_inl, Sum.elim_inr, cA]
    rw [hlA_sum Finset.univ _ _ z (lieBracket_eb i j z.1), sub_eq_add_neg]
    congr 1
    -- the vertical part: `Σ_a Ω^a (u qe_a) = F u`
    set Fq := curvA A z.1 (eb b i z.1) (eb b j z.1)
    have hFim : (star z.2 * Fq * z.2).re = 0 := by
      rw [re_star_mul_mul, re_curvA hA hAim, zero_mul]
    have hΩ : ∀ a, Ωc b A i j a z = ⟪star z.2 * Fq * z.2, qe a⟫ := fun a => by
      have h := inner_mul_left_unit' (star z.2) (Fq * z.2) (z.2 * qe a) (by
        rw [Quaternion.normSq_star, hz])
      rw [Ωc, ← h, ← mul_assoc (star z.2) z.2 (qe a), hu, one_mul, mul_assoc]
    refine Prod.ext ?_ ?_
    · simp [vfA, Prod.fst_sum]
    · simp only [Prod.snd_neg, Prod.snd_sum, Prod.smul_snd, vfA]
      have hsum := sum_inner_qe hFim
      have e1 : ∑ a, (-(r z.1) * Ωc b A i j a z) • ((r z.1)⁻¹ • (z.2 * qe a)) =
          -(z.2 * ∑ a, ⟪star z.2 * Fq * z.2, qe a⟫ • qe a) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hΩ, smul_smul, mul_smul_comm, ← neg_smul]
        congr 1
        field_simp [hr0 z.1]
      rw [e1, hsum, ← mul_assoc, ← mul_assoc, hu', one_mul]
  · -- [X_i, E_c]
    show lieBracket ℝ (hlA A (eb b i)) (vfA r (qe c)) z = _
    rw [lieBracket_hlA_vfA hA (contDiff_eb i) hr hr0]
    simp only [Fa, Sum.elim_inl, Sum.elim_inr, cA, zero_smul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single c (fun d _ hd => by simp [kron, Ne.symm hd]) (by simp)]
    simp [kron, ϑf]
  · -- [E_a, X_j]
    show lieBracket ℝ (vfA r (qe a)) (hlA A (eb b j)) z = _
    rw [lieBracket_swap, lieBracket_hlA_vfA hA (contDiff_eb j) hr hr0]
    simp only [Fa, Sum.elim_inl, Sum.elim_inr, cA, zero_smul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single a (fun d _ hd => by simp [kron, Ne.symm hd]) (by simp)]
    simp [kron, ϑf, neg_smul]
  · -- [E_a, E_c]
    show lieBracket ℝ (vfA r (qe a)) (vfA r (qe c)) z = _
    rw [lieBracket_vfA hr hr0, qe_comm, vfA_sum, Finset.smul_sum]
    simp only [Fa, Sum.elim_inr, cA, zero_smul, Finset.sum_const_zero, zero_add, smul_smul]

theorem contDiff_Fa (hA : ContDiff ℝ ∞ A) (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0)
    (α : Fin n ⊕ Fin 3) : ContDiff ℝ ∞ (Fa b A r α) := by
  rcases α with i | a
  · show ContDiff ℝ ∞ (hlA A (eb b i))
    have h1 : ContDiff ℝ ∞ fun z : K × Quaternion ℝ => eb b i z.1 := (contDiff_eb i).comp contDiff_fst
    exact h1.prodMk ((((hA.comp contDiff_fst).clm_apply h1).neg).mul contDiff_snd)
  · show ContDiff ℝ ∞ (vfA r (qe a))
    exact contDiff_const.prodMk (((hr.inv hr0).comp contDiff_fst).smul
      (contDiff_snd.mul contDiff_const))

theorem injective_mfderiv_emb (p : K × S3) :
    Injective (mfderiv (IN K) 𝓘(ℝ, K × Quaternion ℝ) (emb (K := K)) p) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  rw [mfderiv_emb_apply] at hv
  have h1 : mvfderiv (IN K) fY p v = 0 := congrArg Prod.fst hv
  have h2 : mvfderiv (IN K) fU p v = 0 := congrArg Prod.snd hv
  exact mvfderiv_fU_injective p ((mvfderiv_fY p v).symm.trans h1) h2

/-- **The bracket table on `K × S³`** ([HLY] `eq:brackets`). -/
theorem mlieBracket_Fr (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0) (α β : Fin n ⊕ Fin 3) (p : K × S3) :
    mlieBracket (IN K) (Fr b A r α) (Fr b A r β) p =
      ∑ γ, cA b A r α β γ (emb p) • Fr b A r γ p := by
  apply injective_mfderiv_emb p
  have hn : minSmoothness ℝ 2 ≤ ((2 : ℕ∞) : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact le_rfl
  have hn' : ((2 : ℕ∞) : ℕ∞ω) ≠ ∞ := by simp
  have hf : ContMDiff (IN K) 𝓘(ℝ, K × Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω) (emb (K := K)) :=
    contMDiff_emb.of_le (by exact_mod_cast le_top)
  have hXa : ∀ γ, ContMDiff 𝓘(ℝ, K × Quaternion ℝ) 𝓘(ℝ, K × Quaternion ℝ).tangent
      ((2 : ℕ∞) : ℕ∞ω) (fun z : K × Quaternion ℝ =>
        (⟨z, Fa b A r γ z⟩ : TangentBundle 𝓘(ℝ, K × Quaternion ℝ) (K × Quaternion ℝ))) := fun γ =>
    contMDiff_vectorSpace_iff_contDiff.2
      ((contDiff_Fa hA hr hr0 γ).of_le (WithTop.coe_le_coe.mpr le_top))
  have h := mfderiv_mlieBracket_of_related_forall (I := IN K) (J := 𝓘(ℝ, K × Quaternion ℝ))
    (f := emb) (p := p) (n := (2 : ℕ∞))
    (X := fun z => (Fa b A r α z : TangentSpace 𝓘(ℝ, K × Quaternion ℝ) z))
    (Y := fun z => (Fa b A r β z : TangentSpace 𝓘(ℝ, K × Quaternion ℝ) z))
    (X' := Fr b A r α) (Y' := Fr b A r β) hn hn' hf
    (fun z => mfderiv_emb_Fr hAim α z) (fun z => mfderiv_emb_Fr hAim β z)
    (contMDiff_Fr hA hr hr0 α) (contMDiff_Fr hA hr hr0 β) (hXa α) (hXa β)
  rw [h]
  have hz : Quaternion.normSq (emb p).2 = 1 := normSq_sphere p.2
  refine (mlieBracket_vs (fun z => (Fa b A r α z : TangentSpace 𝓘(ℝ, K × Quaternion ℝ) z))
    (fun z => (Fa b A r β z : TangentSpace 𝓘(ℝ, K × Quaternion ℝ) z)) (emb p)).trans
    ((lieBracket_Fa hA hAim hr hr0 α β (emb p) hz).trans ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_smul, mfderiv_emb_Fr hAim γ p]
  rfl

end Table

end

end ExoticSpheres8And10
