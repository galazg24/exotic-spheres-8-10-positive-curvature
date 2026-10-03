/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Package

/-! # The base curvature in an orthonormal frame, and `K_B ≥ κ` from `sec_B ≥ κ`

On an open `U ⊆ B` with a smooth `g`-orthonormal frame `e`:
* `riemannTensorAt_base_frame`: `RiemannianGeometry`'s `Rm_B(e_i, e_j, e_k, e_l)` is the frame formula
  `RBB g e b i j k l` (the input of the HHHH block);
* `riemannTensorAt_base_sum`: `Rm_B(X, Y, Y, X) = KBf (RBB g e b) X Y` for `X = Σ X_i e_i`;
* `KB_ge_of_sec`: if `RiemannianGeometry`'s sectional curvature of `g` is `≥ κ`, then
  `κ · gram(X, Y) ≤ KBf (RBB g e b) X Y`. This is D2's hypothesis `hKB`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff

noncomputable section

section BaseCurv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] {n : ℕ}
  {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g) (hUo : IsOpen U)
  (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
  (horthB : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) (hn : finrank ℝ E = n)

include hpg horthB hn in
theorem span_base_frame {b : B} (hb : b ∈ U) (w : TangentSpace I b) :
    w = ∑ k, g b w (e k b) • e k b :=
  span_of_orthonormal_at hpg (horthB b hb) (by rw [Fintype.card_fin, hn]) w

include hsg hpg hgs hUo he horthB hn in
/-- **`RiemannianGeometry`'s base curvature on the frame is the frame formula `RBB`.** -/
theorem riemannTensorAt_base_frame {b : B} (hb : b ∈ U) (i j k l : Fin n) :
    riemannTensorAt hsg hpg.isNondegenerate (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω) b
      (e i b) (e j b) (e k b) (e l b) = S3Connection.RBB g e b i j k l := by
  have hbr : ∀ α β, ∀ y ∈ U, mlieBracket I (e α) (e β) y =
      ∑ γ, S3Connection.cBb g e α β γ y • e γ y :=
    fun α β y hy => span_base_frame hpg horthB hn hy _
  have hc : ∀ α β γ, ∀ y ∈ U, MDifferentiableAt I 𝓘(ℝ) (S3Connection.cBb g e α β γ) y :=
    fun α β γ y hy => (S3Connection.contMDiffAt_cBb hgs hUo he hy α β γ).mdifferentiableAt
      (by simp)
  have hF : ∀ α, ∀ y ∈ U, ContMDiffAt I I.tangent ((2 : ℕ∞) : ℕ∞ω) (T% (e α)) y :=
    fun α y hy => (he α y hy).of_le S3Connection.two_le_infty''
  have hfr := riemannTensorAt_frame_loc hsg hpg (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω)
    hUo hb hF (fun α β y hy => horthB y hy α β) (fun y hy w => span_base_frame hpg horthB hn hy w)
    hbr hc i j k l
  have hcBd := fun p q s => hc p q s b hb
  have dB : ∀ p q s t : Fin n, mvfderiv I (frameΓ (S3Connection.cBb g e) p q s) b (e t b) =
      dΓB (S3Connection.dcBB g e b) t p q s := by
    intro p q s t
    have hfe : frameΓ (S3Connection.cBb g e) p q s = fun z =>
        (S3Connection.cBb g e p q s z - S3Connection.cBb g e p s q z -
          S3Connection.cBb g e q s p z) * (1 / 2) := by
      funext z; simp only [frameΓ]; ring
    rw [hfe, mvfderiv_mul_const_real (f := fun z => S3Connection.cBb g e p q s z -
      S3Connection.cBb g e p s q z - S3Connection.cBb g e q s p z)
      (((hcBd p q s).sub (hcBd p s q)).sub (hcBd q s p))]
    have hs : ∀ (f g' : B → ℝ), MDifferentiableAt I 𝓘(ℝ) f b → MDifferentiableAt I 𝓘(ℝ) g' b →
        mvfderiv I (fun z => f z - g' z) b (e t b) =
          mvfderiv I f b (e t b) - mvfderiv I g' b (e t b) := fun f g' hf hg => by
      have := (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv
      exact congrArg (fun L => L (e t b)) this
    rw [hs (fun z => S3Connection.cBb g e p q s z - S3Connection.cBb g e p s q z)
      (S3Connection.cBb g e q s p) ((hcBd p q s).sub (hcBd p s q)) (hcBd q s p),
      hs (S3Connection.cBb g e p q s) (S3Connection.cBb g e p s q) (hcBd p q s) (hcBd p s q)]
    simp only [dΓB, S3Connection.dcBB]; ring
  rw [hfr, dB, dB]
  rfl

include hsg hpg hgs hUo he horthB hn in
set_option synthInstance.maxHeartbeats 400000 in
/-- `Rm_B(X, Y, Y, X) = K_B(X, Y)` in the frame. -/
theorem riemannTensorAt_base_sum {b : B} (hb : b ∈ U) (X Y : Fin n → ℝ) :
    riemannTensorAt hsg hpg.isNondegenerate (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω) b
      (∑ i, X i • e i b) (∑ i, Y i • e i b) (∑ i, Y i • e i b) (∑ i, X i • e i b) =
      KBf (S3Connection.RBB g e b) X Y := by
  have hfirst : ∀ c d w : TangentSpace I b,
      riemannTensorAt hsg hpg.isNondegenerate (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω) b
        (∑ i, X i • e i b) c d w =
      ∑ i, X i * riemannTensorAt hsg hpg.isNondegenerate
        (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω) b (e i b) c d w := by
    intro c d w
    rw [riemannTensorAt_pair_symm]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun α _ => by rw [riemannTensorAt_pair_symm]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hfirst, riemannTensorAt_base_frame hsg hpg hgs hUo he horthB hn hb,
    Finset.mul_sum]
  unfold KBf
  rw [sum4_rev]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by ring

include horthB in
theorem pairing_base_sum {b : B} (hb : b ∈ U) (a c : Fin n → ℝ) :
    g b (∑ i, a i • e i b) (∑ j, c j • e j b) = Prop31Algebra.dot a c := by
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, horthB b hb, kron, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Prop31Algebra.dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

include hsg hpg hgs hUo he horthB hn in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`sec_B ≥ κ` gives D2's `K_B ≥ κ · gram`** in the frame. -/
theorem KB_ge_of_sec {κ : ℝ}
    (hsec : ∀ (b : B) (u v : TangentSpace I b), LinearIndependent ℝ ![u, v] →
      κ ≤ sectionalCurvatureAt hsg hpg (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω) b u v)
    {b : B} (hb : b ∈ U) (X Y : Fin n → ℝ) :
    κ * Prop31Algebra.gram X Y ≤ KBf (S3Connection.RBB g e b) X Y := by
  have hgram : gramDet g b (∑ i, X i • e i b) (∑ i, Y i • e i b) = Prop31Algebra.gram X Y := by
    unfold gramDet
    rw [pairing_base_sum horthB hb, pairing_base_sum horthB hb, pairing_base_sum horthB hb]
    rfl
  rw [← riemannTensorAt_base_sum hsg hpg hgs hUo he horthB hn hb X Y]
  by_cases hli : LinearIndependent ℝ ![∑ i, X i • e i b, ∑ i, Y i • e i b]
  · have hpos := gramDet_pos hsg hpg hli
    have h := hsec b _ _ hli
    rw [sectionalCurvatureAt_def, le_div_iff₀ hpos, hgram] at h
    exact h
  · rw [← hgram, gramDet_eq_zero_of_not_linearIndependent hli, mul_zero]
    rw [LinearIndependent.pair_iff] at hli
    simp only [not_forall, not_and_or] at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    rcases eq_or_ne t 0 with rfl | ht
    · have hs : s ≠ 0 := by rcases hne with h' | h'; exacts [h', absurd rfl h']
      have hu : ∑ i, X i • e i b = 0 :=
        (smul_eq_zero.1 (by simpa using hst)).resolve_left hs
      rw [hu, ContinuousLinearMap.map_zero]
    · have h2 : ∑ i, Y i • e i b = -((t⁻¹ * s) • ∑ i, X i • e i b) := by
        have := congrArg (fun w : TangentSpace I b => (t⁻¹ : ℝ) • w) hst
        simp only [smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_zero] at this
        exact eq_neg_of_add_eq_zero_right this
      rw [h2]
      simp only [map_neg, map_smul, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        riemannTensorAt_self_left, smul_zero, neg_zero, le_refl]

end BaseCurv

end

end ExoticSpheres8And10
