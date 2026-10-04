/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.RayLift

/-! # §3, Step 3: smooth dependence of ray transport on the direction

[GG] Step 3: "Parallel transport depends smoothly on `v`. Hence `s_N` is a smooth section."

* `exists_cutoff`, `contDiff_cutoff_smul`: smooth cutoffs (infrastructure);
* `pieceCoeff`: the chart-`j` transport equation on the `k`-th piece of the ray, rescaled to
  `[0,1]` and globalised by a cutoff, as smooth imaginary coefficients (`LinCoeff`) with
  parameter `v`;
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real Filter Topology

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Cutoff

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- A smooth cutoff equal to `1` on a compact `K` and supported in an open `Ω ⊇ K`. -/
theorem exists_cutoff {K Ω : Set X} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ χ : X → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x ∈ K, χ x = 1) ∧ tsupport χ ⊆ Ω := by
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, X)
    (n := (⊤ : ℕ∞)) hK.isClosed hKL
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, fun x hx => hf1.self_of_nhdsSet x hx, ?_⟩
  refine (closure_minimal (fun x hx => ?_) hL.isClosed).trans hLΩ
  by_contra h; exact hx (hf0 x h)

/-- A cutoff times a function smooth on an open set containing its support is smooth. -/
theorem contDiff_cutoff_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {χ : X → ℝ}
    {f : X → F} {Ω : Set X} (hΩ : IsOpen Ω) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) : ContDiff ℝ ∞ fun x => χ x • f x := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ Ω
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hΩ.mem_nhds hx))
  · have hnot : x ∉ tsupport χ := fun h => hx (hsupp h)
    refine contDiffAt_const (c := (0 : F)) |>.congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hnot] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]

end Cutoff

section Pieces

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

local notation "V" => Vs e

namespace StarBundle

/-- The rescaled chart-`j` coefficient on the piece `[t, t + h]` of the ray `τ ↦ τv`. -/
def pieceF (j : Sn) (t h : ℝ) (p : ℝ × V) : ℍ[ℝ] := h • -(B.A j ((t + h * p.1) • p.2) p.2)

/-- The open set where the rescaled piece stays in the chart. -/
def pieceΩ (j : Sn) (t h : ℝ) : Set (ℝ × V) := {p | (t + h * p.1) • p.2 ∈ B.O j}

theorem isOpen_pieceΩ (j : Sn) (t h : ℝ) : IsOpen (B.pieceΩ j t h) :=
  (B.isOpen_O j).preimage ((continuous_const.add (continuous_const.mul continuous_fst)).smul
    continuous_snd)

theorem contDiffOn_pieceF (j : Sn) (t h : ℝ) :
    ContDiffOn ℝ ∞ (B.pieceF j t h) (B.pieceΩ j t h) := by
  have hmap : ContDiff ℝ ∞ fun p : ℝ × V => (t + h * p.1) • p.2 :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).smul contDiff_snd
  have hA : ContDiffOn ℝ ∞ (fun p : ℝ × V => B.A j ((t + h * p.1) • p.2)) (B.pieceΩ j t h) :=
    (B.contDiffOn_A j).comp hmap.contDiffOn fun _ hp => hp
  have hB : ContDiffOn ℝ ∞ (fun p : ℝ × V => B.A j ((t + h * p.1) • p.2) p.2) (B.pieceΩ j t h) :=
    hA.clm_apply contDiffOn_snd
  exact (contDiffOn_const (c := h)).smul hB.neg

theorem pieceF_re (j : Sn) (t h : ℝ) {p : ℝ × V} (hp : p ∈ B.pieceΩ j t h) :
    (B.pieceF j t h p).re = 0 := by
  rw [pieceF, Quaternion.re_smul, Quaternion.re_neg, B.A_re j hp, neg_zero, smul_zero]

/-- **The piece coefficients** as a `LinCoeff`, equal to `pieceF` on `[0,1] × closedBall v₀ r`. -/
theorem exists_pieceCoeff (j : Sn) (t h : ℝ) (v₀ : V) (r : ℝ)
    (hK : Icc (0 : ℝ) 1 ×ˢ closedBall v₀ r ⊆ B.pieceΩ j t h) :
    ∃ C : LinCoeff V, ∀ σ ∈ Icc (0 : ℝ) 1, ∀ v ∈ closedBall v₀ r,
      C.M (σ, v) = B.pieceF j t h (σ, v) := by
  obtain ⟨χ, hχ, hχ1, hχs⟩ := exists_cutoff (isCompact_Icc.prod (isCompact_closedBall v₀ r))
    (B.isOpen_pieceΩ j t h) hK
  refine ⟨⟨fun p => χ p • B.pieceF j t h p,
    contDiff_cutoff_smul (B.isOpen_pieceΩ j t h) hχ hχs (B.contDiffOn_pieceF j t h),
    fun p => ?_⟩, fun σ hσ v hv => ?_⟩
  · rw [Quaternion.re_smul]
    by_cases hp : p ∈ B.pieceΩ j t h
    · rw [B.pieceF_re j t h hp, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hχs h')), zero_smul]
  · show χ (σ, v) • _ = _
    rw [hχ1 _ ⟨hσ, hv⟩, one_smul]


/-- **Uniform pieces**: near `v₀`, one subdivision of `[0,1]` and one chart per piece work for all
`v ∈ closedBall v₀ r`. -/
theorem exists_pieces (v₀ : V) : ∃ (N : ℕ) (r : ℝ) (j : ℕ → Sn), 0 < r ∧
    ∀ k ≤ N, Icc (0 : ℝ) 1 ×ˢ closedBall v₀ r ⊆ B.pieceΩ (j k) (k / (N + 1)) (1 / (N + 1)) := by
  have hK : IsCompact ((fun τ : ℝ => τ • v₀) '' Icc 0 1) :=
    isCompact_Icc.image (continuous_id.smul continuous_const)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun j => B.isOpen_O j)
    (fun x _ => mem_iUnion.2 ⟨_, B.mem_O_self x⟩)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖v₀‖ / δ)
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hNv : ‖v₀‖ / (N + 1) < δ / 2 := by
    rw [div_lt_iff₀ hN1]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  haveI : Nonempty Sn := ⟨R.phiN 0⟩
  choose! j hj using fun k : ℕ => hleb ((k / (N + 1) : ℝ) • v₀)
  refine ⟨N, δ / 2, fun k => if hk : k ≤ N then j k else R.phiN 0, half_pos hδ, fun k hk => ?_⟩
  rintro ⟨σ, v⟩ ⟨hσ, hv⟩
  have hk' : ((k : ℝ) / (N + 1)) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hN1).2 (by exact_mod_cast Nat.le_succ_of_le hk)⟩
  have hmem := hj k ⟨_, hk', rfl⟩
  show ((k : ℝ) / (N + 1) + 1 / (N + 1) * σ) • v ∈ B.O (if hk : k ≤ N then j k else _)
  rw [dif_pos hk]
  apply hmem
  rw [mem_ball, dist_eq_norm, mem_closedBall, dist_eq_norm] at *
  set τ := (k : ℝ) / (N + 1) + 1 / (N + 1) * σ
  have hσ0 : 0 ≤ 1 / ((N : ℝ) + 1) * σ := mul_nonneg (by positivity) hσ.1
  have hτ0 : 0 ≤ τ := add_nonneg (by positivity) hσ0
  have hτ1 : τ ≤ 1 := by
    have : τ = (k + σ) / (N + 1) := by simp only [τ]; field_simp
    rw [this, div_le_one hN1]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    linarith [hσ.2]
  calc ‖τ • v - ((k : ℝ) / (N + 1)) • v₀‖
      = ‖τ • (v - v₀) + (1 / (N + 1) * σ) • v₀‖ := by congr 1; simp only [τ]; module
    _ ≤ τ * ‖v - v₀‖ + 1 / (N + 1) * σ * ‖v₀‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hτ0, Real.norm_of_nonneg hσ0]
    _ ≤ 1 * (δ / 2) + 1 / (N + 1) * 1 * ‖v₀‖ :=
        add_le_add (mul_le_mul hτ1 hv (norm_nonneg _) zero_le_one) (by gcongr; exact hσ.2)
    _ < δ := by
        have : 1 / (N + 1) * 1 * ‖v₀‖ = ‖v₀‖ / (N + 1) := by ring
        rw [this]; linarith


open Classical in
/-- The rescaled chart solution on a piece `[t, t + h]`, starting from `c` at `t`. -/
def chartSol (C : LinCoeff V) (t h : ℝ) (v : V) (c : S3) (τ : ℝ) : S3 :=
  if hn : ‖C.sol v ((τ - t) / h) * (c : ℍ[ℝ])‖ = 1 then ⟨_, mem_sphere_zero_iff_norm.2 hn⟩ else 1

theorem chartSol_coe (C : LinCoeff V) {t h : ℝ} (hh : 0 < h) (v : V) (c : S3) {τ : ℝ}
    (hτ : τ ∈ Icc t (t + h)) :
    ((chartSol C t h v c τ : S3) : ℍ[ℝ]) = C.sol v ((τ - t) / h) * (c : ℍ[ℝ]) := by
  have hs : (τ - t) / h ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [hτ.1]) hh.le, (div_le_one hh).2 (by linarith [hτ.2])⟩
  have hn : ‖C.sol v ((τ - t) / h) * (c : ℍ[ℝ])‖ = 1 := by
    rw [norm_mul, C.norm_sol v _ hs, one_mul]; exact mem_sphere_zero_iff_norm.1 c.2
  rw [chartSol, dif_pos hn]

theorem chartSol_start (C : LinCoeff V) {t h : ℝ} (hh : 0 < h) (v : V) (c : S3) :
    chartSol C t h v c t = c := by
  apply Subtype.ext
  rw [chartSol_coe C hh v c ⟨le_rfl, by linarith⟩, sub_self, zero_div, C.sol_zero, one_mul]

theorem chartSol_end (C : LinCoeff V) {t h : ℝ} (hh : 0 < h) (v : V) (c : S3) :
    ((chartSol C t h v c (t + h) : S3) : ℍ[ℝ]) = C.T v * (c : ℍ[ℝ]) := by
  rw [chartSol_coe C hh v c ⟨by linarith, le_rfl⟩, add_sub_cancel_left, div_self hh.ne']; rfl

theorem chartSol_deriv (C : LinCoeff V) (j : Sn) {t h : ℝ} (hh : 0 < h) {v₀ : V} {r : ℝ}
    (hC : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ v ∈ closedBall v₀ r, C.M (σ, v) = B.pieceF j t h (σ, v))
    {v : V} (hv : v ∈ closedBall v₀ r) (c : S3) {τ : ℝ} (hτ : τ ∈ Icc t (t + h)) :
    HasDerivWithinAt (fun τ => ((chartSol C t h v c τ : S3) : ℍ[ℝ]))
      (-(B.A j (τ • v) v) * chartSol C t h v c τ) (Icc t (t + h)) τ := by
  set sc : ℝ → ℝ := fun τ => (τ - t) / h
  have hsc : MapsTo sc (Icc t (t + h)) (Icc 0 1) := fun τ hτ =>
    ⟨div_nonneg (by linarith [hτ.1]) hh.le, (div_le_one hh).2 (by linarith [hτ.2])⟩
  have hs : HasDerivWithinAt sc (1 / h) (Icc t (t + h)) τ := by
    have := ((hasDerivAt_id τ).sub_const t).div_const h
    simpa [sc] using this.hasDerivWithinAt
  have h1 := ((C.hasDeriv_sol v (sc τ) (hsc hτ)).scomp τ hs hsc).mul_const (c : ℍ[ℝ])
  refine (h1.congr (fun τ' hτ' => chartSol_coe C hh v c hτ') (chartSol_coe C hh v c hτ)
    ).congr_deriv ?_
  rw [chartSol_coe C hh v c hτ, hC _ (hsc hτ) v hv, pieceF]
  have ht : t + h * sc τ = τ := by simp only [sc]; field_simp; ring
  simp only [ht, smul_mul_assoc, smul_smul, one_div, inv_mul_cancel₀ hh.ne', one_smul, mul_assoc]
  rfl



/-- The fibre coordinates at the subdivision points. -/
def coordRec (j : ℕ → Sn) (tk : ℕ → ℝ) (T3 : ℕ → V → S3) (p₀ : E) : ℕ → V → S3
  | 0 => fun _ => B.fib (j 0) p₀
  | k + 1 => fun v => B.fib (j (k + 1))
      (B.ract (B.σ (j k) (tk (k + 1) • v)) (T3 k v * coordRec j tk T3 p₀ k v))

variable [T2Space E]

/-- **The transported point** `s⁰(v) = Γ_v(1)`, the endpoint of the horizontal lift of the ray
`τ ↦ τv` from `p₀`. -/
def rayEnd (p₀ : E) (hp₀ : B.proj p₀ = R.phiN 0) (v : V) : E :=
  (B.exists_lift v p₀ hp₀).choose 1

theorem rayEnd_eq {p₀ : E} (hp₀ : B.proj p₀ = R.phiN 0) {v : V} {Γ : ℝ → E}
    (hΓ : B.IsLiftOn v Γ 1) (h0 : Γ 0 = p₀) : B.rayEnd p₀ hp₀ v = Γ 1 :=
  B.lift_unique (B.exists_lift v p₀ hp₀).choose_spec.1 hΓ
    (by rw [(B.exists_lift v p₀ hp₀).choose_spec.2, h0]) 1 ⟨zero_le_one, le_rfl⟩

theorem proj_rayEnd (p₀ : E) (hp₀ : B.proj p₀ = R.phiN 0) (v : V) :
    B.proj (B.rayEnd p₀ hp₀ v) = R.phiN v := by
  have := (B.exists_lift v p₀ hp₀).choose_spec.1.1 1 ⟨zero_le_one, le_rfl⟩
  rw [one_smul] at this; exact this

/-- **[GG] Step 3: transport depends smoothly on the direction.** -/
theorem contMDiffAt_rayEnd (p₀ : E) (hp₀ : B.proj p₀ = R.phiN 0) (v₀ : V) :
    ContMDiffAt 𝓘(ℝ, V) (IP m) ∞ (B.rayEnd p₀ hp₀) v₀ := by
  obtain ⟨N, r, j, hr, hpieces⟩ := B.exists_pieces v₀
  set h : ℝ := 1 / (N + 1) with hh_def
  have hh : 0 < h := by positivity
  set tk : ℕ → ℝ := fun k => (k : ℝ) / (N + 1) with htk_def
  have htk : ∀ k : ℕ, tk (k + 1) = tk k + h := fun k => by
    simp only [tk, h]; push_cast; ring
  have htk0 : tk 0 = 0 := by simp [tk]
  have htkN : tk (N + 1) = 1 := by
    simp only [tk]; push_cast; exact div_self (by positivity)
  have hC : ∀ k, ∃ C : LinCoeff V, k ≤ N → ∀ σ ∈ Icc (0 : ℝ) 1, ∀ v ∈ closedBall v₀ r,
      C.M (σ, v) = B.pieceF (j k) (tk k) h (σ, v) := fun k => by
    by_cases hk : k ≤ N
    · obtain ⟨C, hC⟩ := B.exists_pieceCoeff (j k) (tk k) h v₀ r (hpieces k hk)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨⟨fun _ => 0, contDiff_const, fun _ => by simp⟩, fun h' => absurd h' hk⟩
  choose C hCspec using hC
  set T3 : ℕ → V → S3 := fun k v =>
    ⟨(C k).T v, mem_sphere_zero_iff_norm.2 ((C k).norm_sol v 1 ⟨zero_le_one, le_rfl⟩)⟩
  set cc := B.coordRec j tk T3 p₀
  -- the pieces stay in their charts
  have hsub : ∀ k ≤ N, ∀ v ∈ closedBall v₀ r, ∀ τ ∈ Icc (tk k) (tk k + h), τ • v ∈ B.O (j k) := by
    intro k hk v hv τ hτ
    have hσ : (τ - tk k) / h ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hτ.1]) hh.le, (div_le_one hh).2 (by linarith [hτ.2])⟩
    have := hpieces k hk (show ((τ - tk k) / h, v) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall v₀ r from ⟨hσ, hv⟩)
    have heq : tk k + h * ((τ - tk k) / h) = τ := by field_simp; ring
    have this' : (tk k + h * ((τ - tk k) / h)) • v ∈ B.O (j k) := this
    rwa [heq] at this'
  -- the explicit lift
  have hlift : ∀ k ≤ N, ∀ v ∈ closedBall v₀ r, ∃ Γ : ℝ → E, B.IsLiftOn v Γ (tk (k + 1)) ∧
      Γ 0 = p₀ ∧ Γ (tk (k + 1)) = B.ract (B.σ (j k) (tk (k + 1) • v)) (T3 k v * cc k v) := by
    intro k hk v hv
    induction k with
    | zero =>
      have e0 : Icc (tk 0) (tk 0 + h) = Icc 0 (tk 0 + h) := by rw [htk0]
      have hs0 := hsub 0 (Nat.zero_le _) v hv
      rw [e0] at hs0
      refine ⟨fun τ => B.ract (B.σ (j 0) (τ • v)) (chartSol (C 0) (tk 0) h v (cc 0 v) τ),
        ?_, ?_, ?_⟩
      · rw [htk 0]
        refine B.isLiftOn_piece v (j 0) hs0 _ fun τ hτ => ?_
        have := B.chartSol_deriv (C 0) (j 0) hh (hCspec 0 (Nat.zero_le _)) hv (cc 0 v)
          (τ := τ) (e0 ▸ hτ)
        rwa [e0] at this
      · show B.ract (B.σ (j 0) ((0 : ℝ) • v)) (chartSol (C 0) (tk 0) h v (cc 0 v) 0) = p₀
        have hw0 : chartSol (C 0) (tk 0) h v (cc 0 v) 0 = B.fib (j 0) p₀ := by
          have := chartSol_start (C 0) hh v (cc 0 v) (t := tk 0)
          rw [htk0] at this ⊢; exact this
        rw [hw0]
        exact (B.eq_ract_fib (j 0) (Γ := fun _ => p₀) (τ := 0) (by rw [zero_smul]; exact hp₀)
          (hs0 0 ⟨le_rfl, by rw [htk0, zero_add]; exact hh.le⟩)).symm
      · show B.ract _ (chartSol (C 0) (tk 0) h v (cc 0 v) (tk (0 + 1))) = _
        congr 1
        apply Subtype.ext
        rw [htk 0]
        exact chartSol_end (C 0) hh v (cc 0 v)
    | succ k ih =>
      obtain ⟨Γ, hΓ, hΓ0, hΓ1⟩ := ih (by omega)
      have hs := hsub (k + 1) hk v hv
      have hw0 : chartSol (C (k + 1)) (tk (k + 1)) h v (cc (k + 1) v) (tk (k + 1)) = B.fib (j (k + 1)) (Γ (tk (k + 1))) := by
        rw [chartSol_start (C (k + 1)) hh v (cc (k + 1) v), hΓ1]; rfl
      have hlt : tk (k + 1) < tk (k + 1) + h := by linarith
      have hext := IsLiftOn.extend B hΓ (by simp only [tk]; positivity) hlt (j (k + 1)) hs _ hw0
        fun τ hτ => B.chartSol_deriv (C (k + 1)) (j (k + 1)) hh (hCspec (k + 1) hk) hv _ hτ
      refine ⟨_, by rw [htk (k + 1)]; exact hext, ?_, ?_⟩
      · show (if (0 : ℝ) ≤ tk (k + 1) then Γ 0 else _) = p₀
        rw [if_pos (by simp only [tk]; positivity), hΓ0]
      · show (if tk (k + 1 + 1) ≤ tk (k + 1) then Γ _ else _) = _
        rw [if_neg (by rw [htk (k + 1)]; linarith)]
        congr 1
        apply Subtype.ext
        rw [htk (k + 1)]
        exact chartSol_end (C (k + 1)) hh v (cc (k + 1) v)
  -- the endpoint formula
  have hend : ∀ v ∈ closedBall v₀ r, B.rayEnd p₀ hp₀ v =
      B.ract (B.σ (j N) (tk (N + 1) • v)) (T3 N v * cc N v) := by
    intro v hv
    obtain ⟨Γ, hΓ, hΓ0, hΓ1⟩ := hlift N le_rfl v hv
    rw [htkN] at hΓ hΓ1
    rw [B.rayEnd_eq hp₀ hΓ hΓ0, hΓ1, htkN]
  -- smoothness of the coordinates
  have hT3 : ∀ k, ContMDiff 𝓘(ℝ, V) (𝓡 3) ∞ (T3 k) := fun k =>
    contMDiff_sphere_of_coe (C k).contDiff_T.contMDiff
  have hσk : ∀ k ≤ N, ContMDiffOn 𝓘(ℝ, V) (IP m) ∞ (fun v => B.σ (j k) (tk (k + 1) • v))
      (ball v₀ r) := fun k hk =>
    (B.contMDiffOn_σ (j k)).comp (contDiff_const_smul (tk (k + 1))).contMDiff.contMDiffOn
      fun v hv => by
        have := hsub k hk v (ball_subset_closedBall hv) (tk (k + 1)) (by rw [htk k]; exact
          ⟨by linarith, le_rfl⟩)
        exact this
  have hcc : ∀ k ≤ N, ContMDiffOn 𝓘(ℝ, V) (𝓡 3) ∞ (cc k) (ball v₀ r) := by
    intro k hk
    induction k with
    | zero => exact contMDiffOn_const
    | succ k ih =>
      have hmul : ContMDiffOn 𝓘(ℝ, V) (𝓡 3) ∞ (fun v => T3 k v * cc k v) (ball v₀ r) :=
        ContMDiff.comp_contMDiffOn (g := fun p : S3 × S3 => p.1 * p.2)
          (f := fun v => (T3 k v, cc k v)) contMDiff_mulS3
          ((hT3 k).contMDiffOn.prodMk (ih (by omega)))
      have hract : ContMDiffOn 𝓘(ℝ, V) (IP m) ∞
          (fun v => B.ract (B.σ (j k) (tk (k + 1) • v)) (T3 k v * cc k v)) (ball v₀ r) :=
        ContMDiff.comp_contMDiffOn (g := fun x : E × S3 => B.ract x.1 x.2)
          (f := fun v => (B.σ (j k) (tk (k + 1) • v), T3 k v * cc k v)) B.ract_smooth
          ((hσk k (by omega)).prodMk hmul)
      refine (B.fib_smooth (j (k + 1))).comp hract fun v hv => ?_
      show B.proj (B.ract _ _) ∈ B.nbhd (j (k + 1))
      have h1 := hsub k (by omega) v (ball_subset_closedBall hv) (tk (k + 1))
        (by rw [htk k]; exact ⟨by linarith, le_rfl⟩)
      have h2 := hsub (k + 1) hk v (ball_subset_closedBall hv) (tk (k + 1)) ⟨le_rfl, by linarith⟩
      rw [B.proj_ract, B.proj_σ _ h1]
      exact h2
  have hF : ContMDiffOn 𝓘(ℝ, V) (IP m) ∞
      (fun v => B.ract (B.σ (j N) (tk (N + 1) • v)) (T3 N v * cc N v)) (ball v₀ r) := by
    have hmul : ContMDiffOn 𝓘(ℝ, V) (𝓡 3) ∞ (fun v => T3 N v * cc N v) (ball v₀ r) :=
      ContMDiff.comp_contMDiffOn (g := fun p : S3 × S3 => p.1 * p.2)
        (f := fun v => (T3 N v, cc N v)) contMDiff_mulS3
        ((hT3 N).contMDiffOn.prodMk (hcc N le_rfl))
    exact ContMDiff.comp_contMDiffOn (g := fun x : E × S3 => B.ract x.1 x.2)
      (f := fun v => (B.σ (j N) (tk (N + 1) • v), T3 N v * cc N v)) B.ract_smooth
      ((hσk N le_rfl).prodMk hmul)
  refine ((hF.contMDiffAt (ball_mem_nhds v₀ hr)).congr_of_eventuallyEq ?_)
  filter_upwards [ball_mem_nhds v₀ hr] with v hv
  exact hend v (ball_subset_closedBall hv)

theorem contMDiff_rayEnd (p₀ : E) (hp₀ : B.proj p₀ = R.phiN 0) :
    ContMDiff 𝓘(ℝ, V) (IP m) ∞ (B.rayEnd p₀ hp₀) := fun v₀ => B.contMDiffAt_rayEnd p₀ hp₀ v₀

end StarBundle

end Pieces

end

end ExoticSpheres8And10
