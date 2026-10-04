/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.StarBundles.Connection

/-! # §3, Step 3: horizontal lifts of rays across trivialising charts

For `v ∈ V` the ray `τ ↦ τv` (a reparametrised meridian under `φ`) is lifted to `E` by solving,
in each chart `j`, the horizontal-lift equation `u_j' = −A_j(τv)(v) u_j` for the fibre
coordinate `u_j = fib_j(Γ)`.

* `fib_ract_σ`: change of fibre coordinate between charts, `u_i = g_{ij} u_j`;
* `chart_switch`: a curve that is horizontal in chart `j` is horizontal in chart `i` (the gauge
  law makes the local equations compatible);
* `IsLiftOn v Γ b`: `Γ` is a horizontal lift of the ray on `[0, b]`.
-/

namespace ExoticSpheres8And10

open Set Metric Function Module Real Filter Topology

open scoped Manifold ContDiff RealInnerProductSpace

open Quaternion

noncomputable section

local notation "S3" => sphere (0 : ℍ[ℝ]) 1

section Ray

variable {m : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ W = (m + 1) + 1)] [FiniteDimensional ℝ W] {e : W} {R : StarRep e} {E : Type}
  [TopologicalSpace E]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin 3))) E]
  [IsManifold (IP m) ∞ E] (B : StarBundle (m := m) R E)

local notation "Sn" => sphere (0 : W) 1

local notation "V" => Vs e

namespace StarBundle

theorem fib_ract_σ (i j : Sn) {v : V} (hi : v ∈ B.O i) (hj : v ∈ B.O j) (u : S3) :
    B.fib i (B.ract (B.σ j v) u) = B.divE (B.σ i v) (B.σ j v) * u := by
  conv_lhs => rw [B.σ_eq i j hi hj, B.ract_mul]
  exact B.fib_sec i _ hi _

/-- **Chart switch.** If near `τ₀` the curve is `Γ = σ_j(τv) · w` with `w` horizontal in chart `j`
at `τ₀`, then its chart-`i` coordinate is horizontal in chart `i` at `τ₀`. -/
theorem chart_switch (i j : Sn) (v : V) (τ₀ : ℝ) (S : Set ℝ) (w : ℝ → S3) (Γ : ℝ → E)
    (hi : τ₀ • v ∈ B.O i) (hj : τ₀ • v ∈ B.O j)
    (hΓ : ∀ᶠ τ in 𝓝[S] τ₀, Γ τ = B.ract (B.σ j (τ • v)) (w τ))
    (hΓ₀ : Γ τ₀ = B.ract (B.σ j (τ₀ • v)) (w τ₀))
    (hw : HasDerivWithinAt (fun τ => ((w τ : S3) : ℍ[ℝ])) (-(B.A j (τ₀ • v) v) * w τ₀) S τ₀) :
    HasDerivWithinAt (fun τ => ((B.fib i (Γ τ) : S3) : ℍ[ℝ]))
      (-(B.A i (τ₀ • v) v) * B.fib i (Γ τ₀)) S τ₀ := by
  have hO : IsOpen {τ : ℝ | τ • v ∈ B.O i ∩ B.O j} :=
    ((B.isOpen_O i).inter (B.isOpen_O j)).preimage (continuous_id.smul continuous_const)
  have hev : ∀ᶠ τ in 𝓝[S] τ₀, ((B.fib i (Γ τ) : S3) : ℍ[ℝ]) = B.gV i j (τ • v) * w τ := by
    filter_upwards [hΓ, mem_nhdsWithin_of_mem_nhds (hO.mem_nhds ⟨hi, hj⟩)] with τ h1 h2
    rw [h1, B.fib_ract_σ i j h2.1 h2.2]; rfl
  have hval : ((B.fib i (Γ τ₀) : S3) : ℍ[ℝ]) = B.gV i j (τ₀ • v) * w τ₀ := by
    rw [hΓ₀, B.fib_ract_σ i j hi hj]; rfl
  have hray : HasDerivWithinAt (fun τ : ℝ => τ • v) v S τ₀ := by
    simpa using ((hasDerivAt_id τ₀).smul_const v).hasDerivWithinAt
  have hg := (B.hasFDerivAt_gV i j ⟨hi, hj⟩).comp_hasDerivWithinAt τ₀ hray
  have hprod := hg.mul hw
  refine (hprod.congr_of_eventuallyEq hev hval).congr_deriv ?_
  -- the gauge law: `Dg = g A_j − A_i g`
  have hc := B.A_compat i j hi hj v
  have hgs : B.gV i j (τ₀ • v) * Star.star (B.gV i j (τ₀ • v)) = 1 :=
    mul_star_of_norm_one (B.norm_gV _ _ _)
  have hD : fderiv ℝ (B.gV i j) (τ₀ • v) v =
      B.gV i j (τ₀ • v) * B.A j (τ₀ • v) v - B.A i (τ₀ • v) v * B.gV i j (τ₀ • v) := by
    rw [hc]
    have : B.gV i j (τ₀ • v) * (Star.star (B.gV i j (τ₀ • v)) * B.A i (τ₀ • v) v *
        B.gV i j (τ₀ • v) + Star.star (B.gV i j (τ₀ • v)) * fderiv ℝ (B.gV i j) (τ₀ • v) v) =
        (B.gV i j (τ₀ • v) * Star.star (B.gV i j (τ₀ • v))) * B.A i (τ₀ • v) v *
          B.gV i j (τ₀ • v) +
        (B.gV i j (τ₀ • v) * Star.star (B.gV i j (τ₀ • v))) * fderiv ℝ (B.gV i j) (τ₀ • v) v := by
      noncomm_ring
    rw [this, hgs, one_mul, one_mul]; abel
  rw [Function.comp_apply, hD, hval]
  noncomm_ring

/-- **Horizontal lift of the ray `τ ↦ τv` on `[0, b]`.** -/
def IsLiftOn (v : V) (Γ : ℝ → E) (b : ℝ) : Prop :=
  (∀ τ ∈ Icc (0 : ℝ) b, B.proj (Γ τ) = R.phiN (τ • v)) ∧
  ∀ i : Sn, ∀ τ ∈ Icc (0 : ℝ) b, τ • v ∈ B.O i →
    HasDerivWithinAt (fun τ => ((B.fib i (Γ τ) : S3) : ℍ[ℝ]))
      (-(B.A i (τ • v) v) * B.fib i (Γ τ)) (Icc 0 b) τ

/-- Near a point of the ray, a curve over the ray is `σ_j · fib_j`. -/
theorem eq_ract_fib (j : Sn) {v : V} {τ : ℝ} {Γ : ℝ → E} (hp : B.proj (Γ τ) = R.phiN (τ • v))
    (hj : τ • v ∈ B.O j) : Γ τ = B.ract (B.σ j (τ • v)) (B.fib j (Γ τ)) := by
  have h := B.sec_fib j (Γ τ) (by rw [hp]; exact hj)
  rw [hp] at h
  exact h.symm


theorem continuousOn_Aray (j : Sn) (v : V) :
    ContinuousOn (fun τ : ℝ => B.A j (τ • v) v) {τ | τ • v ∈ B.O j} :=
  ((B.contDiffOn_A j).continuousOn.comp (continuous_id.smul continuous_const).continuousOn
    fun _ h => h).clm_apply continuousOn_const

theorem A_re_ray (j : Sn) {v : V} {τ : ℝ} (h : τ • v ∈ B.O j) :
    (-(B.A j (τ • v) v)).re = 0 := by
  rw [Quaternion.re_neg, B.A_re j h, neg_zero]

theorem im_of_re {q : ℍ[ℝ]} (h : q.re = 0) : q.im = q := by
  ext <;> simp [h]

open Classical in
/-- **Local solutions in one chart** on a subinterval `[a, b]` of the ray. -/
theorem exists_piece (j : Sn) (v : V) {a b : ℝ} (hab : a < b)
    (hsub : ∀ τ ∈ Icc a b, τ • v ∈ B.O j) (w₀ : S3) :
    ∃ w : ℝ → S3, w a = w₀ ∧ ∀ τ ∈ Icc a b, HasDerivWithinAt (fun τ => ((w τ : S3) : ℍ[ℝ]))
      (-(B.A j (τ • v) v) * w τ) (Icc a b) τ := by
  have hba : 0 < b - a := sub_pos.2 hab
  set M : ℝ → ℍ[ℝ] := fun σ => ((b - a) • -(B.A j ((a + (b - a) * σ) • v) v)).im with hM
  have hmaps : MapsTo (fun σ : ℝ => a + (b - a) * σ) (Icc 0 1) (Icc a b) := fun σ hσ =>
    ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
  have hc : ContinuousOn (fun σ : ℝ => B.A j ((a + (b - a) * σ) • v) v) (Icc 0 1) :=
    (B.continuousOn_Aray j v).comp (by fun_prop : Continuous fun σ : ℝ => a + (b - a) * σ).continuousOn
      fun σ hσ => hsub _ (hmaps hσ)
  have hMc : ContinuousOn M (Icc 0 1) :=
    Quaternion.continuous_im.comp_continuousOn ((continuousOn_const (c := b - a)).smul hc.neg)
  obtain ⟨u, hu0, hun, hu⟩ := exists_transport M hMc (fun σ => by simp [M]) 0
    ⟨le_rfl, zero_le_one⟩
  have hMeq : ∀ σ ∈ Icc (0 : ℝ) 1, M σ = (b - a) • -(B.A j ((a + (b - a) * σ) • v) v) :=
    fun σ hσ => im_of_re (by rw [Quaternion.re_smul, B.A_re_ray j (hsub _ (hmaps hσ)), smul_zero])
  set sc : ℝ → ℝ := fun τ => (τ - a) / (b - a)
  have hsc : MapsTo sc (Icc a b) (Icc 0 1) := fun τ hτ =>
    ⟨div_nonneg (by linarith [hτ.1]) hba.le, (div_le_one hba).2 (by linarith [hτ.2])⟩
  have hsc_inv : ∀ τ, a + (b - a) * sc τ = τ := fun τ => by
    simp only [sc]; field_simp; ring
  set U : ℝ → ℍ[ℝ] := fun τ => u (sc τ) * (w₀ : ℍ[ℝ])
  have hUn : ∀ τ ∈ Icc a b, ‖U τ‖ = 1 := fun τ hτ => by
    simp only [U]; rw [norm_mul, hun _ (hsc hτ), one_mul]; exact mem_sphere_zero_iff_norm.1 w₀.2
  have hUd : ∀ τ ∈ Icc a b, HasDerivWithinAt U (-(B.A j (τ • v) v) * U τ) (Icc a b) τ := by
    intro τ hτ
    have hs : HasDerivWithinAt sc (1 / (b - a)) (Icc a b) τ := by
      have := ((hasDerivAt_id τ).sub_const a).div_const (b - a)
      simpa [sc] using this.hasDerivWithinAt
    have h1 := ((hu (sc τ) (hsc hτ)).scomp τ hs hsc).mul_const (w₀ : ℍ[ℝ])
    refine h1.congr_deriv ?_
    rw [hMeq _ (hsc hτ), hsc_inv τ]
    simp only [smul_mul_assoc, smul_smul, one_div, inv_mul_cancel₀ hba.ne', one_smul, U, mul_assoc]
  refine ⟨fun τ => if h : ‖U τ‖ = 1 then ⟨U τ, mem_sphere_zero_iff_norm.2 h⟩ else 1, ?_, ?_⟩
  · have h0 : U a = w₀ := by simp [U, sc, hu0]
    have hn : ‖U a‖ = 1 := by rw [h0]; exact mem_sphere_zero_iff_norm.1 w₀.2
    apply Subtype.ext
    show ((if h : ‖U a‖ = 1 then (⟨U a, mem_sphere_zero_iff_norm.2 h⟩ : S3) else 1 : S3) : ℍ[ℝ]) =
      (w₀ : ℍ[ℝ])
    rw [dif_pos hn]; exact h0
  · intro τ hτ
    have hcoe : ∀ τ' ∈ Icc a b, (((if h : ‖U τ'‖ = 1 then ⟨U τ', mem_sphere_zero_iff_norm.2 h⟩
        else 1 : S3)) : ℍ[ℝ]) = U τ' := fun τ' hτ' => by rw [dif_pos (hUn τ' hτ')]
    refine ((hUd τ hτ).congr hcoe (hcoe τ hτ)).congr_deriv ?_
    rw [hcoe τ hτ]


/-- A lift defined by a single chart solution. -/
theorem isLiftOn_piece (v : V) {b : ℝ} (j : Sn) (hsub : ∀ τ ∈ Icc 0 b, τ • v ∈ B.O j)
    (w : ℝ → S3) (hw : ∀ τ ∈ Icc 0 b, HasDerivWithinAt (fun τ => ((w τ : S3) : ℍ[ℝ]))
      (-(B.A j (τ • v) v) * w τ) (Icc 0 b) τ) :
    B.IsLiftOn v (fun τ => B.ract (B.σ j (τ • v)) (w τ)) b :=
  ⟨fun τ hτ => by rw [B.proj_ract, B.proj_σ j (hsub τ hτ)],
   fun i τ hτ hi => B.chart_switch i j v τ (Icc 0 b) w _ hi (hsub τ hτ)
     (Eventually.of_forall fun _ => rfl) rfl (hw τ hτ)⟩

theorem nhdsWithin_Icc_left {a b τ : ℝ} (h : τ < a) : Icc 0 a ∈ 𝓝[Icc 0 b] τ :=
  mem_nhdsWithin.2 ⟨Iio a, isOpen_Iio, h, fun x hx => ⟨hx.2.1, hx.1.le⟩⟩

theorem nhdsWithin_Icc_right {a b τ : ℝ} (h : a < τ) : Icc a b ∈ 𝓝[Icc 0 b] τ :=
  mem_nhdsWithin.2 ⟨Ioi a, isOpen_Ioi, h, fun x hx => ⟨hx.1.le, hx.2.2⟩⟩

/-- **Extension of a lift by one chart solution.** -/
theorem IsLiftOn.extend {v : V} {Γ : ℝ → E} {a b : ℝ} (hΓ : B.IsLiftOn v Γ a) (ha : 0 ≤ a)
    (hab : a < b) (j : Sn) (hsub : ∀ τ ∈ Icc a b, τ • v ∈ B.O j) (w : ℝ → S3)
    (hw0 : w a = B.fib j (Γ a))
    (hw : ∀ τ ∈ Icc a b, HasDerivWithinAt (fun τ => ((w τ : S3) : ℍ[ℝ]))
      (-(B.A j (τ • v) v) * w τ) (Icc a b) τ) :
    B.IsLiftOn v (fun τ => if τ ≤ a then Γ τ else B.ract (B.σ j (τ • v)) (w τ)) b := by
  set Γ' : ℝ → E := fun τ => if τ ≤ a then Γ τ else B.ract (B.σ j (τ • v)) (w τ)
  have hΓa : Γ a = B.ract (B.σ j (a • v)) (w a) := by
    rw [hw0]; exact B.eq_ract_fib j (hΓ.1 a ⟨ha, le_rfl⟩) (hsub a ⟨le_rfl, hab.le⟩)
  have hle : ∀ τ, τ ≤ a → Γ' τ = Γ τ := fun τ h => if_pos h
  have hform : ∀ τ ∈ Icc a b, Γ' τ = B.ract (B.σ j (τ • v)) (w τ) := by
    intro τ hτ
    by_cases h : τ ≤ a
    · have : τ = a := le_antisymm h hτ.1
      subst this; rw [hle _ le_rfl, hΓa]
    · exact if_neg h
  refine ⟨fun τ hτ => ?_, fun i τ hτ hi => ?_⟩
  · by_cases h : τ ≤ a
    · rw [hle τ h]; exact hΓ.1 τ ⟨hτ.1, h⟩
    · rw [hform τ ⟨(not_le.1 h).le, hτ.2⟩, B.proj_ract,
        B.proj_σ j (hsub τ ⟨(not_le.1 h).le, hτ.2⟩)]
  have hleft : ∀ τ ∈ Icc (0 : ℝ) a, τ • v ∈ B.O i →
      HasDerivWithinAt (fun τ => ((B.fib i (Γ' τ) : S3) : ℍ[ℝ]))
        (-(B.A i (τ • v) v) * B.fib i (Γ' τ)) (Icc 0 a) τ := fun τ hτ hi => by
    rw [hle τ hτ.2]
    exact (hΓ.2 i τ hτ hi).congr (fun τ' hτ' => by rw [hle τ' hτ'.2]) (by rw [hle τ hτ.2])
  have hright : ∀ τ ∈ Icc a b, τ • v ∈ B.O i →
      HasDerivWithinAt (fun τ => ((B.fib i (Γ' τ) : S3) : ℍ[ℝ]))
        (-(B.A i (τ • v) v) * B.fib i (Γ' τ)) (Icc a b) τ := fun τ hτ hi =>
    B.chart_switch i j v τ (Icc a b) w Γ' hi (hsub τ hτ)
      (eventually_nhdsWithin_of_forall fun τ' hτ' => hform τ' hτ') (hform τ hτ) (hw τ hτ)
  rcases lt_trichotomy τ a with hlt | heq | hgt
  · exact (hleft τ ⟨hτ.1, hlt.le⟩ hi).mono_of_mem_nhdsWithin (nhdsWithin_Icc_left hlt)
  · subst heq
    have := (hleft τ ⟨hτ.1, le_rfl⟩ hi).union (hright τ ⟨le_rfl, hab.le⟩ hi)
    rwa [Icc_union_Icc_eq_Icc hτ.1 hab.le] at this
  · exact (hright τ ⟨hgt.le, hτ.2⟩ hi).mono_of_mem_nhdsWithin (nhdsWithin_Icc_right hgt)

/-- **Existence of horizontal lifts of rays** (from any point over `o_N`). -/
theorem exists_lift (v : V) (p₀ : E) (hp : B.proj p₀ = R.phiN 0) :
    ∃ Γ : ℝ → E, B.IsLiftOn v Γ 1 ∧ Γ 0 = p₀ := by
  have hopen : ∀ j : Sn, IsOpen {τ : ℝ | τ • v ∈ B.O j} := fun j =>
    (B.isOpen_O j).preimage (continuous_id.smul continuous_const)
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ j : Sn, {τ : ℝ | τ • v ∈ B.O j} := fun τ _ =>
    mem_iUnion.2 ⟨_, B.mem_O_self (τ • v)⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen hcover
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  have hN0 : (0 : ℝ) < N + 1 := by positivity
  -- pieces `[k/(N+1), (k+1)/(N+1)]`
  have hpiece : ∀ k : ℕ, k ≤ N → ∃ j : Sn, ∀ τ ∈ Icc ((k : ℝ) / (N + 1)) ((k + 1) / (N + 1)),
      τ • v ∈ B.O j := by
    intro k hk
    have hk' : (k : ℝ) / (N + 1) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hN0).2 (by exact_mod_cast Nat.le_succ_of_le hk)⟩
    obtain ⟨j, hj⟩ := hleb _ hk'
    refine ⟨j, fun τ hτ => hj ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 : τ - k / (N + 1) ≤ 1 / (N + 1) := by
      have := hτ.2; rw [add_div] at this; linarith
    have h2 : 0 ≤ τ - k / (N + 1) := by linarith [hτ.1]
    constructor <;> linarith
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → ∃ Γ : ℝ → E,
      B.IsLiftOn v Γ ((k : ℝ) / (N + 1)) ∧ Γ 0 = p₀ := by
    intro k hk1 hk2
    induction k, hk1 using Nat.le_induction with
    | base =>
      obtain ⟨j, hj⟩ := hpiece 0 (Nat.zero_le _)
      simp only [Nat.cast_zero, zero_add, zero_div] at hj
      obtain ⟨w, hw0, hw⟩ := B.exists_piece j v (by positivity : (0 : ℝ) < 1 / (N + 1)) hj
        (B.fib j p₀)
      refine ⟨_, by exact_mod_cast B.isLiftOn_piece v j hj w hw, ?_⟩
      have h0 : (0 : ℝ) • v ∈ B.O j := hj 0 ⟨le_rfl, by positivity⟩
      have := B.eq_ract_fib j (Γ := fun _ => p₀) (τ := 0) (by rw [zero_smul]; exact hp) h0
      show B.ract (B.σ j ((0 : ℝ) • v)) (w 0) = p₀
      rw [hw0]; exact this.symm
    | succ k hk ih =>
      obtain ⟨Γ, hΓ, hΓ0⟩ := ih (by omega)
      obtain ⟨j, hj⟩ := hpiece k (by omega)
      have hlt : (k : ℝ) / (N + 1) < (k + 1) / (N + 1) := by gcongr; linarith
      obtain ⟨w, hw0, hw⟩ := B.exists_piece j v hlt hj (B.fib j (Γ (k / (N + 1))))
      refine ⟨fun τ => if τ ≤ (k : ℝ) / (N + 1) then Γ τ else B.ract (B.σ j (τ • v)) (w τ), ?_, ?_⟩
      · have := IsLiftOn.extend B hΓ (by positivity) hlt j hj w hw0 hw
        rwa [show ((k + 1 : ℕ) : ℝ) = k + 1 by push_cast; ring]
      · show (if (0 : ℝ) ≤ k / (N + 1) then Γ 0 else _) = p₀
        rw [if_pos (by positivity), hΓ0]
  obtain ⟨Γ, hΓ, hΓ0⟩ := key (N + 1) (by omega) le_rfl
  refine ⟨Γ, ?_, hΓ0⟩
  rwa [show ((N + 1 : ℕ) : ℝ) / (N + 1) = 1 by push_cast; exact div_self hN0.ne'] at hΓ


theorem IsLiftOn.continuousOn {v : V} {Γ : ℝ → E} {b : ℝ} (hΓ : B.IsLiftOn v Γ b) :
    ContinuousOn Γ (Icc 0 b) := by
  intro τ hτ
  have hj : τ • v ∈ B.O (R.phiN (τ • v)) := B.mem_O_self _
  set j := R.phiN (τ • v)
  have hd := hΓ.2 j τ hτ hj
  have hc1 : ContinuousWithinAt (fun τ => B.fib j (Γ τ)) (Icc 0 b) τ :=
    (Topology.IsInducing.subtypeVal.continuousWithinAt_iff).2 hd.continuousWithinAt
  have hray : ContinuousWithinAt (fun τ : ℝ => τ • v) (Icc 0 b) τ :=
    (continuous_id.smul continuous_const).continuousWithinAt
  have hc2 : ContinuousWithinAt (fun τ : ℝ => B.σ j (τ • v)) (Icc 0 b) τ :=
    ContinuousAt.comp_continuousWithinAt (g := B.σ j) (f := fun τ : ℝ => τ • v)
      ((B.contMDiffOn_σ j).continuousOn.continuousAt ((B.isOpen_O j).mem_nhds hj)) hray
  have hc3 : ContinuousWithinAt (fun τ => B.ract (B.σ j (τ • v)) (B.fib j (Γ τ))) (Icc 0 b) τ :=
    B.ract_smooth.continuous.continuousAt.comp_continuousWithinAt (hc2.prodMk hc1)
  have hO : {τ' : ℝ | τ' • v ∈ B.O j} ∈ 𝓝 τ :=
    ((B.isOpen_O j).preimage (continuous_id.smul continuous_const)).mem_nhds hj
  refine hc3.congr_of_eventuallyEq ?_ (B.eq_ract_fib j (hΓ.1 τ hτ) hj)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with τ' h1 h2
  exact B.eq_ract_fib j (hΓ.1 τ' h1) h2

/-- Local uniqueness of lifts near a point where they agree. -/
theorem lift_local_unique {v : V} {Γ Γ' : ℝ → E} (hΓ : B.IsLiftOn v Γ 1)
    (hΓ' : B.IsLiftOn v Γ' 1) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (h0 : Γ t₀ = Γ' t₀) :
    ∃ ε > 0, ∀ τ ∈ Icc (0 : ℝ) 1, |τ - t₀| < ε → Γ τ = Γ' τ := by
  have hj : t₀ • v ∈ B.O (R.phiN (t₀ • v)) := B.mem_O_self _
  set j := R.phiN (t₀ • v)
  have hT : IsOpen {τ : ℝ | τ • v ∈ B.O j} :=
    (B.isOpen_O j).preimage (continuous_id.smul continuous_const)
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hT t₀ hj
  set ε := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  set lo := max 0 (t₀ - ε)
  set hi := min 1 (t₀ + ε)
  have hεε : ε < ε₀ := half_lt_self hε₀
  have hlo : t₀ - ε ≤ lo := le_max_right _ _
  have hhi : hi ≤ t₀ + ε := min_le_right _ _
  have hIT : ∀ τ ∈ Icc lo hi, τ • v ∈ B.O j := fun τ hτ => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hτ.1]
    · linarith [hτ.2])
  have hI01 : Icc lo hi ⊆ Icc 0 1 := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((B.continuousOn_Aray j v).mono hIT) (s := Icc lo hi)
  set K : NNReal := ⟨max K₀ 0, le_max_right _ _⟩
  have hLip : ∀ t ∈ Icc lo hi, LipschitzOnWith K (fun y : ℍ[ℝ] => -(B.A j (t • v) v) * y) univ := by
    intro t ht
    refine (LipschitzWith.of_dist_le_mul fun y z => ?_).lipschitzOnWith
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_right ((hK₀ t ht).trans (le_max_left _ _)) (norm_nonneg _)
  set u := fun τ => ((B.fib j (Γ τ) : S3) : ℍ[ℝ])
  set u' := fun τ => ((B.fib j (Γ' τ) : S3) : ℍ[ℝ])
  have hd : ∀ τ ∈ Icc lo hi, HasDerivWithinAt u (-(B.A j (τ • v) v) * u τ) (Icc 0 1) τ :=
    fun τ hτ => hΓ.2 j τ (hI01 hτ) (hIT τ hτ)
  have hd' : ∀ τ ∈ Icc lo hi, HasDerivWithinAt u' (-(B.A j (τ • v) v) * u' τ) (Icc 0 1) τ :=
    fun τ hτ => hΓ'.2 j τ (hI01 hτ) (hIT τ hτ)
  have hc : ContinuousOn u (Icc lo hi) := fun τ hτ => ((hd τ hτ).continuousWithinAt).mono hI01
  have hc' : ContinuousOn u' (Icc lo hi) := fun τ hτ => ((hd' τ hτ).continuousWithinAt).mono hI01
  have hu0 : u t₀ = u' t₀ := by simp only [u, u', h0]
  have ht₀I : t₀ ∈ Icc lo hi :=
    ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩
  have hfw : EqOn u u' (Icc t₀ hi) := ODE_solution_unique_of_mem_Icc_right
    (v := fun t y => -(B.A j (t • v) v) * y) (s := fun _ => univ) (K := K)
    (fun t ht => hLip t ⟨ht₀I.1.trans ht.1, ht.2.le⟩)
    (hc.mono (Icc_subset_Icc ht₀I.1 le_rfl))
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ⟨(le_max_left _ _).trans (ht₀I.1.trans ht.1),
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ (hd t ⟨ht₀I.1.trans ht.1, ht.2.le⟩))
    (fun _ _ => mem_univ _)
    (hc'.mono (Icc_subset_Icc ht₀I.1 le_rfl))
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ⟨(le_max_left _ _).trans (ht₀I.1.trans ht.1),
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ (hd' t ⟨ht₀I.1.trans ht.1, ht.2.le⟩))
    (fun _ _ => mem_univ _) hu0
  have hbw : EqOn u u' (Icc lo t₀) := ODE_solution_unique_of_mem_Icc_left
    (v := fun t y => -(B.A j (t • v) v) * y) (s := fun _ => univ) (K := K)
    (fun t ht => hLip t ⟨ht.1.le, ht.2.trans ht₀I.2⟩)
    (hc.mono (Icc_subset_Icc le_rfl ht₀I.2))
    (fun t ht => hasDerivWithinAt_Iic_of_Icc ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      ht.2.trans ht₀.2⟩ (hd t ⟨ht.1.le, ht.2.trans ht₀I.2⟩))
    (fun _ _ => mem_univ _)
    (hc'.mono (Icc_subset_Icc le_rfl ht₀I.2))
    (fun t ht => hasDerivWithinAt_Iic_of_Icc ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      ht.2.trans ht₀.2⟩ (hd' t ⟨ht.1.le, ht.2.trans ht₀I.2⟩))
    (fun _ _ => mem_univ _) hu0
  refine ⟨ε, hε, fun τ hτ hτε => ?_⟩
  rw [abs_lt] at hτε
  have hτI : τ ∈ Icc lo hi :=
    ⟨max_le hτ.1 (by linarith), le_min hτ.2 (by linarith)⟩
  have huτ : u τ = u' τ := by
    rcases le_total τ t₀ with h | h
    · exact hbw ⟨hτI.1, h⟩
    · exact hfw ⟨h, hτI.2⟩
  have hf : B.fib j (Γ τ) = B.fib j (Γ' τ) := Subtype.ext huτ
  rw [B.eq_ract_fib j (hΓ.1 τ hτ) (hIT τ hτI), B.eq_ract_fib j (hΓ'.1 τ hτ) (hIT τ hτI), hf]

/-- **Uniqueness of horizontal lifts of rays.** -/
theorem lift_unique [T2Space E] {v : V} {Γ Γ' : ℝ → E} (hΓ : B.IsLiftOn v Γ 1)
    (hΓ' : B.IsLiftOn v Γ' 1) (h0 : Γ 0 = Γ' 0) : ∀ τ ∈ Icc (0 : ℝ) 1, Γ τ = Γ' τ := by
  haveI : ConnectedSpace (Icc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.1 (isConnected_Icc zero_le_one)
  set S : Set (Icc (0 : ℝ) 1) := {t | Γ t = Γ' t}
  have hS : IsClopen S := by
    constructor
    · exact isClosed_eq hΓ.continuousOn.restrict hΓ'.continuousOn.restrict
    · refine Metric.isOpen_iff.2 fun t ht => ?_
      obtain ⟨ε, hε, hloc⟩ := B.lift_local_unique hΓ hΓ' t t.2 ht
      refine ⟨ε, hε, fun s hs => hloc s s.2 ?_⟩
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hs
      exact hs
  have := hS.eq_univ ⟨⟨0, le_rfl, zero_le_one⟩, h0⟩
  intro τ hτ
  have hmem : (⟨τ, hτ⟩ : Icc (0 : ℝ) 1) ∈ S := this ▸ mem_univ _
  exact hmem

end StarBundle

end Ray

end

end ExoticSpheres8And10
