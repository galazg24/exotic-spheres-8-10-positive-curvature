/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Northern.Warped
import ExoticSpheres8And10.Geometry.RoundMetric
import ExoticSpheres8And10.Curvature.Northern.ProfilesExistence

/-! # §4: [GG]'s northern filling has positive sectional curvature on star-horizontal planes

The northern metric of [GG] is `ds² + F(s)² h_{S^{n−1}} + r(s)² h_{S³}` with the profiles
`F = Fprof δ` and `r = rprof r_a d δ ℓ_N` of `A7_Existence`, for `0 < s ≤ ℓ_N`.

`S4_North` applies to doubly warped metrics with warping functions positive on all of `ℝ`,
because `RiemannianGeometry`'s curvature is defined for a metric on the whole manifold. [GG]'s `F` vanishes at
`s = 0`. By `riemannTensorAt_wG`, the curvature at `s` depends only on the 2-jets `(F, F', F'')`
and `(r, r', r'')` at `s`. So at each `s` we use a globally positive `C^∞` function with [GG]'s
2-jet there (`jetFun`), and round fibres in normal coordinates (`HR`, at the origin).

* `jetFun`: `a e^{β(t−s)+γ(t−s)²}` has 2-jet `(a, b, c)` at `s` (`jetFun_self`, `deriv_jetFun`,
  `deriv2_jetFun`);
* `northern_sectionalCurvature_pos`: **for [GG]'s parameters, at every `s ∈ (0, ℓ_N]`, `RiemannianGeometry`'s
  sectional curvature is positive on every star-horizontal plane**, for every `K` with
  `‖K‖ ≤ 2`, `T = −(F/r)K^*`.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

/-! ### Realising a 2-jet by a positive function -/

/-- `a e^{β(t−s)+γ(t−s)²}` with `β = b/a`, `γ = (c/a − β²)/2`: 2-jet `(a, b, c)` at `s`. -/
def jetFun (s a b c : ℝ) (t : ℝ) : ℝ :=
  a * exp (b / a * (t - s) + (c / a - (b / a) ^ 2) / 2 * (t - s) ^ 2)

theorem contDiff_jetFun (s a b c : ℝ) : ContDiff ℝ ∞ (jetFun s a b c) := by
  unfold jetFun; fun_prop

theorem jetFun_pos {s a b c : ℝ} (ha : 0 < a) (t : ℝ) : 0 < jetFun s a b c t := by
  unfold jetFun; positivity

theorem jetFun_self (s a b c : ℝ) : jetFun s a b c s = a := by simp [jetFun]

theorem hasDerivAt_jetFun (s a b c t : ℝ) :
    HasDerivAt (jetFun s a b c)
      (jetFun s a b c t * (b / a + 2 * ((c / a - (b / a) ^ 2) / 2) * (t - s))) t := by
  have hq : HasDerivAt (fun t : ℝ => b / a * (t - s) + (c / a - (b / a) ^ 2) / 2 * (t - s) ^ 2)
      (b / a + 2 * ((c / a - (b / a) ^ 2) / 2) * (t - s)) t := by
    have h1 := ((hasDerivAt_id t).sub_const s).const_mul (b / a)
    have h2 := (((hasDerivAt_id t).sub_const s).pow 2).const_mul ((c / a - (b / a) ^ 2) / 2)
    refine (h1.add h2).congr_deriv ?_
    simp; ring
  have h := (hq.exp).const_mul a
  refine h.congr_deriv ?_
  simp only [jetFun]; ring

theorem deriv_jetFun (s a b c : ℝ) :
    deriv (jetFun s a b c) = fun t =>
      jetFun s a b c t * (b / a + 2 * ((c / a - (b / a) ^ 2) / 2) * (t - s)) :=
  funext fun t => (hasDerivAt_jetFun s a b c t).deriv

theorem deriv_jetFun_self {s a b c : ℝ} (ha : a ≠ 0) : deriv (jetFun s a b c) s = b := by
  rw [(hasDerivAt_jetFun s a b c s).deriv, jetFun_self]; field_simp; ring

theorem deriv2_jetFun_self {s a b c : ℝ} (ha : a ≠ 0) :
    deriv (deriv (jetFun s a b c)) s = c := by
  rw [deriv_jetFun]
  have h := (hasDerivAt_jetFun s a b c s).mul
    (((hasDerivAt_id s).sub_const s).const_mul (2 * ((c / a - (b / a) ^ 2) / 2)) |>.const_add
      (b / a))
  have h' : HasDerivAt (fun t => jetFun s a b c t *
      (b / a + 2 * ((c / a - (b / a) ^ 2) / 2) * (t - s))) _ s := h
  rw [h'.deriv, jetFun_self]
  simp only [id, sub_self, mul_zero, add_zero, mul_one]
  field_simp
  ring

/-! ### [GG]'s northern filling -/

section NorthD

variable {H Vv : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Vv] [InnerProductSpace ℝ Vv] [FiniteDimensional ℝ Vv]

/-- [GG]'s angular profile `F = Fprof δ`, realised near `s` by its 2-jet. -/
def northF (δ s : ℝ) : ℝ → ℝ :=
  jetFun s (Fprof δ s) (Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)))
    (-(Fprof δ s / δ ^ 2) * Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) ^ 2)

/-- [GG]'s fibre profile `r = rprof r_a d δ ℓ`, realised near `s` by its 2-jet. -/
def northR (ra d δ ℓ s : ℝ) : ℝ → ℝ :=
  jetFun s (rprof ra d δ ℓ s) (d * etaCut (s / δ)) (d * (deriv etaCut (s / δ) * (1 / δ)))

/-- **[GG] §4, northern filling: positive sectional curvature on star-horizontal planes.** For
the parameters of `northern_filling_pos` (`eq:delta`, `eq:bdata`, `q_sℓ_N ≤ ½`, `d < 1`), at
every `s ∈ (0, ℓ_N]`, for every `K` with `‖K‖ ≤ 2`, the doubly warped metric with [GG]'s 2-jets at
`s` and round fibres has **positive `RiemannianGeometry` sectional curvature** on every plane spanned by an
independent star-horizontal pair `(λ, X, TX)`, `(μ, Y, TY)`, `T = −(F/r)K^*`. -/
theorem northern_sectionalCurvature_pos (Cη : ℝ) (hC0 : 0 ≤ Cη)
    (hC : ∀ x, |deriv etaCut x| ≤ Cη)
    (a ε A0 Fa δ ra qs d : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) (hFa : 0 < Fa) (hδ : 0 < δ)
    (hδ3 : δ ^ 3 ≤ 1 / (128 * A0 * Fa * (1 + Cη))) (hra : 0 < ra)
    (hra2 : ra ^ 2 = ε * Real.exp (ε * A0 * |Real.cos a|)) (hqs : qs = ε * A0 * Fa / 2)
    (hd : d = ra * qs) (hql : qs * Gδ δ Fa ≤ 1 / 2) (hd1 : d < 1)
    (s : ℝ) (hs : s ∈ Ioc 0 (Gδ δ Fa))
    (K : Vv →L[ℝ] H) (hK : ‖K‖ ≤ 2) (X Y : H) (lam mu : ℝ)
    (hind : LinearIndependent ℝ
      ![((lam, X, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X) :
          ℝ × H × Vv),
        (mu, Y, (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) Y)]) :
    have hF0 : ∀ t, northF δ s t ≠ 0 := fun t => (jetFun_pos (Fprof_pos hs.1) t).ne'
    have hr0 : ∀ t, northR ra d δ (Gδ δ Fa) s t ≠ 0 := fun t => (jetFun_pos (by
      have hdl : d * Gδ δ Fa ≤ ra / 2 := by
        have : 0 ≤ qs := by rw [hqs]; positivity
        rw [hd]; nlinarith
      have := (rprof_bounds (δ := δ) (by rw [hd, hqs]; positivity) hs.1.le hs.2 hdl).1
      linarith) t).ne'
    0 < sectionalCurvatureAt (isSymm_wG isSymm_HR isSymm_HR)
      (isPosDef_wG hF0 hr0 isPosDef_HR isPosDef_HR)
      (isContMDiffMetricSection_cmet (contDiff2_wG (contDiff_jetFun _ _ _ _)
        (contDiff_jetFun _ _ _ _) contDiff_HR contDiff_HR)) ((s, 0, 0) : ℝ × H × Vv)
      (toTSv _ (scaledVec (northF δ s) (northR ra d δ (Gδ δ Fa) s) s lam X
        ((-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) X)))
      (toTSv _ (scaledVec (northF δ s) (northR ra d δ (Gδ δ Fa) s) s mu Y
        ((-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) Y))) := by
  intro hF0 hr0
  have hFs : Fprof δ s ≠ 0 := (Fprof_pos hs.1).ne'
  have hrs : rprof ra d δ (Gδ δ Fa) s ≠ 0 := by
    have := hr0 s; rwa [northR, jetFun_self] at this
  have eF : northF δ s s = Fprof δ s := jetFun_self _ _ _ _
  have eR : northR ra d δ (Gδ δ Fa) s s = rprof ra d δ (Gδ δ Fa) s := jetFun_self _ _ _ _
  have eF1 : deriv (northF δ s) s = Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) :=
    deriv_jetFun_self hFs
  have eR1 : deriv (northR ra d δ (Gδ δ Fa) s) s = d * etaCut (s / δ) := deriv_jetFun_self hrs
  have eF2 : deriv (deriv (northF δ s)) s =
      -(Fprof δ s / δ ^ 2) * Real.exp (-(Fprof δ s) ^ 2 / (2 * δ ^ 2)) ^ 2 :=
    deriv2_jetFun_self hFs
  have eR2 : deriv (deriv (northR ra d δ (Gδ δ Fa) s)) s =
      d * (deriv etaCut (s / δ) * (1 / δ)) := deriv2_jetFun_self hrs
  have hN := northern_filling_pos Cη hC0 hC a ε A0 Fa δ ra qs d hε hA0 hFa hδ hδ3 hra hra2 hqs hd
    hql hd1 s hs K hK X Y lam mu hind
  have hT : (-(Fprof δ s / rprof ra d δ (Gδ δ Fa) s) • ContinuousLinearMap.adjoint K) =
      (-(northF δ s s / northR ra d δ (Gδ δ Fa) s s) • ContinuousLinearMap.adjoint K) := by
    rw [eF, eR]
  refine sectionalCurvatureAt_wG_pos_of_num (contDiff_jetFun _ _ _ _) (contDiff_jetFun _ _ _ _)
    contDiff_HR contDiff_HR contDiff_ΓR contDiff_ΓR hF0 hr0 isSymm_HR isSymm_HR isPosDef_HR
    isPosDef_HR HR_ΓR HR_ΓR ((s, 0, 0) : ℝ × H × Vv) HR_zero HR_zero fibreRm_round fibreRm_round
    _ X Y lam mu ?_ hind
  show 0 < northNumerator (northF δ s s) (northR ra d δ (Gδ δ Fa) s s) (deriv (northF δ s) s)
    (deriv (northR ra d δ (Gδ δ Fa) s) s) (deriv (deriv (northF δ s)) s)
    (deriv (deriv (northR ra d δ (Gδ δ Fa) s)) s) _ X Y lam mu
  rw [eF, eR, eF1, eR1, eF2, eR2]
  exact hN

/-- **Non-vacuity of `northern_sectionalCurvature_pos`.** Its hypotheses are jointly satisfiable:
parameters from `northern_filling_hyps_satisfiable` (`A₀ = F_a = 1`, `a = π/2`, `s = ℓ_N`), on
`H = Vv = ℝ` with `K = 0`, and the independent pair `(0, 1, 0)`, `(1, 0, 0)`. -/
theorem northern_sectionalCurvature_hyps_satisfiable :
    ∃ Cη δ ε ra qs d : ℝ, 0 ≤ Cη ∧ (∀ x, |deriv etaCut x| ≤ Cη) ∧ 0 < δ ∧
      δ ^ 3 ≤ 1 / (128 * 1 * 1 * (1 + Cη)) ∧ 0 < ε ∧ 0 < ra ∧
      ra ^ 2 = ε * Real.exp (ε * 1 * |Real.cos (π / 2)|) ∧ qs = ε * 1 * 1 / 2 ∧ d = ra * qs ∧
      qs * Gδ δ 1 ≤ 1 / 2 ∧ d < 1 ∧ Gδ δ 1 ∈ Ioc 0 (Gδ δ 1) ∧
      ‖(0 : ℝ →L[ℝ] ℝ)‖ ≤ 2 ∧
      LinearIndependent ℝ
        ![((0, 1, (-(Fprof δ (Gδ δ 1) / rprof ra d δ (Gδ δ 1) (Gδ δ 1)) •
            ContinuousLinearMap.adjoint (0 : ℝ →L[ℝ] ℝ)) 1) : ℝ × ℝ × ℝ),
          (1, 0, (-(Fprof δ (Gδ δ 1) / rprof ra d δ (Gδ δ 1) (Gδ δ 1)) •
            ContinuousLinearMap.adjoint (0 : ℝ →L[ℝ] ℝ)) 0)] := by
  obtain ⟨Cη, δ, ε, ra, qs, d, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    northern_filling_hyps_satisfiable
  refine ⟨Cη, δ, ε, ra, qs, d, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, by simp, ?_⟩
  simp only [map_zero, smul_zero, ContinuousLinearMap.zero_apply]
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have e1 := congrArg Prod.fst hab
  have e2 := congrArg (fun q : ℝ × ℝ × ℝ => q.2.1) hab
  simp at e1 e2
  exact ⟨e2, e1⟩

end NorthD

end

end ExoticSpheres8And10
