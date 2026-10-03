/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Continuity
import ExoticSpheres8And10.Curvature.Prop31.Bundle.PotentialConnection
import ExoticSpheres8And10.Curvature.Prop31.Bundle.HessianNaturality

/-! # A model with `dim B = 2` and `Ω ≠ 0` for [HLY] Prop. 3.1

* **Base.** `B = CDisk 2 1`, the closed unit disk in `ℝ²`: a compact manifold **with
  boundary**. Its metric is the round metric `HR = (1 + |x|²/4)⁻² |dx|²`, pulled back along
  `val`. This is a closed geodesic cap of the unit sphere, with sectional curvature `1`
  (`sec_gD`).
* **Bundle and connection.** The trivial bundle `B × S³` with the connection of potential
  `t₀ dt₁ ⊗ i` (`potConn`). Its curvature is `(dt₀ ∧ dt₁) ⊗ i ≠ 0` at **every** point
  (`curvNormSq_disk_pos`).
* **Warping function.** `φ = A · hR`, with `hR = cos t` the height function, so that
  `−Hess φ = A hR g ≥ (3A/5) g` on the cap (`hessAt_φD`).

`hly_prop31_model_disk`: for a suitable `A`, every hypothesis of
`hly_prop31_global_intrinsic` holds, with `κ = 1`, and `M₀`, `M₁` from compactness. So
`G_ε` has positive sectional curvature on `B × S³` for small `ε`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local notation "D2" => CDisk 2 (1 : ℝ)

section Disk

/-- The round metric on the cap, pulled back along `val`. -/
def gD : Π x : D2, TangentSpace (𝓡∂ 2) x →L[ℝ] TangentSpace (𝓡∂ 2) x →L[ℝ] ℝ :=
  pullMet (HR (K := E2)) Subtype.val

theorem isSymm_gD : IsSymm gD :=
  isSymm_pullMet fun y a b => by simp only [HR_apply, real_inner_comm]

theorem isPosDef_gD : IsPosDef gD :=
  isPosDef_pullMet (fun y a ha => by
    rw [HR_apply]; exact mul_pos (ψR_pos y) (real_inner_self_pos.2 ha))
    (isInvertible_mfderiv_val_disk 1)

theorem isContMDiffMetricSection_gD : IsContMDiffMetricSection E2 ∞ gD :=
  isContMDiffMetricSection_pullMet contDiff_HR (contMDiff_val_disk 1)

/-- The differential of `val`, as a vector of `ℝ²`. -/
def dvalE (b : D2) (u : TangentSpace (𝓡∂ 2) b) : E2 := mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) Subtype.val b u

theorem gD_apply (b : D2) (u v : TangentSpace (𝓡∂ 2) b) :
    gD b u v = HR (b.1 : E2) (dvalE b u) (dvalE b v) := rfl

theorem injective_dval (b : D2) :
    Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) (Subtype.val : D2 → E2) b) := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_val_disk 1 b
  rw [← hL]; exact L.injective

/-- **The cap has sectional curvature `1`.** -/
theorem sec_gD (b : D2) (u v : TangentSpace (𝓡∂ 2) b) (h : LinearIndependent ℝ ![u, v]) :
    1 ≤ sectionalCurvatureAt isSymm_gD isPosDef_gD
      (IsContMDiffMetricSection.of_le' isContMDiffMetricSection_gD two_le_infty_ω) b u v := by
  rw [sectionalCurvatureAt_pullback (contMDiff_val_disk 1) (isInvertible_mfderiv_val_disk 1)
    (fun x u v => rfl) isSymm_gD isPosDef_gD _ isSymm_HR isPosDef_HR
    (isContMDiffMetricSection_cmet contDiff2_HR)]
  have hli : LinearIndependent ℝ ![dvalE b u, dvalE b v] := by
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    apply injective_dval b
    rw [map_add, map_smul, map_smul, map_zero]
    exact hst
  exact (sectionalCurvatureAt_HR hli).symm.le

/-- The height function on the cap is at least `3/5`. -/
theorem hR_ge (b : D2) : 3 / 5 ≤ hR (b.1 : E2) := by
  have hb : ‖(b.1 : E2)‖ ^ 2 ≤ 1 ^ 2 := b.2
  unfold hR
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The warping function `φ = A · hR`. -/
def φD (A : ℝ) (b : D2) : ℝ := A * hR (b.1 : E2)

theorem contMDiff_φD (A : ℝ) : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ (φD A) :=
  ((contDiff_const.mul contDiff_hR).contMDiff).comp (contMDiff_val_disk 1)

/-- **`Hess φ = −A hR g`** on the cap. -/
theorem hessAt_φD (A : ℝ) (b : D2) (v : TangentSpace (𝓡∂ 2) b) :
    hessAt gD (φD A) b v v = -(A * (hR (b.1 : E2) * gD b v v)) := by
  set w : E2 := dvalE b v with hw
  set W : Π z : E2, TangentSpace 𝓘(ℝ, E2) z := toTS fun _ => w with hWdef
  set Y := mpullback (𝓡∂ 2) 𝓘(ℝ, E2) (Subtype.val : D2 → E2) W with hYdef
  have hYb : Y b = v := by
    rw [hYdef, mpullback_apply]
    exact mpullback_mfderiv (isInvertible_mfderiv_val_disk 1) v
  have hW : ∀ z, ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E2).tangent ∞ (T% W) z :=
    fun z => cmdiffAt_toTS contDiffAt_const
  have hYd : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2).tangent (T% Y) b :=
    MDifferentiableAt.mpullback_vectorField (n := ∞) ((hW _).mdifferentiableAt (by simp))
      ((contMDiff_val_disk 1) b) (isInvertible_mfderiv_val_disk 1 b) two_le_infty'
  have h1 : hessF gD (φD A) Y Y b = hessAt gD (φD A) b v v := by
    rw [hessAt_eq isSymm_gD isPosDef_gD isContMDiffMetricSection_gD (contMDiff_φD A) Y Y hYd, hYb]
  have hgm : IsMDiffMetric E2 gD :=
    (IsContMDiffMetricSection.of_le' isContMDiffMetricSection_gD two_le_infty_ω).isMDiffMetric
      (by simp)
  have hφ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ (fun x : E2 => A * hR x) :=
    (contDiff_const.mul contDiff_hR).contMDiff
  have h2 := hessF_mpullback (f := (Subtype.val : D2 → E2)) (contMDiff_val_disk 1)
    (isInvertible_mfderiv_val_disk 1) (fun x u v => rfl) isSymm_gD isPosDef_gD.isNondegenerate hgm
    isSymm_HR isPosDef_HR.isNondegenerate (isMDiffMetric_cmet (contDiff_HR.of_le (WithTop.coe_le_coe.mpr le_top)))
    hφ (X := W) (Y := W) (x := b) (Eventually.of_forall hW)
  rw [← h1]
  show hessF gD ((fun x : E2 => A * hR x) ∘ Subtype.val) Y Y b = _
  rw [h2, hessF_cmet_const ((contDiff_const.mul contDiff_hR).of_le (WithTop.coe_le_coe.mpr le_top)) w,
    hess_hRA, gD_apply]

/-- The coordinates `t₀, t₁` on the cap. -/
def tD (i : Fin 2) (b : D2) : ℝ := (b.1 : E2) i

theorem contMDiff_tD (i : Fin 2) : ContMDiff (𝓡∂ 2) 𝓘(ℝ) ∞ (tD i) :=
  (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).contMDiff.comp (contMDiff_val_disk 1)

theorem mvfderiv_tD (i : Fin 2) (z : D2) (v : TangentSpace (𝓡∂ 2) z) :
    mvfderiv (𝓡∂ 2) (tD i) z v = dvalE z v i := by
  have hv : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, E2) (Subtype.val : D2 → E2) z :=
    (contMDiff_val_disk 1 z).mdifferentiableAt (by simp)
  rw [show tD i = (EuclideanSpace.proj i : E2 →L[ℝ] ℝ) ∘ Subtype.val from rfl,
    mvfderiv_clm_comp _ hv v]
  rfl

/-- The connection with potential `t₀ dt₁ ⊗ i`. -/
def CD : S3Connection (trivPB (𝓡∂ 2) D2) :=
  potConn (𝓡∂ 2) D2 (contMDiff_tD 0) (contMDiff_tD 1) (qe_re 0)

/-- Lagrange: two `g`-orthonormal vectors of the cap have independent coordinate differentials. -/
theorem det_ne_zero (b : D2) {e0 e1 : TangentSpace (𝓡∂ 2) b} (h00 : gD b e0 e0 = 1)
    (h01 : gD b e0 e1 = 0) (h11 : gD b e1 e1 = 1) :
    mvfderiv (𝓡∂ 2) (tD 0) b e0 * mvfderiv (𝓡∂ 2) (tD 1) b e1 -
      mvfderiv (𝓡∂ 2) (tD 0) b e1 * mvfderiv (𝓡∂ 2) (tD 1) b e0 ≠ 0 := by
  simp only [mvfderiv_tD]
  set a : E2 := dvalE b e0
  set a' : E2 := dvalE b e1
  have hip : ∀ x y : E2, ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := fun x y => by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  rw [gD_apply, HR_apply, hip] at h00 h01 h11
  have hψ := ψR_pos (b.1 : E2)
  have hdot : a 0 * a' 0 + a 1 * a' 1 = 0 := by
    rcases mul_eq_zero.1 h01 with h | h
    · exact absurd h hψ.ne'
    · exact h
  intro hdet
  have hlag : (a 0 * a' 1 - a' 0 * a 1) ^ 2 + (a 0 * a' 0 + a 1 * a' 1) ^ 2 =
      (a 0 * a 0 + a 1 * a 1) * (a' 0 * a' 0 + a' 1 * a' 1) := by ring
  rw [hdet, hdot] at hlag
  have hA : 0 < a 0 * a 0 + a 1 * a 1 := by
    by_contra hc
    have : a 0 * a 0 + a 1 * a 1 = 0 :=
      le_antisymm (not_lt.1 hc) (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    rw [this, mul_zero] at h00; exact zero_ne_one h00
  have hA' : 0 < a' 0 * a' 0 + a' 1 * a' 1 := by
    by_contra hc
    have : a' 0 * a' 0 + a' 1 * a' 1 = 0 :=
      le_antisymm (not_lt.1 hc) (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    rw [this, mul_zero] at h11; exact zero_ne_one h11
  nlinarith [mul_pos hA hA']

theorem finrank_E2 : finrank ℝ E2 = 2 := finrank_euclideanSpace_fin

/-- **The curvature of `CD` is nonzero at every point.** -/
theorem curvNormSq_disk_pos (y : D2 × S3) : 0 < CD.curvNormSq gD y := by
  have hspec := frameAt_spec isSymm_gD isPosDef_gD isContMDiffMetricSection_gD
    ((trivPB (𝓡∂ 2) D2).proj y)
  unfold S3Connection.curvNormSq
  generalize frameAt gD ((trivPB (𝓡∂ 2) D2).proj y) = fr at hspec ⊢
  obtain ⟨hb, hUo, he, hor⟩ := hspec
  set b := (trivPB (𝓡∂ 2) D2).proj y
  set e := fr.2
  let i0 : Fin (finrank ℝ E2) := ⟨0, by rw [finrank_E2]; norm_num⟩
  let i1 : Fin (finrank ℝ E2) := ⟨1, by rw [finrank_E2]; norm_num⟩
  have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hev : ∀ i, ∀ᶠ z in 𝓝 b, ContMDiffAt (𝓡∂ 2) (𝓡∂ 2).tangent ∞ (T% (e i)) z :=
    fun i => by filter_upwards [hUo.mem_nhds hb] with z hz using he i z hz
  have hF := curvF_potConn (contMDiff_tD 0) (contMDiff_tD 1) (qe_re 0) b (hev i0) (hev i1)
  set c := mvfderiv (𝓡∂ 2) (tD 0) b (e i0 b) * mvfderiv (𝓡∂ 2) (tD 1) b (e i1 b) -
    mvfderiv (𝓡∂ 2) (tD 0) b (e i1 b) * mvfderiv (𝓡∂ 2) (tD 1) b (e i0 b) with hc
  have hc0 : c ≠ 0 := det_ne_zero b (by rw [hor b hb]; simp [kron])
    (by rw [hor b hb]; simp [kron, hi]) (by rw [hor b hb]; simp [kron])
  set u := (trivPB (𝓡∂ 2) D2).fU b y
  set w := star u * (c • qe 0) * u with hwdef
  have hΩ : ∀ a, CD.tΩ b e i0 i1 a y = ⟪w, qe a⟫ := fun a => by
    simp only [S3Connection.tΩ]
    rw [show CD = potConn (𝓡∂ 2) D2 (contMDiff_tD 0) (contMDiff_tD 1) (qe_re 0) from rfl, hF]
  have hu : u ≠ 0 := by
    intro h0
    have h1 := normSq_sphere ((trivPB (𝓡∂ 2) D2).fib b y)
    change Quaternion.normSq u = 1 at h1
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hq0 : qe 0 ≠ 0 := fun h => by
    have h1 := inner_qe 0 0
    rw [h, inner_zero_left] at h1
    simp [kron] at h1
  have hw0 : w ≠ 0 :=
    mul_ne_zero (mul_ne_zero (star_ne_zero.2 hu) (smul_ne_zero hc0 hq0)) hu
  have hre : w.re = 0 := by
    rw [hwdef, re_star_mul_mul]
    simp [qe_re]
  have hex : ∃ a, ⟪w, qe a⟫ ≠ 0 := by
    by_contra hall'
    have hall : ∀ a, ⟪w, qe a⟫ = 0 := fun a => by
      by_contra ha; exact hall' ⟨a, ha⟩
    have h := sum_inner_qe hre
    simp only [hall, zero_smul, Finset.sum_const_zero] at h
    exact hw0 h.symm
  obtain ⟨a, ha⟩ := hex
  have hpos : 0 < ∑ a', CD.tΩ b e i0 i1 a' y ^ 2 :=
    Finset.sum_pos' (fun a' _ => sq_nonneg _)
      ⟨a, Finset.mem_univ _, by rw [hΩ]; exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 ha).symm⟩
  unfold Prop31Algebra.OmSq S3Connection.ΩP
  calc (0 : ℝ) < ∑ a', CD.tΩ b e i0 i1 a' y ^ 2 := hpos
    _ ≤ ∑ j, ∑ a', CD.tΩ b e i0 j a' y ^ 2 :=
        Finset.single_le_sum (f := fun j => ∑ a', CD.tΩ b e i0 j a' y ^ 2)
          (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i1)
    _ ≤ ∑ i, ∑ j, ∑ a', CD.tΩ b e i j a' y ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ∑ a', CD.tΩ b e i j a' y ^ 2)
          (fun i _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ i0)

/-- **Non-vacuity, with `dim B = 2` and `Ω ≠ 0`.** On the round cap `CDisk 2 1` (a manifold with
boundary, `sec = 1`), with the trivial bundle and the connection `CD`:
* the curvature of `CD` is nonzero at every point of `B × S³`;
* for a suitable `A`, every hypothesis of `hly_prop31_global_intrinsic` holds, so
  `G_ε = π^*g + ε e^{ε A hR} Q(ω, ω)` has positive sectional curvature for small `ε`. -/
theorem hly_prop31_model_disk :
    (∀ y : D2 × S3, 0 < CD.curvNormSq gD y) ∧
    ∃ A : ℝ, ∃ ε₀ > 0, ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      ∀ (y : D2 × S3) (u v : TangentSpace ((𝓡∂ 2).prod (𝓡 3)) y), LinearIndependent ℝ ![u, v] →
        0 < sectionalCurvatureAt (CD.isSymm_connMetric isSymm_gD (φD A) ε)
          (CD.isPosDef_connMetric isPosDef_gD (φD A) hε)
          (IsContMDiffMetricSection.of_le'
            (CD.isContMDiffMetricSection_connMetric isContMDiffMetricSection_gD (contMDiff_φD A) ε)
            two_le_infty_ω) y u v := by
  refine ⟨curvNormSq_disk_pos, ?_⟩
  obtain ⟨M0, M1, hM0, hM1, hb0, hb1⟩ :=
    CD.exists_curv_bounds isSymm_gD isPosDef_gD isContMDiffMetricSection_gD
  set Λ := 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 / 1 * (M1 + 1) ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨5 * Λ / 3, hly_prop31_global_intrinsic isSymm_gD isPosDef_gD isContMDiffMetricSection_gD
    one_pos sec_gD CD (contMDiff_φD _) hM0 hM1 hb0 hb1 ?_ le_rfl⟩
  intro b v
  rw [hessAt_φD, neg_neg]
  have hg0 : 0 ≤ gD b v v := by
    rw [gD_apply, HR_apply]
    exact mul_nonneg (ψR_pos _).le real_inner_self_nonneg
  have hh := hR_ge b
  nlinarith [mul_nonneg hΛ0 hg0, mul_nonneg (mul_nonneg hΛ0 hg0) (sub_nonneg.2 hh)]

end Disk

end

end ExoticSpheres8And10
