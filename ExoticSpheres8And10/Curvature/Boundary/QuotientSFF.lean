/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Boundary.Model

/-! # §4.4: the second fundamental form of a quotient cap boundary, in coordinates

* `gradAt_cmet_inverse`, `contDiffAt_unitNormal_cmet`: in a chart, the unit normal of a smooth
  function is smooth wherever its differential is nonzero;
* `mfderiv_Φc_slice`: `dΦc` at `(Y, z30)` is the identity;
* **`sff_quot_GW`**: for the star quotient `(V, g_B)` of `(V × S³, GW β w)` and a `ρ`-invariant
  base function `hb`, at `Y` and for `c ∈ V`, with `Zh = SQ.hlift c` the horizontal lift at
  `(Y, 1)`:

    `sff_{g_B}(hb)(c, c) = β(Dν_B·Zh₁, Zh₁) + ½ Dβ(ν_B)(Zh₁, Zh₁) + w·Dw(ν_B)·|Zh₂|²`,

  where `ν_B` is the `β`-unit normal of `hb`. This is [D]'s `B(Y, Y) = B_source(X + U, X + U)`,
  made explicit for warped products.
-/

open RiemannianGeometry Bundle VectorField

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section UnitNormal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {G : E → E →L[ℝ] E →L[ℝ] ℝ}

theorem gradAt_cmet_inverse (hnd : IsNondegenerate (cmet G)) (f : E → ℝ) (x : E) :
    fromTS (gradAt hnd f x) = ContinuousLinearMap.inverse (G x) (fderiv ℝ f x) := by
  have hinv : (G x).IsInvertible := isInvertible_g (g := cmet G) (hnd x)
  rw [gradAt_cmet hnd (v := ContinuousLinearMap.inverse (G x) (fderiv ℝ f x)) fun w => by
    rw [hinv.self_apply_inverse]]
  rfl

theorem contDiffAt_gradAt_cmet (hnd : IsNondegenerate (cmet G)) (hG : ContDiff ℝ ∞ G)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    ContDiffAt ℝ ∞ (fun y => fromTS (gradAt hnd f y)) x := by
  simp only [gradAt_cmet_inverse]
  have hinv : (G x).IsInvertible := isInvertible_g (g := cmet G) (hnd x)
  exact (hinv.contDiffAt_map_inverse.comp x hG.contDiffAt).clm_apply
    ((hf.fderiv_right (m := ∞) le_rfl).contDiffAt)

theorem contDiffAt_unitNormal_cmet (hpos : IsPosDef (cmet G)) (hG : ContDiff ℝ ∞ G)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (hx : fderiv ℝ f x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => fromTS (unitNormal hpos.isNondegenerate f y)) x := by
  set hnd := hpos.isNondegenerate
  have hg := contDiffAt_gradAt_cmet hnd hG hf x
  have hGg : ContDiffAt ℝ ∞ (fun y => G y (fromTS (gradAt hnd f y)) (fromTS (gradAt hnd f y))) x :=
    (hG.contDiffAt.clm_apply hg).clm_apply hg
  have hne : gradAt hnd f x ≠ 0 := by
    intro h
    apply hx
    ext w
    have := g_gradAt hnd f x (toTSv x w)
    rw [h, map_zero, ContinuousLinearMap.zero_apply, mvfderiv_model] at this
    exact this.symm
  have hpx : 0 < G x (fromTS (gradAt hnd f x)) (fromTS (gradAt hnd f x)) := hpos x _ hne
  have hs : ContDiffAt ℝ ∞ (fun y => (√(G y (fromTS (gradAt hnd f y))
      (fromTS (gradAt hnd f y))))⁻¹) x :=
    (hGg.sqrt hpx.ne').inv (Real.sqrt_pos.2 hpx).ne'
  exact hs.smul hg

end UnitNormal

section Slice

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem mfderiv_Φc_slice (Y : V) (b : TangentSpace 𝓘(ℝ, V × E3) (Y, z30)) :
    mfderiv 𝓘(ℝ, V × E3) (IN V) (Φc (V := V)) (Y, z30) b = b := by
  have h1 : MDifferentiableAt 𝓘(ℝ, V × E3) 𝓘(ℝ, V) (fun p : V × E3 => p.1) (Y, z30) :=
    (((contDiff_fst : ContDiff ℝ ∞ (Prod.fst : V × E3 → V)).contMDiff) _).mdifferentiableAt
      (by simp)
  set L : V × E3 →L[ℝ] E3 := ContinuousLinearMap.snd ℝ V E3
  have hσ : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 3) σ3 (L (Y, z30)) :=
    (contMDiff_σ3 _).mdifferentiableAt (by simp)
  have hL : MDifferentiableAt 𝓘(ℝ, V × E3) 𝓘(ℝ, E3) L (Y, z30) := L.mdifferentiableAt
  have hc : mfderiv 𝓘(ℝ, V × E3) (𝓡 3) (σ3 ∘ L) (Y, z30) =
      (mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 (L (Y, z30))).comp L := by
    rw [mfderiv_comp _ hσ hL, L.hasMFDerivAt.mfderiv]
    rfl
  have hpr := mfderiv_prodMk h1 (hσ.comp _ hL)
  have e1 : Φc (V := V) = fun p : V × E3 => (p.1, (σ3 ∘ L) p) := rfl
  have hm : mfderiv 𝓘(ℝ, E3) (𝓡 3) σ3 (L (Y, z30)) = ContinuousLinearMap.id ℝ E3 := mfderiv_σ3
  rw [e1, hpr, hc, hm, mfderiv_eq_fderiv]
  have hf : fderiv ℝ (fun p : V × E3 => p.1) (Y, z30) = ContinuousLinearMap.fst ℝ V E3 := fderiv_fst
  rw [hf]
  rfl

theorem Φc_slice (Y : V) : Φc (Y, z30) = (Y, (1 : S3)) := by
  show (Y, σ3 z30) = _; rw [σ3_z30]

end Slice

section Quot

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ρV : S3 →* (V ≃ₗᵢ[ℝ] V)}
  (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, V →L[ℝ] V) ∞ fun q : S3 => ((ρV q : V ≃L[ℝ] V) : V →L[ℝ] V))
  {β : V → V →L[ℝ] V →L[ℝ] ℝ} {w : V → ℝ}
  (hβ : ContDiff ℝ ∞ β) (hβs : ∀ Y a b, β Y a b = β Y b a) (hβp : ∀ Y a, a ≠ 0 → 0 < β Y a a)
  (hβn : ∀ Y a, 0 ≤ β Y a a) (hw : ContDiff ℝ ∞ w) (hw0 : ∀ Y, w Y ≠ 0)
  (hβρ : ∀ (q : S3) Y a b, β (ρV q Y) (ρV q a) (ρV q b) = β Y a b)
  (hwρ : ∀ q Y, w (ρV q Y) = w Y)

/-- The `β`-unit normal of a base function with `β`-gradient `vB`. -/
def nuB (β : V → V →L[ℝ] V →L[ℝ] ℝ) (vB : V → V) (y : V) : V :=
  (√(β y (vB y) (vB y)))⁻¹ • vB y

include hρ hβ hβs hβp hβn hw hw0 hβρ hwρ in
/-- **The second fundamental form of a quotient cap boundary** for the star quotient of a warped
product `GW β w`: with `Zh = SQ.hlift c` the horizontal lift at `(Y, 1)`,
`sff(c, c) = β(Dν_B Zh₁, Zh₁) + ½ Dβ(ν_B)(Zh₁, Zh₁) + w·Dw(ν_B)·|Zh₂|²`. -/
theorem sff_quot_GW {hb : V → ℝ} (hhb : ContDiff ℝ ∞ hb) (hhbρ : ∀ q Y, hb (ρV q Y) = hb Y)
    {Y : V} (hdY : fderiv ℝ hb Y ≠ 0) {vB : V → V} (hvB : ContDiff ℝ ∞ vB)
    (hvBeq : ∀ y c, β y (vB y) c = fderiv ℝ hb y c) (c : V) :
    sff (SQ.isPosDef_cmet_gB' (ρV := ρV) (GsW_pos (w := w) hβp hβn hw0)).isNondegenerate hb Y
        (toTSv Y c) (toTSv Y c) =
      β Y (fderiv ℝ (nuB β vB) Y (SQ.hlift ρV (GsW β w) Y c).1) (SQ.hlift ρV (GsW β w) Y c).1 +
        (1 / 2) * fderiv ℝ β Y (nuB β vB Y) (SQ.hlift ρV (GsW β w) Y c).1
          (SQ.hlift ρV (GsW β w) Y c).1 +
        w Y * fderiv ℝ w Y (nuB β vB Y) *
          ⟪(SQ.hlift ρV (GsW β w) Y c).2, (SQ.hlift ρV (GsW β w) Y c).2⟫ := by
  set hGpos := GsW_pos (w := w) hβp hβn hw0
  set Zh := SQ.hlift ρV (GsW β w) Y c
  let instM : Bundle.RiemannianBundle (TangentSpace (IN V) : V × S3 → Type) :=
    ⟨(toContMDiffRiemannianMetric (n := 2) (isSymm_GW (w := w) hβs) (isPosDef_GW hβp hβn hw0)
      (isContMDiffMetricSection_GW hβ hw 2)).toRiemannianMetric⟩
  let instB : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, V) : V → Type) :=
    ⟨(toContMDiffRiemannianMetric (n := ∞) (SQ.isSymm_cmet_gB' (ρV := ρV) (GsW_symm (w := w) hβs))
      (SQ.isPosDef_cmet_gB' hGpos)
      (isContMDiffMetricSection_cmet (SQ.contDiff_gB ρV hGpos (contDiff_GsW hβ hw)))).toRiemannianMetric⟩
  have hM : ∀ p u v, tangentMetric (IN V) (V × S3) p u v = GW β w p u v := fun _ _ _ => rfl
  have hB : ∀ y a b, tangentMetric 𝓘(ℝ, V) V y a b = SQ.gB ρV (GsW β w) y a b :=
    fun _ _ _ => rfl
  have hriem := SQ.isRiemannianSubmersionAtPoint_all hρ (GsW_symm (w := w) hβs) hGpos GW_slice
    (GW_starN hρ hβρ hwρ) hM hB
  have hsub := isSubmersionAtPoint_πN (ρV := ρV) hρ
  have hgBsm : ContDiff ℝ ∞ (SQ.gB ρV (GsW β w)) := SQ.contDiff_gB ρV hGpos (contDiff_GsW hβ hw)
  have hgM2 : IsContMDiffMetricSection (V × E3) ((2 : ℕ∞) : ℕ∞ω)
      (tangentMetric (IN V) (V × S3)) := isContMDiffMetricSection_GW hβ hw 2
  have hgB2 : IsContMDiffMetricSection V ((2 : ℕ∞) : ℕ∞ω) (tangentMetric 𝓘(ℝ, V) V) :=
    isContMDiffMetricSection_cmet (hgBsm.of_le (by exact_mod_cast le_top))
  have hf3 : ContMDiff (IN V) 𝓘(ℝ, V) ((2 + 1 : ℕ∞)) (πN ρV) :=
    (contMDiff_πN hρ).of_le (by exact_mod_cast le_top)
  have hhbd : ∀ z, MDiffAt hb (πN ρV z) := fun z =>
    ((hhb.contMDiff) _).mdifferentiableAt (by simp)
  -- the base unit normal is smooth near `Y`
  have hdev : ∀ᶠ y in 𝓝 Y, fderiv ℝ hb y ≠ 0 :=
    ((hhb.continuous_fderiv (by simp)).continuousAt).eventually_ne hdY
  have hνBsm : ∀ᶠ q in 𝓝 Y, ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V).tangent ((2 : ℕ∞) : ℕ∞ω)
      (T% (unitNormal (isNondegenerate_tangentMetric' (I := 𝓘(ℝ, V)) (M := V)) hb)) q := by
    filter_upwards [hdev] with y hy
    have h := contDiffAt_unitNormal_cmet (SQ.isPosDef_cmet_gB' hGpos) hgBsm hhb hy
    exact cmdiffAt_toTS (h.of_le (by exact_mod_cast le_top))
  -- the constant base field `c`
  set Y₁ : Π q : V, TangentSpace 𝓘(ℝ, V) q := toTS fun _ => c
  have hY₁ : ∀ᶠ q in 𝓝 Y, ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V).tangent ((2 : ℕ∞) : ℕ∞ω) (T% Y₁) q :=
    Eventually.of_forall fun q => cmdiffAt_toTS contDiffAt_const
  -- (1) descent
  have hdesc := sff_submersion (n := 2) (by simp) (by simp) hf3 hgM2 hgB2 hsub hriem hhbd
    (p := (Y, (1 : S3))) (Y₁ := Y₁) (by rw [πN_slice]; exact hY₁) (by rw [πN_slice]; exact hνBsm)
  have hF : (fun y : V => sff (isNondegenerate_tangentMetric' (I := 𝓘(ℝ, V)) (M := V)) hb y
      (toTSv y c) (toTSv y c)) (πN ρV (Y, 1)) =
      (fun y : V => sff (isNondegenerate_tangentMetric' (I := 𝓘(ℝ, V)) (M := V)) hb y
        (toTSv y c) (toTSv y c)) Y :=
    congrArg (fun y : V => sff (isNondegenerate_tangentMetric' (I := 𝓘(ℝ, V)) (M := V)) hb y
      (toTSv y c) (toTSv y c)) (πN_slice (ρV := ρV) Y)
  -- (2) `hb ∘ π = hb ∘ fY`
  have ehb : hb ∘ πN ρV = hb ∘ fY := funext fun z => hhbρ _ _
  -- (3) the horizontal lift is `SQ.hlift`
  have hvert : ∀ b, tsN (Y, 1) (ιv ρV Y b) ∈
      verticalSpace (IN V) 𝓘(ℝ, V) (πN ρV) (Y, 1) := fun b => by
    rw [mem_verticalSpace_iff]
    show dπN ρV Y (KY ρV Y b, b) = 0
    rw [dπN_apply hρ, sub_self]
  have hlift_eq : horizontalLiftField (IN V) 𝓘(ℝ, V) (πN ρV) Y₁ (Y, 1) = tsN (Y, 1) Zh := by
    rw [horizontalLiftField_eq_horizontalLift (hsub _) (hriem _)]
    set u := horizontalLift (hsub (Y, 1)) (Y₁ (πN ρV (Y, 1)))
    have hu := horizontalLift_mem (hsub (Y, 1)) (Y₁ (πN ρV (Y, 1)))
    have hdu : dπN ρV Y u = c := horizontalLift_spec (hsub (Y, 1)) (Y₁ (πN ρV (Y, 1)))
    have hhor : ∀ b, GsW β w Y u (ιv ρV Y b) = 0 := by
      intro b
      have := (Submodule.mem_orthogonal _ _).1 hu _ (hvert b)
      rw [inner_eq_tangentMetric, hM, GW_slice] at this
      exact (GsW_symm hβs Y u (ιv ρV Y b)).trans this
    have h1 := SQ.eq_hlift ρV hGpos Y hhor
    rw [← dπN_eq hρ, hdu] at h1
    exact h1
  -- (4) the chart `Φc`
  have hΦi := isInvertible_mfderiv_Φc (V := V) (w := fun _ => (1 : ℝ)) (fun _ => one_ne_zero)
  have hsM := isSymm_cmet_Gwarp (w := w) hβs
  have hpM := isPosDef_cmet_Gwarp (w := w) hβp hβn hw0
  have hgMw : IsMDiffMetric (V × E3) (cmet (Gwarp β w)) :=
    isMDiffMetric_cmet ((contDiff_Gwarp hβ hw).of_le (by simp))
  have hgNw : IsMDiffMetric (V × E3) (tangentMetric (IN V) (V × S3)) :=
    isMDiffMetric_of_isContMDiffMetricSection hgM2
  have hhY : ContMDiff (IN V) 𝓘(ℝ, ℝ) ∞ (hb ∘ fY) := hhb.contMDiff.comp contMDiff_fY
  have hνM : MDifferentiableAt (IN V) (IN V).tangent (fun y => (⟨y, unitNormal
      (isNondegenerate_tangentMetric' (I := IN V) (M := V × S3)) (hb ∘ fY) y⟩ :
        TangentBundle (IN V) (V × S3))) (Φc (Y, z30)) := by
    rw [Φc_slice, ← ehb]
    have e : unitNormal (isNondegenerate_tangentMetric' (I := IN V) (M := V × S3)) (hb ∘ πN ρV) =
        horizontalLiftField (IN V) 𝓘(ℝ, V) (πN ρV)
          (unitNormal (isNondegenerate_tangentMetric' (I := 𝓘(ℝ, V)) (M := V)) hb) :=
      funext fun z => unitNormal_comp_submersion (hsub z) (hriem z) (hhbd z)
        ((hf3 z).mdifferentiableAt (by simp))
    rw [e]
    have h := contMDiffAt_horizontalLiftField (m := 2) isOpen_univ (mem_univ (Y, (1 : S3)))
      hf3.contMDiffOn (hgM2 _) (hgB2 _) (by rw [πN_slice]; exact hνBsm.self_of_nhds)
    exact h.mdifferentiableAt (by simp)
  have hpb := sff_pullback (f := Φc (V := V)) contMDiff_Φc hΦi (fun x u v => hpull_Φc_GW x u v)
    hsM hpM.isNondegenerate hgMw (isSymm_GW hβs) isNondegenerate_tangentMetric' hgNw hhY hνM
    (toTSv (Y, z30) Zh) (toTSv (Y, z30) Zh)
  rw [mfderiv_Φc_slice] at hpb
  have hF2 : (fun q : V × S3 => sff (isNondegenerate_tangentMetric' (I := IN V) (M := V × S3))
      (hb ∘ fY) q (tsN q Zh) (tsN q Zh)) (Φc (Y, z30)) =
      (fun q : V × S3 => sff (isNondegenerate_tangentMetric' (I := IN V) (M := V × S3))
        (hb ∘ fY) q (tsN q Zh) (tsN q Zh)) (Y, 1) :=
    congrArg (fun q : V × S3 => sff (isNondegenerate_tangentMetric' (I := IN V) (M := V × S3))
      (hb ∘ fY) q (tsN q Zh) (tsN q Zh)) (Φc_slice Y)
  -- (5) the warped formula at `(Y, z30)`
  have hvB0 : β Y (vB Y) (vB Y) ≠ 0 := by
    intro h0
    apply hdY
    have hv : vB Y = 0 := by
      by_contra hne; exact (hβp Y _ hne).ne' h0
    ext c'; rw [← hvBeq, hv]; simp
  have hνB1 : ContDiffAt ℝ 1 (nuB β vB) Y := by
    have hq : ContDiffAt ℝ ∞ (fun y => β y (vB y) (vB y)) Y :=
      ((hβ.clm_apply hvB).clm_apply hvB).contDiffAt
    have hpos : 0 < β Y (vB Y) (vB Y) := lt_of_le_of_ne (hβn Y _) (Ne.symm hvB0)
    exact (((hq.sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne').smul hvB.contDiffAt).of_le
      (by exact_mod_cast le_top)
  have hνeq : ∀ᶠ q in 𝓝 ((Y, z30) : V × E3), unitNormal hpM.isNondegenerate (hb ∘ Prod.fst) q =
      toTS (fun q : V × E3 => (nuB β vB q.1, (0 : E3))) q :=
    Eventually.of_forall fun q => unitNormal_Gwarp hpM.isNondegenerate
      ((hhb.differentiable (by simp)) q.1) (hvBeq q.1)
  have hw' := sff_warp hβ hw hβs hpM.isNondegenerate (hb := hb) (p := ((Y, z30) : V × E3))
    hνB1 hνeq Zh
  have hψ : ψR (z30 : E3) = 1 := by rw [z30_eq]; simp [ψR]
  rw [hψ, one_mul] at hw'
  -- chain
  refine Eq.trans ?_ hw'
  refine Eq.trans hF.symm ?_
  refine Eq.trans hdesc ?_
  rw [ehb, hlift_eq]
  refine Eq.trans hF2.symm ?_
  exact hpb.symm

end Quot

end

end ExoticSpheres8And10
