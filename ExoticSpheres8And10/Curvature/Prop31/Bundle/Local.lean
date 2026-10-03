/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Defs

/-! # Principal `S³`-bundles: smoothness of `G_ε`, and the local form of the connection

* `contMDiff_pairing_along`: `p ↦ g(f p)(df V, df W)` is smooth for a smooth metric `g` on `B`,
  smooth `f : P → B` and smooth fields `V, W` on `P`;
* `isContMDiffMetricSection_connMetric`: `G_ε` is a smooth metric section.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Along

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] {H' : Type} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

/-- **The pairing along a map is smooth**: `p ↦ g(f p)(df_p V p, df_p W p)`, at a point. -/
theorem contMDiffAt_pairing_along {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
    (hg : IsContMDiffMetricSection E ∞ g) {f : M → B} (hf : ContMDiff J I ∞ f)
    {V W : Π p : M, TangentSpace J p} {x : M} (hV : ContMDiffAt J J.tangent ∞ (T% V) x)
    (hW : ContMDiffAt J J.tangent ∞ (T% W) x) :
    ContMDiffAt J 𝓘(ℝ) ∞ (fun p => g (f p) (mfderiv J I f p (V p)) (mfderiv J I f p (W p))) x := by
  have hψ : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (y : B) ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (f m) (g (f m))) x :=
    (hg (f x)).comp x (hf x)
  have hT : ContMDiff J.tangent I.tangent ∞ (tangentMap J I f) :=
    hf.contMDiff_tangentMap (by simp)
  have hv : ContMDiffAt J I.tangent ∞
      (fun m ↦ TotalSpace.mk' E (E := TangentSpace I) (f m) (mfderiv J I f m (V m))) x :=
    (hT _).comp x hV
  have hw : ContMDiffAt J I.tangent ∞
      (fun m ↦ TotalSpace.mk' E (E := TangentSpace I) (f m) (mfderiv J I f m (W m))) x :=
    (hT _).comp x hW
  have h : ContMDiffAt J (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (f z)
        (g (f z) (mfderiv J I f z (V z)) (mfderiv J I f z (W z)))) x :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) hψ hv hw
  simp only [Bundle.contMDiffAt_totalSpace] at h
  exact h.2

end Along

section Metric

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

/-- **`G_ε` is a smooth metric section.** -/
theorem isContMDiffMetricSection_connMetric
    {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
    (hg : IsContMDiffMetricSection E ∞ g) {φ : B → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (ε : ℝ) :
    IsContMDiffMetricSection (E × E3) (⊤ : ℕ∞) (C.connMetric g φ ε) := by
  refine isContMDiffMetricSection_of_scalars _ fun x V W hV hW => ?_
  have hV' : ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% V) x := hV
  have hW' : ContMDiffAt (I.prod (𝓡 3)) (I.prod (𝓡 3)).tangent ∞ (T% W) x := hW
  have h1 := contMDiffAt_pairing_along hg Pb.proj_smooth hV' hW'
  have h2 : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞
      (fun p => ⟪C.conn p (V p), C.conn p (W p)⟫) x :=
    ((ipL (Quaternion ℝ)).contMDiff.contMDiffAt.comp x (C.smooth V x hV')).clm_apply
      (C.smooth W x hW')
  have h3 : ContMDiffAt (I.prod (𝓡 3)) 𝓘(ℝ) ∞
      (fun p => ε * Real.exp (ε * φ (Pb.proj p))) x :=
    contMDiffAt_const.mul (Real.contDiff_exp.contMDiff.contMDiffAt.comp x
      (contMDiffAt_const.mul ((hφ.comp Pb.proj_smooth) x)))
  have h4 := h1.add (h3.mul h2)
  refine (h4.of_le (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [C.connMetric_apply]
  simp only [Pi.add_apply, Pi.mul_apply]

end S3Connection

end Metric

section Vertical

theorem contMDiff_lmulS3 (u : S3) : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun q : S3 => u * q) :=
  contMDiff_mulS3.comp (contMDiff_const.prodMk contMDiff_id)

theorem mdifferentiableAt_lmulS3 (u q : S3) :
    MDifferentiableAt (𝓡 3) (𝓡 3) (fun q : S3 => u * q) q :=
  (contMDiff_lmulS3 u q).mdifferentiableAt (by simp)

/-- `d(L_u)₁ ∘ d(L_{u⁻¹})_u = id`. -/
theorem mfderiv_lmul_right_inv (u : S3) (Y : TangentSpace (𝓡 3) u) :
    mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u * q) 1
      (mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u⁻¹ * q) u Y) = Y := by
  have hc := mfderiv_comp u (mdifferentiableAt_lmulS3 u (u⁻¹ * u)) (mdifferentiableAt_lmulS3 u⁻¹ u)
  have hid : ((fun q : S3 => u * q) ∘ fun q : S3 => u⁻¹ * q) = id :=
    funext fun q => by simp [mul_inv_cancel_left]
  rw [hid, mfderiv_id] at hc
  have h1 := congrArg (fun L => L Y) hc
  have key : ∀ y (hy : u⁻¹ * u = y),
      Y = mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u * q) y
        (mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u⁻¹ * q) u Y) := by
    intro y hy; subst hy; exact h1
  exact (key 1 (inv_mul_cancel u)).symm

/-- `dι_u ∘ d(L_u)₁ = u · ι3`. -/
theorem mvfderiv_val_lmul (u : S3) (ζ : E3) :
    mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) u
      (mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u * q) 1 ζ) = (u : Quaternion ℝ) * ι3 ζ := by
  have hv : ∀ q : S3, MDifferentiableAt (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) q :=
    fun q => ((contMDiff_coe_sphere (m := 1)) q).mdifferentiableAt one_ne_zero
  have key : ∀ y (hy : u * 1 = y),
      mvfderiv (𝓡 3) ((Subtype.val : S3 → Quaternion ℝ) ∘ fun q : S3 => u * q) 1 ζ =
        mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) y
          (mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u * q) 1 ζ) := by
    intro y hy; subst hy; exact mvfderiv_comp' (hv _) (mdifferentiableAt_lmulS3 u 1) ζ
  rw [← key u (mul_one u)]
  have e : ((Subtype.val : S3 → Quaternion ℝ) ∘ fun q : S3 => u * q) =
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ) (u : Quaternion ℝ)) ∘
        (Subtype.val : S3 → Quaternion ℝ) := rfl
  rw [e, mvfderiv_clm_comp _ (hv 1) ζ, mvfderiv_val_one]
  rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

/-- **The connection on fibre directions**: `ω(d(ract s)_u Y) = ū · dι(Y)`. -/
theorem conn_mfderiv_ract_left (s : P) (u : S3) (Y : TangentSpace (𝓡 3) u) :
    C.conn (Pb.ract s u) (mfderiv (𝓡 3) (I.prod (𝓡 3)) (Pb.ract s) u Y) =
      star (u : Quaternion ℝ) * mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) u Y := by
  set ζ := mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u⁻¹ * q) u Y
  rw [← mfderiv_lmul_right_inv u Y, mvfderiv_val_lmul u ζ]
  have hr : ∀ q : S3, MDifferentiableAt (𝓡 3) (I.prod (𝓡 3)) (Pb.ract s) q :=
    fun q => (Pb.contMDiff_ract_left s q).mdifferentiableAt (by simp)
  have key : ∀ y (hy : u * 1 = y),
      mfderiv (𝓡 3) (I.prod (𝓡 3)) (Pb.ract s ∘ fun q : S3 => u * q) 1 ζ =
        mfderiv (𝓡 3) (I.prod (𝓡 3)) (Pb.ract s) y
          (mfderiv (𝓡 3) (𝓡 3) (fun q : S3 => u * q) 1 ζ) := by
    intro y hy; subst hy
    rw [mfderiv_comp 1 (hr _) (mdifferentiableAt_lmulS3 u 1)]; rfl
  rw [← key u (mul_one u)]
  have e : (Pb.ract s ∘ fun q : S3 => u * q) = Pb.ract (Pb.ract s u) :=
    funext fun q => (Pb.ract_mul s u q).symm
  rw [e]
  have hv := C.vert (Pb.ract s u) ζ
  rw [show Pb.fund ζ (Pb.ract s u) = mfderiv (𝓡 3) (I.prod (𝓡 3)) (Pb.ract (Pb.ract s u)) 1 ζ
    from rfl] at hv
  rw [hv, ← mul_assoc, star_mul_self_sphere, one_mul]

/-- **The connection on base directions** (equivariance): `ω(d(ract · u)_s X) = ū ω(X) u`. -/
theorem conn_mfderiv_ract_right (s : P) (u : S3) (X : TangentSpace (I.prod (𝓡 3)) s) :
    C.conn (Pb.ract s u) (mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) (Pb.ract · u) s X) =
      star (u : Quaternion ℝ) * C.conn s X * u :=
  C.equiv s u X

end S3Connection

end Vertical

section Decomp

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]

namespace PrincipalS3Bundle

variable (Pb : PrincipalS3Bundle I B P)

theorem mdiffAt_proj (p : P) : MDifferentiableAt (I.prod (𝓡 3)) I Pb.proj p :=
  (Pb.proj_smooth p).mdifferentiableAt (by simp)

theorem mdiffAt_sec (b₀ : B) {b : B} (hb : b ∈ Pb.nbhd b₀) :
    MDifferentiableAt I (I.prod (𝓡 3)) (Pb.sec b₀) b :=
  ((Pb.sec_smooth b₀).contMDiffAt ((Pb.nbhd_open b₀).mem_nhds hb)).mdifferentiableAt (by simp)

theorem nhds_preimage (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) :
    Pb.proj ⁻¹' Pb.nbhd b₀ ∈ 𝓝 p :=
  ((Pb.nbhd_open b₀).preimage Pb.proj_smooth.continuous).mem_nhds hp

theorem mdiffAt_fib (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀) :
    MDifferentiableAt (I.prod (𝓡 3)) (𝓡 3) (Pb.fib b₀) p :=
  ((Pb.fib_smooth b₀).contMDiffAt (Pb.nhds_preimage b₀ hp)).mdifferentiableAt (by simp)

/-- **The tangent decomposition** in a local trivialisation:
`v = d(ract · u)(ds(dπ v)) + d(ract s)(d fib v)`, with `s = sec(π p)` and `u = fib p`. -/
theorem tangent_decomp (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (v : TangentSpace (I.prod (𝓡 3)) p) :
    v = mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) (Pb.ract · (Pb.fib b₀ p)) (Pb.sec b₀ (Pb.proj p))
          (mfderiv I (I.prod (𝓡 3)) (Pb.sec b₀) (Pb.proj p) (mfderiv (I.prod (𝓡 3)) I Pb.proj p v)) +
        mfderiv (𝓡 3) (I.prod (𝓡 3)) (Pb.ract (Pb.sec b₀ (Pb.proj p))) (Pb.fib b₀ p)
          (mfderiv (I.prod (𝓡 3)) (𝓡 3) (Pb.fib b₀) p v) := by
  set σ : P → P := fun x => Pb.sec b₀ (Pb.proj x)
  set Θ : P → P := fun x => uncurry Pb.ract (σ x, Pb.fib b₀ x)
  have hΘ : Θ =ᶠ[𝓝 p] id := by
    filter_upwards [Pb.nhds_preimage b₀ hp] with x hx using Pb.sec_fib b₀ x hx
  have h1 : mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) Θ p v = v := by
    rw [hΘ.mfderiv_eq, mfderiv_id]; rfl
  have hσ : MDifferentiableAt (I.prod (𝓡 3)) (I.prod (𝓡 3)) σ p :=
    (Pb.mdiffAt_sec b₀ hp).comp p (Pb.mdiffAt_proj p)
  have hτ := Pb.mdiffAt_fib b₀ hp
  have hR : MDifferentiableAt ((I.prod (𝓡 3)).prod (𝓡 3)) (I.prod (𝓡 3)) (uncurry Pb.ract)
      (σ p, Pb.fib b₀ p) := (Pb.ract_smooth _).mdifferentiableAt (by simp)
  have h2 : mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) Θ p v =
      mfderiv ((I.prod (𝓡 3)).prod (𝓡 3)) (I.prod (𝓡 3)) (uncurry Pb.ract) (σ p, Pb.fib b₀ p)
        (mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) σ p v, mfderiv (I.prod (𝓡 3)) (𝓡 3) (Pb.fib b₀) p v) := by
    have hc := mfderiv_comp p (f := fun x => (σ x, Pb.fib b₀ x)) (g := uncurry Pb.ract) hR
      (hσ.prodMk hτ)
    rw [show Θ = uncurry Pb.ract ∘ (fun x => (σ x, Pb.fib b₀ x)) from rfl, hc,
      ContinuousLinearMap.comp_apply, mfderiv_prodMk hσ hτ]
    rfl
  replace h2 := h2.trans (mfderiv_prod_eq_add_apply hR)
  have h3 : mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) σ p v =
      mfderiv I (I.prod (𝓡 3)) (Pb.sec b₀) (Pb.proj p) (mfderiv (I.prod (𝓡 3)) I Pb.proj p v) := by
    rw [show σ = Pb.sec b₀ ∘ Pb.proj from rfl,
      mfderiv_comp p (Pb.mdiffAt_sec b₀ hp) (Pb.mdiffAt_proj p)]
    rfl
  rw [h3] at h2
  rw [h2] at h1
  exact h1.symm

end PrincipalS3Bundle

namespace S3Connection

variable {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

/-- The local connection potential `A = s^*ω` of the section `s = sec b₀`. -/
def pot (b₀ b : B) (w : TangentSpace I b) : Quaternion ℝ :=
  C.conn (Pb.sec b₀ b) (mfderiv I (I.prod (𝓡 3)) (Pb.sec b₀) b w)

/-- **The local form of the connection**: `ω = ū (π^*A) u + ū du`, with `u = fib`. -/
theorem conn_local (b₀ : B) {p : P} (hp : Pb.proj p ∈ Pb.nbhd b₀)
    (v : TangentSpace (I.prod (𝓡 3)) p) :
    C.conn p v = star (Pb.fib b₀ p : Quaternion ℝ) * C.pot b₀ (Pb.proj p)
        (mfderiv (I.prod (𝓡 3)) I Pb.proj p v) * (Pb.fib b₀ p : Quaternion ℝ) +
      star (Pb.fib b₀ p : Quaternion ℝ) *
        mvfderiv (I.prod (𝓡 3)) (fun x => (Pb.fib b₀ x : Quaternion ℝ)) p v := by
  have hpp : Pb.ract (Pb.sec b₀ (Pb.proj p)) (Pb.fib b₀ p) = p := Pb.sec_fib b₀ p hp
  have hv : ∀ y (hy : Pb.fib b₀ p = y),
      mvfderiv (I.prod (𝓡 3)) (fun x => (Pb.fib b₀ x : Quaternion ℝ)) p v =
        mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) y
          (mfderiv (I.prod (𝓡 3)) (𝓡 3) (Pb.fib b₀) p v) := by
    intro y hy; subst hy
    exact mvfderiv_comp' (((contMDiff_coe_sphere (m := 1)) _).mdifferentiableAt one_ne_zero)
      (Pb.mdiffAt_fib b₀ hp) v
  calc C.conn p v = C.conn (Pb.ract (Pb.sec b₀ (Pb.proj p)) (Pb.fib b₀ p)) v := by rw [hpp]
    _ = C.conn (Pb.ract (Pb.sec b₀ (Pb.proj p)) (Pb.fib b₀ p))
          (mfderiv (I.prod (𝓡 3)) (I.prod (𝓡 3)) (Pb.ract · (Pb.fib b₀ p)) (Pb.sec b₀ (Pb.proj p))
            (mfderiv I (I.prod (𝓡 3)) (Pb.sec b₀) (Pb.proj p) (mfderiv (I.prod (𝓡 3)) I Pb.proj p v)) +
          mfderiv (𝓡 3) (I.prod (𝓡 3)) (Pb.ract (Pb.sec b₀ (Pb.proj p))) (Pb.fib b₀ p)
            (mfderiv (I.prod (𝓡 3)) (𝓡 3) (Pb.fib b₀) p v)) :=
        congrArg _ (Pb.tangent_decomp b₀ hp v)
    _ = _ := by
        rw [map_add, C.conn_mfderiv_ract_right, C.conn_mfderiv_ract_left, hv _ rfl]
        rfl

end S3Connection

end Decomp

section PosDef

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

/-- A tangent vector killed by `dπ` and by `ω` is zero. -/
theorem eq_zero_of_proj_conn {p : P} {v : TangentSpace (I.prod (𝓡 3)) p}
    (h1 : mfderiv (I.prod (𝓡 3)) I Pb.proj p v = 0) (h2 : C.conn p v = 0) : v = 0 := by
  set b₀ := Pb.proj p
  have hp : Pb.proj p ∈ Pb.nbhd b₀ := Pb.mem_nbhd b₀
  have hloc := C.conn_local b₀ hp v
  rw [h2, h1, show C.pot b₀ (Pb.proj p) 0 = 0 by simp [pot], mul_zero, zero_mul, zero_add] at hloc
  set u := Pb.fib b₀ p
  have hu : (u : Quaternion ℝ) * star (u : Quaternion ℝ) = 1 := mul_star_self_sphere u
  have hd : mvfderiv (I.prod (𝓡 3)) (fun x => (Pb.fib b₀ x : Quaternion ℝ)) p v = 0 := by
    have := congrArg (fun q => (u : Quaternion ℝ) * q) hloc
    simp only [mul_zero] at this
    rw [← mul_assoc, hu, one_mul] at this
    exact this.symm
  have hv : mvfderiv (𝓡 3) (Subtype.val : S3 → Quaternion ℝ) u
      (mfderiv (I.prod (𝓡 3)) (𝓡 3) (Pb.fib b₀) p v) = 0 := by
    exact (mvfderiv_comp' (((contMDiff_coe_sphere (m := 1)) _).mdifferentiableAt one_ne_zero)
      (Pb.mdiffAt_fib b₀ hp) v).symm.trans hd
  have hf : mfderiv (I.prod (𝓡 3)) (𝓡 3) (Pb.fib b₀) p v = 0 := by
    apply mfderiv_coe_sphere_injective (n := 3) u
    exact hv.trans
      (map_zero (mfderiv (𝓡 3) 𝓘(ℝ, Quaternion ℝ) (Subtype.val : S3 → Quaternion ℝ) u)).symm
  have hdec := Pb.tangent_decomp b₀ hp v
  rw [h1, hf, map_zero, map_zero, map_zero, add_zero] at hdec
  exact hdec

/-- **`G_ε` is positive definite** for `ε > 0`. -/
theorem isPosDef_connMetric {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
    (hg : IsPosDef g) (φ : B → ℝ) {ε : ℝ} (hε : 0 < ε) : IsPosDef (C.connMetric g φ ε) := by
  intro p v hv
  rw [C.connMetric_apply]
  have hc : 0 < ε * Real.exp (ε * φ (Pb.proj p)) := mul_pos hε (Real.exp_pos _)
  by_cases h1 : mfderiv (I.prod (𝓡 3)) I Pb.proj p v = 0
  · have h2 : C.conn p v ≠ 0 := fun h2 => hv (C.eq_zero_of_proj_conn h1 h2)
    simp only [h1, map_zero, ContinuousLinearMap.zero_apply, zero_add]
    exact mul_pos hc (real_inner_self_pos.2 h2)
  · exact add_pos_of_pos_of_nonneg (hg _ _ h1) (mul_nonneg hc.le real_inner_self_nonneg)

end S3Connection

end PosDef

end

end ExoticSpheres8And10
