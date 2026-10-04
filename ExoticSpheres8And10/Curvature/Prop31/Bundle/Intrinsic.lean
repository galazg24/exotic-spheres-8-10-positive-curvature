/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.InvarianceDOmega
import ExoticSpheres8And10.Curvature.Prop31.Bundle.ModelInterval

/-! # [HLY] Prop. 3.1 with intrinsic, pointwise hypotheses

Using the invariance results of `PB_Invariance` and `PB_InvarianceD`:
* `curvNormSq C g y` and `dcurvNormSq C g y` are `Σ(Ω_{ij}^a)²` and `Σ((D_kΩ)_{ij}^a)²` at
  `y`. They are computed in a chosen orthonormal frame and trivialisation near `π y`, and they
  equal the value in **every** orthonormal frame and every trivialisation (`curvNormSq_eq`,
  `dcurvNormSq_eq`). These are [GG]'s `2|Ω|²` and `2|DΩ|²`, since [GG] sums over `i < j`.
* `hessAt g φ b v w` is the Hessian at a point. It equals `hessF g φ X Y b` for every pair of
  fields differentiable at `b` with values `v`, `w` (`hessAt_eq`).
* **`hly_prop31_global_intrinsic`** is `hly_prop31_global` with the pointwise hypotheses
  `|Ω|² ≤ M₀²`, `|DΩ|² ≤ M₁²` and `−Hess φ ≥ Λ g`.
* `hly_prop31_intrinsic_interval` is its non-vacuity model on `[−1, 1] × S³`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

section Frames

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]

/-- A smooth `g`-orthonormal frame on an open set. -/
def IsONFrameOn (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) (U : Set B)
    (e : Fin (finrank ℝ E) → Π b : B, TangentSpace I b) : Prop :=
  IsOpen U ∧ (∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b) ∧
    (∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j)

open Classical in
/-- A chosen smooth orthonormal frame near `b` (junk if none exists). -/
def frameAt (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) (b : B) :
    Set B × (Fin (finrank ℝ E) → Π b : B, TangentSpace I b) :=
  if h : ∃ q : Set B × (Fin (finrank ℝ E) → Π b : B, TangentSpace I b),
      b ∈ q.1 ∧ IsONFrameOn g q.1 q.2 then Classical.choose h else (∅, fun _ _ => 0)

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)

include hsg hpg hgs in
theorem frameAt_spec (b : B) :
    b ∈ (frameAt g b).1 ∧ IsONFrameOn g (frameAt g b).1 (frameAt g b).2 := by
  have hex : ∃ q : Set B × (Fin (finrank ℝ E) → Π b : B, TangentSpace I b),
      b ∈ q.1 ∧ IsONFrameOn g q.1 q.2 := by
    obtain ⟨U, hUo, hbU, e, he, hor⟩ := exists_orthonormal_frame_near hsg hpg hgs rfl b
    exact ⟨(U, e), hbU, hUo, he, hor⟩
  rw [frameAt, dif_pos hex]
  exact Classical.choose_spec hex

/-- The constant-coefficient extension of `v ∈ T_bB` in the chosen frame. -/
def extF (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) (b : B)
    (v : TangentSpace I b) : Π z : B, TangentSpace I z :=
  fun z => ∑ i, g b v ((frameAt g b).2 i b) • (frameAt g b).2 i z

/-- **The Hessian at a point**: `Hess φ_b(v, w)`. -/
def hessAt (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) (φ : B → ℝ) (b : B)
    (v w : TangentSpace I b) : ℝ :=
  hessF g φ (extF g b v) (extF g b w) b

include hsg hpg hgs in
theorem extF_self (b : B) (v : TangentSpace I b) : extF g b v b = v :=
  (span_base_frame hpg (frameAt_spec hsg hpg hgs b).2.2.2 rfl
    (frameAt_spec hsg hpg hgs b).1 v).symm

include hsg hpg hgs in
theorem contMDiffAt_extF (b : B) (v : TangentSpace I b) :
    ContMDiffAt I I.tangent ∞ (T% (extF g b v)) b :=
  ContMDiffAt.sum_section (t := fun i z => g b v ((frameAt g b).2 i b) • (frameAt g b).2 i z)
    fun i _ => contMDiffAt_const.smul_section
      ((frameAt_spec hsg hpg hgs b).2.2.1 i b (frameAt_spec hsg hpg hgs b).1)

theorem hessF_left_congr {φ : B → ℝ} {X X' Y : Π x : B, TangentSpace I x} {b : B}
    (h : X b = X' b) : hessF g φ X Y b = hessF g φ X' Y b := by
  unfold hessF; rw [h]

include hsg hpg hgs in
/-- **`hessF` is pointwise**: it is `hessAt` of the values. -/
theorem hessAt_eq {φ : B → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {b : B}
    (X Y : Π x : B, TangentSpace I x) (hY : MDiffAt (T% Y) b) :
    hessF g φ X Y b = hessAt g φ b (X b) (Y b) := by
  obtain ⟨hb, hUo, he, hor⟩ := frameAt_spec hsg hpg hgs b
  have hext := contMDiffAt_extF hsg hpg hgs b (Y b)
  unfold hessAt
  rw [hessF_expand_right hsg hpg hgs hUo he hor rfl hφ hb X Y hY,
    hessF_expand_right hsg hpg hgs hUo he hor rfl hφ hb (extF g b (X b)) (extF g b (Y b))
      (hext.mdifferentiableAt (by simp)), extF_self hsg hpg hgs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hessF_left_congr (X' := extF g b (X b)) (extF_self hsg hpg hgs b (X b)).symm]

end Frames

section Norms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P]
  [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb)

namespace S3Connection

/-- `Σ_{i,j,a}(Ω_{ij}^a)²` at `y`, in the chosen frame and the trivialisation at `π y`. -/
def curvNormSq (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) (y : P) : ℝ :=
  Prop31Algebra.OmSq (C.ΩP (frameAt g (Pb.proj y)).2 (Pb.proj y) y)

/-- `Σ_{k,i,j,a}((D_kΩ)_{ij}^a)²` at `y`, in the chosen frame and the trivialisation at `π y`. -/
def dcurvNormSq (g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) (y : P) : ℝ :=
  ∑ k, ∑ i, ∑ j, ∑ c,
    C.DΩP g (frameAt g (Pb.proj y)).2 (fun _ => (1 : ℝ)) (Pb.proj y) y k i j c ^ 2

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)

include hsg hpg hgs in
/-- **`|Ω|²` is intrinsic**: every orthonormal frame and every trivialisation give `curvNormSq`. -/
theorem curvNormSq_eq {b₀ : B} {U : Set B} {e : Fin (finrank ℝ E) → Π b : B, TangentSpace I b}
    (hUo : IsOpen U) (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
    (hor : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) {y : P}
    (hy0 : Pb.proj y ∈ Pb.nbhd b₀) (hyU : Pb.proj y ∈ U) :
    Prop31Algebra.OmSq (C.ΩP e b₀ y) = C.curvNormSq g y := by
  have hspec := frameAt_spec hsg hpg hgs (Pb.proj y)
  unfold curvNormSq
  generalize frameAt g (Pb.proj y) = fr at hspec ⊢
  obtain ⟨hb, hUo', he', hor'⟩ := hspec
  have hg : C.ΩP e b₀ y = C.ΩP e (Pb.proj y) y := by
    funext i j a
    exact C.tΩ_gauge hy0 (Pb.mem_nbhd _) e (fun k => ev_smooth_of_mem hUo he hyU k) i j a
  rw [hg]
  exact C.OmSq_frame hsg hpg hgs hUo' hUo he' he hor' hor rfl (Pb.proj y) (Pb.mem_nbhd _) hb
    hyU

include hsg hpg hgs in
/-- **`|DΩ|²` is intrinsic**: every orthonormal frame and every trivialisation give
`dcurvNormSq`. -/
theorem dcurvNormSq_eq {b₀ : B} {U : Set B} {e : Fin (finrank ℝ E) → Π b : B, TangentSpace I b}
    (hUo : IsOpen U) (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
    (hor : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j) {y : P}
    (hy0 : Pb.proj y ∈ Pb.nbhd b₀) (hyU : Pb.proj y ∈ U) (r : B → ℝ) :
    ∑ k, ∑ i, ∑ j, ∑ c, C.DΩP g e r b₀ y k i j c ^ 2 = C.dcurvNormSq g y := by
  have hspec := frameAt_spec hsg hpg hgs (Pb.proj y)
  unfold dcurvNormSq
  generalize frameAt g (Pb.proj y) = fr at hspec ⊢
  obtain ⟨hb, hUo', he', hor'⟩ := hspec
  rw [C.DΩP_gauge hUo he hy0 (Pb.mem_nbhd _) hyU r, C.DΩP_r _ r (fun _ => 1)]
  exact C.DΩsq_frame hsg hpg hgs hUo' hUo he' he hor' hor rfl (Pb.proj y) (Pb.mem_nbhd _) hb hyU
    (fun _ => 1)

end S3Connection

end Norms

section Global

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P]
  [IsManifold (I.prod (𝓡 3)) ∞ P]

/-- **[HLY] Prop. 3.1, global form, with intrinsic pointwise hypotheses.**
* `curvNormSq ≤ 2M₀²` is [GG]'s `|Ω| ≤ M₀`, and `dcurvNormSq ≤ 2M₁²` is `|DΩ| ≤ M₁`. Both
  quantities are frame- and trivialisation-independent (`curvNormSq_eq`, `dcurvNormSq_eq`).
* `hessAt` is the Hessian at a point (`hessAt_eq`).

The conclusion is that of `hly_prop31_global`. -/
theorem hly_prop31_global_intrinsic [CompactSpace B]
    {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
    (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)
    {κ : ℝ} (hκ : 0 < κ)
    (hsec : ∀ (b : B) (u v : TangentSpace I b), LinearIndependent ℝ ![u, v] →
      κ ≤ sectionalCurvatureAt hsg hpg (IsContMDiffMetricSection.of_le' hgs two_le_infty_ω) b u v)
    {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {φ : B → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {M0 M1 Λ : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hΩ : ∀ y : P, C.curvNormSq g y ≤ 2 * M0 ^ 2)
    (hDΩ : ∀ y : P, C.dcurvNormSq g y ≤ 2 * M1 ^ 2)
    (hHess : ∀ (b : B) (v : TangentSpace I b), Λ * g b v v ≤ -hessAt g φ b v v)
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 ≤ Λ) :
    ∃ ε₀ > 0, ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      ∀ (y : P) (u v : TangentSpace (I.prod (𝓡 3)) y), LinearIndependent ℝ ![u, v] →
        0 < sectionalCurvatureAt (C.isSymm_connMetric hsg φ ε) (C.isPosDef_connMetric hpg φ hε)
          (IsContMDiffMetricSection.of_le' (C.isContMDiffMetricSection_connMetric hgs hφ ε)
            two_le_infty_ω) y u v := by
  refine hly_prop31_global hsg hpg hgs rfl hκ hsec C hφ hM0 hM1 ?_ ?_ ?_ hΛ
  · intro b₀ U e hUo hUn he hor y hy
    rw [C.curvNormSq_eq hsg hpg hgs hUo he hor (hUn hy) hy]
    exact hΩ y
  · intro b₀ U e hUo hUn he hor y hy
    rw [C.dcurvNormSq_eq hsg hpg hgs hUo he hor (hUn hy) hy]
    exact hDΩ y
  · intro b X hX
    rw [hessAt_eq hsg hpg hgs hφ X X (hX.mdifferentiableAt (by simp))]
    exact hHess b (X b)

end Global

/-! ## The interval model, for the intrinsic form -/

section IntervalIntrinsic

local notation "Iv" => CDisk 1 (1 : ℝ)

theorem curvNormSq_interval (y : Iv × S3) :
    (flatConn (𝓡∂ 1) Iv).curvNormSq gIv y = 0 := OmSq_flat _ _ _

theorem dcurvNormSq_interval (y : Iv × S3) :
    (flatConn (𝓡∂ 1) Iv).dcurvNormSq gIv y = 0 := by
  simp only [S3Connection.dcurvNormSq, DΩP_flat]
  norm_num

theorem hessAt_interval (b : Iv) (v : TangentSpace (𝓡∂ 1) b) :
    1024 * gIv b v v ≤ -hessAt gIv φIv b v v := by
  have h := hessF_model b (extF gIv b v)
    (contMDiffAt_extF isSymm_gIv isPosDef_gIv isContMDiffMetricSection_gIv b v)
  rwa [extF_self isSymm_gIv isPosDef_gIv isContMDiffMetricSection_gIv] at h

/-- **Non-vacuity of `hly_prop31_global_intrinsic`** on `[−1, 1] × S³`. -/
theorem hly_prop31_intrinsic_interval :
    ∃ ε₀ > 0, ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      ∀ (y : Iv × S3) (u v : TangentSpace ((𝓡∂ 1).prod (𝓡 3)) y), LinearIndependent ℝ ![u, v] →
        0 < sectionalCurvatureAt ((flatConn (𝓡∂ 1) Iv).isSymm_connMetric isSymm_gIv φIv ε)
          ((flatConn (𝓡∂ 1) Iv).isPosDef_connMetric isPosDef_gIv φIv hε)
          (IsContMDiffMetricSection.of_le'
            ((flatConn (𝓡∂ 1) Iv).isContMDiffMetricSection_connMetric
              isContMDiffMetricSection_gIv contMDiff_φIv ε) two_le_infty_ω) y u v :=
  hly_prop31_global_intrinsic isSymm_gIv isPosDef_gIv isContMDiffMetricSection_gIv one_pos
    (sec_model_vacuous 1) (flatConn (𝓡∂ 1) Iv) contMDiff_φIv (M0 := 0) (M1 := 0) (Λ := 1024)
    le_rfl le_rfl (fun y => by rw [curvNormSq_interval]; norm_num)
    (fun y => by rw [dcurvNormSq_interval]; norm_num) hessAt_interval (by norm_num)

end IntervalIntrinsic

end

end ExoticSpheres8And10
