/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.Prop31.Bundle.Blocks
import ExoticSpheres8And10.Curvature.HLYModel.Package

/-! # D2's interface at a point of a principal `S³`-bundle with connection

At `y ∈ π⁻¹(U)`, with the connection-metric frame `Fr = (X_i, E_a)`:
* `vecFP y v = Σ_i v.1 i X_i + Σ_a v.2 a E_a`;
* `RmPP y v w z t`: the frame-component curvature. It is `RiemannianGeometry`'s Riemann tensor of `G_ε` on
  `vecFP` (`riemannTensorAt_vecFP`), so it is multilinear with `RiemannianGeometry`'s symmetries;
* D2's six block hypotheses, with the data at `y`:
  - `ΩP = Ω_{ij}^a(y)`, `ϑP = ϑ(y)`, `rP = r(π y)`;
  - `NP` and `DΩP`, from the frame derivatives;
  - `KBP`, the base curvature in the frame `e`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Module

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)


section CompPackage

/-! ## The six blocks from frame components, abstractly

`RmC R` is the 4-linear form with frame components `R`. If the components satisfy HLY's six
block formulas, `RmC R` satisfies D2's six block hypotheses. This is pure algebra. -/

variable {n : ℕ} (R : Fin n ⊕ Fin 3 → Fin n ⊕ Fin 3 → Fin n ⊕ Fin 3 → Fin n ⊕ Fin 3 → ℝ)

/-- The 4-linear form with frame components `R`. -/
def RmC (v w z t : Prop31Algebra.Tv n) : ℝ :=
  ∑ α, ∑ β, ∑ γ, ∑ δ, coef v α * coef w β * coef z γ * coef t δ * R α β γ δ

/-- `K_B(X, Y) = R^B(X, Y, Y, X)`, in components. -/
def KBf (RB : Fin n → Fin n → Fin n → Fin n → ℝ) (X Y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, X i * Y j * Y k * X l * RB i j k l

variable {R}

theorem RmC_HVHV {N : Fin n → Fin n → ℝ} {Ω : Fin n → Fin n → Fin 3 → ℝ} {r : ℝ}
    (h : ∀ i j a c, R (.inl i) (.inr a) (.inr c) (.inl j) =
      N i j * kron a c + r ^ 2 / 4 * ∑ k, Ω i k c * Ω j k a - 1 / 4 * ∑ d, Prop31Algebra.cst a c d * Ω i j d)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    RmC R (Prop31Algebra.hv X) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.hv Y) =
      ∑ i, ∑ j, ∑ a, ∑ c, X i * U a * V c * Y j * Prop31Algebra.FHVHV N Ω r i j a c := by
  simp only [RmC, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  rfl

theorem RmC_HHVV {Ω : Fin n → Fin n → Fin 3 → ℝ} {r : ℝ}
    (h : ∀ i j a c, R (.inl i) (.inl j) (.inr a) (.inr c) =
      r ^ 2 / 4 * ∑ k, (Ω i k a * Ω j k c - Ω j k a * Ω i k c) + 1 / 2 * ∑ d, Prop31Algebra.cst a c d * Ω i j d)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    RmC R (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.vv U) (Prop31Algebra.vv V) =
      ∑ i, ∑ j, ∑ a, ∑ c, X i * Y j * U a * V c * Prop31Algebra.FHHVV Ω r i j a c := by
  simp only [RmC, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, h]
  rfl

theorem RmC_HVVV {Ω : Fin n → Fin n → Fin 3 → ℝ} {ϑ : Fin n → ℝ} {r : ℝ}
    (h : ∀ i a c d, R (.inl i) (.inr a) (.inr c) (.inr d) =
      r / 2 * ∑ k, ϑ k * (kron a c * Ω i k d - kron a d * Ω i k c))
    (X : Fin n → ℝ) (U V Z : Fin 3 → ℝ) :
    RmC R (Prop31Algebra.hv X) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.vv Z) =
      ∑ i, ∑ a, ∑ c, ∑ d, X i * U a * V c * Z d * Prop31Algebra.FHVVV Ω ϑ r i a c d := by
  simp only [RmC, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, h]
  rfl

theorem RmC_HHHV {Ω : Fin n → Fin n → Fin 3 → ℝ} {DΩ : Fin n → Fin n → Fin n → Fin 3 → ℝ}
    {ϑ : Fin n → ℝ} {r : ℝ}
    (h : ∀ i j k a, R (.inl i) (.inl j) (.inl k) (.inr a) =
      -(r / 2) * (DΩ i j k a - DΩ j i k a) - r / 2 * (ϑ i * Ω j k a - ϑ j * Ω i k a) +
        r * ϑ k * Ω i j a)
    (X Y Z : Fin n → ℝ) (U : Fin 3 → ℝ) :
    RmC R (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.hv Z) (Prop31Algebra.vv U) =
      ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * Z k * U a * Prop31Algebra.FHHHV Ω DΩ ϑ r i j k a := by
  simp only [RmC, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, h]
  rfl

theorem RmC_VVVV {s : ℝ}
    (h : ∀ a c d e, R (.inr a) (.inr c) (.inr d) (.inr e) =
      s * (kron c d * kron a e - kron a d * kron c e))
    (U V Z T : Fin 3 → ℝ) :
    RmC R (Prop31Algebra.vv (n := n) U) (Prop31Algebra.vv V) (Prop31Algebra.vv Z) (Prop31Algebra.vv T) =
      s * (Prop31Algebra.dot V Z * Prop31Algebra.dot U T - Prop31Algebra.dot U Z * Prop31Algebra.dot V T) := by
  simp only [RmC, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, h]
  simp only [Fin.sum_univ_three, Prop31Algebra.dot, kron]
  simp
  ring

theorem RmC_HHHH {RB : Fin n → Fin n → Fin n → Fin n → ℝ} {Ω : Fin n → Fin n → Fin 3 → ℝ} {r : ℝ}
    (hΩ : ∀ i j a, Ω j i a = -Ω i j a)
    (h : ∀ i j k l, R (.inl i) (.inl j) (.inl k) (.inl l) =
      RB i j k l + r ^ 2 / 4 * ∑ d, (Ω i k d * Ω j l d - Ω j k d * Ω i l d) +
        r ^ 2 / 2 * ∑ d, Ω i j d * Ω k l d)
    (X Y : Fin n → ℝ) :
    RmC R (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.hv Y) (Prop31Algebra.hv X) =
      KBf RB X Y - 3 / 4 * r ^ 2 * ∑ c, Prop31Algebra.ΩXY Ω X Y c ^ 2 := by
  simp only [RmC, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, h]
  have key : ∀ i j k l : Fin n, X i * Y j * Y k * X l *
      (RB i j k l + r ^ 2 / 4 * ∑ d, (Ω i k d * Ω j l d - Ω j k d * Ω i l d) +
        r ^ 2 / 2 * ∑ d, Ω i j d * Ω k l d) =
      X i * Y j * Y k * X l * RB i j k l +
        r ^ 2 / 4 * (X i * Y j * Y k * X l * ∑ d, Ω i k d * Ω j l d) -
        r ^ 2 / 4 * (X i * Y j * Y k * X l * ∑ d, Ω j k d * Ω i l d) +
        r ^ 2 / 2 * (X i * Y j * Y k * X l * ∑ d, Ω i j d * Ω k l d) := by
    intro i j k l; rw [Finset.sum_sub_distrib]; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl
    fun k _ => Finset.sum_congr rfl fun l _ => key i j k l]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [pair13d Ω Ω X Y Y X, pair23d Ω Ω X Y Y X, pair12d Ω Ω X Y Y X]
  have hanti : ∀ d, ∀ i j, (fun a b => Ω a b d) j i = -(fun a b => Ω a b d) i j :=
    fun d i j => hΩ i j d
  have hYX : ∀ d, bf2 (fun a b => Ω a b d) Y X = -bf2 (fun a b => Ω a b d) X Y :=
    fun d => bf2_anti (hanti d) X Y
  have hYY : ∀ d, bf2 (fun a b => Ω a b d) Y Y = 0 := fun d => bf2_anti_self (hanti d) Y
  have hW : ∀ c, Prop31Algebra.ΩXY Ω X Y c = bf2 (fun a b => Ω a b c) X Y := fun c => rfl
  simp only [hYX, hYY, hW, zero_mul, mul_zero, Finset.sum_const_zero, mul_neg,
    Finset.sum_neg_distrib, sq]
  unfold KBf
  ring

end CompPackage

section Package

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ModelProd H E3) P] [IsManifold (I.prod (𝓡 3)) ∞ P]
  {Pb : PrincipalS3Bundle I B P} (C : S3Connection Pb) {n : ℕ}

namespace S3Connection

variable {g : Π b : B, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ}
  {e : Fin n → Π b : B, TangentSpace I b} {U : Set B} {r : B → ℝ}

variable (g e r) in
/-- The vector `Σ_i v.1 i X_i + Σ_a v.2 a E_a` at `y`. -/
def vecFP (b₀ : B) (y : P) (v : Prop31Algebra.Tv n) : TangentSpace (I.prod (𝓡 3)) y :=
  ∑ α, coef v α • C.Fr b₀ e r α y

variable (g e r) in
/-- The frame-component curvature at `y`. -/
def RmPP (b₀ : B) (y : P) : Prop31Algebra.Tv n → Prop31Algebra.Tv n → Prop31Algebra.Tv n → Prop31Algebra.Tv n → ℝ :=
  RmC (RmF (tcB (Pb := Pb) g e) (C.tΩ b₀ e) (trf (Pb := Pb) r) (tϑ (Pb := Pb) r e) (C.Fr b₀ e r) y)

theorem RmPP_add1 (b₀ : B) (y : P) (v v' w z t : Prop31Algebra.Tv n) :
    C.RmPP g e r b₀ y (v + v') w z t = C.RmPP g e r b₀ y v w z t + C.RmPP g e r b₀ y v' w z t := by
  simp only [RmPP, RmC, coef_add, add_mul, Finset.sum_add_distrib]

theorem RmPP_add2 (b₀ : B) (y : P) (v w w' z t : Prop31Algebra.Tv n) :
    C.RmPP g e r b₀ y v (w + w') z t = C.RmPP g e r b₀ y v w z t + C.RmPP g e r b₀ y v w' z t := by
  simp only [RmPP, RmC, coef_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem RmPP_add3 (b₀ : B) (y : P) (v w z z' t : Prop31Algebra.Tv n) :
    C.RmPP g e r b₀ y v w (z + z') t = C.RmPP g e r b₀ y v w z t + C.RmPP g e r b₀ y v w z' t := by
  simp only [RmPP, RmC, coef_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem RmPP_add4 (b₀ : B) (y : P) (v w z t t' : Prop31Algebra.Tv n) :
    C.RmPP g e r b₀ y v w z (t + t') = C.RmPP g e r b₀ y v w z t + C.RmPP g e r b₀ y v w z t' := by
  simp only [RmPP, RmC, coef_add, add_mul, mul_add, Finset.sum_add_distrib]

variable {φ : B → ℝ} {ε : ℝ}
  (hsg : IsSymm g) (hpg : IsPosDef g) (hgs : IsContMDiffMetricSection E ∞ g)
  (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hε : 0 < ε) (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hr0 : ∀ b, r b ≠ 0)
  (hr2 : ∀ b, r b ^ 2 = ε * Real.exp (ε * φ b)) (b₀ : B) (hUo : IsOpen U)
  (hUn : U ⊆ Pb.nbhd b₀) (he : ∀ i, ∀ b ∈ U, ContMDiffAt I I.tangent ∞ (T% (e i)) b)
  (horthB : ∀ b ∈ U, ∀ i j, g b (e i b) (e j b) = kron i j)
  (hspanB : ∀ b ∈ U, ∀ w : TangentSpace I b, w = ∑ k, g b w (e k b) • e k b)
  (hn : Module.finrank ℝ E = n)

include hsg hpg hgs hφ hε hr hr0 hr2 hUo hUn he horthB hspanB hn in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 4000000 in
/-- **`RmPP` is `RiemannianGeometry`'s Riemann tensor of `G_ε`**, on the vectors `vecFP`. -/
theorem riemannTensorAt_vecFP {y : P} (hy : Pb.proj y ∈ U) (v w z t : Prop31Algebra.Tv n) :
    riemannTensorAt (C.isSymm_connMetric hsg φ ε) (C.isPosDef_connMetric hpg φ hε).isNondegenerate
        (IsContMDiffMetricSection.of_le' (C.isContMDiffMetricSection_connMetric hgs hφ ε)
          two_le_infty_ω) y
        (C.vecFP e r b₀ y v) (C.vecFP e r b₀ y w) (C.vecFP e r b₀ y z) (C.vecFP e r b₀ y t) =
      C.RmPP g e r b₀ y v w z t := by
  have key := C.riemannTensorAt_Fr hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy
  -- linearity in the first slot, through the pair symmetry (direct `map_sum` there does not fire)
  have hfirst : ∀ b c d : TangentSpace (I.prod (𝓡 3)) y,
      riemannTensorAt (C.isSymm_connMetric hsg φ ε)
        (C.isPosDef_connMetric hpg φ hε).isNondegenerate
        (IsContMDiffMetricSection.of_le' (C.isContMDiffMetricSection_connMetric hgs hφ ε)
          two_le_infty_ω) y (∑ α, coef v α • C.Fr b₀ e r α y) b c d =
      ∑ α, coef v α * riemannTensorAt (C.isSymm_connMetric hsg φ ε)
        (C.isPosDef_connMetric hpg φ hε).isNondegenerate
        (IsContMDiffMetricSection.of_le' (C.isContMDiffMetricSection_connMetric hgs hφ ε)
          two_le_infty_ω) y (C.Fr b₀ e r α y) b c d := by
    intro b c d
    rw [riemannTensorAt_pair_symm]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun α _ => by rw [riemannTensorAt_pair_symm]
  unfold vecFP RmPP RmC
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hfirst, key, Finset.mul_sum]
  rw [sum4_rev]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by ring

include hsg hpg hgs hφ hε hr hr0 hr2 hUo hUn he horthB hspanB hn in
theorem RmPP_swap_left {y : P} (hy : Pb.proj y ∈ U) (v w z t : Prop31Algebra.Tv n) :
    C.RmPP g e r b₀ y w v z t = -C.RmPP g e r b₀ y v w z t := by
  rw [← C.riemannTensorAt_vecFP hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy,
    ← C.riemannTensorAt_vecFP hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy]
  exact riemannTensorAt_swap_left _ _ _ _ _ _ _

include hsg hpg hgs hφ hε hr hr0 hr2 hUo hUn he horthB hspanB hn in
theorem RmPP_swap_right {y : P} (hy : Pb.proj y ∈ U) (v w z t : Prop31Algebra.Tv n) :
    C.RmPP g e r b₀ y v w t z = -C.RmPP g e r b₀ y v w z t := by
  rw [← C.riemannTensorAt_vecFP hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy,
    ← C.riemannTensorAt_vecFP hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy]
  exact riemannTensorAt_swap_right _ _ _ _ _ _ _

include hsg hpg hgs hφ hε hr hr0 hr2 hUo hUn he horthB hspanB hn in
theorem RmPP_pair {y : P} (hy : Pb.proj y ∈ U) (v w z t : Prop31Algebra.Tv n) :
    C.RmPP g e r b₀ y z t v w = C.RmPP g e r b₀ y v w z t := by
  rw [← C.riemannTensorAt_vecFP hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy,
    ← C.riemannTensorAt_vecFP hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy]
  exact riemannTensorAt_pair_symm _ _ _ _ _ _ _


/-! ### D2's data at `y`

The base data, at `b = π y`: `N`, the base curvature `R^B`, and their derivative inputs, all
in the frame `e`. The bundle data, at `y`: `Ω`, `dΩ` and `DΩ`. -/

variable (g e) in
/-- `e_l(c^B_{ijk})` at `b`. -/
def dcBB (b : B) (l i j k : Fin n) : ℝ := mvfderiv I (cBb g e i j k) b (e l b)

variable (e r) in
/-- `e_k(ϑ_i)` at `b`. -/
def dϑB (b : B) (k i : Fin n) : ℝ := mvfderiv I (ϑb r e i) b (e k b)

variable (g e r) in
/-- `N_{ij} = −e_i(ϑ_j) − ϑ_iϑ_j − Σ_k Γ^B_{ikj}ϑ_k` at `b`. -/
def NB (b : B) : Fin n → Fin n → ℝ := Nf (cBb g e) (ϑb r e) b (dϑB e r b)

variable (g e) in
/-- The base curvature `R^B_{ijkl}` at `b`, by the frame formula. -/
def RBB (b : B) : Fin n → Fin n → Fin n → Fin n → ℝ := RBf (cBb g e) b (dcBB g e b)

variable (e) in
/-- `Ω_{ij}^a` at `y`. -/
def ΩP (b₀ : B) (y : P) (i j : Fin n) (a : Fin 3) : ℝ := C.tΩ b₀ e i j a y

variable (e r) in
/-- `X_k(Ω_{ij}^c)` at `y`. -/
def dΩP (b₀ : B) (y : P) (k i j : Fin n) (c : Fin 3) : ℝ :=
  mvfderiv (I.prod (𝓡 3)) (C.tΩ b₀ e i j c) y (C.Fr b₀ e r (.inl k) y)

variable (g e r) in
/-- `(D_kΩ)_{ij}^a` at `y`. -/
def DΩP (b₀ : B) (y : P) : Fin n → Fin n → Fin n → Fin 3 → ℝ :=
  DΩf (tcB (Pb := Pb) g e) (C.tΩ b₀ e) y (C.dΩP e r b₀ y)

include hsg hpg hgs hφ hε hr hr2 hUo hUn he horthB hspanB hn in
/-- **[HLY] Prop. 3.1, pointwise, on a principal `S³`-bundle with connection.**
At `y ∈ π⁻¹(U)`, for `RiemannianGeometry`'s curvature of `G_ε`, given D2's quantitative data: `|Ω| ≤ M₀`,
`|DΩ| ≤ M₁`, `N ≥ ν`, `K_B ≥ κ`, and the ε-budget. The six curvature blocks are theorems. -/
theorem prop31_at_P (hrpos : ∀ b, 0 < r b) {y : P} (hy : Pb.proj y ∈ U)
    (ν κ M0 M1 Λ D0 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hκ : 0 < κ)
    (hOm : Prop31Algebra.OmSq (C.ΩP e b₀ y) ≤ 2 * M0 ^ 2)
    (hDOm : ∑ i, ∑ j, ∑ k, ∑ a, C.DΩP g e r b₀ y i j k a ^ 2 ≤ 2 * M1 ^ 2)
    (hν : ∀ x : Fin n → ℝ, ν * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, NB g e r (Pb.proj y) i j * x i * x j)
    (hKB : ∀ X Y, κ * Prop31Algebra.gram X Y ≤ KBf (RBB g e (Pb.proj y)) X Y)
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 / κ * (M1 + 1) ^ 2 ≤ Λ)
    (hr2' : r (Pb.proj y) ^ 2 ≤ 2 * ε)
    (htD : √(∑ k, ϑb r e k (Pb.proj y) ^ 2) ≤ ε * D0 / 2)
    (hνΛ : ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4 ≤ ν)
    (hA2 : 2 * ε * M0 ≤ 1) (hA3 : ε * D0 * M0 ≤ 1) (hB2 : 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ κ)
    (hC1 : ε * D0 ^ 2 ≤ Λ / 4) (hC2 : 2 * ε ^ 3 * D0 ^ 2 ≤ 1)
    (hC3 : 32 * 4 ^ 2 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 ≤ Λ)
    (X Y : Fin n → ℝ) (U₁ V₁ : Fin 3 → ℝ) :
    min (min (κ / 2) (ε * Λ / 8)) (1 / (8 * ε)) * Prop31Algebra.totalGram X Y U₁ V₁ ≤
      riemannTensorAt (C.isSymm_connMetric hsg φ ε) (C.isPosDef_connMetric hpg φ hε).isNondegenerate
        (IsContMDiffMetricSection.of_le' (C.isContMDiffMetricSection_connMetric hgs hφ ε)
          two_le_infty_ω) y
        (C.vecFP e r b₀ y (X, U₁)) (C.vecFP e r b₀ y (Y, V₁)) (C.vecFP e r b₀ y (Y, V₁))
        (C.vecFP e r b₀ y (X, U₁)) := by
  have hr0 : ∀ b, r b ≠ 0 := fun b => (hrpos b).ne'
  rw [C.riemannTensorAt_vecFP hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn hy]
  have hyn := hUn hy
  have hcBdB : ∀ i j k, MDifferentiableAt I 𝓘(ℝ) (cBb g e i j k) (Pb.proj y) :=
    fun i j k => (contMDiffAt_cBb hgs hUo he hy i j k).mdifferentiableAt (by simp)
  have hϑdB : ∀ i, MDifferentiableAt I 𝓘(ℝ) (ϑb r e i) (Pb.proj y) :=
    fun i => (contMDiffAt_ϑb hr hr0 he hy i).mdifferentiableAt (by simp)
  have hrdB : MDifferentiableAt I 𝓘(ℝ) r (Pb.proj y) := (hr _).mdifferentiableAt (by simp)
  have hcBd : ∀ i j k, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (tcB (Pb := Pb) g e i j k) y :=
    fun i j k => (hcBdB i j k).comp y (Pb.mdiffAt_proj y)
  have hΩd : ∀ i j a, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (C.tΩ b₀ e i j a) y :=
    fun i j a => (C.contMDiffAt_tΩ b₀ hUo hUn he hy i j a).mdifferentiableAt (by simp)
  have hrd : MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (trf (Pb := Pb) r) y :=
    hrdB.comp y (Pb.mdiffAt_proj y)
  have hϑd : ∀ i, MDifferentiableAt (I.prod (𝓡 3)) 𝓘(ℝ) (tϑ (Pb := Pb) r e i) y :=
    fun i => (hϑdB i).comp y (Pb.mdiffAt_proj y)
  have hr0y : trf (Pb := Pb) r y ≠ 0 := hr0 _
  have hcB_H : ∀ l i j k, mvfderiv (I.prod (𝓡 3)) (tcB (Pb := Pb) g e i j k) y
      (C.Fr b₀ e r (.inl l) y) = dcBB g e (Pb.proj y) l i j k :=
    fun l i j k => C.mvfderiv_comp_proj_Fr_H (h := cBb g e i j k) b₀ hyn (hcBdB i j k) l
  have hϑ_H : ∀ k i, mvfderiv (I.prod (𝓡 3)) (tϑ (Pb := Pb) r e i) y
      (C.Fr b₀ e r (.inl k) y) = dϑB e r (Pb.proj y) k i :=
    fun k i => C.mvfderiv_comp_proj_Fr_H (h := ϑb r e i) b₀ hyn (hϑdB i) k
  have hr_H : ∀ k, mvfderiv (I.prod (𝓡 3)) (trf (Pb := Pb) r) y (C.Fr b₀ e r (.inl k) y) =
      trf (Pb := Pb) r y * tϑ (Pb := Pb) r e k y := fun k => by
    have h1 := C.mvfderiv_comp_proj_Fr_H (h := r) (e := e) (r := r) b₀ hyn hrdB k
    have h0 := hr0 (Pb.proj y)
    show mvfderiv (I.prod (𝓡 3)) (r ∘ Pb.proj) y (C.Fr b₀ e r (.inl k) y) =
      r (Pb.proj y) * (mvfderiv I r (Pb.proj y) (e k (Pb.proj y)) / r (Pb.proj y))
    rw [h1]
    field_simp
  have hr_V : ∀ a, mvfderiv (I.prod (𝓡 3)) (trf (Pb := Pb) r) y (C.Fr b₀ e r (.inr a) y) = 0 :=
    fun a => C.mvfderiv_comp_proj_Fr_V (h := r) b₀ hrdB a
  have hΩ_V : ∀ a i j c, mvfderiv (I.prod (𝓡 3)) (C.tΩ b₀ e i j c) y (C.Fr b₀ e r (.inr a) y) =
      (trf (Pb := Pb) r y)⁻¹ * ∑ d, C.tΩ b₀ e i j d y * Prop31Algebra.cst d a c :=
    fun a i j c => C.mvfderiv_tΩ_V hr hr0 b₀ hUo hUn he hy i j a c
  have hΩanti : ∀ i j a, C.tΩ b₀ e j i a y = -C.tΩ b₀ e i j a y := fun i j a => C.tΩ_anti b₀ i j a y
  have hcBanti : ∀ i j l, tcB (Pb := Pb) g e j i l y = -tcB (Pb := Pb) g e i j l y :=
    fun i j l => cBb_anti i j l _
  have bHVHV := fun i j a c => RmF_HVHV (cBf := tcB (Pb := Pb) g e) (Ωf := C.tΩ b₀ e) (rf := trf (Pb := Pb) r)
    (ϑf := tϑ (Pb := Pb) r e) (F := C.Fr b₀ e r) (z₀ := y) (dϑ := dϑB e r (Pb.proj y))
    (hΩd := hΩd) (hrd := hrd) (hϑd := hϑd) (hr0 := hr0y) (hr_V := hr_V) (hϑ_H := hϑ_H)
    (hΩ_V := hΩ_V) (hΩanti := hΩanti) i j a c
  have bHHVV := fun i j a c => RmF_HHVV (cBf := tcB (Pb := Pb) g e) (Ωf := C.tΩ b₀ e) (rf := trf (Pb := Pb) r)
    (ϑf := tϑ (Pb := Pb) r e) (F := C.Fr b₀ e r) (z₀ := y) (hrd := hrd) (hr0 := hr0y) (hΩanti := hΩanti) i j a c
  have bHVVV := fun i a c d => RmF_HVVV (cBf := tcB (Pb := Pb) g e) (Ωf := C.tΩ b₀ e) (rf := trf (Pb := Pb) r)
    (ϑf := tϑ (Pb := Pb) r e) (F := C.Fr b₀ e r) (z₀ := y) (hrd := hrd) (hr0 := hr0y) (hr_H := hr_H) i a c d
  have bHHHV := fun i j k a => RmF_HHHV (cBf := tcB (Pb := Pb) g e) (Ωf := C.tΩ b₀ e) (rf := trf (Pb := Pb) r)
    (ϑf := tϑ (Pb := Pb) r e) (F := C.Fr b₀ e r) (z₀ := y)
    (dΩ := C.dΩP e r b₀ y) (hrd := hrd) (hΩd := hΩd) (hr_H := hr_H) (hΩ_H := fun k i j c => rfl)
    (hcBanti := hcBanti) i j k a
  have bVVVV := fun a c d e' => RmF_VVVV (cBf := tcB (Pb := Pb) g e) (Ωf := C.tΩ b₀ e) (rf := trf (Pb := Pb) r)
    (ϑf := tϑ (Pb := Pb) r e) (F := C.Fr b₀ e r) (z₀ := y) (hrd := hrd) (hr0 := hr0y)
    (hr_V := hr_V) a c d e'
  have bHHHH := fun i j k l => RmF_HHHH (cBf := tcB (Pb := Pb) g e) (Ωf := C.tΩ b₀ e) (rf := trf (Pb := Pb) r)
    (ϑf := tϑ (Pb := Pb) r e) (F := C.Fr b₀ e r) (z₀ := y) (dcB := dcBB g e (Pb.proj y))
    (hcBd := hcBd) (hcB_H := hcB_H) i j k l
  have hS : 0 ≤ ∑ k, ϑb r e k (Pb.proj y) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  exact Prop31Algebra.prop31_pointwise (C.RmPP g e r b₀ y)
    (C.RmPP_add1 b₀ y) (C.RmPP_add2 b₀ y) (C.RmPP_add3 b₀ y) (C.RmPP_add4 b₀ y)
    (fun a b c d => C.RmPP_swap_left hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn
      hy a b c d)
    (fun a b c d => C.RmPP_swap_right hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn
      hy a b c d)
    (fun a b c d => C.RmPP_pair hsg hpg hgs hφ hε hr hr0 hr2 b₀ hUo hUn he horthB hspanB hn
      hy a b c d)
    (NB g e r (Pb.proj y)) (C.ΩP e b₀ y) (C.DΩP g e r b₀ y) (fun k => ϑb r e k (Pb.proj y))
    (KBf (RBB g e (Pb.proj y))) (r (Pb.proj y)) (√(∑ k, ϑb r e k (Pb.proj y) ^ 2)) ν κ M0 M1 ε Λ D0
    (hrpos _) (Real.sqrt_nonneg _) hM0 hM1 hκ hε hΩanti (Real.sq_sqrt hS).symm hOm hDOm hν hKB
    (RmC_HHHH (RB := RBB g e (Pb.proj y)) (Ω := C.ΩP e b₀ y) (r := r (Pb.proj y)) hΩanti bHHHH)
    (fun X U V Y => RmC_HVHV (N := NB g e r (Pb.proj y)) (Ω := C.ΩP e b₀ y) (r := r (Pb.proj y))
      bHVHV X Y U V)
    (RmC_HHVV (Ω := C.ΩP e b₀ y) (r := r (Pb.proj y)) bHHVV)
    (RmC_HVVV (Ω := C.ΩP e b₀ y) (ϑ := fun k => ϑb r e k (Pb.proj y)) (r := r (Pb.proj y)) bHVVV)
    (RmC_HHHV (Ω := C.ΩP e b₀ y) (DΩ := C.DΩP g e r b₀ y) (ϑ := fun k => ϑb r e k (Pb.proj y))
      (r := r (Pb.proj y)) bHHHV)
    (fun U V Z T => by
      rw [Real.sq_sqrt hS]
      exact RmC_VVVV (s := 1 / r (Pb.proj y) ^ 2 - ∑ k, ϑb r e k (Pb.proj y) ^ 2) bVVVV U V Z T)
    hΛ hr2' htD hνΛ hA2 hA3 hB2 hC1 hC2 hC3 X Y U₁ V₁

end S3Connection

end Package

end

end ExoticSpheres8And10
