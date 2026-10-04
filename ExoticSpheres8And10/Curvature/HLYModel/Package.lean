/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Curvature.HLYModel.BlocksCentre
import ExoticSpheres8And10.Curvature.Prop31.Pointwise
import RiemannianGeometry.RiemannSymmetries

/-! # §4, HLY model: the curvature blocks in D2's form

D2's `prop31_pointwise` takes a quadrilinear `Rm` on `Tv n = ℝⁿ × ℝ³` with the curvature
symmetries and the six block formulas. Here that `Rm` is **`RiemannianGeometry`'s Riemann tensor** of the connection
metric `GH`, read in the frame `X_i, E_a` at the point `(0, u)`:

* `vecF p v = Σ_i v.1 i X_i + Σ_a v.2 a E_a`;
* `RmP p v w y z`, the frame-component expression;
* `riemannTensorAt_vecF`: `riemannTensorAt (vecF v) (vecF w) (vecF y) (vecF z) = RmP v w y z`;
* `RmP_add*`, `RmP_swap*`, `RmP_pair`: multilinearity and symmetries, the latter from `RiemannianGeometry`;
* `RmP_HVHV` … `RmP_HHHH`: D2's block hypotheses, with `N = N0`, `Ω = Ω0`, `DΩ = DΩ0`,
  `ϑ = ϑ0`, `KB = gram` and `t² = Σ ϑ0²`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

/-! ## Contraction lemmas -/

section Contract

variable {ι : Type*} [Fintype ι]

/-- The bilinear form `B_f(x, y) = Σ_{i,j} f_{ij} x_i y_j` (D2's `ΩXY` shape). -/
def bf2 (f : ι → ι → ℝ) (x y : ι → ℝ) : ℝ := ∑ i, ∑ j, f i j * x i * y j

theorem bf2_swap (f : ι → ι → ℝ) (x y : ι → ℝ) : bf2 f y x = bf2 (fun i j => f j i) x y := by
  unfold bf2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bf2_anti {f : ι → ι → ℝ} (hf : ∀ i j, f j i = -f i j) (x y : ι → ℝ) :
    bf2 f y x = -bf2 f x y := by
  rw [bf2_swap]
  unfold bf2
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hf]; ring

theorem bf2_anti_self {f : ι → ι → ℝ} (hf : ∀ i j, f j i = -f i j) (x : ι → ℝ) :
    bf2 f x x = 0 := by
  have := bf2_anti hf x x
  linarith

theorem bf2_kron [DecidableEq ι] (x y : ι → ℝ) : bf2 kron x y = Prop31Algebra.dot x y := by
  unfold bf2 Prop31Algebra.dot
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [kron, ite_mul]

theorem pair13 (f g : ι → ι → ℝ) (x1 x2 x3 x4 : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, x1 i * x2 j * x3 k * x4 l * (f i k * g j l) =
      bf2 f x1 x3 * bf2 g x2 x4 := by
  unfold bf2
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem pair23 (f g : ι → ι → ℝ) (x1 x2 x3 x4 : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, x1 i * x2 j * x3 k * x4 l * (f j k * g i l) =
      bf2 f x2 x3 * bf2 g x1 x4 := by
  rw [mul_comm (bf2 f x2 x3)]
  unfold bf2
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem pair12 (f g : ι → ι → ℝ) (x1 x2 x3 x4 : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, x1 i * x2 j * x3 k * x4 l * (f i j * g k l) =
      bf2 f x1 x2 * bf2 g x3 x4 := by
  unfold bf2
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => by ring

variable {κ : Type*} [Fintype κ]

theorem pair13d (F G : ι → ι → κ → ℝ) (x1 x2 x3 x4 : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, x1 i * x2 j * x3 k * x4 l * ∑ d, F i k d * G j l d =
      ∑ d, bf2 (fun a b => F a b d) x1 x3 * bf2 (fun a b => G a b d) x2 x4 := by
  simp_rw [Finset.mul_sum]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset κ))]
  exact Finset.sum_congr rfl fun d _ => pair13 _ _ x1 x2 x3 x4

theorem pair23d (F G : ι → ι → κ → ℝ) (x1 x2 x3 x4 : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, x1 i * x2 j * x3 k * x4 l * ∑ d, F j k d * G i l d =
      ∑ d, bf2 (fun a b => F a b d) x2 x3 * bf2 (fun a b => G a b d) x1 x4 := by
  simp_rw [Finset.mul_sum]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset κ))]
  exact Finset.sum_congr rfl fun d _ => pair23 _ _ x1 x2 x3 x4

theorem pair12d (F G : ι → ι → κ → ℝ) (x1 x2 x3 x4 : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, x1 i * x2 j * x3 k * x4 l * ∑ d, F i j d * G k l d =
      ∑ d, bf2 (fun a b => F a b d) x1 x2 * bf2 (fun a b => G a b d) x3 x4 := by
  simp_rw [Finset.mul_sum]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset κ))]
  exact Finset.sum_congr rfl fun d _ => pair12 _ _ x1 x2 x3 x4

theorem sum4_rev (f : ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm

end Contract

/-! ## `RiemannianGeometry`'s curvature of `GH`, in D2's coordinates -/

section Package

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

/-- The frame coefficients of `v ∈ Tv n = ℝⁿ × ℝ³`. -/
def coef (v : Prop31Algebra.Tv n) : Fin n ⊕ Fin 3 → ℝ := Sum.elim v.1 v.2

theorem coef_add (v w : Prop31Algebra.Tv n) (α : Fin n ⊕ Fin 3) : coef (v + w) α = coef v α + coef w α := by
  rcases α with i | a <;> rfl

theorem coef_hv_inl (X : Fin n → ℝ) (i : Fin n) : coef (Prop31Algebra.hv X) (.inl i) = X i := rfl
theorem coef_hv_inr (X : Fin n → ℝ) (a : Fin 3) : coef (Prop31Algebra.hv X) (.inr a) = 0 := rfl
theorem coef_vv_inl (U : Fin 3 → ℝ) (i : Fin n) : coef (Prop31Algebra.vv (n := n) U) (.inl i) = 0 := rfl
theorem coef_vv_inr (U : Fin 3 → ℝ) (a : Fin 3) : coef (Prop31Algebra.vv (n := n) U) (.inr a) = U a := rfl

variable (b A r) in
/-- The tangent vector `Σ_i v.1 i X_i + Σ_a v.2 a E_a` at `p`. -/
def vecF (p : K × S3) (v : Prop31Algebra.Tv n) : TangentSpace (IN K) p := ∑ α, coef v α • Fr b A r α p

variable (b A r) in
/-- The curvature at `p` in frame components. -/
def RmP (p : K × S3) (v w y z : Prop31Algebra.Tv n) : ℝ :=
  ∑ α, ∑ β, ∑ γ, ∑ δ, coef v α * coef w β * coef y γ * coef z δ * RmA b A r α β γ δ (emb p)

section Hyp

variable (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
  (hr0 : ∀ x, r x ≠ 0)

include hA hAim hr hr0

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RmP` is `RiemannianGeometry`'s Riemann tensor of the connection metric**, on the vectors `vecF`. -/
theorem riemannTensorAt_vecF (p : K × S3) (v w y z : Prop31Algebra.Tv n) :
    riemannTensorAt isSymm_GH (isPosDef_GH (A := A) hr0).isNondegenerate
      (isContMDiffMetricSection_GH hA hr) p (vecF b A r p v) (vecF b A r p w) (vecF b A r p y)
      (vecF b A r p z) = RmP b A r p v w y z := by
  unfold vecF RmP
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, riemannTensorAt_Fr hA hAim hr hr0]
  refine (sum4_rev _).trans ?_
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by ring

theorem RmP_swap_left (p : K × S3) (v w y z : Prop31Algebra.Tv n) :
    RmP b A r p w v y z = -RmP b A r p v w y z := by
  rw [← riemannTensorAt_vecF hA hAim hr hr0, ← riemannTensorAt_vecF hA hAim hr hr0]
  exact riemannTensorAt_swap_left _ _ _ _ _ _ _

theorem RmP_swap_right (p : K × S3) (v w y z : Prop31Algebra.Tv n) :
    RmP b A r p v w z y = -RmP b A r p v w y z := by
  rw [← riemannTensorAt_vecF hA hAim hr hr0, ← riemannTensorAt_vecF hA hAim hr hr0]
  exact riemannTensorAt_swap_right _ _ _ _ _ _ _

theorem RmP_pair (p : K × S3) (v w y z : Prop31Algebra.Tv n) :
    RmP b A r p y z v w = RmP b A r p v w y z := by
  rw [← riemannTensorAt_vecF hA hAim hr hr0, ← riemannTensorAt_vecF hA hAim hr hr0]
  exact riemannTensorAt_pair_symm _ _ _ _ _ _ _

end Hyp

theorem RmP_add1 (p : K × S3) (v v' w y z : Prop31Algebra.Tv n) :
    RmP b A r p (v + v') w y z = RmP b A r p v w y z + RmP b A r p v' w y z := by
  simp only [RmP, coef_add, add_mul, Finset.sum_add_distrib]

theorem RmP_add2 (p : K × S3) (v w w' y z : Prop31Algebra.Tv n) :
    RmP b A r p v (w + w') y z = RmP b A r p v w y z + RmP b A r p v w' y z := by
  simp only [RmP, coef_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem RmP_add3 (p : K × S3) (v w y y' z : Prop31Algebra.Tv n) :
    RmP b A r p v w (y + y') z = RmP b A r p v w y z + RmP b A r p v w y' z := by
  simp only [RmP, coef_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem RmP_add4 (p : K × S3) (v w y z z' : Prop31Algebra.Tv n) :
    RmP b A r p v w y (z + z') = RmP b A r p v w y z + RmP b A r p v w y z' := by
  simp only [RmP, coef_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem emb_zero (u : S3) : emb ((0 : K), u) = ((0 : K), (u : Quaternion ℝ)) := rfl

/-! ## D2's block hypotheses at `(0, u)` -/

section Blocks

variable (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0) (hr : ContDiff ℝ ∞ r)
  (hr0 : ∀ x, r x ≠ 0)

include hA hAim hr hr0

theorem RmP_HVHV (u : S3) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    RmP b A r ((0 : K), u) (Prop31Algebra.hv X) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.hv Y) =
      ∑ i, ∑ j, ∑ a, ∑ c, X i * U a * V c * Y j *
        Prop31Algebra.FHVHV (N0 b r) (Ω0 b A (u : Quaternion ℝ)) (r 0) i j a c := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_zero,
    RmA_HVHV hA hAim hr hr0 _ (normSq_sphere u)]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  rfl

theorem RmP_HHVV (u : S3) (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    RmP b A r ((0 : K), u) (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.vv U) (Prop31Algebra.vv V) =
      ∑ i, ∑ j, ∑ a, ∑ c, X i * Y j * U a * V c *
        Prop31Algebra.FHHVV (Ω0 b A (u : Quaternion ℝ)) (r 0) i j a c := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_zero,
    RmA_HHVV hA hAim hr hr0 _ (normSq_sphere u)]
  rfl

theorem RmP_HVVV (u : S3) (X : Fin n → ℝ) (U V Z : Fin 3 → ℝ) :
    RmP b A r ((0 : K), u) (Prop31Algebra.hv X) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.vv Z) =
      ∑ i, ∑ a, ∑ c, ∑ d, X i * U a * V c * Z d *
        Prop31Algebra.FHVVV (Ω0 b A (u : Quaternion ℝ)) (ϑ0 b r) (r 0) i a c d := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_zero,
    RmA_HVVV hA hAim hr hr0 _ (normSq_sphere u)]
  rfl

theorem RmP_HHHV (u : S3) (X Y Z : Fin n → ℝ) (U : Fin 3 → ℝ) :
    RmP b A r ((0 : K), u) (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.hv Z) (Prop31Algebra.vv U) =
      ∑ i, ∑ j, ∑ k, ∑ a, X i * Y j * Z k * U a *
        Prop31Algebra.FHHHV (Ω0 b A (u : Quaternion ℝ)) (DΩ0 b A r u) (ϑ0 b r) (r 0) i j k a := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_zero,
    RmA_HHHV hA hAim hr hr0 _ (normSq_sphere u)]
  rfl

theorem RmP_VVVV (u : S3) (U V Z T : Fin 3 → ℝ) :
    RmP b A r ((0 : K), u) (Prop31Algebra.vv U) (Prop31Algebra.vv V) (Prop31Algebra.vv Z) (Prop31Algebra.vv T) =
      (1 / r 0 ^ 2 - ∑ k, ϑ0 b r k ^ 2) *
        (Prop31Algebra.dot V Z * Prop31Algebra.dot U T - Prop31Algebra.dot U Z * Prop31Algebra.dot V T) := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_zero,
    RmA_VVVV hA hAim hr hr0 _ (normSq_sphere u)]
  simp only [Fin.sum_univ_three, Prop31Algebra.dot, kron]
  simp
  ring

theorem RmP_HHHH (u : S3) (X Y : Fin n → ℝ) :
    RmP b A r ((0 : K), u) (Prop31Algebra.hv X) (Prop31Algebra.hv Y) (Prop31Algebra.hv Y) (Prop31Algebra.hv X) =
      Prop31Algebra.gram X Y - 3 / 4 * r 0 ^ 2 * ∑ c, Prop31Algebra.ΩXY (Ω0 b A (u : Quaternion ℝ)) X Y c ^ 2 := by
  simp only [RmP, Fintype.sum_sum_type, coef_hv_inl, coef_hv_inr, coef_vv_inl, coef_vv_inr,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, emb_zero,
    RmA_HHHH hA hAim hr hr0 _ (normSq_sphere u)]
  set Ω := Ω0 b A (u : Quaternion ℝ)
  have key : ∀ i j k l : Fin n, X i * Y j * Y k * X l *
      (kron i l * kron j k - kron i k * kron j l +
        r 0 ^ 2 / 4 * ∑ d, (Ω i k d * Ω j l d - Ω j k d * Ω i l d) +
        r 0 ^ 2 / 2 * ∑ d, Ω i j d * Ω k l d) =
      X i * Y j * Y k * X l * (kron j k * kron i l) - X i * Y j * Y k * X l * (kron i k * kron j l) +
        r 0 ^ 2 / 4 * (X i * Y j * Y k * X l * ∑ d, Ω i k d * Ω j l d) -
        r 0 ^ 2 / 4 * (X i * Y j * Y k * X l * ∑ d, Ω j k d * Ω i l d) +
        r 0 ^ 2 / 2 * (X i * Y j * Y k * X l * ∑ d, Ω i j d * Ω k l d) := by
    intro i j k l; rw [Finset.sum_sub_distrib]; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl
    fun k _ => Finset.sum_congr rfl fun l _ => key i j k l]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [pair23 kron kron X Y Y X, pair13 kron kron X Y Y X, pair13d Ω Ω X Y Y X, pair23d Ω Ω X Y Y X,
    pair12d Ω Ω X Y Y X]
  have hanti : ∀ d, ∀ i j, (fun a b => Ω a b d) j i = -(fun a b => Ω a b d) i j :=
    fun d i j => Ωc_swap i j d _
  have hYX : ∀ d, bf2 (fun a b => Ω a b d) Y X = -bf2 (fun a b => Ω a b d) X Y :=
    fun d => bf2_anti (hanti d) X Y
  have hYY : ∀ d, bf2 (fun a b => Ω a b d) Y Y = 0 := fun d => bf2_anti_self (hanti d) Y
  have hXX : ∀ d, bf2 (fun a b => Ω a b d) X X = 0 := fun d => bf2_anti_self (hanti d) X
  have hW : ∀ c, Prop31Algebra.ΩXY Ω X Y c = bf2 (fun a b => Ω a b c) X Y := fun c => rfl
  simp only [hYX, hYY, hXX, hW, bf2_kron, mul_zero, Finset.sum_const_zero, mul_neg,
    Finset.sum_neg_distrib, Prop31Algebra.gram, Prop31Algebra.dot_comm Y X, sq]
  ring

end Blocks

/-- **[HLY] Prop. 3.1, pointwise, for `RiemannianGeometry`'s curvature of the connection metric**, at the chart
centre `(0, u)`. The curvature blocks are no longer hypotheses: they are the theorems above.
What remains assumed is the quantitative data of D2 (`‖Ω‖ ≤ M₀`, `‖DΩ‖ ≤ M₁`, `N ≥ ν`, the
ε-budget), with `κ = 1` (the round base) and `t = |ϑ|`. -/
theorem hly_prop31_centre (hA : ContDiff ℝ ∞ A) (hAim : ∀ x v, (A x v).re = 0)
    (hr : ContDiff ℝ ∞ r) (hrpos : ∀ x, 0 < r x) (u : S3) (ν M0 M1 ε Λ D0 : ℝ)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hε : 0 < ε)
    (hOm : Prop31Algebra.OmSq (Ω0 b A (u : Quaternion ℝ)) ≤ 2 * M0 ^ 2)
    (hDOm : ∑ i, ∑ j, ∑ k, ∑ a, DΩ0 b A r u i j k a ^ 2 ≤ 2 * M1 ^ 2)
    (hν : ∀ x : Fin n → ℝ, ν * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, N0 b r i j * x i * x j)
    (hΛ : 16 * 4 * M0 ^ 2 + 64 * 4 ^ 2 * (M1 + 1) ^ 2 ≤ Λ)
    (hr2 : r 0 ^ 2 ≤ 2 * ε) (htD : √(∑ k, ϑ0 b r k ^ 2) ≤ ε * D0 / 2)
    (hνΛ : ε * Λ / 2 - ε ^ 2 * D0 ^ 2 / 4 ≤ ν)
    (hA2 : 2 * ε * M0 ≤ 1) (hA3 : ε * D0 * M0 ≤ 1)
    (hB2 : 64 * 4 ^ 2 * ε * M0 ^ 2 ≤ 1)
    (hC1 : ε * D0 ^ 2 ≤ Λ / 4) (hC2 : 2 * ε ^ 3 * D0 ^ 2 ≤ 1)
    (hC3 : 32 * 4 ^ 2 * ε ^ 3 * D0 ^ 2 * M0 ^ 2 ≤ Λ)
    (X Y : Fin n → ℝ) (U V : Fin 3 → ℝ) :
    min (min (1 / 2) (ε * Λ / 8)) (1 / (8 * ε)) * Prop31Algebra.totalGram X Y U V ≤
      riemannTensorAt isSymm_GH (isPosDef_GH (A := A) fun x => (hrpos x).ne').isNondegenerate
        (isContMDiffMetricSection_GH hA hr) ((0 : K), u) (vecF b A r _ (X, U))
        (vecF b A r _ (Y, V)) (vecF b A r _ (Y, V)) (vecF b A r _ (X, U)) := by
  have hr0 : ∀ x, r x ≠ 0 := fun x => (hrpos x).ne'
  rw [riemannTensorAt_vecF hA hAim hr hr0]
  have hS : 0 ≤ ∑ k, ϑ0 b r k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  exact Prop31Algebra.prop31_pointwise (RmP b A r ((0 : K), u))
    (RmP_add1 _) (RmP_add2 _) (RmP_add3 _) (RmP_add4 _)
    (fun a b c d => RmP_swap_left hA hAim hr hr0 _ a b c d)
    (fun a b c d => RmP_swap_right hA hAim hr hr0 _ a b c d)
    (fun a b c d => RmP_pair hA hAim hr hr0 _ a b c d)
    (N0 b r) (Ω0 b A (u : Quaternion ℝ)) (DΩ0 b A r u) (ϑ0 b r) Prop31Algebra.gram (r 0)
    (√(∑ k, ϑ0 b r k ^ 2)) ν 1 M0 M1 ε Λ D0
    (hrpos 0) (Real.sqrt_nonneg _) hM0 hM1 one_pos hε
    (fun i j a => Ωc_swap i j a _) (Real.sq_sqrt hS).symm hOm hDOm hν
    (fun X Y => by rw [one_mul])
    (RmP_HHHH hA hAim hr hr0 u)
    (fun X U V Y => RmP_HVHV hA hAim hr hr0 u X Y U V)
    (RmP_HHVV hA hAim hr hr0 u) (RmP_HVVV hA hAim hr hr0 u) (RmP_HHHV hA hAim hr hr0 u)
    (fun U V Z T => by rw [RmP_VVVV hA hAim hr hr0 u, Real.sq_sqrt hS])
    (by rw [div_one]; exact hΛ) hr2 htD hνΛ hA2 hA3 hB2 hC1 hC2 hC3 X Y U V


end Package

/-! ## Non-vacuity: a flat connection with a concave fibre radius -/

section Witness

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K}

/-- The flat potential. -/
def A0 : K → K →L[ℝ] Quaternion ℝ := fun _ => 0

/-- The fibre radius `r(x) = exp(−256|x|²)`: `ϑ(0) = 0` and `N = −r⁻¹ Hess r = 512`. -/
def rW (x : K) : ℝ := Real.exp (-256 * ‖x‖ ^ 2)

theorem contDiff_rW : ContDiff ℝ ∞ (rW (K := K)) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).exp

theorem rW_pos (x : K) : 0 < rW x := Real.exp_pos _

theorem Ωc_A0 (i j : Fin n) (a : Fin 3) : Ωc b (A0 (K := K)) i j a = fun _ => 0 := by
  funext z
  have h : fderiv ℝ (A0 (K := K)) z.1 = 0 := by
    rw [show A0 (K := K) = fun _ => 0 from rfl]; simp
  simp [Ωc, curvA, h, A0]

theorem ϑf_rW (i : Fin n) (x : K) : ϑf b rW i x = -512 * ⟪x, eb b i x⟫ := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-256 : ℝ)).exp
  have e : rW (K := K) = fun y => Real.exp (-256 * ‖y‖ ^ 2) := rfl
  unfold ϑf
  rw [e, h.fderiv]
  have hp := (Real.exp_pos (-256 * ‖x‖ ^ 2)).ne'
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp
  ring

theorem ϑ0_rW (i : Fin n) : ϑ0 b rW i = 0 := by
  simp [ϑ0, ϑf_rW]

theorem dϑ0_rW (k i : Fin n) : dϑ0 b rW k i = -512 * kron k i := by
  have e : ϑf b rW i = fun x => -512 * ⟪x, eb b i x⟫ := funext (ϑf_rW i)
  have hg : HasFDerivAt (eb b i) (fderiv ℝ (eb b i) 0) (0 : K) :=
    ((contDiff_eb i).differentiable (by simp) 0).hasFDerivAt
  have h := ((hasFDerivAt_id (0 : K)).inner ℝ hg).const_mul (-512 : ℝ)
  unfold dϑ0
  rw [e, show (fun x : K => -512 * ⟪x, eb b i x⟫) = fun x => -512 * ⟪id x, eb b i x⟫ from rfl,
    h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, fderivInnerCLM_apply, id,
    inner_zero_left, zero_add, eb_zero, b.inner_eq_ite, kron, smul_eq_mul]

theorem N0_rW (i j : Fin n) : N0 b rW i j = 512 * kron i j := by
  simp only [N0, dϑ0_rW, ϑ0_rW]; ring

/-- **The hypotheses of `hly_prop31_centre` are jointly satisfiable**: `A = 0`,
`r = exp(−256|x|²)`, `u = 1`, `ν = 512`, `M₀ = M₁ = 0`, `ε = 1`, `Λ = 1024`, `D₀ = 0`. -/
theorem hly_prop31_centre_satisfiable :
    ContDiff ℝ ∞ (A0 (K := K)) ∧ (∀ x v, (A0 (K := K) x v).re = 0) ∧
      ContDiff ℝ ∞ (rW (K := K)) ∧ (∀ x, 0 < rW (K := K) x) ∧
      Prop31Algebra.OmSq (Ω0 b (A0 (K := K)) 1) ≤ 2 * 0 ^ 2 ∧
      (∑ i, ∑ j, ∑ k, ∑ a, DΩ0 b (A0 (K := K)) rW 1 i j k a ^ 2 ≤ 2 * 0 ^ 2) ∧
      (∀ x : Fin n → ℝ, 512 * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, N0 b rW i j * x i * x j) ∧
      (16 * 4 * (0 : ℝ) ^ 2 + 64 * 4 ^ 2 * (0 + 1) ^ 2 ≤ 1024) ∧
      rW (K := K) 0 ^ 2 ≤ 2 * 1 ∧ √(∑ k, ϑ0 b (rW (K := K)) k ^ 2) ≤ 1 * 0 / 2 ∧
      ((1 : ℝ) * 1024 / 2 - 1 ^ 2 * 0 ^ 2 / 4 ≤ 512) ∧ (2 * 1 * (0 : ℝ) ≤ 1) ∧
      ((1 : ℝ) * 0 * 0 ≤ 1) ∧ (64 * 4 ^ 2 * 1 * (0 : ℝ) ^ 2 ≤ 1) ∧
      ((1 : ℝ) * 0 ^ 2 ≤ 1024 / 4) ∧ (2 * (1 : ℝ) ^ 3 * 0 ^ 2 ≤ 1) ∧
      (32 * 4 ^ 2 * (1 : ℝ) ^ 3 * 0 ^ 2 * 0 ^ 2 ≤ 1024) := by
  refine ⟨contDiff_const, fun _ _ => rfl, contDiff_rW, rW_pos, ?_, ?_, ?_, by norm_num, ?_, ?_,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · simp [Prop31Algebra.OmSq, Ω0, Ωc_A0]
  · simp [DΩ0, Ωc_A0]
  · intro x
    simp only [N0_rW, kron, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, sq]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by ring)
  · simp [rW]
  · simp [ϑ0_rW]

end Witness

end

end ExoticSpheres8And10
