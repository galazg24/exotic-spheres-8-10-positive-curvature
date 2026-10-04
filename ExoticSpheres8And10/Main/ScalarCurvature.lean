/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García
Developed with extensive assistance from Claude (Anthropic), used through Claude Code.
-/
import ExoticSpheres8And10.Geometry.SFF.LevelSets

/-! # Scalar curvature, and `sec > 0 ⇒ scal > 0`

`RiemannianGeometry`'s foundations have the Riemann tensor `Rm` and the sectional curvature, but no scalar
curvature. Here:
* `IsOrthonormalFrame g x b`: `b : Fin (dim) → T_xX` is `g_x`-orthonormal;
* `scalarCurvatureAt … x b = Σ_{i,j} Rm(b_i, b_j, b_j, b_i)`, the scalar curvature computed in the
  frame `b`. This is the usual `scal = Σ_{i≠j} sec(b_i, b_j)`;
* `HasPosScalMetric I X`: a smooth metric whose scalar curvature is positive **in every
  orthonormal frame at every point**. So the definition makes no choice of frame;
* `exists_orthonormalFrame`: orthonormal frames exist, so the condition is not vacuous;
* **`HasPosCurvMetric.hasPosScalMetric`**: in dimension `≥ 2`, `sec > 0` implies `scal > 0`.
-/

open RiemannianGeometry

namespace ExoticSpheres8And10

open Module

open scoped Manifold ContDiff

noncomputable section

section Scalar

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- `b` is a `g_x`-orthonormal frame of `T_xX`. -/
def IsOrthonormalFrame (g : Π x : X, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : X)
    (b : Fin (finrank ℝ E) → TangentSpace I x) : Prop :=
  ∀ i j, g x (b i) (b j) = if i = j then 1 else 0

/-- **The scalar curvature at `x`**, in the orthonormal frame `b`:
`Σ_{i,j} Rm(b_i, b_j, b_j, b_i)`. -/
def scalarCurvatureAt {g : Π x : X, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hs : IsSymm g) (hp : IsPosDef g) (hg : IsContMDiffMetricSection E ∞ g) (x : X)
    (b : Fin (finrank ℝ E) → TangentSpace I x) : ℝ :=
  ∑ i, ∑ j, riemannTensorAt hs hp.isNondegenerate (IsContMDiffMetricSection.of_le' hg two_le_infty_ω)
    x (b i) (b j) (b j) (b i)

variable (I X) in
/-- A smooth metric of **positive scalar curvature**: positive in every orthonormal frame, at
every point. -/
def HasPosScalMetric : Prop :=
  ∃ (g : Π x : X, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (hs : IsSymm g)
    (hp : IsPosDef g) (hg : IsContMDiffMetricSection E ∞ g),
    ∀ (x : X) (b : Fin (finrank ℝ E) → TangentSpace I x), IsOrthonormalFrame g x b →
      0 < scalarCurvatureAt hs hp hg x b

/-- **Orthonormal frames exist** for every metric at every point. So `HasPosScalMetric` is not
vacuous. -/
theorem exists_orthonormalFrame {g : Π x : X, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hs : IsSymm g) (hp : IsPosDef g) (x : X) :
    ∃ b : Fin (finrank ℝ E) → TangentSpace I x, IsOrthonormalFrame g x b := by
  let B : LinearMap.BilinForm ℝ (TangentSpace I x) :=
    LinearMap.mk₂ ℝ (fun u v => g x u v) (fun u u' v => by simp) (fun c u v => by simp)
      (fun u v v' => by simp) (fun c u v => by simp)
  have hB : LinearMap.IsSymm B := LinearMap.isSymm_def.2 fun u v => hs x u v
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℝ) hB
  have hpos : ∀ i, 0 < g x (v i) (v i) := fun i => hp x _ (v.ne_zero i)
  refine ⟨fun i => (Real.sqrt (g x (v i) (v i)))⁻¹ • v i, fun i j => ?_⟩
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hs0 := Real.sqrt_pos.2 (hpos i)
    have hsq := Real.mul_self_sqrt (hpos i).le
    field_simp
    linarith
  · rw [if_neg hij]
    have h0 : B (v i) (v j) = 0 := hv hij
    have : g x (v i) (v j) = 0 := h0
    rw [this, mul_zero, mul_zero]

/-- Orthonormal vectors are linearly independent. -/
theorem linearIndependent_of_orthonormal
    {g : Π x : X, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} (hs : IsSymm g) {x : X}
    {u v : TangentSpace I x} (huu : g x u u = 1) (hvv : g x v v = 1) (huv : g x u v = 0) :
    LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun w => g x w u) hst
  have h2 := congrArg (fun w => g x w v) hst
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, map_zero, ContinuousLinearMap.zero_apply] at h1 h2
  rw [huu, hs x v u, huv] at h1
  rw [hvv, huv] at h2
  constructor <;> linarith

/-- **`sec > 0` implies `scal > 0`** (in dimension `≥ 2`), in every orthonormal frame. -/
theorem scalarCurvatureAt_pos {g : Π x : X, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hs : IsSymm g) (hp : IsPosDef g) (hg : IsContMDiffMetricSection E ∞ g)
    (h2 : 2 ≤ finrank ℝ E) (x : X)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      0 < sectionalCurvatureAt hs hp (IsContMDiffMetricSection.of_le' hg two_le_infty_ω) x u v)
    (b : Fin (finrank ℝ E) → TangentSpace I x) (hb : IsOrthonormalFrame g x b) :
    0 < scalarCurvatureAt hs hp hg x b := by
  set hg2 := IsContMDiffMetricSection.of_le' hg two_le_infty_ω
  have hterm : ∀ i j, i ≠ j →
      0 < riemannTensorAt hs hp.isNondegenerate hg2 x (b i) (b j) (b j) (b i) := by
    intro i j hij
    have hii : g x (b i) (b i) = 1 := by rw [hb i i, if_pos rfl]
    have hjj : g x (b j) (b j) = 1 := by rw [hb j j, if_pos rfl]
    have hij' : g x (b i) (b j) = 0 := by rw [hb i j, if_neg hij]
    have h := hsec _ _ (linearIndependent_of_orthonormal hs hii hjj hij')
    have hgram : gramDet g x (b i) (b j) = 1 := by rw [gramDet, hii, hjj, hij']; ring
    rwa [sectionalCurvatureAt_def, hgram, div_one] at h
  have hdiag : ∀ i, riemannTensorAt hs hp.isNondegenerate hg2 x (b i) (b i) (b i) (b i) = 0 :=
    fun i => riemannTensorAt_self_right hs hp.isNondegenerate hg2 (b i) (b i) (b i)
  have hnn : ∀ i j, 0 ≤ riemannTensorAt hs hp.isNondegenerate hg2 x (b i) (b j) (b j) (b i) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hdiag]
    · exact (hterm i j hij).le
  let i0 : Fin (finrank ℝ E) := ⟨0, by omega⟩
  let i1 : Fin (finrank ℝ E) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  unfold scalarCurvatureAt
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) ⟨i0, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun j _ => hnn i0 j) ⟨i1, Finset.mem_univ _, hterm i0 i1 h01⟩

variable (I X) in
/-- **`sec > 0 ⇒ scal > 0`**, for metrics. -/
theorem HasPosCurvMetric.hasPosScalMetric (h2 : 2 ≤ finrank ℝ E) :
    HasPosCurvMetric I X → HasPosScalMetric I X := by
  rintro ⟨g, hs, hp, hg, hsec⟩
  exact ⟨g, hs, hp, hg, fun x b hb => scalarCurvatureAt_pos hs hp hg h2 x (hsec x) b hb⟩

end Scalar

end

end ExoticSpheres8And10
