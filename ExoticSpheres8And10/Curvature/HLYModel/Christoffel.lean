/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.HLYModel.Curvature

/-! # §4, HLY model: the connection coefficients ([HLY] `eq:Koszul1`, `eq:Koszul2`)

`frameΓ (cA ..) α β γ = g(∇_{F_α} F_β, F_γ)`, from the bracket table. The eight patterns:

* `Γ(X_i, X_j, X_k) = Γ^B_{ijk}`,
* `Γ(X_i, X_j, E_a) = −(r/2) Ω_{ij}^a`,
* `Γ(X_i, E_a, X_j) = (r/2) Ω_{ij}^a`,
* `Γ(X_i, E_a, E_c) = 0`,
* `Γ(E_a, X_i, X_j) = (r/2) Ω_{ij}^a`,
* `Γ(E_a, X_i, E_c) = ϑ_i δ_{ac}`,
* `Γ(E_a, E_c, X_i) = −ϑ_i δ_{ac}`,
* `Γ(E_a, E_c, E_d) = cst_{acd} / (2r)`.

These are [HLY] `eq:Koszul1`–`eq:Koszul2`.
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section Gamma

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} {b : OrthonormalBasis (Fin n) ℝ K} {A : K → K →L[ℝ] Quaternion ℝ} {r : K → ℝ}

theorem curvA_swap (x v w : K) : curvA A x w v = -curvA A x v w := by
  unfold curvA; abel

theorem Ωc_swap (i j : Fin n) (a : Fin 3) (z : K × Quaternion ℝ) :
    Ωc b A j i a z = -Ωc b A i j a z := by
  unfold Ωc
  rw [curvA_swap, neg_mul, inner_neg_left]

theorem cst_swap12 (a c d : Fin 3) : Prop31Algebra.cst c a d = -Prop31Algebra.cst a c d := Prop31Algebra.cst_anti a c d

theorem cst_swap23 (a c d : Fin 3) : Prop31Algebra.cst a d c = -Prop31Algebra.cst a c d := by
  fin_cases a <;> fin_cases c <;> fin_cases d <;> simp [Prop31Algebra.cst, Prop31Algebra.lc]

theorem cst_cycle (a c d : Fin 3) : Prop31Algebra.cst c d a = Prop31Algebra.cst a c d := by
  fin_cases a <;> fin_cases c <;> fin_cases d <;> simp [Prop31Algebra.cst, Prop31Algebra.lc]

theorem kron_comm {ι : Type*} [DecidableEq ι] (a c : ι) : kron a c = kron c a := by
  simp only [kron, eq_comm]

variable (b A r)

/-- The base Christoffel coefficients `Γ^B_{ijk} = ½(c^B_{ijk} − c^B_{ikj} − c^B_{jki})`. -/
def ΓB (i j k : Fin n) (x : K) : ℝ := (cB b i j k x - cB b i k j x - cB b j k i x) / 2

variable {b A r}

theorem Γ_HHH (i j k : Fin n) :
    frameΓ (cA b A r) (.inl i) (.inl j) (.inl k) = fun z => ΓB b i j k z.1 := rfl

theorem Γ_HHV (i j : Fin n) (a : Fin 3) :
    frameΓ (cA b A r) (.inl i) (.inl j) (.inr a) = fun z => -(r z.1 / 2) * Ωc b A i j a z := by
  funext z; simp only [frameΓ, cA]; ring

theorem Γ_HVH (i j : Fin n) (a : Fin 3) :
    frameΓ (cA b A r) (.inl i) (.inr a) (.inl j) = fun z => r z.1 / 2 * Ωc b A i j a z := by
  funext z; simp only [frameΓ, cA]; ring

theorem Γ_HVV (i : Fin n) (a c : Fin 3) :
    frameΓ (cA b A r) (.inl i) (.inr a) (.inr c) = fun _ => 0 := by
  funext z; simp only [frameΓ, cA, kron_comm c a]; ring

theorem Γ_VHH (i j : Fin n) (a : Fin 3) :
    frameΓ (cA b A r) (.inr a) (.inl i) (.inl j) = fun z => r z.1 / 2 * Ωc b A i j a z := by
  funext z; simp only [frameΓ, cA]; ring

theorem Γ_VHV (i : Fin n) (a c : Fin 3) :
    frameΓ (cA b A r) (.inr a) (.inl i) (.inr c) = fun z => ϑf b r i z.1 * kron a c := by
  funext z; simp only [frameΓ, cA, kron_comm c a]; ring

theorem Γ_VVH (i : Fin n) (a c : Fin 3) :
    frameΓ (cA b A r) (.inr a) (.inr c) (.inl i) = fun z => -(ϑf b r i z.1 * kron a c) := by
  funext z; simp only [frameΓ, cA, kron_comm c a]; ring

theorem Γ_VVV (a c d : Fin 3) :
    frameΓ (cA b A r) (.inr a) (.inr c) (.inr d) = fun z => (r z.1)⁻¹ / 2 * Prop31Algebra.cst a c d := by
  funext z; simp only [frameΓ, cA]; rw [cst_swap23 a c d, cst_cycle a c d]; ring

theorem ΓB_eq (i j k : Fin n) (x : K) :
    ΓB b i j k x = (⟪x, b k⟫ * kron i j - ⟪x, b j⟫ * kron i k) / 2 := by
  simp only [ΓB, cB_eq]
  rw [kron_comm k j, kron_comm k i, kron_comm j i]
  ring

theorem ΓB_zero (i j k : Fin n) : ΓB b i j k 0 = 0 := by simp [ΓB_eq]

theorem cB_zero (i j k : Fin n) : cB b i j k 0 = 0 := by simp [cB_eq]

theorem eb_zero (i : Fin n) : eb b i 0 = b i := by simp [eb, cfac]

end Gamma

end

end ExoticSpheres8And10
