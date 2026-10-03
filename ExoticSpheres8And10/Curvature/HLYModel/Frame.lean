/-
Copyright (c) 2026 Fernando Galaz-García. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Galaz-García (Department of Mathematical Sciences, Durham University),
Claude Opus 5.5 (Anthropic), which wrote the Lean under Fernando Galaz-García's supervision
-/
import ExoticSpheres8And10.Curvature.HLYModel.Fields
import ExoticSpheres8And10.Curvature.HLYModel.Ambient

/-! # §4, HLY model: the orthonormal frame of a connection metric on `K × S³`

Data: an orthonormal basis `b` of `K`, a gauge potential `A : K → L(K, Im ℍ)` and a fibre radius
`r > 0`. The base metric is the round metric `HR` (stereographic), with orthonormal frame
`e_i(x) = (1 + |x|²/4) b_i`, normal at `0`.

* `qe a`: the quaternion units `i, j, k`, a `Q`-orthonormal basis of `Im ℍ` with
  `[qe a, qe b] = Σ_c cst_abc qe c`; `ζq a ∈ ℝ³` with `ι3 (ζq a) = qe a`.
* `FH i`: the horizontal lift of `e_i`, `(1 + |x|²/4) Bw(b_i) + Σ_a h_{ia} Rv(ζq a)`.
* `FV a = r⁻¹ Rv(ζq a)`: [HLY]'s `E_a = r⁻¹ e_a^#`.
* `emb p = (p.1, p.2) : K × S³ → K × ℍ`, and the frame reads ambiently as `hlA A e_i` and
  `vfA r (qe a)` (`mfderiv_emb_FH`, `mfderiv_emb_FV`).
-/

open RiemannianGeometry VectorField Bundle

namespace ExoticSpheres8And10

open Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The quaternion units. -/
def qI : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def qJ : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def qK : Quaternion ℝ := ⟨0, 0, 0, 1⟩

@[simp] theorem qI_re : qI.re = 0 := rfl
@[simp] theorem qI_imI : qI.imI = 1 := rfl
@[simp] theorem qI_imJ : qI.imJ = 0 := rfl
@[simp] theorem qI_imK : qI.imK = 0 := rfl
@[simp] theorem qJ_re : qJ.re = 0 := rfl
@[simp] theorem qJ_imI : qJ.imI = 0 := rfl
@[simp] theorem qJ_imJ : qJ.imJ = 1 := rfl
@[simp] theorem qJ_imK : qJ.imK = 0 := rfl
@[simp] theorem qK_re : qK.re = 0 := rfl
@[simp] theorem qK_imI : qK.imI = 0 := rfl
@[simp] theorem qK_imJ : qK.imJ = 0 := rfl
@[simp] theorem qK_imK : qK.imK = 1 := rfl

/-- The quaternion units `i, j, k`. -/
def qe : Fin 3 → Quaternion ℝ := ![qI, qJ, qK]

theorem qe_re (a : Fin 3) : (qe a).re = 0 := by fin_cases a <;> simp [qe]

theorem inner_quat (x y : Quaternion ℝ) :
    ⟪x, y⟫ = x.re * y.re + x.imI * y.imI + x.imJ * y.imJ + x.imK * y.imK := by
  rw [Quaternion.inner_def, Quaternion.re_mul]
  simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

theorem qe_mem (a : Fin 3) : qe a ∈ (ℝ ∙ ((-1 : S3) : Quaternion ℝ))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hn : ((-1 : S3) : Quaternion ℝ) = -1 := rfl
  rw [hn, inner_neg_left, neg_eq_zero, inner_quat]
  fin_cases a <;> simp [qe, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]

/-- `ζq a ∈ T₁S³` with `ι3 (ζq a) = qe a`. -/
def ζq (a : Fin 3) : E3 := U3 ⟨qe a, qe_mem a⟩

theorem ι3_ζq (a : Fin 3) : ι3 (ζq a) = qe a := by
  rw [ι3_apply, ζq, LinearIsometryEquiv.symm_apply_apply]

theorem inner_qe (a b : Fin 3) : ⟪qe a, qe b⟫ = kron a b := by
  rw [inner_quat]
  fin_cases a <;> fin_cases b <;> simp [qe, kron]

theorem inner_qe_right (w : Quaternion ℝ) (a : Fin 3) :
    ⟪w, qe a⟫ = ![w.imI, w.imJ, w.imK] a := by
  rw [inner_quat]
  fin_cases a <;> simp [qe]

/-- An imaginary quaternion is the sum of its components along `i, j, k`. -/
theorem sum_inner_qe {w : Quaternion ℝ} (hw : w.re = 0) : ∑ a, ⟪w, qe a⟫ • qe a = w := by
  rw [Fin.sum_univ_three, inner_qe_right, inner_qe_right, inner_qe_right]
  ext <;> simp [qe, hw]

/-- `re(ū q u) = re(q) |u|²`. -/
theorem re_star_mul_mul (u q : Quaternion ℝ) :
    (star u * q * u).re = q.re * Quaternion.normSq u := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    Quaternion.normSq_def']
  ring

theorem normSq_sphere (u : S3) : Quaternion.normSq (u : Quaternion ℝ) = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, mem_sphere_zero_iff_norm.1 u.2, one_mul]

theorem star_mul_self_sphere (u : S3) : star (u : Quaternion ℝ) * (u : Quaternion ℝ) = 1 := by
  rw [Quaternion.star_mul_self, normSq_sphere]; rfl

theorem mul_star_self_sphere (u : S3) : (u : Quaternion ℝ) * star (u : Quaternion ℝ) = 1 := by
  rw [Quaternion.self_mul_star, normSq_sphere]; rfl

section Frame

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ K) (A : K → K →L[ℝ] Quaternion ℝ) (r : K → ℝ)

/-- The conformal factor `1 + |x|²/4` of the round frame. -/
def cfac (x : K) : ℝ := 1 + ‖x‖ ^ 2 / 4

/-- The round orthonormal frame `e_i(x) = (1 + |x|²/4) b_i` of `HR`. -/
def eb (i : Fin n) (x : K) : K := cfac x • b i

/-- The vertical coefficients of the horizontal lift, `h_{ia} = −⟪A(e_i) u, u qe_a⟫`, so that
`−ū A(e_i) u = Σ_a h_{ia} qe a`. -/
def hco (i : Fin n) (a : Fin 3) (p : K × S3) : ℝ :=
  -⟪A p.1 (eb b i p.1) * (p.2 : Quaternion ℝ), (p.2 : Quaternion ℝ) * qe a⟫

/-- **The horizontal frame field** `X_i`. -/
def FH (i : Fin n) : Π p : K × S3, TangentSpace (IN K) p :=
  (fun p : K × S3 => cfac p.1) • Bw (b i) + ∑ a, (fun p => hco b A i a p) • Rv (ζq a)

/-- **The vertical frame field** `E_a = r⁻¹ e_a^#`. -/
def FV (a : Fin 3) : Π p : K × S3, TangentSpace (IN K) p :=
  (fun p : K × S3 => (r p.1)⁻¹) • Rv (ζq a)

/-- The frame, indexed by `Fin n ⊕ Fin 3`. -/
def Fr : Fin n ⊕ Fin 3 → Π p : K × S3, TangentSpace (IN K) p := Sum.elim (FH b A) (FV r)

/-- Its ambient counterpart on `K × ℍ`. -/
def Fa : Fin n ⊕ Fin 3 → K × Quaternion ℝ → K × Quaternion ℝ :=
  Sum.elim (fun i => hlA A (eb b i)) (fun a => vfA r (qe a))

variable {b A r}

theorem mvfderiv_fY_FH (i : Fin n) (p : K × S3) :
    mvfderiv (IN K) fY p (FH b A i p) = eb b i p.1 := by
  simp only [FH, Pi.add_apply, Finset.sum_apply, Pi.smul_apply', map_add, map_sum, map_smul,
    mvfderiv_fY_Bw, mvfderiv_fY_Rv, smul_zero, Finset.sum_const_zero, add_zero, eb]

theorem mvfderiv_fU_FH (hAim : ∀ x v, (A x v).re = 0) (i : Fin n) (p : K × S3) :
    mvfderiv (IN K) fU p (FH b A i p) = -(A p.1 (eb b i p.1)) * (p.2 : Quaternion ℝ) := by
  simp only [FH, Pi.add_apply, Finset.sum_apply, Pi.smul_apply', map_add, map_sum, map_smul,
    mvfderiv_fU_Bw, mvfderiv_fU_Rv, smul_zero, zero_add, ι3_ζq]
  set u : Quaternion ℝ := (p.2 : Quaternion ℝ)
  have hu' : u * star u = 1 := mul_star_self_sphere p.2
  have hre : (-(star u * A p.1 (eb b i p.1) * u)).re = 0 := by
    rw [Quaternion.re_neg, re_star_mul_mul, hAim, zero_mul, neg_zero]
  have hsum := sum_inner_qe hre
  have hco' : ∀ a, hco b A i a p = ⟪-(star u * A p.1 (eb b i p.1) * u), qe a⟫ := fun a => by
    have h := inner_mul_left_unit p.2 (star u * A p.1 (eb b i p.1) * u) (qe a)
    have e : u * (star u * A p.1 (eb b i p.1) * u) = A p.1 (eb b i p.1) * u := by
      rw [← mul_assoc, ← mul_assoc, hu', one_mul]
    rw [e] at h
    rw [hco, inner_neg_left, h]
  calc ∑ a, hco b A i a p • (u * qe a) = u * ∑ a, hco b A i a p • qe a := by
        rw [Finset.mul_sum]; simp [mul_smul_comm]
    _ = u * -(star u * A p.1 (eb b i p.1) * u) := by rw [← hsum]; simp only [hco']
    _ = -(A p.1 (eb b i p.1)) * u := by
        rw [mul_neg, ← mul_assoc, ← mul_assoc, hu', one_mul, neg_mul]

theorem mvfderiv_fY_FV (a : Fin 3) (p : K × S3) : mvfderiv (IN K) fY p (FV r a p) = 0 := by
  simp only [FV, Pi.smul_apply', map_smul, mvfderiv_fY_Rv, smul_zero]

theorem mvfderiv_fU_FV (a : Fin 3) (p : K × S3) :
    mvfderiv (IN K) fU p (FV r a p) = (r p.1)⁻¹ • ((p.2 : Quaternion ℝ) * qe a) := by
  simp only [FV, Pi.smul_apply', map_smul, mvfderiv_fU_Rv, ι3_ζq]

/-- The embedding `K × S³ → K × ℍ`. -/
def emb (p : K × S3) : K × Quaternion ℝ := (p.1, (p.2 : Quaternion ℝ))

theorem contMDiff_emb : ContMDiff (IN K) 𝓘(ℝ, K × Quaternion ℝ) ∞ (emb (K := K)) :=
  contMDiff_fY.prodMk_space contMDiff_fU

theorem mfderiv_emb_apply (p : K × S3) (v : TangentSpace (IN K) p) :
    mfderiv (IN K) 𝓘(ℝ, K × Quaternion ℝ) emb p v =
      (mvfderiv (IN K) fY p v, mvfderiv (IN K) fU p v) := by
  have he : MDifferentiableAt (IN K) 𝓘(ℝ, K × Quaternion ℝ) (emb (K := K)) p :=
    (contMDiff_emb p).mdifferentiableAt (by simp)
  have h1 := mfderiv_comp p (ContinuousLinearMap.fst ℝ K (Quaternion ℝ)).mdifferentiableAt he
  have h2 := mfderiv_comp p (ContinuousLinearMap.snd ℝ K (Quaternion ℝ)).mdifferentiableAt he
  rw [(ContinuousLinearMap.fst ℝ K (Quaternion ℝ)).hasMFDerivAt.mfderiv] at h1
  rw [(ContinuousLinearMap.snd ℝ K (Quaternion ℝ)).hasMFDerivAt.mfderiv] at h2
  refine Prod.ext ?_ ?_
  · have := congrArg (fun L => L v) h1
    exact this.symm
  · have := congrArg (fun L => L v) h2
    exact this.symm

theorem mfderiv_emb_Fr (hAim : ∀ x v, (A x v).re = 0) (α : Fin n ⊕ Fin 3) (p : K × S3) :
    mfderiv (IN K) 𝓘(ℝ, K × Quaternion ℝ) emb p (Fr b A r α p) = Fa b A r α (emb p) := by
  rw [mfderiv_emb_apply]
  rcases α with i | a
  · show (mvfderiv (IN K) fY p (FH b A i p), mvfderiv (IN K) fU p (FH b A i p)) = hlA A (eb b i) _
    rw [mvfderiv_fY_FH, mvfderiv_fU_FH hAim]
    rfl
  · show (mvfderiv (IN K) fY p (FV r a p), mvfderiv (IN K) fU p (FV r a p)) = vfA r (qe a) _
    rw [mvfderiv_fY_FV, mvfderiv_fU_FV]
    rfl

theorem contMDiff_cfac : ContMDiff (IN K) 𝓘(ℝ) ∞ fun p : K × S3 => cfac p.1 :=
  (contDiff_const.add ((contDiff_norm_sq ℝ).div_const 4)).contMDiff.comp contMDiff_fY

theorem contMDiff_hco (hA : ContDiff ℝ ∞ A) (i : Fin n) (a : Fin 3) :
    ContMDiff (IN K) 𝓘(ℝ) ∞ (hco b A i a) := by
  have hebc : ContDiff ℝ ∞ (eb b i) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).div_const 4)).smul contDiff_const
  have hamb : ContDiff ℝ ∞ fun z : K × Quaternion ℝ =>
      -⟪A z.1 (eb b i z.1) * z.2, z.2 * qe a⟫ := by
    have hAz : ContDiff ℝ ∞ fun z : K × Quaternion ℝ => A z.1 (eb b i z.1) :=
      (hA.comp contDiff_fst).clm_apply (hebc.comp contDiff_fst)
    exact ((hAz.mul contDiff_snd).inner ℝ (contDiff_snd.mul contDiff_const)).neg
  have h2 : ContMDiff (IN K) 𝓘(ℝ) ∞
      ((fun z : K × Quaternion ℝ => -⟪A z.1 (eb b i z.1) * z.2, z.2 * qe a⟫) ∘ emb) :=
    hamb.contMDiff.comp contMDiff_emb
  exact h2

theorem contMDiff_Fr (hA : ContDiff ℝ ∞ A) (hr : ContDiff ℝ ∞ r) (hr0 : ∀ x, r x ≠ 0)
    (α : Fin n ⊕ Fin 3) :
    ContMDiff (IN K) (IN K).tangent ((2 : ℕ∞) : ℕ∞ω) (T% (Fr b A r α)) := by
  rcases α with i | a
  · show ContMDiff (IN K) (IN K).tangent _ (T% (FH b A i))
    refine ContMDiff.add_section ?_ ?_
    · exact (contMDiff_cfac.of_le (by exact_mod_cast le_top)).smul_section (contMDiff_Bw (b i))
    · have := ContMDiff.sum_section (s := Finset.univ)
        (t := fun a (p : K × S3) => ((fun p => hco b A i a p) • Rv (ζq a)) p)
        (n := ((2 : ℕ∞) : ℕ∞ω)) (fun a _ =>
          ((contMDiff_hco hA i a).of_le (by exact_mod_cast le_top)).smul_section
            (contMDiff_Rv (K := K) _))
      have e : (∑ a, (fun p : K × S3 => hco b A i a p) • Rv (K := K) (ζq a)) =
          fun p => ∑ a, ((fun p : K × S3 => hco b A i a p) • Rv (K := K) (ζq a)) p := by
        funext p; exact Finset.sum_apply _ _ _
      rw [e]; exact this
  · show ContMDiff (IN K) (IN K).tangent _ (T% (FV r a))
    have hri : ContMDiff (IN K) 𝓘(ℝ) ∞ fun p : K × S3 => (r p.1)⁻¹ :=
      ((hr.inv hr0).contMDiff).comp contMDiff_fY
    exact (hri.of_le (by exact_mod_cast le_top)).smul_section (contMDiff_Rv (K := K) _)

end Frame

end

end ExoticSpheres8And10

namespace ExoticSpheres8And10

open RiemannianGeometry VectorField Bundle Set Function Filter Topology Real

open scoped Manifold ContDiff RealInnerProductSpace

set_option maxSynthPendingDepth 3

noncomputable section

local notation "S3" => Metric.sphere (0 : Quaternion ℝ) 1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Metric

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {n : ℕ} (A : K → K →L[ℝ] Quaternion ℝ) (r : K → ℝ)

/-- The connection form, right-translated by `u`: `θ(v) = A_x(dx v) u + du(v)`. -/
def θL (p : K × S3) : TangentSpace (IN K) p →L[ℝ] Quaternion ℝ :=
  (((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (p.2 : Quaternion ℝ)).comp
    ((A p.1).comp (mvfderiv (IN K) fY p))) + mvfderiv (IN K) fU p

theorem θL_apply (p : K × S3) (v : TangentSpace (IN K) p) :
    θL A p v = A p.1 (mvfderiv (IN K) fY p v) * (p.2 : Quaternion ℝ) + mvfderiv (IN K) fU p v :=
  rfl

/-- **The connection metric** `G = HR(dx, dx) + r(x)² |A_x(dx) u + du|²` on `K × S³`
([HLY] `eq:connectionmetric`, `π^*g_B + r² Q(ω, ω)`, with `|ω| = |u⁻¹Au + u⁻¹du| = |Au + du|`). -/
def GH (p : K × S3) : TangentSpace (IN K) p →L[ℝ] TangentSpace (IN K) p →L[ℝ] ℝ :=
  letI : NormedAddCommGroup (TangentSpace (IN K) p) := inferInstanceAs (NormedAddCommGroup (K × E3))
  letI : NormedSpace ℝ (TangentSpace (IN K) p) := inferInstanceAs (NormedSpace ℝ (K × E3))
  ψR p.1 • bil (ipL K) (mvfderiv (IN K) fY p) + (r p.1 ^ 2) • bil (ipL (Quaternion ℝ)) (θL A p)

theorem GH_apply (p : K × S3) (v w : TangentSpace (IN K) p) :
    GH A r p v w = ψR p.1 * ⟪mvfderiv (IN K) fY p v, mvfderiv (IN K) fY p w⟫ +
      r p.1 ^ 2 * ⟪θL A p v, θL A p w⟫ := rfl

variable {A r}

theorem isSymm_GH : IsSymm (GH A r) := fun p v w => by
  rw [GH_apply, GH_apply, real_inner_comm (mvfderiv (IN K) fY p v),
    real_inner_comm (θL A p v)]

theorem isPosDef_GH (hr0 : ∀ x, r x ≠ 0) : IsPosDef (GH A r) := fun p v hv => by
  rw [GH_apply]
  have hψ := ψR_pos p.1
  have hr2 : 0 < r p.1 ^ 2 := by have := hr0 p.1; positivity
  by_cases h1 : mvfderiv (IN K) fY p v = 0
  · have h2 : θL A p v ≠ 0 := by
      intro h
      rw [θL_apply, h1, map_zero, zero_mul, zero_add] at h
      exact hv (mvfderiv_fU_injective p ((mvfderiv_fY p v).symm.trans h1) h)
    have := real_inner_self_pos.2 h2
    rw [h1, inner_zero_left, mul_zero, zero_add]
    positivity
  · have := real_inner_self_pos.2 h1
    have : 0 ≤ ⟪θL A p v, θL A p v⟫ := real_inner_self_nonneg
    positivity

variable {b : OrthonormalBasis (Fin n) ℝ K}

theorem θL_FH (hAim : ∀ x v, (A x v).re = 0) (i : Fin n) (p : K × S3) :
    θL A p (FH b A i p) = 0 := by
  rw [θL_apply, mvfderiv_fY_FH, mvfderiv_fU_FH hAim, neg_mul, add_neg_cancel]

theorem θL_FV (a : Fin 3) (p : K × S3) :
    θL A p (FV r a p) = (r p.1)⁻¹ • ((p.2 : Quaternion ℝ) * qe a) := by
  rw [θL_apply, mvfderiv_fY_FV, mvfderiv_fU_FV, map_zero, zero_mul, zero_add]

theorem psiR_cfac (x : K) : ψR x * cfac x ^ 2 = 1 := by
  unfold ψR cfac
  have : (0 : ℝ) < (1 + ‖x‖ ^ 2 / 4) ^ 2 := by positivity
  field_simp

/-- **The frame is `G`-orthonormal.** -/
theorem GH_Fr (hAim : ∀ x v, (A x v).re = 0) (hr0 : ∀ x, r x ≠ 0) (α β : Fin n ⊕ Fin 3)
    (p : K × S3) : GH A r p (Fr b A r α p) (Fr b A r β p) = kron α β := by
  rcases α with i | a <;> rcases β with j | c
  · show GH A r p (FH b A i p) (FH b A j p) = _
    rw [GH_apply, mvfderiv_fY_FH, mvfderiv_fY_FH, θL_FH hAim, θL_FH hAim, inner_zero_left,
      mul_zero, add_zero, eb, eb, real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite]
    have h := psiR_cfac p.1
    simp only [kron, Sum.inl.injEq]
    split_ifs <;> nlinarith
  · show GH A r p (FH b A i p) (FV r c p) = _
    rw [GH_apply, mvfderiv_fY_FV, θL_FH hAim, inner_zero_right, inner_zero_left]
    simp [kron]
  · show GH A r p (FV r a p) (FH b A j p) = _
    rw [GH_apply, mvfderiv_fY_FV, θL_FH hAim, inner_zero_right, inner_zero_left]
    simp [kron]
  · show GH A r p (FV r a p) (FV r c p) = _
    rw [GH_apply, mvfderiv_fY_FV, θL_FV, θL_FV, inner_zero_left, mul_zero, zero_add,
      real_inner_smul_left, real_inner_smul_right, inner_mul_left_unit, inner_qe]
    have hr := hr0 p.1
    simp only [kron, Sum.inr.injEq]
    split_ifs <;> field_simp

theorem isContMDiffMetricSection_GH (hA : ContDiff ℝ ∞ A) (hr : ContDiff ℝ ∞ r) :
    IsContMDiffMetricSection (K × E3) 2 (GH A r) := by
  refine isContMDiffMetricSection_of_scalars (m := 2) _ fun x V W hV hW => ?_
  have hmn : ((2 : ℕ∞) : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast le_top
  have dY : ∀ {U : Π y : K × S3, TangentSpace (IN K) y},
      ContMDiffAt (IN K) (IN K).tangent ((2 : ℕ∞) : ℕ∞ω)
        (fun y => (⟨y, U y⟩ : TangentBundle (IN K) (K × S3))) x →
      ContMDiffAt (IN K) 𝓘(ℝ, K) ((2 : ℕ∞) : ℕ∞ω) (fun y => mvfderiv (IN K) fY y (U y)) x :=
    fun hU => contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x)
      contMDiff_fY.contMDiffOn hmn hU
  have dU : ∀ {U : Π y : K × S3, TangentSpace (IN K) y},
      ContMDiffAt (IN K) (IN K).tangent ((2 : ℕ∞) : ℕ∞ω)
        (fun y => (⟨y, U y⟩ : TangentBundle (IN K) (K × S3))) x →
      ContMDiffAt (IN K) 𝓘(ℝ, Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω)
        (fun y => mvfderiv (IN K) fU y (U y)) x :=
    fun hU => contMDiffAt_mvfderiv_apply_of_contMDiffOn isOpen_univ (mem_univ x)
      contMDiff_fU.contMDiffOn hmn hU
  have hAx : ContMDiffAt (IN K) 𝓘(ℝ, K →L[ℝ] Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω)
      (fun y : K × S3 => A y.1) x :=
    ((hA.contMDiff.comp contMDiff_fY) x).of_le (by exact_mod_cast le_top)
  have hu : ContMDiffAt (IN K) 𝓘(ℝ, Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω) (fU (V := K)) x :=
    (contMDiff_fU x).of_le (by exact_mod_cast le_top)
  have θs : ∀ {U : Π y : K × S3, TangentSpace (IN K) y},
      ContMDiffAt (IN K) (IN K).tangent ((2 : ℕ∞) : ℕ∞ω)
        (fun y => (⟨y, U y⟩ : TangentBundle (IN K) (K × S3))) x →
      ContMDiffAt (IN K) 𝓘(ℝ, Quaternion ℝ) ((2 : ℕ∞) : ℕ∞ω) (fun y => θL A y (U y)) x :=
    fun hU => ((contMDiffAt_const (c := ContinuousLinearMap.mul ℝ (Quaternion ℝ))).clm_apply
      (hAx.clm_apply (dY hU)) |>.clm_apply hu).add (dU hU)
  have hψ : ContMDiffAt (IN K) 𝓘(ℝ) ((2 : ℕ∞) : ℕ∞ω) (fun y : K × S3 => ψR y.1) x := by
    have : ContDiff ℝ ∞ fun y : K => ψR y := by
      unfold ψR
      exact ((contDiff_const.add ((contDiff_norm_sq ℝ).div_const 4)).pow 2).inv
        fun y => by positivity
    exact ((this.contMDiff.comp contMDiff_fY) x).of_le (by exact_mod_cast le_top)
  have hr2 : ContMDiffAt (IN K) 𝓘(ℝ) ((2 : ℕ∞) : ℕ∞ω) (fun y : K × S3 => r y.1 ^ 2) x :=
    ((((hr.pow 2).contMDiff).comp contMDiff_fY) x).of_le (by exact_mod_cast le_top)
  have t1 := hψ.mul ((contMDiffAt_const (c := ipL K)).clm_apply (dY hV) |>.clm_apply (dY hW))
  have t2 := hr2.mul ((contMDiffAt_const (c := ipL (Quaternion ℝ))).clm_apply (θs hV)
    |>.clm_apply (θs hW))
  exact t1.add t2

end Metric

end

end ExoticSpheres8And10
