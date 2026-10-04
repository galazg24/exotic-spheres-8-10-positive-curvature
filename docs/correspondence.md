# Correspondence between [D] and the Lean formalisation

This document is for readers who want to check that the Lean statements say what [D] says.
For each numbered item of [D] it lists:
- the Lean declarations that prove it, and its status;
- every place where the Lean statement differs from the wording of [D], with the reason the
  difference is harmless.

Module names are relative to `ExoticSpheres8And10`. Declaration names are in the namespace
`ExoticSpheres8And10` unless stated otherwise.

**Status codes.**
- **K**: proved, checked by Lean's kernel, standard axioms only.
- **K\***: proved, assuming one or more of the imported results below as explicit hypotheses.
- **I**: imported: a published result, entering as a named hypothesis.
- **B**: logical bookkeeping over imported facts.

## 1. Reading the main theorems

### Theorems A and B (`Main.TheoremsAB`)

`theoremA` (dimension 8, representation `rep8 = ρ₈`) and `theoremB` (dimension 10,
`rep10 = ρ₁₀`) have the same form. For a smooth manifold `E` and `B : StarBundle rep8 E`:

1. **Polar normal form.** There are polar data `D` with `D.ρ = ρ₈`, and a homeomorphism
   `E/S³_⋆ ≃ₜ QuotSpace D`.
2. **Positive curvature.** `RWGluing (QuotSpace D) → HasPosCurvMetric (QuotSpace D)`.

How to read the objects in this statement:
- **`StarBundle ρ E`** is [D]'s special `S³`-`S³` bundle (`def:starbundle`). It consists of a
  smooth projection `E → Sⁿ`, a smooth free right `S³`-action, transitive on fibres with local
  trivialisations, and a smooth free star action commuting with it and covering `ρ`. Sperança's
  theorem [Sp] says that the exotic 8-sphere (resp. the order-three homotopy 10-spheres) is the
  star quotient of such a bundle for `ρ₈` (resp. `ρ₁₀`). That is the second imported input.
- **`QuotSpace D`** is a smooth manifold: two open caps of `Sⁿ` glued by `(t, y) ↦ (π − t, σ(y))`.
  - It is the quotient manifold of the polar bundle `P_θ` by the star action: the quotient
    map is smooth and surjective, its fibres are the star orbits, and smooth maps out of it are
    exactly those whose composite with the quotient map is smooth (`PolarBundles.StarQuotient`).
  - `prop_polar` (`StarBundles.Equivariant`) gives a diffeomorphism `P_θ ≅ E` that is
    equivariant for both actions. So the map `E → QuotSpace D` has the same universal property
    (`contMDiff_iff_comp_starQuotMap`), and `QuotSpace D` is `E/S³_⋆` *as a smooth manifold*.
    The homeomorphism in the statement is the underlying map.
- **`HasPosCurvMetric I M`** means: there is a smooth (`C^∞`) Riemannian metric on `M`
  (symmetric, positive definite, a smooth section) whose sectional curvature is positive on
  every 2-plane. Sectional curvature is `sectionalCurvatureAt` of `RiemannianGeometry`, which is
  defined from the Levi-Civita connection by the Koszul formula.
- **`RWGluing`** (`Geometry.SFF.LevelSets`) is the instance of the Reiser–Wraith gluing theorem
  [RW, Theorem A(i)] that [D] uses (`prop:gluing`). Suppose `M` is compact and is cut by a
  regular level set `Σ = {f = c}` into `M_N = {f ≤ c}` and `M_S = {f ≥ c}`. Suppose each piece
  carries a smooth metric of positive sectional curvature, the two induced metrics on `Σ` agree,
  and the second fundamental forms satisfy `B_N + B_S ≥ 0`. Then `M` admits a smooth metric of
  positive sectional curvature. Why this is a special case of [RW]:
  - `M_N` and `M_S` are compact manifolds with boundary `Σ`;
  - RW's glued manifold `M_N ∪_id M_S` is diffeomorphic to `M`;
  - admitting a metric with `sec > 0` is a diffeomorphism invariant.

### Corollary C (`Main.CorollaryC`)

`corollaryC_dim8_geom` and `corollaryC_dim10_geom` are stated for an abstract group `Θ`, with
the relation `Rep M x` ("the manifold `M` represents `x ∈ Θ`"):
- `SECc Rep x`: some representative of `x` admits `sec > 0`;
- `PSCc Rep x`: some representative of `x` admits positive scalar curvature.

The Kervaire–Milnor identifications `Θ₈ ≅ ℤ/2`, `Θ₁₀ ≅ ℤ/6`, the standard sphere representing
`0`, Hitchin's `α`, and orientation reversal are hypotheses (section 3).

The following are **proved**, not assumed:
- `sec > 0 ⇒ scal > 0` (`HasPosCurvMetric.hasPosScalMetric`, `Main.ScalarCurvature`);
- the round sphere has `sec > 0` (`hasPosCurvMetric_sphere`, `Main.RoundSphere`).

`SECc_of_theoremA` and `SECc_of_theoremB` connect Corollary C to Theorems A and B.

## 2. Item by item

| [D] | Lean | Status |
|---|---|---|
| Def. special `S³`-`S³` bundle, `def:starbundle` | `StarBundle`, `StarRep` (`StarBundles.StarBundle`) | K (definitions) |
| `def:polar`, `eq:equiv`, `eq:transition`, `eq:staraction`; the star action is well defined, smooth at the poles, free, and commutes with the principal action | `PolarData`, `PolarBundle`, `polarBundle_isStarBundle` (`PolarBundles.*`) | K |
| `lem:attaching` (1): `D_α` is a smooth closed disk | `lem_attaching_1`, `lem_attaching_smooth` (`PolarBundles.AttachingDiffeo`, `PolarBundles.AttachingDisks`) | K |
| `lem:attaching` (2), `eq:sigma`: `y_S = σ(y_N)`, `σ̂ = σ⁻¹` | `markings`, `polarX_κS`, `sigmaDiffeoV` | K |
| `lem:attaching` (3): `P_θ/S³_⋆ ≅ D_N ∪_σ D_S` | `lem_attaching_3`, `DiskGluingModel`, `diskGluing_unique` (`Geometry.Boundary.DiskGluing`) | K |
| `prop:polar` (Steps 1–6, `eq:model`, `eq:sectionequiv`) | `StarBundle.prop_polar` (`StarBundles.*`) | K |
| `lem:K` | `lem_K` (`Main.Representations`), `norm_KY_le` (`ActionField.Bridge`) | K (stronger than stated) |
| `thm:HLYgeneral` | `hly_general` (`Curvature.HLYGeneral`) | K\* (RW) |
| `fact:prop31` ([HLY] Prop. 3.1), `eq:Lambda` | `hly_prop31_global_intrinsic` (`Curvature.Prop31.Bundle.Intrinsic`); round-base instance `hly_prop31_at`; models `hly_prop31_intrinsic_interval`, `hly_prop31_model_disk` | K |
| Southern filling: `eq:potentials`, gauge compatibility, star invariance, `M₀`, `M₁ < ∞`, `φ = −A₀ cos t`, `eq:south`, smoothness at `o_S`, O'Neill | `southern_cap_pos`, `southern_quotient_pos_D` (`Curvature.Southern.*`), `Curvature.ONeill` | K |
| `eq:bdata`, `𝓑_S` | `fibreS`, `baseS_eq`, `sff_τ`, `gB_τ` (`Curvature.Boundary.*`) | K |
| Northern filling: `eq:north`, the star-horizontal graph, `eq:Tbound`, `eq:graphestimates`, `eq:areaestimate` | `Curvature.Northern.*` | K |
| `eq:fullcurvature` | `riemannTensorAt_wG`, `riemannTensorAt_wG_orthonormal` (`Curvature.WarpedProduct`) | K |
| `eq:northcriterion`, `eq:delta`, the profiles `F`, `r`, `η`, `ℓ_N` | `northern_filling_pos`, `north_hup` (`Curvature.Northern.*`) | K |
| Smoothness at the centre; centre curvature `δ⁻²`; Gram matrix; O'Neill; `sec g_N > 0` | `northern_quotient_pos` (`Curvature.Northern.Cap`) | K |
| `𝓑_N`, boundary values `μ_N`, `q_s` | `baseN_eq`, `fibreN` (`Curvature.Boundary.Values`) | K |
| Boundary compatibility: `h_N = σ^*h_S`, cometric `LL^*`, `eq:shapesum` | `bdry_model_metric`, `bdry_model_sff`, `sff_quot_GW`, `LLstar_eq` | K |
| `eq:compat`, `c_B > 0` | `bdry_model_sff_cB`, `bdry_model_compat` (`Curvature.Boundary.StrictCompat`) | K |
| `prop:gluing` (Reiser–Wraith) | `RWGluing`, `RWData` | I |
| Proof of `thm:HLYgeneral` (choice of parameters) | `hly_general`, with explicit parameters | K |
| `rem:general_bound` | `remark_general_bound_RW` (`Curvature.DHZ`); [DHZ] Prop. 5.1 as `dhz_prop51` | K\* (RW) |
| `eq:rho8`, `eq:rho10`, `e₈`, `e₁₀` as star representations | `rep8`, `rep10` (`Main.Representations`) | K |
| `E¹¹`, `E¹³` are star bundles ([Sp]) | hypothesis `B : StarBundle rep8 E` (resp. `rep10`) | I |
| `thm:speranca` | (outside the Lean statements) | I |
| Theorems A and B | `theoremA`, `theoremB` | K\* (RW, [Sp]) |
| Theorem B: reversing orientation gives the other generator | hypothesis `hneg` of `corollaryC_dim10_geom` | I |
| Corollary C | `corollaryC_dim10_geom`, `corollaryC_dim8_geom` | B over [KM], [Hi], orientation, [Sp] (I); `sec ⇒ scal` and the round sphere: K |

## 3. Imported inputs, exactly as they enter

| Input | Lean hypothesis | Used by |
|---|---|---|
| [RW] Theorem A(i), in the form of `prop:gluing` | `hRW : RWGluing … (QuotSpace D)` | `hly_general`, `theoremA`, `theoremB`, `remark_general_bound_RW` |
| [Sp]: `E¹¹` (resp. `E¹³`) is a star bundle for `ρ₈` (resp. `ρ₁₀`) whose star quotient is the exotic sphere | `B : StarBundle rep8 E` (resp. `rep10`); `SECc_of_theoremA/B` take "the quotient represents the generator" as a hypothesis | Theorems A, B; Corollary C |
| [KM]: `Θ₈ ≅ ℤ/2`, `Θ₁₀ ≅ ℤ/6`; the standard sphere represents `0` | `eΘ : Θ ≃+ ZMod 2` (resp. `ZMod 6`), `hround : Rep (Sph n) 0` | Corollary C |
| [Hi]: `α` is nonzero and vanishes under positive scalar curvature | `hα : α ≠ 0`, `hHitchin : ∀ x, PSCc Rep x → α x = 0` | Corollary C (dimension 10) |
| Orientation reversal negates the class | `hneg : Rep M x → Rep M (−x)` | Corollary C (dimension 10) |

No other hypothesis of a main theorem is an unproved mathematical assertion. The remaining
hypotheses are the data of the statement: the manifold, the bundle, the representation.

## 4. Statement differences that remain, and why they are harmless

### §2: polar data and polar bundles
1. **Southern chart.** Lean writes `U_S × S³` as `U_N × S³` through the reflection `R` of `V`.
   `R` is an isometry commuting with `ρ` and fixing `S(V)`, and it sends `t` to `π − t`. The
   transition becomes `(ζ, u) ↦ (Rζ, θ(x)u)`. This changes coordinates on the `S` chart, not the
   object. The southern disk coordinate is exactly [D]'s `ζ_S = (π − t)x` (`diskN_neg`,
   `DS_eq`).
2. **Dimension.** `n = m + 1 ≥ 1`. [D] assumes `n ≥ 3`, which is never needed, so the Lean
   statements are more general.
3. **"Principal bundle", "star bundle".** Mathlib has no smooth principal bundles. Lean lists
   the defining properties instead: smooth free actions, transitivity on fibres, equivariant
   local trivialisations, and Hausdorffness (`polarBundle_isStarBundle`). A principal-bundle
   isomorphism is a diffeomorphism covering the identity of `Sⁿ` that commutes with the action.
   This is the standard meaning.
4. **The quotient manifold** `P_θ/S³_⋆` is constructed (`QuotSpace D`) and characterised by its
   universal property, rather than obtained from a general quotient-manifold theorem, which
   Mathlib lacks.
5. **`lem:attaching` (1).** "`D_α` is diffeomorphic to the closed disk" is stated as follows:
   `D_α = ψ_α(𝔻)`, where `ψ_α` is a diffeomorphism from an open ball onto an open subset of
   `X`; and `j_α : 𝔻 → X` is smooth (as a map of a manifold with boundary), has invertible
   differential everywhere, is a closed embedding, and has image `D_α`. `D_α` has no smooth
   structure of its own in [D], so this is the standard meaning.
6. **`lem:attaching` (3).** [D]'s "smooth disk gluing" `D_N ∪_σ D_S` uses a product collar. Lean
   defines this gluing (`DiskGluingModel`), proves it is unique up to diffeomorphism for any
   collar width (`diskGluing_unique`), and proves `X ≃ₘ D_N ∪_σ D_S` (`lem_attaching_3`).

### §3: `prop:polar`
1. **Connections** are represented by `Im ℍ`-valued potentials in local trivialisations,
   satisfying the gauge law, which Mathlib lacks for principal bundles. Horizontal lifts solve
   `u' = −A(c')u` in every chart. [D] uses one global connection; Lean builds the invariant
   connection over each cap separately. Steps 3–4 use the connection only over each cap.
2. **Averaging.** Lean averages `L_{q⁻¹}^*ω₀` against left-invariant Haar measure, where [D]
   averages `L_q^*ω₀` against right-invariant measure. On the compact group `S³` these agree.
3. **Coordinates on `U_N`.** Lean uses stereographic coordinates
   `φ(v) = ((1−|v|²)e + 2v)/(1+|v|²)` rather than `exp_{o_N}`. Rays of `φ` are reparametrised
   meridians, and horizontal lifts do not depend on the parametrisation.
4. **Step 2** is proved by a different argument: every injective continuous endomorphism of
   `S³` is inner (`injContEndoInner_S3`). This does not need [D]'s dimension argument for
   `dφ₁`, and it needs no external reference.
5. **Step 6** is proved by a different route. Lean modifies the two equivariant sections so that
   `s'_N = s'_S · θ(x)` holds exactly, with `θ = (s_S⁻¹s_N)|_{S(V)}`. This gives [D]'s conclusion
   (`θ` constant along meridians and conjugation-equivariant) without parallel transport for a
   single connection.

### §4: curvature
1. **One choice of parameters.** Lean fixes `cos a = −3/5` (`F_a = 4/5`) and
   `δ = min(1, 1/(128 A₀ F_a (1 + C_η)))`. [D] allows a range. These satisfy every constraint
   that [D]'s proof uses. [D]'s condition `δ ≤ F_a/2` is used in [D] only to get `η = 1` near
   `ℓ_N`, and Lean checks that consequence directly. One choice suffices for an existence
   statement.
2. **The northern disk** is identified with `{t ≤ a}` by the scaled stereographic chart
   `ψ_N = ψ₁/5` rather than [D]'s `t = (a/ℓ_N)s`. Any diffeomorphism does for an existence
   statement.
3. **`lem:K`** is proved in a stronger form: for every `y` in the closed unit ball and every
   `ξ ∈ ℍ`. For `ρ₁₀` it does not need `x ∈ Im ℍ`.
4. **`B_N + B_S`.** The gluing input needs `≥ 0`, and that is what `hly_general` uses. [D]'s
   strict bound `≥ c_B h` with `c_B > 0` is also proved (`bdry_model_compat`). Lean's constant
   has the same shape as [D]'s, with Lean's own normalisation of the two base terms.
5. **[HLY] Proposition 3.1** (`hly_prop31_global_intrinsic`).
   - **`eq:Lambda`.** Lean assumes `Λ ≥ 16·4·M₀² + 64·4²κ⁻¹(M₁+1)²`; [D] has an extra `+4`.
     Every `Λ` satisfying [D]'s condition satisfies Lean's, so the Lean theorem is stronger.
   - **Norm convention.** [D] writes `|Ω|² = Σ_{i<j,a}(Ω_{ij}^a)²`. Lean's `curvNormSq` sums over
     all `i, j`, which is twice that, so `|Ω| ≤ M₀` reads `curvNormSq ≤ 2M₀²`. The same holds for
     `DΩ`.
   - **Intrinsic norms.** `curvNormSq` and `dcurvNormSq` are computed in an orthonormal frame
     and a local trivialisation. They are proved independent of both (`curvNormSq_eq`,
     `dcurvNormSq_eq`, `Curvature.Prop31.Bundle.Invariance*`).
   - **The Hessian.** `hessAt` is proved to be a tensor (`hessAt_eq`).
   - **Generality.** The base is any compact manifold with corners, so boundary is allowed, as
     [D] requires.
   - **Non-vacuity.** Two models:
     - `[−1, 1] × S³` with the flat connection;
     - the closed round cap of `S²` × `S³`, with a connection whose curvature is nonzero at every
       point.
6. **[DHZ] Proposition 5.1** (`dhz_prop51`). Lean keeps [D]'s northern profile instead of
   [DHZ]'s; the proposition asserts existence, so the choice is immaterial. It proves
   `B_N + J_β^*B_S ≥ 0`, which is what the gluing theorem needs. `n ≥ 3` is not needed.

### §5: the main theorems
1. **Coordinates.** `W₈ = ℝ ⊕ (ℍ⊕ℍ)` and `W₁₀ = ℝ³ ⊕ (ℍ⊕ℍ)` carry the `L²` norm. `ρ₁₀` acts
   trivially on the first factor and by `(w, x) ↦ (qw, qxq⁻¹)` on `ℍ⊕ℍ`, exactly `eq:rho10`.
2. **Positive scalar curvature** (`HasPosScalMetric`) is required in every orthonormal frame.
   Scalar curvature does not depend on the frame, so this is psc. The Hitchin input is
   therefore implied by Hitchin's theorem.
3. **"The round sphere"** is Mathlib's `Metric.sphere` in `ℝⁿ⁺¹`, with its standard smooth
   structure and the induced metric.

## 5. Non-vacuity

Every main theorem is applied to a concrete instance, so that its hypotheses are satisfiable:
- `theoremA (prodBundle rep8)` and `theoremB (prodBundle rep10)`: the product star bundles
  `Sⁿ × S³` for the actual representations `ρ₈`, `ρ₁₀`;
- `prop_polar_trivBundle`;
- `corollaryC_dim10_geom_satisfiable`;
- the two models of `hly_prop31_global_intrinsic`;
- `remark_general_bound_RW (m := 7) (prodBundle rep8)`.

The imported hypotheses themselves (`RWGluing`, Sperança's identification, Kervaire–Milnor,
Hitchin) cannot be witnessed inside Lean. They are published theorems.

## References

See `README.md`.
