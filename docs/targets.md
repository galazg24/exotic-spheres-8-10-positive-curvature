# Formalisation targets

The development was organised as a list of targets. Docstrings refer to them by these labels,
for example "A7" or "D2(b)". This page says what each label means and where it lives.

Each **A** target is a self-contained new argument of [D] that needs only Mathlib. Each **B**
target is a step in the skeleton of [D] `prop:polar`. Each **D** target is a quantitative core
of a step of He–Liu–Yau [HLY] that [D] relies on. The rest of [D] (§§2–5, the main theorems,
and the general [HLY] Proposition 3.1) builds on these.

| Label | Content | [D] / [HLY] reference | Modules (`ExoticSpheres8And10.…`) |
|---|---|---|---|
| A1 | Bound on the infinitesimal action fields, `‖K_y ξ‖ ≤ 2‖ξ‖` | [D] `lem:K` | `ActionField.Bound`, `ActionField.Derivative`, `ActionField.Maximum`, `Main.Representations` |
| A2 | Attaching-map algebra: `y_S = σ(y_N)`, `σ̂ = σ⁻¹` | [D] `lem:attaching`(2) | `PolarBundles.AttachingAlgebra`, `PolarBundles.AttachingSphere` |
| A3 | Orientation of the attaching map | [D] `lem:attaching`(3) | `PolarBundles.Orientation`, `PolarBundles.OrientationDerivative`, `PolarBundles.OrientationSphere` |
| A4 | Gauge algebra of the southern filling | [D] §4.2, items 1 and 3 | `Curvature.Southern.Gauge` |
| A5 | Area inequalities for the star-horizontal graph | [D] §4.3, "Horizontal graph" | `Curvature.Northern.Area` |
| A6 | From the curvature formula to positivity | [D] `eq:fullcurvature` | `Curvature.Criterion`, `Curvature.CriterionDivision` |
| A7 | The northern profile inequalities and their existence | [D] §4.3, "Choice of profiles" | `Curvature.Northern.Profiles*` |
| A8 | Boundary eigenvalue bound and `eq:compat` | [D] §4.4, "Boundary compatibility" | `Curvature.Boundary.Eigenvalues`, `Curvature.Boundary.Cometric`, `Curvature.Boundary.ShapeSum` |
| A9 | Group theory in Corollary C and Theorem B | [D] §5 | `Main.GroupTheory` |
| B1 | Injective continuous endomorphisms of `S³` are inner | [D] `prop:polar`, Step 2 | `StarBundles.InnerEndomorphisms`, `StarBundles.CircleEndomorphisms`, `StarBundles.Continuity` |
| B2 | Equivariance of the transition `θ` | [D] `prop:polar`, Steps 4–6 | `StarBundles.Skeleton` |
| B3 | Independence of the transition from `t` | [D] `prop:polar`, Step 6 | `StarBundles.Skeleton`, `StarBundles.Transport` |
| D1 | The interpolation core of the positive gluing lemma | [HLY] Appendix B.2–B.5 | `Curvature.HLYGluing.Hermite`, `Curvature.HLYGluing.Planes` |
| D2 | The quantitative layer of Proposition 3.1: the ε-budget (a) and the six curvature blocks (b) | [HLY] §3, `prop:concave` | `Curvature.Prop31.*` |

The namespace `ExoticSpheres8And10.Prop31Algebra` contains the purely algebraic part of D2(b).
