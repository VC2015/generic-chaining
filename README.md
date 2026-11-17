# Generic chaining in Lean

This project proves the finite expectation form of Dirksen's mixed-tail theorem and both directions of the finite Gaussian majorizing-measure theorem. The index set may contain repeated vectors and the canonical distance may be a pseudometric.

For vectors `a : T → EuclideanSpace ℝ (Fin r)`, the Gaussian process is evaluated under the concrete product of `r` standard real Gaussian laws. Its canonical distance is `d(s,t) = ‖a s - a t‖`, and its width `W(T)` is the expected **one-sided** maximum of the projections. The checked statements are

$$
\gamma_2(T,d) \le C\,W(T), \qquad W(T) \le 100\,\gamma_2(T,d).
$$

The positive constant `C = gaussianMajorizingConstant` is fixed before the dimension, index set, and vectors. The public theorems are `GenericChaining.gamma2_le_gaussianWidth` and `GenericChaining.gaussianWidth_le_gamma2`; `finite_gaussian_majorizing_measure` exports them together with both constants quantified first. The extended chaining costs are proved finite before conversion to real values. Common translations preserve width and cost; a singleton has both width and cost zero.

| Lean modules | Checked results |
|---|---|
| `Functional`, `FiniteNets`, `Discrete` | Indexed and finite-subset chaining definitions agree; surjective pullbacks preserve the functional; the discrete γ₁ bound is logarithmic. |
| `CommonNet`, `Link`, `ChainEdges`, `FiniteCost`, `ChainGeometry` | Common representatives, the consecutive weighted-link bound, edge counting, terminating near-optimal nets, and finite chain-length estimates. |
| `MixedTail`, `TailExpectation`, `ChainingExpectation`, `Dirksen` | `dirksen_expectation` proves E max abs(Xₜ − Xₜ₀) ≤ 48(γ₂ + γ₁) + 2 max E abs(Xₜ − Xₜ₀), including zero distances and zero total chain length. |
| `GaussianCore`, `GaussianMetric`, `GaussianTail`, `GaussianWidth`, `GaussianFiniteWidth` | Concrete product Gaussian law, projection MGFs and tails, canonical second moments, integrable finite maxima, local widths, translations, and repeated vectors. |
| `GaussianStein`, `GaussianProductStein`, `GaussianSmoothMax`, `GaussianSoftMaxStein`, `GaussianInterpolation`, `GaussianComparison`, `GaussianEmbedding` | Scalar and product Stein identities, smooth-max calculus, differentiation under the integral, orthogonal embeddings, and finite Sudakov–Fernique comparison. |
| `GaussianMinoration`, `GaussianGrowth`, `GaussianLocalGrowth`, `GaussianGrowthFunctional` | Explicit iid Gaussian maximum minoration and concrete local width growth for separated centers with local radius at most one eighth of the separation. |
| `GrowthPartitions`, `LabelledNets`, `LabelledCost`, `GrowthChaining` | Actual greedy labelled partitions, branch telescoping, inverse-mass threshold cuts, exact admissible capacities, and comparison with the repository's γ₂ functional. |
| `GaussianFunctional`, `GaussianChaining` | Scaling and diameter control, the majorizing-measure lower bound, and the converse obtained from Dirksen. |
| `GaussianGeometry` | Zero second moments identify coordinates almost surely; surjective quotient processes have the same finite maximum. |

The lower bound is the direction needed for Lemma C.2 of the rectangle CLT. The rectangle project can import a fixed revision and instantiate it on the signed coordinates and zero. The full moment and deviation forms of Dirksen's theorem and extensions to infinite index sets remain future work.

The completed Dirksen checkpoint is commit `59b590c` (`GenericChaining.dirksen_expectation`). Its exact type, the two Gaussian theorem types, and the joint statement are recorded in [CHECKED_THEOREMS.md](CHECKED_THEOREMS.md). The construction and source references are in [PROOF_PLAN.md](PROOF_PLAN.md) and [GAUSSIAN_ASSIGNMENT.md](GAUSSIAN_ASSIGNMENT.md).

The project pins Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With elan installed, run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The build and audit pass. The audit traverses the exported mathematical declarations and rejects admissions or axioms outside `propext`, `Classical.choice`, and `Quot.sound`.
