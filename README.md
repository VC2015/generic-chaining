# Generic chaining in Lean

This project develops two finite-index theorems that can be used together whenever the increments of a process exhibit Gaussian tails at moderate deviations and exponential tails at larger deviations. Dirksen's inequality bounds the expected maximum using two admissible-net functionals. Talagrand's Gaussian majorizing-measure theorem identifies the Gaussian functional, up to universal constants, with the expected maximum of a Gaussian process in its canonical distance. The finite expectation form of Dirksen’s theorem is proved here with the universal constant 48. Talagrand’s Gaussian lower bound remains open. The modules below contain the checked results.

| Lean module | Checked result |
|---|---|
| `Functional`, `FiniteNets` | The indexed and finite-subset definitions of the chaining functional agree. Pulling the distance back by a surjection preserves the functional. |
| `Discrete` | The discrete distance of scale δ has γ₁ at most 2δ⌊log₂ m⌋ on m ≥ 2 points and zero cost on a singleton. |
| `CommonNet` | Given two choices of centers, each occupied pair admits a representative whose combined weighted approximation error is at most twice the original error. |
| `MixedTail` | A mixed-tail increment hypothesis implies a simultaneous bound for all edges on all levels of a finite chain. The bound is uniform in the number of levels and allows dependent increments. |
| `Link`, `ChainEdges`, `ChainGeometry` | Consecutive common representatives have weighted link length at most twice the new approximation error plus four times the old one; their finite chains have controlled cardinalities and total length. |
| `FiniteCost` | Finite distances have finite γ₁ and γ₂, and nearly optimal admissible nets can be chosen to terminate exactly on the full index set. |
| `TailExpectation`, `ChainingExpectation`, `Dirksen` | `dirksen_expectation` proves E maxₜ abs(Xₜ − Xₜ₀) ≤ 48(γ₂ + γ₁) + 2 maxₜ E abs(Xₜ − Xₜ₀) for mixed-tail increments and finite pseudometrics. The proof includes zero distances and zero total chain length. |
| `GaussianGeometry` | A contrast with zero second moment vanishes almost surely. A finite process and its surjective reindexing have the same maximum almost surely when matched coordinates have zero squared contrast in expectation. |

The first application is Lemma C.2 of the rectangle CLT. There the index set consists of the signed coordinates and zero. The discrete distance accounts for the uniform bound on each summand. The canonical Gaussian distance accounts for the covariance of the sum, including singular covariance. The construction of the expectation proof and the remaining Gaussian and moment targets are specified in the [proof plan](PROOF_PLAN.md). [Rectangle CLT, Appendix C](https://arxiv.org/abs/2611.21474v1)

With Lean's elan toolchain manager installed, run the following commands from the repository root. The project pins Lean 4.19.0 and the same mathlib revision as the original rectangle-CLT verification. The first command retrieves precompiled dependencies.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean checks every proof through the import `GenericChaining`. The last command also traverses the dependencies of every public theorem and fails on an admission or an axiom outside the usual three foundations of mathlib, `propext`, `Classical.choice`, and `Quot.sound`. The imported modules depend only on mathlib and its dependencies.
