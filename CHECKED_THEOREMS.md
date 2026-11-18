# Checked theorem statements

The completed Dirksen proof was preserved at commit `59b590c`, declaration `GenericChaining.dirksen_expectation`. Its audit passes with only `propext`, `Classical.choice`, and `Quot.sound`.

The two Gaussian entry points are `GenericChaining.gamma2_le_gaussianWidth` and `GenericChaining.gaussianWidth_le_gamma2`. They use the concrete product standard Gaussian law, the canonical distance `‖a s - a t‖₊`, and the expected one-sided maximum. Finiteness, translations, singleton families, and repeated vectors are proved in the supporting modules.

`dirksenConstant = 48` and `gaussianExpectationConstant = 100`. The lower constant is the fixed positive real `growthChainingConstant / gaussianGrowthConstant`, where

```lean
growthChainingConstant =
  (2 + 64 * Real.sqrt 2) / Real.sqrt (Real.log 2) + 768 * Real.sqrt 2
gaussianGrowthConstant =
  (1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2))) / 4
```

The following is Lean's `#check` output with implicit arguments exposed. The build and the transitive audit of these declarations pass with the existing three-axiom allowlist.

## Dirksen checkpoint

```lean
@GenericChaining.dirksen_expectation : ∀ {T : Type u_1} {Ω : Type u_2} [inst : Fintype T] [inst : Nonempty T]
  [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [inst_1 : MeasureTheory.IsProbabilityMeasure μ]
  (X : T → Ω → ℝ) (d₁ d₂ : T → T → NNReal),
  (∀ (t : T), d₁ t t = 0) →
    (∀ (t : T), d₂ t t = 0) →
      (∀ (s t : T), d₁ s t = d₁ t s) →
        (∀ (s t : T), d₂ s t = d₂ t s) →
          (∀ (s t c : T), d₁ s t ≤ d₁ s c + d₁ t c) →
            (∀ (s t c : T), d₂ s t ≤ d₂ s c + d₂ t c) →
              GenericChaining.HasMixedTail μ X d₁ d₂ →
                (∀ (s t : T), MeasureTheory.Integrable (fun ω => X s ω - X t ω) μ) →
                  ∀ (t₀ : T),
                    ∫ (ω : Ω), GenericChaining.incrementMaximum X t₀ ω ∂μ ≤
                      GenericChaining.dirksenConstant *
                          ((GenericChaining.gamma2 fun s t => ↑(d₂ s t)).toReal +
                            (GenericChaining.gamma1 fun s t => ↑(d₁ s t)).toReal) +
                        2 * ⨆ t, ∫ (ω : Ω), |X t ω - X t₀ ω| ∂μ
```

## Gaussian majorizing-measure lower bound

```lean
@GenericChaining.gamma2_le_gaussianWidth : ∀ {T : Type u_1} [inst : Fintype T] [inst_1 : Nonempty T] {r : ℕ}
  (a : T → EuclideanSpace ℝ (Fin r)),
  (GenericChaining.gamma2 fun s t => ↑(GenericChaining.canonicalDist a s t)).toReal ≤
    GenericChaining.gaussianMajorizingConstant * GenericChaining.gaussianWidth a
```

## Dirksen-based Gaussian converse

```lean
@GenericChaining.gaussianWidth_le_gamma2 : ∀ {T : Type u_1} [inst : Fintype T] [inst_1 : Nonempty T] {r : ℕ}
  (a : T → EuclideanSpace ℝ (Fin r)),
  GenericChaining.gaussianWidth a ≤
    GenericChaining.gaussianExpectationConstant *
      (GenericChaining.gamma2 fun s t => ↑(GenericChaining.canonicalDist a s t)).toReal
```

## Joint theorem with constants first

```lean
GenericChaining.finite_gaussian_majorizing_measure : ∃ Cₗ Cᵤ,
  0 < Cₗ ∧
    0 < Cᵤ ∧
      ∀ (r : ℕ) (T : Type u_1) [inst : Fintype T] [inst_1 : Nonempty T] (a : T → EuclideanSpace ℝ (Fin r)),
        (GenericChaining.gamma2 fun s t => ↑(GenericChaining.canonicalDist a s t)).toReal ≤
            Cₗ * GenericChaining.gaussianWidth a ∧
          GenericChaining.gaussianWidth a ≤
            Cᵤ * (GenericChaining.gamma2 fun s t => ↑(GenericChaining.canonicalDist a s t)).toReal
```
