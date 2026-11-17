import GenericChaining
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Companion to the numbered report. These examples ask the kernel to match
the statements to the existing proofs. No additional mathematical axioms. -/
open MeasureTheory GenericChaining
open scoped ENNReal NNReal BigOperators
namespace ChainingReport

-- Theorem 1, implemented by Dirksen.dirksen_expectation.
example {T Ω : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : T → Ω → ℝ) (d₁ d₂ : T → T → ℝ≥0)
    (diag₁ : ∀ t, d₁ t t = 0) (diag₂ : ∀ t, d₂ t t = 0)
    (symm₁ : ∀ s t, d₁ s t = d₁ t s) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (htail : HasMixedTail μ X d₁ d₂)
    (hInt : ∀ s t, Integrable (fun ω => X s ω - X t ω) μ) (t₀ : T) :
    ∫ ω, incrementMaximum X t₀ ω ∂μ ≤
      48 * ((gamma2 (fun s t => (d₂ s t : ℝ≥0∞))).toReal +
        (gamma1 (fun s t => (d₁ s t : ℝ≥0∞))).toReal) +
      2 * ⨆ t, ∫ ω, |X t ω - X t₀ ω| ∂μ := dirksen_expectation X d₁ d₂ diag₁ diag₂ symm₁ symm₂ tri₁ tri₂ htail hInt t₀

-- Lemma 1, implemented by Link.weighted_link_bound.
example {T : Type*} (d₁ d₂ : T → T → ℝ≥0)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (symm₁ : ∀ s t, d₁ s t = d₁ t s) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (k : ℕ) (t p q : T) (eprev enext : ℝ)
    (hprev : (2 : ℝ) ^ k * d₁ t p + Real.sqrt 2 ^ k * d₂ t p ≤ 2 * eprev)
    (hnext : (2 : ℝ) ^ (k + 1) * d₁ t q + Real.sqrt 2 ^ (k + 1) * d₂ t q ≤
      2 * enext) :
    (2 : ℝ) ^ (k + 1) * d₁ p q + Real.sqrt 2 ^ (k + 1) * d₂ p q ≤
      2 * enext + 4 * eprev := weighted_link_bound d₁ d₂ tri₁ tri₂ symm₁ symm₂ k t p q eprev enext hprev hnext

-- Lemma 2, implemented by ChainingExpectation.finite_chain_expectation.
example {T Ω : Type*} [Fintype T] [Nonempty T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [DecidableEq T] {X : T → Ω → ℝ} {d₁ d₂ : T → T → ℝ≥0}
    (htail : HasMixedTail μ X d₁ d₂)
    (hInt : ∀ s t, Integrable (fun ω => X s ω - X t ω) μ)
    (r : ℕ → T → T) (K : ℕ) (t₀ : T)
    (hstart : ∀ t, r 0 t = t₀) (hend : ∀ t, r K t = t)
    (hcard : ∀ k, (Finset.univ.image (r k)).card ≤ capacity k ^ 2)
    {B : ℝ} (hB : 0 ≤ B)
    (hlength : ∀ t, (∑ k ∈ Finset.range K,
      ((2 : ℝ) ^ (k+1) * d₁ (r k t) (r (k+1) t) +
       Real.sqrt 2 ^ (k+1) * d₂ (r k t) (r (k+1) t))) ≤ B) :
    ∫ ω, incrementMaximum X t₀ ω ∂μ ≤ 8 * B := finite_chain_expectation htail hInt r K t₀ hstart hend hcard hB hlength

-- Theorem 2, implemented by GaussianChaining.gamma2_le_gaussianWidth.
example {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) :
    (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal ≤
      (growthChainingConstant / gaussianGrowthConstant) * gaussianWidth a := gamma2_le_gaussianWidth a

-- Theorem 2, implemented by GaussianChaining.gaussianWidth_le_gamma2.
example {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) :
    gaussianWidth a ≤ 100 *
      (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal := gaussianWidth_le_gamma2 a

-- Theorem 2, implemented by GaussianChaining.finite_gaussian_majorizing_measure.
example :
    ∃ Cₗ Cᵤ : ℝ, 0 < Cₗ ∧ 0 < Cᵤ ∧
      ∀ (r : ℕ) (T : Type*) [Fintype T] [Nonempty T]
        (a : T → EuclideanSpace ℝ (Fin r)),
        (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal ≤ Cₗ * gaussianWidth a ∧
        gaussianWidth a ≤ Cᵤ * (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal := finite_gaussian_majorizing_measure

-- Lemma 3, implemented by GaussianComparison.gaussianWidth_mono_of_increment_le.
example {I : Type*} [Fintype I] [Nonempty I]
    {r s : ℕ} (A : I → EuclideanSpace ℝ (Fin r)) (B : I → EuclideanSpace ℝ (Fin s))
    (hinc : ∀ i j, ‖B i-B j‖^2 ≤ ‖A i-A j‖^2) : gaussianWidth B ≤ gaussianWidth A := gaussianWidth_mono_of_increment_le A B hinc

-- Lemma 4, implemented by GaussianMinoration.standardGaussian_iid_max_explicit_lower_bound.
example {m : ℕ} [NeZero m] :
    (1 - Real.exp (-(Real.exp (-1) / (2 * Real.sqrt (2 * Real.pi))))) *
        Real.sqrt (Real.log (m : ℝ)) ≤
      ∫ g : Fin m → ℝ, (⨆ i, g i) ∂standardGaussian m := by
  have heq : Real.exp (-1) / (2 * Real.sqrt (2 * Real.pi)) = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1) / 2 := by rw [div_eq_mul_inv, mul_inv_rev]; ring
  rw [heq]
  exact standardGaussian_iid_max_explicit_lower_bound (m := m)

-- Lemma 5, implemented by GaussianLocalGrowth.gaussian_local_growth.
example {m r : ℕ} [NeZero m] {T : Type*}
    [Fintype T] [Nonempty T]
    (a : Fin m → T → EuclideanSpace ℝ (Fin r))
    (c : Fin m → EuclideanSpace ℝ (Fin r)) {δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ δ / 8)
    (hcent : ∀ i j, i ≠ j → δ ≤ ‖c i - c j‖)
    (hloc : ∀ i t, ‖a i t - c i‖ ≤ ρ)
    (b : ℝ) (hb : ∀ i, b ≤ gaussianWidth (a i)) :
    b + gaussianGrowthConstant * δ * Real.sqrt (Real.log (m : ℝ)) ≤
      gaussianWidth (fun it : Fin m × T => a it.1 it.2) := gaussian_local_growth a c hδ hρ hsmall hcent hloc b hb

-- Lemma 6, implemented by GrowthChaining.gamma2_le_of_localGrowth_exact.
example {T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] (d : T → T → ℝ≥0) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s)
    (tri : ∀ s t c, d s t ≤ d s c + d t c)
    (F : Finset T → ℝ) (hF : Monotone F) (hFnn : ∀ A, 0 ≤ F A)
    {c : ℝ} (hc : 0 < c)
    (hgrowth : ∀ (A N : Finset T) (h : ℝ), N.Nonempty → N ⊆ A → 0 < h →
      (∀ s ∈ N, ∀ t ∈ N, s ≠ t → h ≤ d s t) →
      ∃ s ∈ N, c * h * Real.sqrt (Real.log (N.card : ℝ)) +
        F (finiteBall (fun x y => (d x y : ℝ)) A (h / 8) s) ≤ F A) :
    (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal ≤
      growthChainingConstant / c * F Finset.univ := by
  apply gamma2_le_of_localGrowth_exact d diag symm tri F hF hFnn hc
  intro A N h b hN hNA hh hsep hb
  obtain ⟨s, hs, H⟩ := hgrowth A N h hN hNA hh hsep
  have hlocal := hb s hs
  rw [show (1 / 8 : ℝ) * h = h / 8 by ring] at hlocal
  exact (add_le_add_left hlocal _).trans H

-- Lemma 7, implemented by Discrete.gamma1_discrete_le_log2.
example {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    (δ : ℝ≥0) (hT : 2 ≤ Fintype.card T) :
    gamma1 (discreteDist (T := T) δ) ≤ ((2 * (Fintype.card T).log2 : ℕ) : ℝ≥0∞) * δ := gamma1_discrete_le_log2 δ hT

-- Lemma 7, implemented by Discrete.gamma1_discrete_singleton.
example {T : Type*} [Fintype T] [Nonempty T] [Subsingleton T]
    [DecidableEq T] (δ : ℝ≥0) : gamma1 (discreteDist (T := T) δ) = 0 := gamma1_discrete_singleton (T := T) δ

-- Numerical witnesses used in the report.
example : growthChainingConstant =
    (2 + 64 * Real.sqrt 2) / Real.sqrt (Real.log 2) + 768 * Real.sqrt 2 := rfl
example : gaussianGrowthConstant =
    (1 - Real.exp (-(Real.exp (-1) / (2 * Real.sqrt (2 * Real.pi))))) / 4 := by
  have h : Real.exp (-1) / (2 * Real.sqrt (2 * Real.pi)) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1) / 2 := by
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [h]
  rfl

end ChainingReport

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``GenericChaining.dirksen_expectation,
    ``GenericChaining.weighted_link_bound,
    ``GenericChaining.finite_chain_expectation,
    ``GenericChaining.gamma2_le_gaussianWidth,
    ``GenericChaining.gaussianWidth_le_gamma2,
    ``GenericChaining.finite_gaussian_majorizing_measure,
    ``GenericChaining.gaussianWidth_mono_of_increment_le,
    ``GenericChaining.standardGaussian_iid_max_explicit_lower_bound,
    ``GenericChaining.gaussian_local_growth,
    ``GenericChaining.gamma2_le_of_localGrowth_exact,
    ``GenericChaining.gamma1_discrete_le_log2,
    ``GenericChaining.gamma1_discrete_singleton]
  for target in targets do
    for dep in (← Lean.collectAxioms target) do
      unless allowed.contains dep do throwError "{target} depends on {dep}"
