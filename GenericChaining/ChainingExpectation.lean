import GenericChaining.MixedTail
import GenericChaining.Link
import GenericChaining.ChainEdges
import GenericChaining.TailExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# From a finite chain to its expected maximum

The probability estimate is applied to the whole chain before integration.
No division by an edge length is needed, so zero distances cause no exception.
-/
namespace GenericChaining
open MeasureTheory
open scoped NNReal BigOperators

variable {T Ω : Type*} [Fintype T] [Nonempty T] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The maximum absolute increment from a fixed base point. -/
noncomputable def incrementMaximum (X : T → Ω → ℝ) (t₀ : T) (ω : Ω) : ℝ :=
  ⨆ t, |X t ω - X t₀ ω|

omit [Nonempty T] [MeasurableSpace Ω] in
lemma incrementMaximum_nonneg (X : T → Ω → ℝ) (t₀ : T) (ω : Ω) :
    0 ≤ incrementMaximum X t₀ ω := by
  exact (abs_nonneg (X t₀ ω - X t₀ ω)).trans
    (le_ciSup ((Set.finite_range (fun t : T => |X t ω - X t₀ ω|)).bddAbove) t₀)

omit [Nonempty T] [MeasurableSpace Ω] in
lemma increment_le_maximum (X : T → Ω → ℝ) (t₀ t : T) (ω : Ω) :
    |X t ω - X t₀ ω| ≤ incrementMaximum X t₀ ω :=
  le_ciSup ((Set.finite_range (fun t : T => |X t ω - X t₀ ω|)).bddAbove) t

omit [Fintype T] [MeasurableSpace Ω] in
lemma incrementMaximum_le (X : T → Ω → ℝ) (t₀ : T) (ω : Ω) {b : ℝ}
    (h : ∀ t, |X t ω - X t₀ ω| ≤ b) : incrementMaximum X t₀ ω ≤ b :=
  ciSup_le h

lemma abs_chain_le (a : ℕ → ℝ) (K : ℕ) :
    |a K - a 0| ≤ ∑ k ∈ Finset.range K, |a (k+1) - a k| := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ |a K - a 0| + |a (K+1) - a K| := by
        have := abs_add_le (a K - a 0) (a (K+1) - a K)
        convert this using 1
        congr 1
        ring
      _ ≤ _ := add_le_add_right ih _

/-- Tail bound for the maximum along a finite representative chain. -/
theorem finite_chain_tail [DecidableEq T] {X : T → Ω → ℝ} {d₁ d₂ : T → T → ℝ≥0}
    (htail : HasMixedTail μ X d₁ d₂) (r : ℕ → T → T) (K : ℕ) (t₀ : T)
    (hstart : ∀ t, r 0 t = t₀) (hend : ∀ t, r K t = t)
    (hcard : ∀ k, (Finset.univ.image (r k)).card ≤ capacity k ^ 2)
    {B : ℝ}
    (hlength : ∀ t, (∑ k ∈ Finset.range K,
      ((2 : ℝ) ^ (k+1) * d₁ (r k t) (r (k+1) t) +
       Real.sqrt 2 ^ (k+1) * d₂ (r k t) (r (k+1) t))) ≤ B)
    {v : ℝ} (hv : 1 ≤ v) :
    μ.real {ω | (5+v)*B < incrementMaximum X t₀ ω} ≤
      2 * Real.exp (-v) / (1 - Real.exp (-v)) := by
  classical
  let E := ⋃ k ∈ Finset.range (K+1), ⋃ e ∈ chainEdges r k,
    badIncrement X d₁ d₂ ((4+v)*2^k) e
  have hg : ∀ ω ∉ E, incrementMaximum X t₀ ω ≤ (5+v)*B := by
    intro ω hω
    apply incrementMaximum_le
    intro t
    have hedge (k : ℕ) (hk : k < K) :
        |X (r (k+1) t) ω - X (r k t) ω| ≤
          (5+v)*((2 : ℝ) ^ (k+1) * d₁ (r k t) (r (k+1) t) +
            Real.sqrt 2 ^ (k+1) * d₂ (r k t) (r (k+1) t)) := by
      have hnot : ω ∉ badIncrement X d₁ d₂ ((4+v)*2^(k+1))
          (r k t, r (k+1) t) := by
        intro hbad
        apply hω
        exact Set.mem_iUnion.mpr ⟨k+1, Set.mem_iUnion.mpr
          ⟨Finset.mem_range.mpr (by omega), Set.mem_iUnion.mpr
          ⟨(r k t, r (k+1) t), Set.mem_iUnion.mpr
          ⟨Finset.mem_image_of_mem _ (Finset.mem_univ t), hbad⟩⟩⟩⟩
      have hh : |X (r k t) ω - X (r (k+1) t) ω| ≤
          Real.sqrt ((4+v)*2^(k+1)) * d₂ (r k t) (r (k+1) t) +
            ((4+v)*2^(k+1)) * d₁ (r k t) (r (k+1) t) := le_of_not_gt hnot
      rw [abs_sub_comm] at hh
      exact hh.trans (by
        simpa only [show (1 : ℝ) + 4 = 5 by norm_num] using (mixed_threshold_le_weight (k+1)
          (c := 4) (v := v) (by norm_num) (by linarith)
          (d₁ (r k t) (r (k+1) t)) (d₂ (r k t) (r (k+1) t))))
    calc
      |X t ω - X t₀ ω| = |X (r K t) ω - X (r 0 t) ω| := by rw [hend, hstart]
      _ ≤ ∑ k ∈ Finset.range K, |X (r (k+1) t) ω - X (r k t) ω| :=
        abs_chain_le (fun k => X (r k t) ω) K
      _ ≤ ∑ k ∈ Finset.range K, (5+v)*
          ((2 : ℝ) ^ (k+1) * d₁ (r k t) (r (k+1) t) +
            Real.sqrt 2 ^ (k+1) * d₂ (r k t) (r (k+1) t)) :=
        Finset.sum_le_sum fun k hk => hedge k (Finset.mem_range.mp hk)
      _ = (5+v)*_ := (Finset.mul_sum ..).symm
      _ ≤ (5+v)*B := mul_le_mul_of_nonneg_left (hlength t) (by linarith)
  have hsub : {ω | (5+v)*B < incrementMaximum X t₀ ω} ⊆ E := by
    intro ω hω
    apply Classical.byContradiction
    intro hn
    exact (not_lt_of_ge (hg ω hn)) hω
  exact (measureReal_mono hsub).trans (htail.dyadic_edge_bound (chainEdges r) (K+1)
    (c := 4) (by norm_num) (by linarith) (fun k _ => chainEdges_card_exp r hcard k))

/-- The universal factor obtained by integrating the finite-chain tail. -/
def chainExpectationConstant : ℝ := 8

lemma chainExpectationConstant_pos : 0 < chainExpectationConstant := by
  norm_num [chainExpectationConstant]

omit [IsProbabilityMeasure μ] in
lemma integrable_incrementMaximum {X : T → Ω → ℝ} (t₀ : T)
    (hInt : ∀ s t, Integrable (fun ω => X s ω - X t ω) μ) :
    Integrable (incrementMaximum X t₀) μ :=
  integrable_iSup_finite (fun t => (hInt t t₀).abs)

/-- The expected maximum along a chain is bounded by a universal constant
 times its deterministic weighted length, including when that length is zero. -/
theorem finite_chain_expectation [DecidableEq T] {X : T → Ω → ℝ} {d₁ d₂ : T → T → ℝ≥0}
    (htail : HasMixedTail μ X d₁ d₂)
    (hInt : ∀ s t, Integrable (fun ω => X s ω - X t ω) μ)
    (r : ℕ → T → T) (K : ℕ) (t₀ : T)
    (hstart : ∀ t, r 0 t = t₀) (hend : ∀ t, r K t = t)
    (hcard : ∀ k, (Finset.univ.image (r k)).card ≤ capacity k ^ 2)
    {B : ℝ} (hB : 0 ≤ B)
    (hlength : ∀ t, (∑ k ∈ Finset.range K,
      ((2 : ℝ) ^ (k+1) * d₁ (r k t) (r (k+1) t) +
       Real.sqrt 2 ^ (k+1) * d₂ (r k t) (r (k+1) t))) ≤ B) :
    ∫ ω, incrementMaximum X t₀ ω ∂μ ≤ chainExpectationConstant * B := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / chainExpectationConstant
  have hδ : 0 < δ := div_pos hε chainExpectationConstant_pos
  have h := integral_le_of_scaled_dyadic_tail_coarse
    (integrable_incrementMaximum t₀ hInt) 5 (B := B+δ) (by linarith)
    (fun v hv => finite_chain_tail htail r K t₀ hstart hend hcard
      (fun t => (hlength t).trans (by linarith)) hv)
  have heq : (5+3)*(B+δ) = chainExpectationConstant*B+ε := by
    dsimp [δ, chainExpectationConstant]
    ring
  rwa [heq] at h

end GenericChaining
