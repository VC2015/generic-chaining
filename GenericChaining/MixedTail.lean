import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Real

/-!
# Simultaneous control of mixed-tail increments

At each level a finite family of pairs is tested. Increasing the tail parameter
by the logarithm of the family size pays for all pairs at that level. The
geometric estimate below sums the remaining probabilities uniformly in depth.
-/

namespace GenericChaining

open MeasureTheory
open scoped NNReal

variable {T Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {X : T → Ω → ℝ} {d₁ d₂ : T → T → ℝ≥0}

/-- The event that an increment exceeds its two-scale threshold.
Multiplicative tail scales may be included in the two distances. -/
def badIncrement (X : T → Ω → ℝ) (d₁ d₂ : T → T → ℝ≥0) (u : ℝ)
    (e : T × T) : Set Ω :=
  {ω | Real.sqrt u * (d₂ e.1 e.2 : ℝ) + u * d₁ e.1 e.2 < |X e.1 ω - X e.2 ω|}

/-- Dirksen's mixed sub-Gaussian and sub-exponential increment condition. -/
def HasMixedTail (μ : Measure Ω) (X : T → Ω → ℝ) (d₁ d₂ : T → T → ℝ≥0) : Prop :=
  ∀ (s t : T) (u : ℝ), 0 < u →
    μ.real (badIncrement X d₁ d₂ u (s, t)) ≤ 2 * Real.exp (-u)

/-- Union bound over the edges of a single level. Dependence between edges is arbitrary. -/
theorem HasMixedTail.level_bound (h : HasMixedTail μ X d₁ d₂)
    (edges : Finset (T × T)) {u : ℝ} (hu : 0 < u) :
    μ.real (⋃ e ∈ edges, badIncrement X d₁ d₂ u e) ≤ edges.card * (2 * Real.exp (-u)) := by
  calc
    _ ≤ ∑ e ∈ edges, μ.real (badIncrement X d₁ d₂ u e) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _e ∈ edges, 2 * Real.exp (-u) :=
      Finset.sum_le_sum fun e _ => h e.1 e.2 u hu
    _ = _ := by simp

/-- If level `k` tests at most `exp (c * 2^k)` edges, then the probability of an
exceedance at any of the first `K` levels is at most `2 exp(-v)/(1-exp(-v))`.
The bound is uniform in `K`. -/
theorem HasMixedTail.dyadic_edge_bound (h : HasMixedTail μ X d₁ d₂)
    (edges : ℕ → Finset (T × T)) (K : ℕ) {c v : ℝ} (hc : 0 ≤ c) (hv : 0 < v)
    (hcard : ∀ k < K, ((edges k).card : ℝ) ≤ Real.exp (c * 2 ^ k)) :
    μ.real (⋃ k ∈ Finset.range K, ⋃ e ∈ edges k,
      badIncrement X d₁ d₂ ((c + v) * 2 ^ k) e) ≤
      2 * Real.exp (-v) / (1 - Real.exp (-v)) := by
  let r := Real.exp (-v)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hv)
  have perLevel (k : ℕ) (hk : k < K) :
      μ.real (⋃ e ∈ edges k, badIncrement X d₁ d₂ ((c + v) * 2 ^ k) e) ≤
        (2 * r) * r ^ k := by
    calc
      _ ≤ (edges k).card * (2 * Real.exp (-((c + v) * 2 ^ k))) :=
        h.level_bound _ (mul_pos (add_pos_of_nonneg_of_pos hc hv) (by positivity))
      _ ≤ Real.exp (c * 2 ^ k) * (2 * Real.exp (-((c + v) * 2 ^ k))) :=
        mul_le_mul_of_nonneg_right (hcard k hk) (by positivity)
      _ = 2 * Real.exp (-v * 2 ^ k) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * Real.exp (-v * (k + 1)) := by
        have hk' : (k : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k))
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hk' (neg_nonpos.mpr hv.le))) (by norm_num)
      _ = (2 * r) * r ^ k := by
        rw [mul_add, mul_one, mul_comm (-v) (k : ℝ), Real.exp_add, Real.exp_nat_mul]
        dsimp [r]
        ring
  let a := 2 * r
  have hsum := (hasSum_geometric_of_lt_one hr0 hr1).mul_left a
  calc
    _ ≤ ∑ k ∈ Finset.range K, μ.real (⋃ e ∈ edges k,
            badIncrement X d₁ d₂ ((c + v) * 2 ^ k) e) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range K, a * r ^ k :=
      Finset.sum_le_sum fun k hk => perLevel k (Finset.mem_range.mp hk)
    _ ≤ ∑' k : ℕ, a * r ^ k := hsum.summable.sum_le_tsum _ (fun k _ =>
      mul_nonneg (mul_nonneg (by norm_num) hr0) (pow_nonneg hr0 k))
    _ = _ := by rw [hsum.tsum_eq, div_eq_mul_inv]

end GenericChaining
