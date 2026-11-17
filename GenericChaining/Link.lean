import GenericChaining.CommonNet
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Weighted lengths of representative links

The error of each representative is controlled in the sum of the two weighted
metrics. Increasing a level multiplies the exponential weight by two and the
Gaussian weight by `sqrt 2`, which is at most two. The triangle inequalities
therefore bound a link by twice the new error plus four times the old error.
-/

namespace GenericChaining

open scoped NNReal ENNReal

/-- The common representatives lemma for finite nonnegative distances and weights. -/
theorem exists_common_representatives_nnreal {T I J : Type*} [Fintype T] [Nonempty T]
    (d₁ d₂ : T → T → ℝ≥0)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (u v : ℝ≥0) (a : I → T) (b : J → T) (i₁ : T → I) (i₂ : T → J) :
    ∃ r : I × J → T, ∀ t, let s := r (i₁ t, i₂ t)
      i₁ s = i₁ t ∧ i₂ s = i₂ t ∧
      u * d₁ t s + v * d₂ t s ≤ 2 * (u * d₁ t (a (i₁ t)) + v * d₂ t (b (i₂ t))) := by
  obtain ⟨r, hr⟩ := exists_common_representatives
    (fun s t => (d₁ s t : ℝ≥0∞)) (fun s t => (d₂ s t : ℝ≥0∞))
    (fun s t c => by
      change (d₁ s t : ℝ≥0∞) ≤ (d₁ s c : ℝ≥0∞) + (d₁ t c : ℝ≥0∞)
      exact_mod_cast tri₁ s t c)
    (fun s t c => by
      change (d₂ s t : ℝ≥0∞) ≤ (d₂ s c : ℝ≥0∞) + (d₂ t c : ℝ≥0∞)
      exact_mod_cast tri₂ s t c)
    (u : ℝ≥0∞) (v : ℝ≥0∞) a b i₁ i₂
  refine ⟨r, fun t => ⟨(hr t).1, (hr t).2.1, ?_⟩⟩
  exact_mod_cast (hr t).2.2

/-- A real-valued version of the common-representative error estimate. -/
theorem exists_common_representatives_real {T I J : Type*} [Fintype T] [Nonempty T]
    (d₁ d₂ : T → T → ℝ≥0)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (a : I → T) (b : J → T) (i₁ : T → I) (i₂ : T → J) :
    ∃ r : I × J → T, ∀ t, let s := r (i₁ t, i₂ t)
      i₁ s = i₁ t ∧ i₂ s = i₂ t ∧
      u * (d₁ t s : ℝ) + v * (d₂ t s : ℝ) ≤
        2 * (u * (d₁ t (a (i₁ t)) : ℝ) + v * (d₂ t (b (i₂ t)) : ℝ)) := by
  obtain ⟨r, hr⟩ := exists_common_representatives_nnreal d₁ d₂ tri₁ tri₂
    ⟨u, hu⟩ ⟨v, hv⟩ a b i₁ i₂
  refine ⟨r, fun t => ⟨(hr t).1, (hr t).2.1, ?_⟩⟩
  exact_mod_cast (hr t).2.2

/-- A consecutive link, weighted at the new level, is bounded by the two
representative approximation errors. This includes zero distances. -/
theorem weighted_link_bound {T : Type*} (d₁ d₂ : T → T → ℝ≥0)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (symm₁ : ∀ s t, d₁ s t = d₁ t s) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (k : ℕ) (t p q : T) (eprev enext : ℝ)
    (hprev : (2 : ℝ) ^ k * d₁ t p + Real.sqrt 2 ^ k * d₂ t p ≤ 2 * eprev)
    (hnext : (2 : ℝ) ^ (k + 1) * d₁ t q + Real.sqrt 2 ^ (k + 1) * d₂ t q ≤
      2 * enext) :
    (2 : ℝ) ^ (k + 1) * d₁ p q + Real.sqrt 2 ^ (k + 1) * d₂ p q ≤
      2 * enext + 4 * eprev := by
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have hd₁ : (d₁ p q : ℝ) ≤ (d₁ t p : ℝ) + d₁ t q := by
    exact_mod_cast (show d₁ p q ≤ d₁ t p + d₁ t q by
      simpa only [symm₁ p t, symm₁ q t] using tri₁ p q t)
  have hd₂ : (d₂ p q : ℝ) ≤ (d₂ t p : ℝ) + d₂ t q := by
    exact_mod_cast (show d₂ p q ≤ d₂ t p + d₂ t q by
      simpa only [symm₂ p t, symm₂ q t] using tri₂ p q t)
  have hscale : Real.sqrt 2 ^ (k + 1) * (d₂ t p : ℝ) ≤
      2 * (Real.sqrt 2 ^ k * (d₂ t p : ℝ)) := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hsqrt
      (show 0 ≤ Real.sqrt 2 ^ k * (d₂ t p : ℝ) by positivity)]
  calc
    _ ≤ (2 : ℝ) ^ (k + 1) * ((d₁ t p : ℝ) + d₁ t q) +
        Real.sqrt 2 ^ (k + 1) * ((d₂ t p : ℝ) + d₂ t q) :=
      add_le_add (mul_le_mul_of_nonneg_left hd₁ (by positivity))
        (mul_le_mul_of_nonneg_left hd₂ (by positivity))
    _ ≤ 2 * ((2 : ℝ) ^ k * d₁ t p + Real.sqrt 2 ^ k * d₂ t p) +
        ((2 : ℝ) ^ (k + 1) * d₁ t q + Real.sqrt 2 ^ (k + 1) * d₂ t q) := by
      simp only [pow_succ] at hscale ⊢
      nlinarith
    _ ≤ 2 * enext + 4 * eprev := by linarith

/-- The Gaussian dyadic weight is exactly the square root of the exponential weight. -/
theorem sqrt_two_pow (k : ℕ) : Real.sqrt ((2 : ℝ) ^ k) = Real.sqrt 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- A dyadic mixed-tail threshold is at most a linear parameter times the
weighted link length. This estimate is uniform in the level. -/
theorem mixed_threshold_le_weight (k : ℕ) {c v : ℝ} (hc : 0 ≤ c) (hv : 0 ≤ v)
    (a b : ℝ≥0) :
    Real.sqrt ((c + v) * (2 : ℝ) ^ k) * b + ((c + v) * (2 : ℝ) ^ k) * a ≤
      (1 + c + v) * ((2 : ℝ) ^ k * a + Real.sqrt 2 ^ k * b) := by
  have hx : 0 ≤ c + v := add_nonneg hc hv
  have hs : Real.sqrt (c + v) ≤ 1 + c + v := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith
  rw [Real.sqrt_mul hx, sqrt_two_pow]
  have hb : 0 ≤ Real.sqrt 2 ^ k * (b : ℝ) := by positivity
  have ha : 0 ≤ (2 : ℝ) ^ k * (a : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hs hb]

end GenericChaining
