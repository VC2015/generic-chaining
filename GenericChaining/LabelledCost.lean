import GenericChaining.GrowthPartitions
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Analytic estimates for cumulative-label cuts

A threshold cut turns a dyadic level into a spatial scale. Grouping those
levels by spatial scale bounds the resulting branch cost by a geometric sum
of the square roots of the cumulative code lengths.
-/

namespace GenericChaining

/-- A finite collection of dyadic square-root weights below a common squared
threshold has total weight at most four times its square root. -/
theorem sum_sqrt_two_pow_le (S : Finset ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hpow : ∀ n ∈ S, (2 : ℝ) ^ n ≤ L) :
    ∑ n ∈ S, Real.sqrt 2 ^ n ≤ 4 * Real.sqrt L := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hm : m ∈ S := S.max'_mem hS
    have hsub : S ⊆ Finset.range (m + 1) := by
      intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' n hn))
    have hqnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hq : 1 < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hq4 : 4 ≤ 3 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hgeom : (∑ n ∈ Finset.range (m + 1), Real.sqrt 2 ^ n) ≤
        4 * Real.sqrt 2 ^ m := by
      apply (mul_le_mul_right (sub_pos.mpr hq)).mp
      have heq := geom_sum_mul (Real.sqrt 2) (m + 1)
      rw [pow_succ] at heq
      have hmul := mul_nonneg (sub_nonneg.mpr hq4) (pow_nonneg hqnn m)
      nlinarith
    have hsq : (Real.sqrt 2 ^ m) ^ 2 = (2 : ℝ) ^ m := by
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hroot : Real.sqrt 2 ^ m ≤ Real.sqrt L := by
      nlinarith [hpow m hm, Real.sq_sqrt hL, pow_nonneg hqnn m, Real.sqrt_nonneg L]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => pow_nonneg hqnn n)).trans (hgeom.trans (by linarith))
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hS0, Finset.sum_empty]
    positivity

/-- Regrouping dyadic cut costs by spatial scale. Only the threshold
inequality and monotonicity of cumulative code length are needed. -/
theorem dyadic_cut_sum_le (cut : ℕ → ℕ) (L : ℕ → ℝ) {α B : ℝ}
    (hα : 0 ≤ α) (hL : ∀ k, 0 ≤ L k) (hmono : Monotone L)
    (hthreshold : ∀ n, (2 : ℝ) ^ n ≤ L (cut n + 1))
    (hspatial : ∀ M, (∑ k ∈ Finset.range M, α ^ k * Real.sqrt (L (k + 1))) ≤ B)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.sqrt 2 ^ n * α ^ cut n ≤ 4 * B := by
  classical
  let M := (Finset.range N).sup cut
  have hcut (n : ℕ) (hn : n ∈ Finset.range N) : cut n ≤ M := Finset.le_sup hn
  have hsingle (n : ℕ) (hn : n ∈ Finset.range N) :
      α ^ cut n ≤ ∑ k ∈ Finset.range (M + 1), if cut n ≤ k then α ^ k else 0 := by
    have hh := Finset.single_le_sum (f := fun k => if cut n ≤ k then α ^ k else 0)
      (s := Finset.range (M + 1)) (fun k _ => by dsimp; split <;> positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hcut n hn)))
    simpa only [le_refl, if_true] using hh
  calc
    _ ≤ ∑ n ∈ Finset.range N, Real.sqrt 2 ^ n *
        (∑ k ∈ Finset.range (M + 1), if cut n ≤ k then α ^ k else 0) :=
      Finset.sum_le_sum fun n hn =>
        mul_le_mul_of_nonneg_left (hsingle n hn) (by positivity)
    _ = ∑ k ∈ Finset.range (M + 1), α ^ k *
        (∑ n ∈ (Finset.range N).filter (fun n => cut n ≤ k), Real.sqrt 2 ^ n) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      split <;> simp_all only [mul_zero, zero_mul, mul_comm]
    _ ≤ ∑ k ∈ Finset.range (M + 1), α ^ k * (4 * Real.sqrt (L (k + 1))) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hα k)
      apply sum_sqrt_two_pow_le _ (hL _)
      intro n hn
      have hnk := (Finset.mem_filter.mp hn).2
      exact (hthreshold n).trans (hmono (Nat.add_le_add_right hnk 1))
    _ = 4 * ∑ k ∈ Finset.range (M + 1), α ^ k * Real.sqrt (L (k + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 4 * B := mul_le_mul_of_nonneg_left (hspatial _) (by norm_num)

/-- The cut cost is summable whenever the spatial code-length cost is bounded. -/
theorem dyadic_cut_tsum_le (cut : ℕ → ℕ) (L : ℕ → ℝ) {α B : ℝ}
    (hα : 0 ≤ α) (hL : ∀ k, 0 ≤ L k) (hmono : Monotone L)
    (hthreshold : ∀ n, (2 : ℝ) ^ n ≤ L (cut n + 1))
    (hspatial : ∀ M, (∑ k ∈ Finset.range M, α ^ k * Real.sqrt (L (k + 1))) ≤ B) :
    Summable (fun n => Real.sqrt 2 ^ n * α ^ cut n) ∧
      ∑' n, Real.sqrt 2 ^ n * α ^ cut n ≤ 4 * B := by
  have ha (n : ℕ) : 0 ≤ Real.sqrt 2 ^ n * α ^ cut n := by positivity
  have hh := dyadic_cut_sum_le cut L hα hL hmono hthreshold hspatial
  exact ⟨summable_of_sum_range_le ha hh, Real.tsum_le_of_sum_range_le ha hh⟩

end GenericChaining

namespace GenericChaining

/-- Finite summation by parts for weighted prefix sums. -/
theorem weighted_prefix_identity (b : ℕ → ℝ) (α : ℝ) (M : ℕ) :
    (1 - α) * (∑ k ∈ Finset.range M, α ^ k * (∑ j ∈ Finset.range (k + 1), b j)) =
      (∑ j ∈ Finset.range M, α ^ j * b j) - α ^ M * (∑ j ∈ Finset.range M, b j) := by
  let P (k : ℕ) := ∑ j ∈ Finset.range k, b j
  have hP (k : ℕ) : P (k + 1) = P k + b k := Finset.sum_range_succ b k
  change (1 - α) * (∑ k ∈ Finset.range M, α ^ k * P (k + 1)) =
    (∑ j ∈ Finset.range M, α ^ j * b j) - α ^ M * P M
  induction M with
  | zero => simp [P]
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ, pow_succ, hP]
    ring

/-- Geometric weighting controls a prefix sum by twice its weighted input. -/
theorem weighted_prefix_le (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) {α : ℝ}
    (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2) (M : ℕ) :
    (∑ k ∈ Finset.range M, α ^ k * (∑ j ∈ Finset.range (k + 1), b j)) ≤
      2 * ∑ j ∈ Finset.range M, α ^ j * b j := by
  have hid := weighted_prefix_identity b α M
  have htail : 0 ≤ α ^ M * (∑ j ∈ Finset.range M, b j) :=
    mul_nonneg (pow_nonneg hα M) (Finset.sum_nonneg fun j _ => hb j)
  have hsum : 0 ≤ ∑ k ∈ Finset.range M, α ^ k * (∑ j ∈ Finset.range (k + 1), b j) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (pow_nonneg hα k) (Finset.sum_nonneg fun j _ => hb j)
  nlinarith

/-- The first moment of a geometric sequence is uniformly bounded for
ratios at most one half. -/
theorem geom_weighted_level_le {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2) (M : ℕ) :
    (∑ k ∈ Finset.range M, α ^ k * (k + 1 : ℝ)) ≤ 4 := by
  have hgeom : (∑ k ∈ Finset.range M, α ^ k) ≤ (2 : ℝ) := by
    have hid := geom_sum_mul_neg α M
    have hsum : 0 ≤ ∑ k ∈ Finset.range M, α ^ k := Finset.sum_nonneg fun k _ => pow_nonneg hα k
    have hpow := pow_nonneg hα M
    nlinarith
  have hprefix := weighted_prefix_le (fun _ => (1 : ℝ)) (fun _ => zero_le_one) hα hαhalf M
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] at hprefix
  nlinarith

/-- A square-root bound for cumulative code lengths reduces the entire
spatial cost to the labelled branch sum and an initial-scale term. -/
theorem spatial_code_sum_le (b L : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k)
    {α A C : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2) (hA : 0 ≤ A)
    (hsqrt : ∀ k, Real.sqrt (L (k + 1)) ≤
      A * (k + 1 : ℝ) + A * (∑ j ∈ Finset.range (k + 1), b j))
    (hbranch : ∀ M, (∑ j ∈ Finset.range M, α ^ j * b j) ≤ C) (M : ℕ) :
    (∑ k ∈ Finset.range M, α ^ k * Real.sqrt (L (k + 1))) ≤ A * (4 + 2 * C) := by
  have hlevel := geom_weighted_level_le hα hαhalf M
  have hprefix := weighted_prefix_le b hb hα hαhalf M
  have hB := hbranch M
  calc
    _ ≤ ∑ k ∈ Finset.range M, α ^ k *
        (A * (k + 1 : ℝ) + A * (∑ j ∈ Finset.range (k + 1), b j)) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hsqrt k) (pow_nonneg hα k)
    _ = A * (∑ k ∈ Finset.range M, α ^ k * (k + 1 : ℝ)) +
        A * (∑ k ∈ Finset.range M, α ^ k * (∑ j ∈ Finset.range (k + 1), b j)) := by
      calc
        _ = ∑ k ∈ Finset.range M,
            (A * (α ^ k * (k + 1 : ℝ)) +
              A * (α ^ k * (∑ j ∈ Finset.range (k + 1), b j))) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith

/-- The complete analytic cut estimate, with a fixed ratio at most one half.
The hypotheses speak only about local labels and cumulative code lengths. -/
theorem dyadic_cut_cost_le (cut : ℕ → ℕ) (L b : ℕ → ℝ)
    {α A B D : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hA : 0 ≤ A) (hD : 0 < D)
    (hb : ∀ k, 0 ≤ b k) (hL : ∀ k, 0 ≤ L k) (hmono : Monotone L)
    (hthreshold : ∀ n, (2 : ℝ) ^ n ≤ L (cut n + 1))
    (hsqrt : ∀ k, Real.sqrt (L (k + 1)) ≤
      A * (k + 1 : ℝ) + A * (∑ j ∈ Finset.range (k + 1), b j))
    (hbranch : ∀ M, (∑ j ∈ Finset.range M, D * α ^ (j + 1) * b j) ≤ B) :
    Summable (fun n => D * (Real.sqrt 2 ^ n * α ^ cut n)) ∧
      (∑' n, D * (Real.sqrt 2 ^ n * α ^ cut n)) ≤ 16 * A * D + 8 * A * B / α := by
  have hC (M : ℕ) : (∑ j ∈ Finset.range M, α ^ j * b j) ≤ B / (D * α) := by
    apply (le_div_iff₀ (mul_pos hD hα)).mpr
    have heq : (∑ j ∈ Finset.range M, α ^ j * b j) * (D * α) =
        ∑ j ∈ Finset.range M, D * α ^ (j + 1) * b j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
    rw [heq]
    exact hbranch M
  have hsp := spatial_code_sum_le b L hb hα.le hαhalf hA hsqrt hC
  obtain ⟨hsum, hbound⟩ := dyadic_cut_tsum_le cut L hα.le hL hmono hthreshold hsp
  refine ⟨hsum.mul_left D, ?_⟩
  rw [tsum_mul_left]
  have hh := mul_le_mul_of_nonneg_left hbound hD.le
  have heq : D * (4 * (A * (4 + 2 * (B / (D * α))))) =
      16 * A * D + 8 * A * B / α := by
    field_simp; ring
  rwa [heq] at hh

end GenericChaining

namespace GenericChaining

/-- The cumulative squared-label code length, normalized to base two. -/
noncomputable def labelCodeLength (lab : ℕ → ℕ) (k : ℕ) : ℝ :=
  2 * k + (2 / Real.log 2) * ∑ j ∈ Finset.range k, Real.log (lab (j + 1) : ℝ)

theorem log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hh ⊢
  exact hh

theorem labelCodeLength_nonneg (lab : ℕ → ℕ) (hlab : ∀ k, 0 < lab k) (k : ℕ) :
    0 ≤ labelCodeLength lab k := by
  have hlog (j : ℕ) : 0 ≤ Real.log (lab j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hlab j)
  unfold labelCodeLength
  exact add_nonneg (by positivity) (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ => hlog _))

theorem labelCodeLength_succ (lab : ℕ → ℕ) (k : ℕ) :
    labelCodeLength lab (k + 1) = labelCodeLength lab k +
      2 + (2 / Real.log 2) * Real.log (lab (k + 1) : ℝ) := by
  simp only [labelCodeLength, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem labelCodeLength_monotone (lab : ℕ → ℕ) (hlab : ∀ k, 0 < lab k) :
    Monotone (labelCodeLength lab) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [labelCodeLength_succ]
  have hh : 0 ≤ (2 / Real.log 2) * Real.log (lab (k + 1) : ℝ) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hlab (k + 1)))
  linarith

theorem labelCodeLength_mul_log_two (lab : ℕ → ℕ) (k : ℕ) :
    labelCodeLength lab k * Real.log 2 =
      (k : ℝ) * Real.log 4 + 2 * ∑ j ∈ Finset.range k, Real.log (lab (j + 1) : ℝ) := by
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold labelCodeLength
  rw [hlog]
  field_simp; ring

/-- Cumulative code lengths have a square-root bound in terms of the local
square-root logarithmic labels. The numerical constant is uniform in depth. -/
theorem labelCodeLength_sqrt_le (lab : ℕ → ℕ) (hlab : ∀ k, 0 < lab k) (k : ℕ) :
    Real.sqrt (labelCodeLength lab (k + 1)) ≤
      2 * (k + 1 : ℝ) + 2 * ∑ j ∈ Finset.range (k + 1),
        Real.sqrt (Real.log (lab (j + 1) : ℝ)) := by
  let b (j : ℕ) := Real.sqrt (Real.log (lab (j + 1) : ℝ))
  have hlog (j : ℕ) : 0 ≤ Real.log (lab j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hlab j)
  have hb (j : ℕ) : 0 ≤ b j := Real.sqrt_nonneg _
  have hbsq (j : ℕ) : b j ^ 2 = Real.log (lab (j + 1) : ℝ) := Real.sq_sqrt (hlog _)
  have hcoeff : 2 / Real.log 2 ≤ (4 : ℝ) := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    linarith [log_two_ge_half]
  have hsumlog : 0 ≤ ∑ j ∈ Finset.range (k + 1), Real.log (lab (j + 1) : ℝ) :=
    Finset.sum_nonneg fun j _ => hlog _
  have hcode : labelCodeLength lab (k + 1) ≤
      4 * (k + 1 : ℝ) + 4 * ∑ j ∈ Finset.range (k + 1), b j ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hcoeff hsumlog
    simp only [hbsq]
    unfold labelCodeLength
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hsum : 0 ≤ ∑ j ∈ Finset.range (k + 1), b j := Finset.sum_nonneg fun j _ => hb _
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.range (k + 1)) (f := b) (fun j _ => hb j)
  have hm : (1 : ℝ) ≤ k + 1 := by have hh : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  change labelCodeLength lab (k + 1) ≤ (2 * (k + 1 : ℝ) +
    2 * ∑ j ∈ Finset.range (k + 1), b j) ^ 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show (0 : ℝ) ≤ k + 1 by positivity),
    mul_nonneg (show (0 : ℝ) ≤ k + 1 by positivity) hsum]

end GenericChaining
