import GenericChaining.FiniteNets

/-!
# The discrete contribution to mixed-tail chaining

Suppose a contrast has a uniform large-deviation scale `δ`. Put distance `δ`
between distinct indices. A chain which lists every index once the slots are
numerous enough gives a logarithmic bound for the entire exponential-tail cost.
-/

namespace GenericChaining

open scoped ENNReal

/-- Scaled discrete distance with zero diagonal. -/
def discreteDist {T : Type*} [DecidableEq T] (δ : ℝ≥0∞) (s t : T) : ℝ≥0∞ :=
  if s = t then 0 else δ

private theorem two_pow_sum (K : ℕ) : ∑ k ∈ Finset.range K, 2 ^ k = 2 ^ K - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have := Nat.two_pow_pos K
    omega

/-- Once all indices fit from level `K` onward, a singleton followed by full nets
has cost at most `(2^K - 1) δ`. -/
theorem gamma1_discrete_le_cutoff {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    (δ : ℝ≥0∞) (K : ℕ) (hK : ∀ k, K ≤ k → Fintype.card T ≤ capacity k) :
    gamma1 (discreteDist (T := T) δ) ≤ ((2 ^ K - 1 : ℕ) : ℝ≥0∞) * δ := by
  classical
  let N : Nets T := fun k =>
    if hk : K ≤ k then Classical.choose (exists_surjection_fin (capacity k) (hK k hk))
    else fun _ => Classical.choice ‹Nonempty T›
  have hzero (k : ℕ) (hk : K ≤ k) (t : T) : netDist (discreteDist δ) N k t = 0 := by
    have hsurj : Function.Surjective (N k) := by
      simpa [N, hk] using Classical.choose_spec (exists_surjection_fin (capacity k) (hK k hk))
    obtain ⟨j, hrep⟩ := hsurj t
    apply le_antisymm _ (zero_le _)
    exact (iInf_le _ j).trans (by simp [hrep, discreteDist])
  have hbound (k : ℕ) (t : T) : netDist (discreteDist δ) N k t ≤ δ := by
    let j : Fin (capacity k) := ⟨0, capacity_pos k⟩
    exact (iInf_le _ j).trans (by simp [discreteDist]; split <;> simp)
  refine (iInf_le _ N).trans (iSup_le fun t => ?_)
  change (∑' k, (2 : ℝ≥0∞) ^ k * netDist (discreteDist δ) N k t) ≤ _
  rw [tsum_eq_sum (s := Finset.range K) (fun k hk => by
    rw [hzero k (by simpa using hk) t, mul_zero])]
  calc
    _ ≤ ∑ k ∈ Finset.range K, (2 : ℝ≥0∞) ^ k * δ :=
      Finset.sum_le_sum fun k _ => mul_le_mul_left' (hbound k t) _
    _ = ((∑ k ∈ Finset.range K, (2 : ℕ) ^ k : ℕ) : ℝ≥0∞) * δ := by
      simp [Finset.sum_mul]
    _ = _ := by rw [two_pow_sum]

/-- For at least two indices, the discrete cost is at most twice the scale times
the integer part of the base-two logarithm of the cardinality. -/
theorem gamma1_discrete_le_log2 {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    (δ : ℝ≥0∞) (hT : 2 ≤ Fintype.card T) :
    gamma1 (discreteDist (T := T) δ) ≤ ((2 * (Fintype.card T).log2 : ℕ) : ℝ≥0∞) * δ := by
  let m := Fintype.card T
  let K := m.log2.log2 + 1
  have hm : 0 < m.log2 := by
    apply (Nat.le_log2 (by omega : m ≠ 0)).2
    exact hT
  have hK (k : ℕ) (hk : K ≤ k) : m ≤ capacity k := by
    cases k with
    | zero => simp [K] at hk
    | succ k =>
      change m ≤ 2 ^ (2 ^ (k + 1))
      have hlog : m.log2 < 2 ^ (k + 1) :=
        (Nat.log2_lt (by omega)).1 (by change m.log2.log2 + 1 ≤ k + 1 at hk; omega)
      exact ((Nat.log2_lt (by omega : m ≠ 0)).1 hlog).le
  have hpow : 2 ^ K ≤ 2 * m.log2 := by
    rw [show K = m.log2.log2 + 1 from rfl, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.log2_self_le (by omega))
  apply (gamma1_discrete_le_cutoff δ K hK).trans
  apply mul_le_mul_right'
  exact Nat.cast_le.mpr (by omega : 2 ^ K - 1 ≤ 2 * m.log2)

/-- A singleton has zero discrete cost at every scale. -/
theorem gamma1_discrete_singleton {T : Type*} [Fintype T] [Nonempty T] [Subsingleton T]
    [DecidableEq T] (δ : ℝ≥0∞) : gamma1 (discreteDist (T := T) δ) = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa using gamma1_discrete_le_cutoff (T := T) δ 0 (fun k _ => by
    exact (Fintype.card_le_one_iff.mpr Subsingleton.elim).trans (capacity_pos k))

end GenericChaining
