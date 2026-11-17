import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.Real.Sqrt

/-!
# Admissible nets and chaining functionals

The first net has one point. Later nets have at most `2^(2^k)` points.
We index the slots in each net and allow repetitions, so the same definitions
work for two different pseudometrics on one index set. All costs take values
in the extended nonnegative reals, including costs of divergent chains.
-/

namespace GenericChaining

open scoped ENNReal

/-- The number of available slots at each level of an admissible sequence. -/
def capacity : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ (2 ^ (k + 1))

theorem capacity_pos (k : ℕ) : 0 < capacity k := by
  cases k with
  | zero => decide
  | succ k => exact Nat.pow_pos (by decide)

/-- Repeating a center fills unused slots without changing the distance to the net. -/
abbrev Nets (T : Type*) := (k : ℕ) → Fin (capacity k) → T

/-- Distance from an index to a net at a given level. -/
noncomputable def netDist {T : Type*} (d : T → T → ℝ≥0∞) (N : Nets T)
    (k : ℕ) (t : T) : ℝ≥0∞ := ⨅ j, d t (N k j)

/-- The largest weighted sum of approximation errors along a branch. -/
noncomputable def cost {T : Type*} (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞)
    (N : Nets T) : ℝ≥0∞ := ⨆ t, ∑' k, w k * netDist d N k t

/-- The least cost over all admissible sequences. -/
noncomputable def gamma {T : Type*} (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞) :
    ℝ≥0∞ := ⨅ N : Nets T, cost w d N

/-- The exponential-tail chaining functional uses the weights `2^k`. -/
noncomputable def gamma1 {T : Type*} (d : T → T → ℝ≥0∞) : ℝ≥0∞ :=
  gamma (fun k => 2 ^ k) d

/-- The Gaussian chaining functional uses the weights `(√2)^k`. -/
noncomputable def gamma2 {T : Type*} (d : T → T → ℝ≥0∞) : ℝ≥0∞ :=
  gamma (fun k => (ENNReal.ofReal (Real.sqrt 2)) ^ k) d

/-- Mapping the centers computes exactly the cost for the pulled-back distance. -/
theorem cost_pullback {S T : Type*} (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞)
    (f : S → T) (hf : Function.Surjective f) (N : Nets S) :
    cost w (fun s t => d (f s) (f t)) N = cost w d (fun k j => f (N k j)) := by
  unfold cost netDist
  exact hf.iSup_comp (fun t => ∑' k, w k * ⨅ j, d t (f (N k j)))

/-- A surjective reindexing preserves the functional. In particular, one can
collapse all zero-distance copies of an index in a pseudometric quotient. -/
theorem gamma_pullback {S T : Type*} (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞)
    (f : S → T) (hf : Function.Surjective f) :
    gamma w (fun s t => d (f s) (f t)) = gamma w d := by
  classical
  apply le_antisymm
  · refine le_iInf fun N => ?_
    let g := Function.surjInv hf
    have hfg : ∀ t, f (g t) = t := Function.rightInverse_surjInv hf
    let M : Nets S := fun k j => g (N k j)
    calc
      gamma w (fun s t => d (f s) (f t)) ≤ _ := iInf_le _ M
      _ = cost w d (fun k j => f (g (N k j))) := cost_pullback w d f hf M
      _ = cost w d N := by simp_rw [hfg]
  · refine le_iInf fun M => ?_
    rw [cost_pullback w d f hf M]
    exact iInf_le _ _

end GenericChaining
