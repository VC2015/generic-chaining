import GenericChaining.Link
import Mathlib.Data.Complex.Exponential

/-!
# Cardinality of consecutive representative links

Each representative family has at most the product of the two net capacities.
A family of consecutive links is contained in the product of its endpoint
families. Its cardinality can therefore be paid for by one universal dyadic
exponential bound.
-/

namespace GenericChaining

/-- The unused level zero is empty; level `k+1` contains the links from
representative `k` to representative `k+1`. -/
def chainEdges {T : Type*} [Fintype T] [DecidableEq T] (r : ℕ → T → T) :
    ℕ → Finset (T × T)
  | 0 => ∅
  | k + 1 => Finset.univ.image (fun t => (r k t, r (k + 1) t))

@[simp] theorem chainEdges_zero {T : Type*} [Fintype T] [DecidableEq T] (r : ℕ → T → T) :
    chainEdges r 0 = ∅ := rfl

@[simp] theorem chainEdges_succ {T : Type*} [Fintype T] [DecidableEq T] (r : ℕ → T → T) (k : ℕ) :
    chainEdges r (k + 1) = Finset.univ.image (fun t => (r k t, r (k + 1) t)) := by
  classical
  rfl

/-- Every link has an endpoint in each of the two representative images. -/
theorem chainEdges_card_le {T : Type*} [Fintype T] [DecidableEq T] (r : ℕ → T → T) (k : ℕ) :
    (chainEdges r (k + 1)).card ≤
      (Finset.univ.image (r k)).card * (Finset.univ.image (r (k + 1))).card := by
  classical
  calc
    _ ≤ ((Finset.univ.image (r k)).product (Finset.univ.image (r (k + 1)))).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    _ = _ := Finset.card_product _ _

/-- A capacity is bounded by `exp (2^k)`, including the special initial level. -/
theorem capacity_real_le_exp (k : ℕ) : (capacity k : ℝ) ≤ Real.exp ((2 : ℝ) ^ k) := by
  have hcap : capacity k ≤ 2 ^ (2 ^ k) := by
    cases k with
    | zero => norm_num [capacity]
    | succ k => exact le_rfl
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (2 : ℝ) ^ (2 ^ k) := by exact_mod_cast hcap
    _ ≤ (Real.exp 1) ^ (2 ^ k) := pow_le_pow_left₀ (by norm_num) htwo _
    _ = Real.exp ((2 : ℝ) ^ k) := by
      rw [← Real.exp_nat_mul]
      simp

/-- The number of links at every level is bounded by a universal dyadic
exponential, independently of the finite index set and of the depth. -/
theorem chainEdges_card_exp {T : Type*} [Fintype T] [DecidableEq T] (r : ℕ → T → T)
    (hcard : ∀ k, (Finset.univ.image (r k)).card ≤ capacity k ^ 2) (k : ℕ) :
    ((chainEdges r k).card : ℝ) ≤ Real.exp (4 * (2 : ℝ) ^ k) := by
  classical
  cases k with
  | zero => simp; positivity
  | succ k =>
    have hp (j : ℕ) : ((Finset.univ.image (r j)).card : ℝ) ≤
        (Real.exp ((2 : ℝ) ^ j)) ^ 2 := by
      calc
        _ ≤ (capacity j : ℝ) ^ 2 := by exact_mod_cast hcard j
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (capacity_real_le_exp j) _
    calc
      _ ≤ ((Finset.univ.image (r k)).card : ℝ) *
          ((Finset.univ.image (r (k + 1))).card : ℝ) := by
        exact_mod_cast chainEdges_card_le r k
      _ ≤ (Real.exp ((2 : ℝ) ^ k)) ^ 2 * (Real.exp ((2 : ℝ) ^ (k + 1))) ^ 2 :=
        mul_le_mul (hp k) (hp (k + 1)) (by positivity) (by positivity)
      _ = Real.exp (2 * (2 : ℝ) ^ k + 2 * (2 : ℝ) ^ (k + 1)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by
        rw [pow_succ]
        nlinarith [show 0 ≤ (2 : ℝ) ^ k by positivity])

end GenericChaining
