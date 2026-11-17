import GenericChaining.Functional
import Mathlib.Data.Finset.Max

/-!
# A common representative for two nets

A nearest center for one distance may be poor for the other. Group points by
their pair of center indices and choose a representative minimizing the sum of
the two weighted errors within each group. At most one representative is used
per pair. Its approximation error is at most twice the original weighted error.
-/

namespace GenericChaining

open scoped ENNReal

private theorem exists_cell_minimizer {T I : Type*} [Fintype T] [Nonempty T]
    (cell : T → I) (err : T → ℝ≥0∞) :
    ∃ r : I → T, ∀ t, cell (r (cell t)) = cell t ∧ err (r (cell t)) ≤ err t := by
  classical
  have pick (i : I) : ∃ s : T, ∀ t, cell t = i → cell s = i ∧ err s ≤ err t := by
    let B := Finset.univ.filter (fun t => cell t = i)
    by_cases hB : B.Nonempty
    · obtain ⟨s, hs, hmin⟩ := B.exists_min_image err hB
      exact ⟨s, fun t ht => ⟨(Finset.mem_filter.mp hs).2,
        hmin t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)⟩⟩
    · refine ⟨Classical.choice ‹Nonempty T›, fun t ht => ?_⟩
      exact (hB ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩).elim
  choose r hr using pick
  exact ⟨r, fun t => hr (cell t) t rfl⟩

/-- Jointly refine two finite approximations. `i₁` and `i₂` assign a point to
its two centers. They may make any choice in a tie. Each distance satisfies
the triangle inequality through a common center (as any pseudometric does). -/
theorem exists_common_representatives {T I J : Type*} [Fintype T] [Nonempty T]
    (d₁ d₂ : T → T → ℝ≥0∞)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (u v : ℝ≥0∞) (a : I → T) (b : J → T) (i₁ : T → I) (i₂ : T → J) :
    ∃ r : I × J → T, ∀ t, let s := r (i₁ t, i₂ t)
      i₁ s = i₁ t ∧ i₂ s = i₂ t ∧
      u * d₁ t s + v * d₂ t s ≤ 2 * (u * d₁ t (a (i₁ t)) + v * d₂ t (b (i₂ t))) := by
  let err := fun t => u * d₁ t (a (i₁ t)) + v * d₂ t (b (i₂ t))
  obtain ⟨r, hr⟩ := exists_cell_minimizer (fun t => (i₁ t, i₂ t)) err
  refine ⟨r, fun t => ?_⟩
  let s := r (i₁ t, i₂ t)
  obtain ⟨hcell, hmin⟩ := hr t
  have h₁ : i₁ s = i₁ t := congrArg Prod.fst hcell
  have h₂ : i₂ s = i₂ t := congrArg Prod.snd hcell
  refine ⟨h₁, h₂, ?_⟩
  calc
    u * d₁ t s + v * d₂ t s ≤
        u * (d₁ t (a (i₁ t)) + d₁ s (a (i₁ t))) +
        v * (d₂ t (b (i₂ t)) + d₂ s (b (i₂ t))) :=
      add_le_add (mul_le_mul_left' (tri₁ t s _) u) (mul_le_mul_left' (tri₂ t s _) v)
    _ = err t + err s := by simp only [err, h₁, h₂, mul_add]; ac_rfl
    _ ≤ err t + err t := add_le_add_left hmin _
    _ = 2 * err t := (two_mul _).symm

end GenericChaining
