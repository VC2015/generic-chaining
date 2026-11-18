import GenericChaining.GaussianWidth
import GenericChaining.GaussianMetric

/-!
# Gaussian width as a functional of finite subsets

The empty set is assigned value zero. On every nonempty finite subset this is
the concrete expected one-sided maximum, with the original vector coordinates.
-/
namespace GenericChaining
open MeasureTheory
open scoped BigOperators

variable {T : Type*} {r : ℕ}

/-- The local Gaussian width functional, defined also on the empty set. -/
noncomputable def finiteGaussianWidth (a : T → EuclideanSpace ℝ (Fin r))
    (A : Finset T) : ℝ := by
  classical
  exact if hA : A.Nonempty then
    letI : Nonempty A := hA.to_subtype
    gaussianWidth (fun t : A => a t.val)
  else 0

@[simp] theorem finiteGaussianWidth_empty (a : T → EuclideanSpace ℝ (Fin r)) :
    finiteGaussianWidth a ∅ = 0 := by simp [finiteGaussianWidth]

lemma finiteGaussianWidth_eq_integral (a : T → EuclideanSpace ℝ (Fin r))
    (A : Finset T) (hA : A.Nonempty) :
    finiteGaussianWidth a A = ∫ g, (⨆ t : A, gaussianLinear (a t.val) g) ∂standardGaussian r := by
  simp only [finiteGaussianWidth, dif_pos hA, gaussianWidth, gaussianMaximum]

theorem finiteGaussianWidth_nonneg (a : T → EuclideanSpace ℝ (Fin r)) (A : Finset T) :
    0 ≤ finiteGaussianWidth a A := by
  classical
  by_cases hA : A.Nonempty
  · letI : Nonempty A := hA.to_subtype
    simpa only [finiteGaussianWidth, dif_pos hA] using
      gaussianWidth_nonneg (fun t : A => a t.val)
  · simp [finiteGaussianWidth, hA]

/-- Local width is monotone even though the process maximum is one-sided. -/
theorem finiteGaussianWidth_mono (a : T → EuclideanSpace ℝ (Fin r))
    {A B : Finset T} (hAB : A ⊆ B) : finiteGaussianWidth a A ≤ finiteGaussianWidth a B := by
  classical
  by_cases hA : A.Nonempty
  · have hB := hA.mono hAB
    letI : Nonempty A := hA.to_subtype
    letI : Nonempty B := hB.to_subtype
    rw [finiteGaussianWidth_eq_integral a A hA, finiteGaussianWidth_eq_integral a B hB]
    apply integral_mono (integrable_iSup_finite (fun t : A => gaussianLinear_integrable (a t.val)))
      (integrable_iSup_finite (fun t : B => gaussianLinear_integrable (a t.val)))
    intro g
    apply ciSup_le
    intro t
    exact le_ciSup ((Set.finite_range (fun s : B => gaussianLinear (a s.val) g)).bddAbove)
      ⟨t.val, hAB t.property⟩
  · simpa [finiteGaussianWidth, hA] using finiteGaussianWidth_nonneg a B

@[simp] theorem finiteGaussianWidth_singleton (a : T → EuclideanSpace ℝ (Fin r)) (t : T) :
    finiteGaussianWidth a {t} = 0 := by
  classical
  letI : Unique ({t} : Finset T) :=
    { default := ⟨t, Finset.mem_singleton_self t⟩
      uniq := fun s => Subtype.ext (Finset.mem_singleton.mp s.property) }
  have hA : ({t} : Finset T).Nonempty := Finset.singleton_nonempty t
  simpa only [finiteGaussianWidth, dif_pos hA] using
    gaussianWidth_singleton (fun s : ({t} : Finset T) => a s.val)

@[simp] theorem finiteGaussianWidth_univ [Fintype T] [Nonempty T]
    (a : T → EuclideanSpace ℝ (Fin r)) : finiteGaussianWidth a Finset.univ = gaussianWidth a := by
  classical
  letI : Nonempty (Finset.univ : Finset T) := Finset.univ_nonempty.to_subtype
  rw [finiteGaussianWidth_eq_integral a Finset.univ Finset.univ_nonempty]
  change gaussianWidth (fun t : (Finset.univ : Finset T) => a t.val) = gaussianWidth a
  exact gaussianWidth_of_vector_quotient Subtype.val
    (fun t => ⟨⟨t, Finset.mem_univ t⟩, rfl⟩) _ _ (fun _ => rfl)

/-- A nonempty finite subset is a surjective image of the original index set.
The map fixes points that already belong to the subset. -/
theorem exists_finset_representative (A : Finset T) (hA : A.Nonempty) :
    ∃ p : T → A, Function.Surjective p ∧ ∀ t : A, p t.val = t := by
  classical
  let p (t : T) : A := if ht : t ∈ A then ⟨t, ht⟩ else Classical.choice hA.to_subtype
  have hp (t : A) : p t.val = t := by simp [p, t.property]
  exact ⟨p, (fun t => ⟨t.val, hp t⟩), hp⟩

/-- Repeating points in a local subset lets all local families use the same
finite index type, without changing their width. -/
theorem finiteGaussianWidth_eq_of_representative [Fintype T] [Nonempty T]
    (a : T → EuclideanSpace ℝ (Fin r)) (A : Finset T) (hA : A.Nonempty)
    (p : T → A) (hp : Function.Surjective p) :
    finiteGaussianWidth a A = gaussianWidth (fun t => a (p t).val) := by
  classical
  letI : Nonempty A := hA.to_subtype
  rw [finiteGaussianWidth_eq_integral a A hA]
  change gaussianWidth (fun t : A => a t.val) = gaussianWidth (fun t => a (p t).val)
  exact (gaussianWidth_of_vector_quotient p hp _ _ (fun _ => rfl)).symm

end GenericChaining
