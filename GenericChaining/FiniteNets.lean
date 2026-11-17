import GenericChaining.Functional
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite subsets and indexed nets

The usual definition of a chaining functional uses nonempty finite subsets.
Here we prove it agrees with the indexed-slot convention, for all level weights.
-/

namespace GenericChaining

open scoped ENNReal

/-- A finite nonempty type fits into a list of centers with repetition whenever
there are at least as many slots as points. -/
theorem exists_surjection_fin {T : Type*} [Fintype T] [Nonempty T]
    (n : ℕ) (hn : Fintype.card T ≤ n) : ∃ f : Fin n → T, Function.Surjective f := by
  classical
  let e := Fintype.equivFin T
  let f (j : Fin n) := if hj : j.val < Fintype.card T then e.symm ⟨j.val, hj⟩
    else Classical.choice ‹Nonempty T›
  refine ⟨f, fun t => ⟨(e t).castLE hn, ?_⟩⟩
  simp [f, (e t).isLt]

/-- An admissible net at each level, given as a finite subset of the index set. -/
structure FiniteNets (T : Type*) where
  centers : ℕ → Finset T
  nonempty : ∀ k, (centers k).Nonempty
  card_le : ∀ k, (centers k).card ≤ capacity k

/-- The classical finite-subset definition gives exactly the indexed functional. -/
theorem gamma_eq_finset {T : Type*} (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞) :
    gamma w d = ⨅ A : FiniteNets T, ⨆ t, ∑' k, w k * ⨅ s : A.centers k, d t s := by
  classical
  apply le_antisymm
  · refine le_iInf fun A => ?_
    have en (k : ℕ) : ∃ f : Fin (capacity k) → A.centers k, Function.Surjective f := by
      haveI : Nonempty (A.centers k) := (A.nonempty k).to_subtype
      apply exists_surjection_fin
      simpa using A.card_le k
    choose f hf using en
    let N : Nets T := fun k j => (f k j).val
    apply (iInf_le _ N).trans
    unfold cost
    refine iSup_le fun t => le_iSup_of_le t ?_
    have he (k : ℕ) : netDist d N k t = ⨅ s : A.centers k, d t s :=
      (hf k).iInf_comp (fun s => d t s.val)
    simp_rw [he]
    exact le_rfl
  · refine le_iInf fun N => ?_
    let A : FiniteNets T :=
      { centers := fun k => Finset.univ.image (N k)
        nonempty := fun k => ⟨N k ⟨0, capacity_pos k⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
        card_le := fun k => by simpa using (Finset.card_image_le (s := Finset.univ) (f := N k)) }
    apply (iInf_le _ A).trans
    unfold cost
    refine iSup_le fun t => le_iSup_of_le t ?_
    have he (k : ℕ) : (⨅ s : A.centers k, d t s) = netDist d N k t := by
      let f (j : Fin (capacity k)) : A.centers k :=
        ⟨N k j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
      have hf : Function.Surjective f := by
        intro s
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp s.property
        exact ⟨j, Subtype.ext hj⟩
      exact (hf.iInf_comp (fun s => d t s.val)).symm
    simp_rw [he]
    exact le_rfl

end GenericChaining
