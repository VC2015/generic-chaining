import GenericChaining.GaussianLocalGrowth
import GenericChaining.GaussianFiniteWidth
import GenericChaining.GrowthPartitions

/-!
# Local Gaussian growth for the finite-subset width functional

Each occupied local ball is represented on the original index type with
repetitions. The concrete Gaussian growth theorem applies to these families;
their combined maximum is bounded by the maximum over the parent set.
-/

namespace GenericChaining

open MeasureTheory
open scoped BigOperators NNReal

/-- Every finite family selected from a parent set has width at most its local width. -/
theorem gaussianWidth_le_finiteGaussianWidth {S T : Type*} [Fintype S] [Nonempty S]
    {r : ℕ} (a : T → EuclideanSpace ℝ (Fin r)) (A : Finset T) (hA : A.Nonempty)
    (q : S → A) : gaussianWidth (fun s => a (q s).val) ≤ finiteGaussianWidth a A := by
  classical
  letI : Nonempty A := hA.to_subtype
  rw [finiteGaussianWidth_eq_integral a A hA]
  apply integral_mono (gaussianMaximum_integrable _)
    (integrable_iSup_finite (fun t : A => gaussianLinear_integrable (a t.val)))
  intro g
  apply ciSup_le
  intro s
  exact le_ciSup (Finite.bddAbove_range (fun t : A => gaussianLinear (a t.val) g)) (q s)

/-- The concrete one-sided Gaussian width satisfies the local growth property
used by the labelled partition construction, with radius exactly one eighth
of the separation and a universal growth coefficient. -/
theorem finiteGaussianWidth_hasLocalGrowth {T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] {r : ℕ} (a : T → EuclideanSpace ℝ (Fin r)) :
    HasLocalGrowth (fun s t => (canonicalDist a s t : ℝ))
      (finiteGaussianWidth a) gaussianGrowthConstant (1 / 8) := by
  classical
  intro A N sep b hN hNA hsep hseparated hwidth
  letI : Nonempty N := hN.to_subtype
  let m := Fintype.card N
  have hm : 0 < m := Fintype.card_pos
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let e : N ≃ Fin m := Fintype.equivFin N
  let center (i : Fin m) : T := (e.symm i).val
  have hcenter (i : Fin m) : center i ∈ N := (e.symm i).property
  have hinj : Function.Injective center := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  let B (i : Fin m) := finiteBall (fun s t => (canonicalDist a s t : ℝ)) A ((1 / 8) * sep) (center i)
  have hB (i : Fin m) : (B i).Nonempty := by
    refine ⟨center i, Finset.mem_filter.mpr ⟨hNA (hcenter i), ?_⟩⟩
    simp only [canonicalDist_self, NNReal.coe_zero]
    positivity
  have hrep (i : Fin m) : ∃ p : T → B i, Function.Surjective p := by
    obtain ⟨p, hp, _⟩ := exists_finset_representative (B i) (hB i)
    exact ⟨p, hp⟩
  choose p hp using hrep
  let x (i : Fin m) (t : T) := a (p i t).val
  let c (i : Fin m) := a (center i)
  have hx (i : Fin m) (t : T) : ‖x i t - c i‖ ≤ (1 / 8) * sep := by
    have hh := (Finset.mem_filter.mp (p i t).property).2
    change ‖a (center i) - a (p i t).val‖ ≤ (1 / 8) * sep at hh
    change ‖a (p i t).val - a (center i)‖ ≤ _
    rwa [norm_sub_rev]
  have hc (i j : Fin m) (hij : i ≠ j) : sep ≤ ‖c i - c j‖ :=
    hseparated (center i) (hcenter i) (center j) (hcenter j)
      (fun h => hij (hinj h))
  have hw (i : Fin m) : b ≤ gaussianWidth (x i) := by
    rw [← finiteGaussianWidth_eq_of_representative a (B i) (hB i) (p i) (hp i)]
    exact hwidth (center i) (hcenter i)
  have hg := gaussian_local_growth x c hsep.le
    (show 0 ≤ (1 / 8 : ℝ) * sep by positivity)
    (show (1 / 8 : ℝ) * sep ≤ sep / 8 by ring_nf; exact le_rfl)
    hc hx b hw
  have hA : A.Nonempty := hN.mono hNA
  let q (it : Fin m × T) : A :=
    ⟨(p it.1 it.2).val, (Finset.mem_filter.mp (p it.1 it.2).property).1⟩
  have hu : gaussianWidth (fun it : Fin m × T => x it.1 it.2) ≤ finiteGaussianWidth a A :=
    gaussianWidth_le_finiteGaussianWidth a A hA q
  have hh := hg.trans hu
  simpa only [m, Fintype.card_coe, add_comm] using hh

end GenericChaining
