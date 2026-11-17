import GenericChaining.FiniteNets
import GenericChaining.FiniteCost
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# From finite covers and labelled partitions to admissible nets

The comparison in this file uses the repository's exact slot capacities,
including the singleton at level zero. Cells need not be disjoint: a diameter
bound for any covering cell suffices to choose a center with that error.
-/

namespace GenericChaining

open scoped NNReal ENNReal

/-- Finite covers with the cardinalities required by admissible nets. -/
structure AdmissibleCovers (T : Type*) where
  cells : ℕ → Finset (Finset T)
  cover : ∀ k t, ∃ A ∈ cells k, t ∈ A
  card_le : ∀ k, (cells k).card ≤ capacity k

variable {T : Type*} [Nonempty T]

/-- Picking one point in each cell of a finite admissible cover gives an
admissible net. The approximation error is bounded by any cellwise bound. -/
theorem exists_nets_of_admissible_covers [DecidableEq T]
    (A : AdmissibleCovers T) (d : T → T → ℝ≥0∞) (δ : ℕ → T → ℝ≥0∞)
    (hdiam : ∀ k t B, B ∈ A.cells k → t ∈ B → ∀ s ∈ B, d t s ≤ δ k t) :
    ∃ N : Nets T, ∀ k t, netDist d N k t ≤ δ k t := by
  classical
  let pick (B : Finset T) : T :=
    if hB : B.Nonempty then Classical.choose hB else Classical.choice ‹Nonempty T›
  have hpick (B : Finset T) (hB : B.Nonempty) : pick B ∈ B := by
    simpa only [pick, dif_pos hB] using Classical.choose_spec hB
  have hnonempty (k : ℕ) : (A.cells k).Nonempty := by
    obtain ⟨B, hB, _⟩ := A.cover k (Classical.choice ‹Nonempty T›)
    exact ⟨B, hB⟩
  have henumerate (k : ℕ) :
      ∃ f : Fin (capacity k) → A.cells k, Function.Surjective f := by
    haveI : Nonempty (A.cells k) := (hnonempty k).to_subtype
    apply exists_surjection_fin
    simpa only [Fintype.card_coe] using A.card_le k
  choose f hf using henumerate
  let N : Nets T := fun k j => pick (f k j)
  refine ⟨N, fun k t => ?_⟩
  obtain ⟨B, hB, ht⟩ := A.cover k t
  obtain ⟨j, hj⟩ := hf k ⟨B, hB⟩
  have hp : N k j ∈ B := by
    dsimp [N]
    rw [hj]
    exact hpick B ⟨t, ht⟩
  exact (iInf_le _ j).trans (hdiam k t B hB ht _ hp)

/-- A branchwise weighted diameter estimate for admissible covers bounds the
indexed-net chaining functional, for arbitrary nonnegative extended weights. -/
theorem gamma_le_cover_cost [DecidableEq T]
    (A : AdmissibleCovers T) (w : ℕ → ℝ≥0∞)
    (d : T → T → ℝ≥0∞) (δ : ℕ → T → ℝ≥0∞)
    (hdiam : ∀ k t B, B ∈ A.cells k → t ∈ B → ∀ s ∈ B, d t s ≤ δ k t) :
    gamma w d ≤ ⨆ t, ∑' k, w k * δ k t := by
  obtain ⟨N, hN⟩ := exists_nets_of_admissible_covers A d δ hdiam
  refine (iInf_le _ N).trans (iSup_le fun t => ?_)
  apply le_iSup_of_le t
  exact ENNReal.tsum_le_tsum fun k => mul_le_mul_left' (hN k t) (w k)

/-- In particular, the Gaussian functional is bounded by an admissible
cover's square-root-weighted branch cost. -/
theorem gamma2_le_cover_cost [DecidableEq T]
    (A : AdmissibleCovers T) (d : T → T → ℝ≥0∞) (δ : ℕ → T → ℝ≥0∞)
    (hdiam : ∀ k t B, B ∈ A.cells k → t ∈ B → ∀ s ∈ B, d t s ≤ δ k t) :
    gamma2 d ≤ ⨆ t, ∑' k, ENNReal.ofReal (Real.sqrt 2) ^ k * δ k t :=
  gamma_le_cover_cost A _ d δ hdiam

end GenericChaining

namespace GenericChaining

open scoped NNReal ENNReal

/-- A closed ball relative to a finite parent set. -/
noncomputable def finiteBall {T : Type*} [DecidableEq T] (d : T → T → ℝ)
    (A : Finset T) (ρ : ℝ) (s : T) : Finset T := A.filter (fun t => d s t ≤ ρ)

theorem finiteBall_mono {T : Type*} [DecidableEq T] (d : T → T → ℝ)
    {A B : Finset T} (hAB : A ⊆ B) (ρ : ℝ) (s : T) :
    finiteBall d A ρ s ⊆ finiteBall d B ρ s := by
  intro t ht
  exact Finset.mem_filter.mpr ⟨hAB (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩

/-- The data produced by the greedy, width-ordered partition at one scale.
The score of a child dominates every sufficiently small subset of that child.
The ordering of the scores is the feature needed in the growth argument. -/
structure GreedyPartition {T : Type*} [DecidableEq T] (d : T → T → ℝ)
    (F : Finset T → ℝ) (A : Finset T) (r ρ : ℝ) where
  length : ℕ
  center : Fin length → T
  cell : Fin length → Finset T
  score : Fin length → ℝ
  center_mem : ∀ i, center i ∈ cell i
  subset : ∀ i, cell i ⊆ A
  cover : ∀ t ∈ A, ∃ i, t ∈ cell i
  disjoint : Pairwise (fun i j => Disjoint (cell i) (cell j))
  diameter : ∀ i, ∀ s ∈ cell i, ∀ t ∈ cell i, d s t ≤ 2 * r
  separated : ∀ i j, i ≠ j → r < d (center i) (center j)
  score_le : ∀ i, score i ≤ F (finiteBall d A ρ (center i))
  antitone : Antitone score
  dominates : ∀ i H, H.Nonempty → H ⊆ cell i →
    (∀ s ∈ H, ∀ t ∈ H, d s t ≤ ρ) → F H ≤ score i

/-- The greedy partition exists for every finite pseudometric set and every
monotone local width functional. This is the finite optimization step in
van Handel's lower-bound partition construction. -/
theorem exists_greedy_partition {T : Type*} [DecidableEq T]
    (d : T → T → ℝ) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s)
    (tri : ∀ s t c, d s t ≤ d s c + d t c)
    (F : Finset T → ℝ) (hF : Monotone F)
    (r ρ : ℝ) (hr : 0 ≤ r) (A : Finset T) :
    Nonempty (GreedyPartition d F A r ρ) := by
  classical
  refine Finset.strongInductionOn A ?_
  intro A ih
  by_cases hA : A.Nonempty
  · obtain ⟨c, hc, hmax⟩ := A.exists_max_image (fun s => F (finiteBall d A ρ s)) hA
    let P := finiteBall d A r c
    let R := A \ P
    have hcP : c ∈ P := Finset.mem_filter.mpr ⟨hc, by simpa [diag] using hr⟩
    have hRA : R ⊆ A := Finset.sdiff_subset
    have hRstrict : R ⊂ A := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hRA, ?_⟩
      intro heq
      have : c ∈ R := heq.symm ▸ hc
      exact (Finset.mem_sdiff.mp this).2 hcP
    obtain ⟨q⟩ := ih R hRstrict
    have hcenter (i : Fin q.length) : q.center i ∈ R := q.subset i (q.center_mem i)
    have hscore (i : Fin q.length) : q.score i ≤ F (finiteBall d A ρ c) :=
      (q.score_le i).trans ((hF (finiteBall_mono d hRA ρ _)).trans
        (hmax (q.center i) (hRA (hcenter i))))
    let center : Fin (q.length + 1) → T := Fin.cases c q.center
    let cell : Fin (q.length + 1) → Finset T := Fin.cases P q.cell
    let score : Fin (q.length + 1) → ℝ :=
      Fin.cases (F (finiteBall d A ρ c)) q.score
    refine ⟨{
      length := q.length + 1
      center := center
      cell := cell
      score := score
      center_mem := ?_
      subset := ?_
      cover := ?_
      disjoint := ?_
      diameter := ?_
      separated := ?_
      score_le := ?_
      antitone := ?_
      dominates := ?_ }⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hcP
      · exact q.center_mem j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Finset.filter_subset _ _
      · exact (q.subset j).trans hRA
    · intro t ht
      by_cases htP : t ∈ P
      · exact ⟨0, htP⟩
      · obtain ⟨i, hi⟩ := q.cover t (Finset.mem_sdiff.mpr ⟨ht, htP⟩)
        exact ⟨i.succ, hi⟩
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro _
          apply Finset.disjoint_left.mpr
          intro t htP htq
          exact (Finset.mem_sdiff.mp (q.subset j' htq)).2 htP
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _
          apply Finset.disjoint_left.mpr
          intro t htq htP
          exact (Finset.mem_sdiff.mp (q.subset i' htq)).2 htP
        · intro hij
          exact q.disjoint (by intro h; exact hij (congrArg Fin.succ h))
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro s hs t ht
        have hs' := (Finset.mem_filter.mp hs).2
        have ht' := (Finset.mem_filter.mp ht).2
        have htri := tri s t c
        rw [symm s c, symm t c] at htri
        linarith
      · exact q.diameter i'
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro _
          have hn := (Finset.mem_sdiff.mp (hcenter j')).2
          exact lt_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨hRA (hcenter j'), h⟩))
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _
          have hn := (Finset.mem_sdiff.mp (hcenter i')).2
          change r < d (q.center i') c
          rw [symm (q.center i') c]
          exact lt_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨hRA (hcenter i'), h⟩))
        · intro hij
          exact q.separated i' j' (by intro h; exact hij (congrArg Fin.succ h))
    · intro i
      refine Fin.cases le_rfl (fun i' => ?_) i
      exact (q.score_le i').trans (hF (finiteBall_mono d hRA ρ _))
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun _ => le_rfl) (fun j' _ => hscore j') j
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij
          exact (not_le_of_gt (Fin.succ_pos i') hij).elim
        · intro hij
          exact q.antitone (Fin.succ_le_succ_iff.mp hij)
    · intro i
      refine Fin.cases ?_ (fun i' => q.dominates i') i
      intro H hH hHP hdiam
      obtain ⟨t, ht⟩ := hH
      have htA : t ∈ A := (Finset.mem_filter.mp (hHP ht)).1
      have hsub : H ⊆ finiteBall d A ρ t := by
        intro s hs
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hHP hs)).1, hdiam t ht s hs⟩
      exact (hF hsub).trans (hmax t htA)
  · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    refine ⟨{
      length := 0
      center := Fin.elim0
      cell := Fin.elim0
      score := Fin.elim0
      center_mem := fun i => Fin.elim0 i
      subset := fun i => Fin.elim0 i
      cover := by simp
      disjoint := fun i => Fin.elim0 i
      diameter := fun i => Fin.elim0 i
      separated := fun i => Fin.elim0 i
      score_le := fun i => Fin.elim0 i
      antitone := fun i => Fin.elim0 i
      dominates := fun i => Fin.elim0 i }⟩

end GenericChaining

namespace GenericChaining

/-- Local growth in a form that avoids choosing a minimizer: any common
lower bound on the widths of the small balls can be added to the packing gain. -/
def HasLocalGrowth {T : Type*} [DecidableEq T] (d : T → T → ℝ)
    (F : Finset T → ℝ) (c α : ℝ) : Prop :=
  ∀ (A N : Finset T) (r b : ℝ), N.Nonempty → N ⊆ A → 0 < r →
    (∀ s ∈ N, ∀ t ∈ N, s ≠ t → r ≤ d s t) →
    (∀ s ∈ N, b ≤ F (finiteBall d A (α * r) s)) →
    c * r * Real.sqrt (Real.log (N.card : ℝ)) + b ≤ F A

theorem GreedyPartition.center_injective {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) : Function.Injective q.center := by
  intro i j h
  by_contra hij
  have hi := q.center_mem i
  have hj : q.center i ∈ q.cell j := by simpa only [h] using q.center_mem j
  exact Finset.disjoint_left.mp (q.disjoint hij) hi hj

/-- A child's rank pays for its local width. Applying growth to the prefix
of its separated centers preserves the child's score because scores decrease. -/
theorem GreedyPartition.rank_growth {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r c α : ℝ}
    (q : GreedyPartition d F A r (α * r))
    (hgrowth : HasLocalGrowth d F c α) (hr : 0 < r) (i : Fin q.length) :
    c * r * Real.sqrt (Real.log ((i.val + 1 : ℕ) : ℝ)) + q.score i ≤ F A := by
  classical
  let N := (Finset.Iic i).image q.center
  have hNi : q.center i ∈ N := Finset.mem_image_of_mem _ (Finset.mem_Iic.mpr le_rfl)
  have hNcard : N.card = i.val + 1 := by
    rw [Finset.card_image_of_injective _ q.center_injective]
    exact Fin.card_Iic i
  have hh := hgrowth A N r (q.score i) ⟨_, hNi⟩ (by
    intro s hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact q.subset j (q.center_mem j)) hr (by
    intro s hs t ht hst
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact (q.separated j k (fun h => hst (congrArg q.center h))).le) (by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    exact (q.antitone (Finset.mem_Iic.mp hj)).trans (q.score_le j))
  simpa only [hNcard] using hh

/-- The same rank gain is valid with the width of any sufficiently small
descendant subset in place of the selected local score. -/
theorem GreedyPartition.rank_growth_descendant {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r c α : ℝ}
    (q : GreedyPartition d F A r (α * r))
    (hgrowth : HasLocalGrowth d F c α) (hr : 0 < r) (i : Fin q.length)
    (H : Finset T) (hH : H.Nonempty) (hsub : H ⊆ q.cell i)
    (hdiam : ∀ s ∈ H, ∀ t ∈ H, d s t ≤ α * r) :
    c * r * Real.sqrt (Real.log ((i.val + 1 : ℕ) : ℝ)) + F H ≤ F A :=
  (add_le_add_left (q.dominates i H hH hsub hdiam) _).trans
    (q.rank_growth hgrowth hr i)

/-- Summing a three-level growth inequality costs at most three copies of
the initial width. This formulation includes finite chains of every depth. -/
theorem three_step_growth_sum_le (a f : ℕ → ℝ) (W : ℝ)
    (hnn : ∀ k, 0 ≤ f k) (hfirst : ∀ k < 3, f k ≤ W)
    (hgrowth : ∀ k, a k + f (k + 3) ≤ f k) (N : ℕ) :
    ∑ k ∈ Finset.range N, a k ≤ 3 * W := by
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun k _ => hgrowth k)
  rw [Finset.sum_add_distrib] at hsum
  have hleft := Finset.sum_range_add f N 3
  have hright := Finset.sum_range_add f 3 N
  rw [Nat.add_comm 3 N] at hright
  have hshift : (∑ k ∈ Finset.range N, f (3 + k)) =
      ∑ k ∈ Finset.range N, f (k + 3) := by
    simp only [Nat.add_comm 3]
  rw [hshift] at hright
  have htail : 0 ≤ ∑ k ∈ Finset.range 3, f (N + k) :=
    Finset.sum_nonneg fun k _ => hnn _
  have hhead : (∑ k ∈ Finset.range 3, f k) ≤ 3 * W := by
    calc
      _ ≤ ∑ _k ∈ Finset.range 3, W :=
        Finset.sum_le_sum fun k hk => hfirst k (Finset.mem_range.mp hk)
      _ = _ := by simp
  linarith

/-- Nonnegative label contributions satisfying three-step growth form a
summable series, with a bound independent of the number of levels. -/
theorem three_step_growth_tsum_le (a f : ℕ → ℝ) (W : ℝ)
    (ha : ∀ k, 0 ≤ a k) (hnn : ∀ k, 0 ≤ f k)
    (hfirst : ∀ k < 3, f k ≤ W)
    (hgrowth : ∀ k, a k + f (k + 3) ≤ f k) :
    Summable a ∧ ∑' k, a k ≤ 3 * W := by
  have h := three_step_growth_sum_le a f W hnn hfirst hgrowth
  exact ⟨summable_of_sum_range_le ha h, Real.tsum_le_of_sum_range_le ha h⟩

end GenericChaining


namespace GenericChaining

noncomputable def GreedyPartition.index {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) (t : T) (ht : t ∈ A) : Fin q.length :=
  Classical.choose (q.cover t ht)

theorem GreedyPartition.index_mem {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) (t : T) (ht : t ∈ A) :
    t ∈ q.cell (q.index t ht) := Classical.choose_spec (q.cover t ht)

noncomputable def GreedyPartition.selectedCell {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) (t : T) : Finset T :=
  if ht : t ∈ A then q.cell (q.index t ht) else ∅

noncomputable def GreedyPartition.selectedLabel {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) (t : T) : ℕ :=
  if ht : t ∈ A then (q.index t ht).val + 1 else 1

theorem GreedyPartition.selectedCell_mem {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) (t : T) (ht : t ∈ A) :
    t ∈ q.selectedCell t := by
  simp only [selectedCell, dif_pos ht]
  exact q.index_mem t ht

theorem GreedyPartition.selectedCell_subset {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) (t : T) : q.selectedCell t ⊆ A := by
  unfold selectedCell
  split
  · exact q.subset _
  · exact Finset.empty_subset _

theorem GreedyPartition.index_eq_of_mem {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) {s t : T} (hs : s ∈ A) (ht : t ∈ A)
    (h : s ∈ q.cell (q.index t ht)) : q.index s hs = q.index t ht := by
  by_contra hn
  exact Finset.disjoint_left.mp (q.disjoint hn) (q.index_mem s hs) h

theorem GreedyPartition.selectedCell_same {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) {s t : T} (ht : t ∈ A)
    (hs : s ∈ q.selectedCell t) : q.selectedCell s = q.selectedCell t := by
  have hsA := q.selectedCell_subset t hs
  have hs' : s ∈ q.cell (q.index t ht) := by simpa only [selectedCell, dif_pos ht] using hs
  simp only [selectedCell, dif_pos hsA, dif_pos ht, q.index_eq_of_mem hsA ht hs']

theorem GreedyPartition.selectedLabel_same {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) {s t : T} (hs : s ∈ A) (ht : t ∈ A)
    (heq : q.selectedCell s = q.selectedCell t) : q.selectedLabel s = q.selectedLabel t := by
  have hst : s ∈ q.selectedCell t := heq ▸ q.selectedCell_mem s hs
  have hst' : s ∈ q.cell (q.index t ht) := by simpa only [selectedCell, dif_pos ht] using hst
  simp only [selectedLabel, dif_pos hs, dif_pos ht, q.index_eq_of_mem hs ht hst']

theorem GreedyPartition.selectedCell_of_label {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {A : Finset T} {r ρ : ℝ}
    (q : GreedyPartition d F A r ρ) {s t : T} (hs : s ∈ A) (ht : t ∈ A)
    (heq : q.selectedLabel s = q.selectedLabel t) : q.selectedCell s = q.selectedCell t := by
  simp only [selectedLabel, dif_pos hs, dif_pos ht] at heq
  have hi : q.index s hs = q.index t ht := Fin.ext (Nat.add_right_cancel heq)
  simp only [selectedCell, dif_pos hs, dif_pos ht, hi]

/-- A rooted sequence of partitions with positive sibling labels. Label
sequences identify cells, which is the property used for counting tree cuts. -/
structure LabelledPartitions (T : Type*) [Fintype T] [DecidableEq T] where
  cell : ℕ → T → Finset T
  root : ∀ t, cell 0 t = Finset.univ
  mem : ∀ k t, t ∈ cell k t
  refines : ∀ k t, cell (k + 1) t ⊆ cell k t
  same_cell : ∀ k s t, s ∈ cell k t → cell k s = cell k t
  label : ℕ → T → ℕ
  label_zero : ∀ t, label 0 t = 1
  label_pos : ∀ k t, 0 < label k t
  label_cell : ∀ k s t, cell k s = cell k t → label k s = label k t
  label_unique : ∀ k s t, cell k s = cell k t →
    label (k + 1) s = label (k + 1) t → cell (k + 1) s = cell (k + 1) t

/-- Iterating an arbitrary finite-set refinement rule, starting with the root. -/
noncomputable def recursiveCells {T : Type*} [Fintype T]
    (R : ℕ → Finset T → T → Finset T) : ℕ → T → Finset T
  | 0, _ => Finset.univ
  | k + 1, t => R k (recursiveCells R k t) t

end GenericChaining

namespace GenericChaining

/-- Repeated greedy refinement constructs labelled partitions whose local
widths satisfy the three-level growth inequality. -/
theorem exists_labelled_partitions_of_growth {T : Type*} [Fintype T] [DecidableEq T]
    (d : T → T → ℝ) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s)
    (tri : ∀ s t c, d s t ≤ d s c + d t c)
    (F : Finset T → ℝ) (hF : Monotone F)
    {c α D : ℝ} (hgrowth : HasLocalGrowth d F c α)
    (hα : 0 < α) (hαsmall : α ≤ 1 / 2) (hD : 0 < D)
    (hdiamRoot : ∀ s t, d s t ≤ 2 * D) :
    ∃ L : LabelledPartitions T,
      (∀ k t, ∀ s ∈ L.cell k t, ∀ u ∈ L.cell k t, d s u ≤ 2 * D * α ^ k) ∧
      (∀ k t, c * (D * α ^ (k + 1)) *
        Real.sqrt (Real.log (L.label (k + 1) t : ℝ)) + F (L.cell (k + 3) t) ≤
          F (L.cell k t)) := by
  classical
  let radius (k : ℕ) := D * α ^ (k + 1)
  have hex (k : ℕ) (A : Finset T) :=
    exists_greedy_partition d diag symm tri F hF (radius k) (α * radius k)
      (by dsimp [radius]; positivity) A
  let Q (k : ℕ) (A : Finset T) : GreedyPartition d F A (radius k) (α * radius k) :=
    Classical.choice (hex k A)
  let R := fun k A t => (Q k A).selectedCell t
  let C := recursiveCells R
  have hmem (k : ℕ) (t : T) : t ∈ C k t := by
    induction k with
    | zero => exact Finset.mem_univ _
    | succ k ih => exact (Q k (C k t)).selectedCell_mem t ih
  have href (k : ℕ) (t : T) : C (k + 1) t ⊆ C k t :=
    (Q k (C k t)).selectedCell_subset t
  have hsame (k : ℕ) (s t : T) (hs : s ∈ C k t) : C k s = C k t := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hsA : s ∈ C k t := href k t hs
      have hp : C k s = C k t := ih hsA
      change (Q k (C k s)).selectedCell s = (Q k (C k t)).selectedCell t
      rw [hp]
      exact (Q k (C k t)).selectedCell_same (hmem k t) hs
  let lab : ℕ → T → ℕ
    | 0, _ => 1
    | k + 1, t => (Q k (C k t)).selectedLabel t
  have hlabelCell (k : ℕ) (s t : T) (heq : C k s = C k t) : lab k s = lab k t := by
    cases k with
    | zero => rfl
    | succ k =>
      have hsA : s ∈ C k t := href k t (heq ▸ hmem (k + 1) s)
      have hp : C k s = C k t := hsame k s t hsA
      change (Q k (C k s)).selectedLabel s = (Q k (C k t)).selectedLabel t
      rw [hp]
      apply (Q k (C k t)).selectedLabel_same hsA (hmem k t)
      change (Q k (C k s)).selectedCell s = (Q k (C k t)).selectedCell t at heq
      rwa [hp] at heq
  let L : LabelledPartitions T := {
    cell := C
    root := fun _ => rfl
    mem := hmem
    refines := href
    same_cell := hsame
    label := lab
    label_zero := fun _ => rfl
    label_pos := by
      intro k t
      cases k with
      | zero => exact Nat.zero_lt_one
      | succ k =>
        change 0 < (Q k (C k t)).selectedLabel t
        unfold GreedyPartition.selectedLabel
        split <;> omega
    label_cell := hlabelCell
    label_unique := by
      intro k s t hpar hlab
      change (Q k (C k s)).selectedCell s = (Q k (C k t)).selectedCell t
      rw [hpar]
      have hsA : s ∈ C k t := hpar ▸ hmem k s
      apply (Q k (C k t)).selectedCell_of_label hsA (hmem k t)
      change (Q k (C k s)).selectedLabel s = (Q k (C k t)).selectedLabel t at hlab
      rwa [hpar] at hlab }
  have hdiam (k : ℕ) (t s : T) (hs : s ∈ C k t)
      (u : T) (hu : u ∈ C k t) : d s u ≤ 2 * D * α ^ k := by
    cases k with
    | zero => simpa only [pow_zero, mul_one] using hdiamRoot s u
    | succ k =>
      have ht := hmem k t
      have hs' : s ∈ (Q k (C k t)).cell ((Q k (C k t)).index t ht) := by
        change s ∈ (Q k (C k t)).selectedCell t at hs
        simpa only [GreedyPartition.selectedCell, dif_pos ht] using hs
      have hu' : u ∈ (Q k (C k t)).cell ((Q k (C k t)).index t ht) := by
        change u ∈ (Q k (C k t)).selectedCell t at hu
        simpa only [GreedyPartition.selectedCell, dif_pos ht] using hu
      simpa only [radius, mul_assoc] using (Q k (C k t)).diameter _ s hs' u hu'
  refine ⟨L, hdiam, ?_⟩
  intro k t
  have ht := hmem k t
  have hsub : C (k + 3) t ⊆ (Q k (C k t)).cell ((Q k (C k t)).index t ht) := by
    have hh := (href (k + 2) t).trans (href (k + 1) t)
    change C (k + 3) t ⊆ (Q k (C k t)).selectedCell t at hh
    simpa only [GreedyPartition.selectedCell, dif_pos ht] using hh
  have hsmall : ∀ s ∈ C (k + 3) t, ∀ u ∈ C (k + 3) t,
      d s u ≤ α * radius k := by
    intro s hs u hu
    have hh := hdiam (k + 3) t s hs u hu
    have hsq : 2 * α ^ 2 ≤ α := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ radius k by dsimp [radius]; positivity)
    rw [show k + 3 = (k + 1) + 2 by omega, pow_add] at hh
    dsimp [radius] at hm ⊢
    nlinarith
  have hh := (Q k (C k t)).rank_growth_descendant hgrowth
    (show 0 < radius k by dsimp [radius]; positivity)
    ((Q k (C k t)).index t ht) (C (k + 3) t) ⟨t, hmem _ t⟩ hsub hsmall
  simpa only [L, lab, GreedyPartition.selectedLabel, dif_pos ht, radius] using hh

/-- The labelled partitions constructed from growth have uniformly bounded
branch cost; the constant depends only on the growth coefficient. -/
theorem exists_labelled_partitions_branch_bound {T : Type*} [Fintype T] [DecidableEq T]
    (d : T → T → ℝ) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s)
    (tri : ∀ s t c, d s t ≤ d s c + d t c)
    (F : Finset T → ℝ) (hF : Monotone F) (hFnn : ∀ A, 0 ≤ F A)
    {c α D : ℝ} (hgrowth : HasLocalGrowth d F c α) (hc : 0 < c)
    (hα : 0 < α) (hαsmall : α ≤ 1 / 2) (hD : 0 < D)
    (hdiamRoot : ∀ s t, d s t ≤ 2 * D) :
    ∃ L : LabelledPartitions T,
      (∀ k t, ∀ s ∈ L.cell k t, ∀ u ∈ L.cell k t, d s u ≤ 2 * D * α ^ k) ∧
      (∀ t, Summable (fun k => D * α ^ (k + 1) *
          Real.sqrt (Real.log (L.label (k + 1) t : ℝ))) ∧
        ∑' k, D * α ^ (k + 1) * Real.sqrt (Real.log (L.label (k + 1) t : ℝ)) ≤
          3 * F Finset.univ / c) := by
  obtain ⟨L, hdiam, hstep⟩ := exists_labelled_partitions_of_growth
    d diag symm tri F hF hgrowth hα hαsmall hD hdiamRoot
  refine ⟨L, hdiam, fun t => ?_⟩
  let a (k : ℕ) := D * α ^ (k + 1) * Real.sqrt (Real.log (L.label (k + 1) t : ℝ))
  have ha (k : ℕ) : 0 ≤ a k := by dsimp [a]; positivity
  have hpartial (N : ℕ) : ∑ k ∈ Finset.range N, a k ≤ 3 * F Finset.univ / c := by
    have hh := three_step_growth_sum_le (fun k => c * a k) (fun k => F (L.cell k t))
      (F Finset.univ) (fun k => hFnn _) (fun k _ => hF (Finset.subset_univ _))
      (fun k => by simpa only [a, mul_assoc] using hstep k t) N
    rw [← Finset.mul_sum] at hh
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm c] using hh
  exact ⟨summable_of_sum_range_le ha hpartial, Real.tsum_le_of_sum_range_le ha hpartial⟩

end GenericChaining

namespace GenericChaining

/-- Growth on two points bounds every distance by the width of the parent.
This is the diameter term needed when cumulative labels are converted to nets. -/
theorem HasLocalGrowth.pair_bound {T : Type*} [DecidableEq T]
    {d : T → T → ℝ} {F : Finset T → ℝ} {c α : ℝ}
    (hgrowth : HasLocalGrowth d F c α) (hc : 0 ≤ c)
    (diag : ∀ t, d t t = 0) (symm : ∀ s t, d s t = d t s)
    (hFnn : ∀ A, 0 ≤ F A) (A : Finset T) {s t : T} (hs : s ∈ A) (ht : t ∈ A) :
    c * d s t * Real.sqrt (Real.log 2) ≤ F A := by
  by_cases hr : 0 < d s t
  · have hst : s ≠ t := by intro heq; subst t; simp [diag] at hr
    have hNsub : ({s, t} : Finset T) ⊆ A := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hs, ht⟩
    have hh := hgrowth A {s, t} (d s t) 0 (by simp) hNsub hr (by
      intro u hu v hv huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (huv rfl).elim
      · exact le_rfl
      · exact (symm _ _).le
      · exact (huv rfl).elim) (fun u _ => hFnn _)
    simpa only [Finset.card_pair hst, Nat.cast_ofNat, add_zero] using hh
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc
      (le_of_not_gt hr)) (Real.sqrt_nonneg _)).trans (hFnn A)

/-- If all finite distances vanish, the Gaussian chaining functional vanishes. -/
theorem gamma2_eq_zero_of_zero_dist {T : Type*} [Nonempty T]
    (d : T → T → NNReal) (hd : ∀ s t, d s t = 0) :
    gamma2 (fun s t => (d s t : ENNReal)) = 0 := by
  let N : Nets T := fun _ _ => Classical.choice ‹Nonempty T›
  have hz (k : ℕ) (t : T) : netDist (fun s t => (d s t : ENNReal)) N k t = 0 := by
    apply le_antisymm _ (zero_le _)
    exact (iInf_le _ ⟨0, capacity_pos k⟩).trans (by simp only [hd, ENNReal.coe_zero, le_refl])
  apply le_antisymm _ (zero_le _)
  refine (iInf_le _ N).trans ?_
  simp only [cost, hz, mul_zero, tsum_zero, iSup_const, le_refl]

end GenericChaining
