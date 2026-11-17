import GenericChaining.GrowthPartitions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Coding labelled partitions by finite masses

A label `j ≥ 1` receives mass `1/(4 j²)`. Their sum is at most one half,
so the total mass of nodes over every finite collection of levels is at most
two. Thresholding these masses pays for the exact admissible-net capacities.
-/

namespace GenericChaining

noncomputable section

open scoped BigOperators NNReal ENNReal

/-- The reciprocal-square series bound needed for the label code. -/
theorem sum_range_reciprocal_sq_le (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤
      2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hstep : (1 : ℝ) / ((N : ℝ) + 1) ^ 2 ≤
        2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) := by
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have heq : 2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) =
          2 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
        field_simp
        ring
      rw [heq]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    linarith

/-- The sum over any finite set of positive labels is at most two. A zero
label contributes zero, so the statement also holds without a positivity premise. -/
theorem sum_reciprocal_sq_le_two (S : Finset ℕ) :
    ∑ j ∈ S, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  classical
  let N := S.sup id
  have hsub : S ⊆ Finset.range (N + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1), (1 : ℝ) / (j : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ j ∈ Finset.range N, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_range_succ']
      simp
    _ ≤ 2 - 2 / ((N : ℝ) + 1) := sum_range_reciprocal_sq_le N
    _ ≤ 2 := by linarith [show 0 ≤ (2 : ℝ) / ((N : ℝ) + 1) by positivity]

/-- The mass assigned to one positive label. -/
def labelMass (j : ℕ) : ℝ := 1 / (4 * (j : ℝ) ^ 2)

theorem labelMass_nonneg (j : ℕ) : 0 ≤ labelMass j := by unfold labelMass; positivity

theorem sum_labelMass_le_half (S : Finset ℕ) : ∑ j ∈ S, labelMass j ≤ 1 / 2 := by
  have heq : (∑ j ∈ S, labelMass j) = (∑ j ∈ S, (1 : ℝ) / (j : ℝ) ^ 2) / 4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [labelMass]
    ring
  rw [heq]
  linarith [sum_reciprocal_sq_le_two S]

/-- Multiplicative mass of a finite sequence of labels. -/
def codeMass : List ℕ → ℝ
  | [] => 1
  | j :: js => labelMass j * codeMass js

@[simp] theorem codeMass_nil : codeMass [] = 1 := rfl

theorem codeMass_nonneg (s : List ℕ) : 0 ≤ codeMass s := by
  induction s with
  | nil => norm_num [codeMass]
  | cons j s ih => exact mul_nonneg (labelMass_nonneg j) ih

@[simp] theorem codeMass_append (s t : List ℕ) : codeMass (s ++ t) = codeMass s * codeMass t := by
  induction s with
  | nil => simp [codeMass]
  | cons j s ih => simp [codeMass, ih, mul_assoc]

@[simp] theorem codeMass_singleton (j : ℕ) : codeMass [j] = labelMass j := by simp [codeMass]

namespace LabelledPartitions

variable {T : Type*} [Fintype T] [DecidableEq T] (P : LabelledPartitions T)

/-- The finite label address of a cell. The initial singleton label is omitted. -/
def code (P : LabelledPartitions T) : ℕ → T → List ℕ
  | 0, _ => []
  | k + 1, t => code P k t ++ [P.label (k + 1) t]

@[simp] theorem code_zero (t : T) : P.code 0 t = [] := rfl
@[simp] theorem code_succ (k : ℕ) (t : T) :
    P.code (k + 1) t = P.code k t ++ [P.label (k + 1) t] := rfl
@[simp] theorem code_length (k : ℕ) (t : T) : (P.code k t).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [code, ih]

/-- Different cells have different finite label addresses. -/
theorem cell_eq_of_code_eq (k : ℕ) {s t : T} (h : P.code k s = P.code k t) :
    P.cell k s = P.cell k t := by
  induction k with
  | zero => simp [P.root]
  | succ k ih =>
    have hh := List.append_inj h (by simp)
    have hp := ih hh.1
    have hl : P.label (k + 1) s = P.label (k + 1) t := by simpa using hh.2
    exact P.label_unique k s t hp hl

/-- The distinct code words at one level. -/
def codes (k : ℕ) : Finset (List ℕ) := Finset.univ.image (P.code k)

/-- Each next-level code has one parent code and one of the labels used there. -/
theorem codes_succ_subset (k : ℕ) :
    P.codes (k + 1) ⊆ ((P.codes k).product (Finset.univ.image (P.label (k + 1)))).image
      (fun p : List ℕ × ℕ => p.1 ++ [p.2]) := by
  intro s hs
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_image.mpr ⟨(P.code k t, P.label (k + 1) t),
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, rfl⟩

/-- Total code mass decreases by at least a factor of two at each level. -/
theorem codes_mass_succ_le (k : ℕ) :
    ∑ s ∈ P.codes (k + 1), codeMass s ≤ (1 / 2) * ∑ s ∈ P.codes k, codeMass s := by
  let J := Finset.univ.image (P.label (k + 1))
  calc
    _ ≤ ∑ s ∈ ((P.codes k).product J).image
        (fun p : List ℕ × ℕ => p.1 ++ [p.2]), codeMass s :=
      Finset.sum_le_sum_of_subset_of_nonneg (P.codes_succ_subset k)
        (fun s _ _ => codeMass_nonneg s)
    _ ≤ ∑ p ∈ (P.codes k).product J, codeMass (p.1 ++ [p.2]) :=
      Finset.sum_image_le_of_nonneg (fun s _ => codeMass_nonneg s)
    _ = ∑ s ∈ P.codes k, codeMass s * ∑ j ∈ J, labelMass j := by
      calc
        _ = ∑ s ∈ P.codes k, ∑ j ∈ J, codeMass (s ++ [j]) :=
          Finset.sum_product (P.codes k) J (fun p : List ℕ × ℕ => codeMass (p.1 ++ [p.2]))
        _ = _ := by simp only [codeMass_append, codeMass_singleton, Finset.mul_sum]
    _ ≤ ∑ s ∈ P.codes k, codeMass s * (1 / 2) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (sum_labelMass_le_half J)
        (codeMass_nonneg s)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Uniform mass estimate for every level of every finite labelled partition. -/
theorem codes_mass_le [Nonempty T] (k : ℕ) :
    ∑ s ∈ P.codes k, codeMass s ≤ (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [codes, code]
    rw [Finset.image_const Finset.univ_nonempty]
    simp
  | succ k ih =>
    calc
      _ ≤ (1 / 2) * ∑ s ∈ P.codes k, codeMass s := P.codes_mass_succ_le k
      _ ≤ (1 / 2) * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- All distinct addresses in the first `N` levels. -/
def nodes (N : ℕ) : Finset (Σ _ : ℕ, List ℕ) :=
  (Finset.range N).sigma (fun k => P.codes k)

/-- All finite initial portions of the labelled tree have total mass at most two. -/
theorem nodes_mass_le [Nonempty T] (N : ℕ) :
    ∑ p ∈ P.nodes N, codeMass p.2 ≤ 2 := by
  change (∑ p ∈ (Finset.range N).sigma (fun k => P.codes k), codeMass p.2) ≤ 2
  rw [Finset.sum_sigma]
  calc
    _ ≤ ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k :=
      Finset.sum_le_sum fun k _ => P.codes_mass_le k
    _ ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
      (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).summable.sum_le_tsum _
        (fun k _ => by positivity)
    _ = 2 := by
      rw [(hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).tsum_eq]
      norm_num

/-- Nodes whose inverse mass is below a given threshold. -/
def eligibleNodes (Q N : ℕ) : Finset (Σ _ : ℕ, List ℕ) :=
  (P.nodes N).filter (fun p => (1 : ℝ) / Q < codeMass p.2)

/-- At most twice the threshold many nodes can have mass greater than its reciprocal. -/
theorem eligibleNodes_card_le [Nonempty T] (Q N : ℕ) (hQ : 0 < Q) :
    (P.eligibleNodes Q N).card ≤ 2 * Q := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmass : ((P.eligibleNodes Q N).card : ℝ) / Q ≤ 2 := by
    calc
      _ = ∑ _p ∈ P.eligibleNodes Q N, (1 : ℝ) / Q := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ P.eligibleNodes Q N, codeMass p.2 :=
        Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2.le
      _ ≤ ∑ p ∈ P.nodes N, codeMass p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => codeMass_nonneg p.2)
      _ ≤ 2 := P.nodes_mass_le N
  exact_mod_cast (div_le_iff₀ hQr).mp hmass

/-- The cell represented by a valid address. The value at an invalid address is empty. -/
def nodeCell (p : Σ _ : ℕ, List ℕ) : Finset T :=
  if h : ∃ t, P.code p.1 t = p.2 then P.cell p.1 (Classical.choose h) else ∅

@[simp] theorem nodeCell_code (k : ℕ) (t : T) :
    P.nodeCell ⟨k, P.code k t⟩ = P.cell k t := by
  dsimp only [nodeCell]
  rw [dif_pos (show ∃ s, P.code k s = P.code k t from ⟨t, rfl⟩)]
  exact P.cell_eq_of_code_eq k (Classical.choose_spec (show ∃ s, P.code k s = P.code k t from ⟨t, rfl⟩))

/-- The finite cover containing all eligible cells. -/
def thresholdCells (Q N : ℕ) : Finset (Finset T) := (P.eligibleNodes Q N).image P.nodeCell

theorem thresholdCells_card_le [Nonempty T] (Q N : ℕ) (hQ : 0 < Q) :
    (P.thresholdCells Q N).card ≤ 2 * Q :=
  (Finset.card_image_le).trans (P.eligibleNodes_card_le Q N hQ)

theorem mem_thresholdCells (Q N k : ℕ) (t : T) (hk : k < N)
    (hm : (1 : ℝ) / Q < codeMass (P.code k t)) :
    P.cell k t ∈ P.thresholdCells Q N := by
  apply Finset.mem_image.mpr
  refine ⟨⟨k, P.code k t⟩, ?_, P.nodeCell_code k t⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hk,
    Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, hm⟩

/-- Every address used by the labelled partition has positive mass. -/
theorem codeMass_pos (k : ℕ) (t : T) : 0 < codeMass (P.code k t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [code_succ, codeMass_append, codeMass_singleton]
    apply mul_pos ih
    unfold labelMass
    have hl : (0 : ℝ) < P.label (k + 1) t := by exact_mod_cast P.label_pos (k + 1) t
    positivity

/-- Every additional positive label decreases the mass by a factor of at least four. -/
theorem codeMass_le_quarter_pow (k : ℕ) (t : T) :
    codeMass (P.code k t) ≤ (1 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hl : (1 : ℝ) ≤ P.label (k + 1) t := by exact_mod_cast P.label_pos (k + 1) t
    have hm : labelMass (P.label (k + 1) t) ≤ 1 / 4 := by
      unfold labelMass
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      nlinarith
    rw [code_succ, codeMass_append, codeMass_singleton, pow_succ]
    exact mul_le_mul ih hm (labelMass_nonneg _) (by positivity)

/-- A finite threshold already forces a cut before level `Q`. -/
theorem codeMass_at_threshold_le (Q : ℕ) (hQ : 0 < Q) (t : T) :
    codeMass (P.code Q t) ≤ (1 : ℝ) / Q := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hp : (Q : ℝ) ≤ (4 : ℝ) ^ Q := by
    have htwo : (Q : ℝ) ≤ (2 : ℝ) ^ Q := by exact_mod_cast (Nat.lt_two_pow_self (n := Q)).le
    exact htwo.trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 4) Q)
  calc
    _ ≤ (1 / 4 : ℝ) ^ Q := P.codeMass_le_quarter_pow Q t
    _ = 1 / (4 : ℝ) ^ Q := by rw [div_pow, one_pow]
    _ ≤ 1 / Q := one_div_le_one_div_of_le hQr hp

/-- The last eligible address on a branch has an ineligible successor. -/
theorem exists_threshold_cut (Q : ℕ) (hQ : 1 < Q) (t : T) :
    ∃ k < Q, (1 : ℝ) / Q < codeMass (P.code k t) ∧
      codeMass (P.code (k + 1) t) ≤ (1 : ℝ) / Q := by
  let S := (Finset.range (Q + 1)).filter (fun k => (1 : ℝ) / Q < codeMass (P.code k t))
  have hQr : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hS : S.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hQr
  let k := S.max' hS
  have hkS : k ∈ S := Finset.max'_mem _ hS
  have hkle : k ≤ Q := by have hh := (Finset.mem_filter.mp hkS).1; simp only [Finset.mem_range] at hh; omega
  have hkne : k ≠ Q := by
    intro h
    have hh := (Finset.mem_filter.mp hkS).2
    rw [h] at hh
    exact (not_lt_of_ge (P.codeMass_at_threshold_le Q (by omega) t)) hh
  have hk : k < Q := by omega
  refine ⟨k, hk, (Finset.mem_filter.mp hkS).2, ?_⟩
  by_contra hh
  have hnext : (1 : ℝ) / Q < codeMass (P.code (k + 1) t) := lt_of_not_ge hh
  have hnextmem : k + 1 < Q + 1 := by omega
  have hn : k + 1 ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hnextmem, hnext⟩
  have hm := Finset.le_max' S (k + 1) hn
  dsimp [k] at hm ⊢
  omega

/-- The double-exponential threshold for admissible level `n+1`. -/
def threshold (n : ℕ) : ℕ := 2 ^ (2 ^ n)

theorem threshold_gt_one (n : ℕ) : 1 < threshold n := by
  unfold threshold
  exact Nat.one_lt_pow (Nat.ne_of_gt (Nat.pow_pos (by decide))) (by decide)

/-- The branch cut used at admissible level `n+1`; admissible level zero is the root. -/
def cutoff (n : ℕ) (t : T) : ℕ :=
  Classical.choose (P.exists_threshold_cut (threshold n) (threshold_gt_one n) t)

theorem cutoff_lt (n : ℕ) (t : T) : P.cutoff n t < threshold n :=
  (Classical.choose_spec (P.exists_threshold_cut (threshold n) (threshold_gt_one n) t)).1

theorem cutoff_mass_gt (n : ℕ) (t : T) :
    (1 : ℝ) / threshold n < codeMass (P.code (P.cutoff n t) t) :=
  (Classical.choose_spec (P.exists_threshold_cut (threshold n) (threshold_gt_one n) t)).2.1

theorem cutoff_succ_mass_le (n : ℕ) (t : T) :
    codeMass (P.code (P.cutoff n t + 1) t) ≤ (1 : ℝ) / threshold n :=
  (Classical.choose_spec (P.exists_threshold_cut (threshold n) (threshold_gt_one n) t)).2.2

/-- The entropy of the successor address pays for the dyadic weight of the cut. -/
theorem cutoff_log_bound (n : ℕ) (t : T) :
    (2 : ℝ) ^ n * Real.log 2 ≤ -Real.log (codeMass (P.code (P.cutoff n t + 1) t)) := by
  have hh := Real.log_le_log (P.codeMass_pos (P.cutoff n t + 1) t) (P.cutoff_succ_mass_le n t)
  have hlog : Real.log (threshold n : ℝ) = (2 : ℝ) ^ n * Real.log 2 := by
    simp only [threshold, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [one_div, Real.log_inv, hlog] at hh
  linarith

/-- The shifted thresholds fit the repository's exact successor capacities. -/
theorem twice_threshold_le_capacity (n : ℕ) : 2 * threshold n ≤ capacity (n + 1) := by
  have hQ : 2 ≤ threshold n := threshold_gt_one n
  have heq : capacity (n + 1) = threshold n ^ 2 := by
    change (2 : ℕ) ^ (2 ^ (n + 1)) = (2 ^ (2 ^ n)) ^ 2
    rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ], pow_mul]
  rw [heq]
  nlinarith

/-- Admissible finite covers selected by inverse-mass thresholds. Level zero
is explicitly a singleton, as required by the repository's gamma functional. -/
def thresholdCovers [Nonempty T] : AdmissibleCovers T where
  cells
    | 0 => {Finset.univ}
    | n + 1 => P.thresholdCells (threshold n) (threshold n)
  cover k t := by
    cases k with
    | zero => exact ⟨Finset.univ, Finset.mem_singleton_self _, Finset.mem_univ _⟩
    | succ n =>
      refine ⟨P.cell 0 t, P.mem_thresholdCells _ _ 0 t (by have := threshold_gt_one n; omega) ?_, P.mem 0 t⟩
      simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
        (by exact_mod_cast threshold_gt_one n : (1 : ℝ) < threshold n)
  card_le k := by
    cases k with
    | zero => simp [capacity]
    | succ n =>
      change (P.thresholdCells (threshold n) (threshold n)).card ≤ capacity (n + 1)
      exact (P.thresholdCells_card_le (threshold n) (threshold n)
        (Nat.zero_lt_of_lt (threshold_gt_one n))).trans (twice_threshold_le_capacity n)

/-- The branch's selected cut is one of the cells in its admissible cover. -/
theorem cutoff_cell_mem [Nonempty T] (n : ℕ) (t : T) :
    P.cell (P.cutoff n t) t ∈ P.thresholdCovers.cells (n + 1) :=
  P.mem_thresholdCells _ _ _ t (P.cutoff_lt n t) (P.cutoff_mass_gt n t)

/-- The logarithm of a code mass is the cumulative rank entropy plus its depth cost. -/
theorem neg_log_codeMass (k : ℕ) (t : T) :
    -Real.log (codeMass (P.code k t)) = (k : ℝ) * Real.log 4 +
      2 * ∑ j ∈ Finset.range k, Real.log (P.label (j + 1) t : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlpos : (0 : ℝ) < P.label (k + 1) t := by exact_mod_cast P.label_pos (k + 1) t
    rw [code_succ, codeMass_append, codeMass_singleton,
      Real.log_mul (ne_of_gt (P.codeMass_pos k t)) (by unfold labelMass; positivity)]
    have hl : Real.log (labelMass (P.label (k + 1) t)) =
        -Real.log 4 - 2 * Real.log (P.label (k + 1) t : ℝ) := by
      unfold labelMass
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity), Real.log_one, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (pow_ne_zero _ (ne_of_gt hlpos)), Real.log_pow]
      ring
    rw [hl, Finset.sum_range_succ]
    push_cast
    linarith

end LabelledPartitions

/-- An admissible net can meet every nonempty cell of an admissible cover. -/
theorem exists_nets_meeting_cells {T : Type*} [Nonempty T] [DecidableEq T]
    (A : AdmissibleCovers T) : ∃ N : Nets T,
      ∀ k B, B ∈ A.cells k → B.Nonempty → ∃ j, N k j ∈ B := by
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
  refine ⟨N, fun k B hB hne => ?_⟩
  obtain ⟨j, hj⟩ := hf k ⟨B, hB⟩
  refine ⟨j, ?_⟩
  dsimp [N]
  rw [hj]
  exact hpick B hne

/-- The inverse-mass cuts give an admissible net with their branchwise diameter errors. -/
theorem LabelledPartitions.exists_threshold_nets {T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] (P : LabelledPartitions T) (d : T → T → ℝ≥0) (D α : ℝ)
    (hdiam : ∀ k t, ∀ s ∈ P.cell k t, ∀ u ∈ P.cell k t, (d s u : ℝ) ≤ 2 * D * α ^ k) :
    ∃ N : Nets T, (∀ t, netDist (fun s t => (d s t : ℝ≥0∞)) N 0 t ≤ ENNReal.ofReal (2 * D)) ∧
      ∀ n t, netDist (fun s t => (d s t : ℝ≥0∞)) N (n + 1) t ≤
        ENNReal.ofReal (2 * D * α ^ (P.cutoff n t)) := by
  obtain ⟨N, hN⟩ := exists_nets_meeting_cells P.thresholdCovers
  refine ⟨N, fun t => ?_, fun n t => ?_⟩
  · obtain ⟨j, hj⟩ := hN 0 Finset.univ (Finset.mem_singleton_self _) Finset.univ_nonempty
    apply (iInf_le _ j).trans
    have hh := hdiam 0 t t (P.mem 0 t) (N 0 j) (by simpa only [P.root] using hj)
    simpa only [pow_zero, mul_one, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hh
  · obtain ⟨j, hj⟩ := hN (n + 1) (P.cell (P.cutoff n t) t) (P.cutoff_cell_mem n t) ⟨t, P.mem _ t⟩
    apply (iInf_le _ j).trans
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (hdiam _ t t (P.mem _ t) _ hj)

/-- The Gaussian functional is bounded by the diameter cost of the labelled
threshold cuts, with the initial root contribution displayed separately. -/
theorem LabelledPartitions.gamma2_le_threshold_cost {T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] (P : LabelledPartitions T) (d : T → T → ℝ≥0) (D α : ℝ)
    (hdiam : ∀ k t, ∀ s ∈ P.cell k t, ∀ u ∈ P.cell k t, (d s u : ℝ) ≤ 2 * D * α ^ k) :
    gamma2 (fun s t => (d s t : ℝ≥0∞)) ≤ ⨆ t,
      ENNReal.ofReal (2 * D) + ∑' n, ENNReal.ofReal (Real.sqrt 2) ^ (n + 1) *
        ENNReal.ofReal (2 * D * α ^ (P.cutoff n t)) := by
  obtain ⟨N, hzero, hsucc⟩ := P.exists_threshold_nets d D α hdiam
  apply (iInf_le _ N).trans
  refine iSup_le fun t => le_iSup_of_le t ?_
  change (∑' k, ENNReal.ofReal (Real.sqrt 2) ^ k *
    netDist (fun s t => (d s t : ℝ≥0∞)) N k t) ≤ _
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, one_mul]
  exact add_le_add (hzero t) (ENNReal.tsum_le_tsum fun n => mul_le_mul_left' (hsucc n t) _)


/-- A real summable cut-cost estimate transfers directly to the Gaussian
functional. Its finite upper bound also justifies taking the real value. -/
theorem LabelledPartitions.gamma2_toReal_le_cut_cost {T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] (P : LabelledPartitions T) (d : T → T → ℝ≥0) (D α C : ℝ)
    (hD : 0 ≤ D) (hα : 0 ≤ α)
    (hdiam : ∀ k t, ∀ s ∈ P.cell k t, ∀ u ∈ P.cell k t, (d s u : ℝ) ≤ 2 * D * α ^ k)
    (hcut : ∀ t, Summable (fun n => D * (Real.sqrt 2 ^ n * α ^ (P.cutoff n t))) ∧
      ∑' n, D * (Real.sqrt 2 ^ n * α ^ (P.cutoff n t)) ≤ C) :
    (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal ≤ 2 * D + 2 * Real.sqrt 2 * C := by
  have hC : 0 ≤ C := (tsum_nonneg (fun n => by positivity :
    ∀ n, 0 ≤ D * (Real.sqrt 2 ^ n * α ^ (P.cutoff n (Classical.choice ‹Nonempty T›))))).trans
      (hcut (Classical.choice ‹Nonempty T›)).2
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  apply (P.gamma2_le_threshold_cost d D α hdiam).trans
  refine iSup_le fun t => ?_
  have ht (n : ℕ) : ENNReal.ofReal (Real.sqrt 2) ^ (n + 1) *
      ENNReal.ofReal (2 * D * α ^ (P.cutoff n t)) =
      ENNReal.ofReal ((2 * Real.sqrt 2) * (D * (Real.sqrt 2 ^ n * α ^ (P.cutoff n t)))) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg 2), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [pow_succ]
    ring
  simp_rw [ht]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((hcut t).1.mul_left (2 * Real.sqrt 2)), tsum_mul_left]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact add_le_add_left (mul_le_mul_of_nonneg_left (hcut t).2 (by positivity)) _

end
end GenericChaining
