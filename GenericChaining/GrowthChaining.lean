import GenericChaining.LabelledNets
import GenericChaining.LabelledCost

/-!
# Local growth controls the admissible-net functional

The growth estimate constructs labelled partitions with a bounded rank cost.
Inverse-mass cuts turn them into admissible nets. The two-point growth estimate
also controls the initial diameter, including the case of a zero functional.
-/
namespace GenericChaining
open scoped NNReal ENNReal

lemma sqrt_log_two_pos : 0 < Real.sqrt (Real.log 2) := by
  exact Real.sqrt_pos.mpr (Real.log_pos (by norm_num))

/-- The two-point consequence of growth controls every distance by the root
functional, with a constant independent of the finite index set. -/
theorem HasLocalGrowth.dist_le_root {T : Type*} [Fintype T] [DecidableEq T]
    (d : T → T → ℝ≥0) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s) (F : Finset T → ℝ)
    (hFnn : ∀ A, 0 ≤ F A) {c α : ℝ}
    (hgrowth : HasLocalGrowth (fun s t => (d s t : ℝ)) F c α) (hc : 0 < c)
    (s t : T) : (d s t : ℝ) ≤ F Finset.univ / (c * Real.sqrt (Real.log 2)) := by
  have hh := hgrowth.pair_bound hc.le (fun t => by simp [diag])
    (fun s t => by simp only [symm]) hFnn Finset.univ
    (Finset.mem_univ s) (Finset.mem_univ t)
  apply (le_div_iff₀ (mul_pos hc sqrt_log_two_pos)).mpr
  nlinarith

/-- A zero root width forces all distances to vanish. -/
theorem HasLocalGrowth.zero_dist_of_root_zero {T : Type*} [Fintype T] [DecidableEq T]
    (d : T → T → ℝ≥0) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s) (F : Finset T → ℝ)
    (hFnn : ∀ A, 0 ≤ F A) {c α : ℝ}
    (hgrowth : HasLocalGrowth (fun s t => (d s t : ℝ)) F c α) (hc : 0 < c)
    (hzero : F Finset.univ = 0) (s t : T) : d s t = 0 := by
  have hh := hgrowth.dist_le_root d diag symm F hFnn hc s t
  rw [hzero, zero_div] at hh
  exact NNReal.coe_eq_zero.mp (le_antisymm hh (d s t).coe_nonneg)

/-- A universal constant for the fixed relative radius `1/8` in local growth. -/
noncomputable def growthChainingConstant : ℝ :=
  (2 + 64*Real.sqrt 2) / Real.sqrt (Real.log 2) + 768*Real.sqrt 2

lemma growthChainingConstant_pos : 0 < growthChainingConstant := by
  unfold growthChainingConstant
  exact add_pos_of_pos_of_nonneg (div_pos (by positivity) sqrt_log_two_pos) (by positivity)

/-- Local width growth at relative radius `1/8` bounds the repository's
admissible-net functional. The constant is independent of all finite data. -/
theorem gamma2_le_of_localGrowth_exact {T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] (d : T → T → ℝ≥0) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s)
    (tri : ∀ s t c, d s t ≤ d s c + d t c)
    (F : Finset T → ℝ) (hF : Monotone F) (hFnn : ∀ A, 0 ≤ F A)
    {c : ℝ} (hc : 0 < c)
    (hgrowth : HasLocalGrowth (fun s t => (d s t : ℝ)) F c (1/8)) :
    (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal ≤
      growthChainingConstant / c * F Finset.univ := by
  have hfinite := gamma2_ne_top d diag
  by_cases hzero : F Finset.univ = 0
  · have hd : ∀ s t, d s t = 0 :=
      hgrowth.zero_dist_of_root_zero d diag symm F hFnn hc hzero
    rw [gamma2_eq_zero_of_zero_dist d hd, ENNReal.toReal_zero, hzero, mul_zero]
  · have hFpos : 0 < F Finset.univ := (hFnn _).lt_of_ne' hzero
    let D := F Finset.univ / (c * Real.sqrt (Real.log 2))
    have hD : 0 < D := div_pos hFpos (mul_pos hc sqrt_log_two_pos)
    have hdiamRoot (s t : T) : (d s t : ℝ) ≤ 2*D := by
      have hh := hgrowth.dist_le_root d diag symm F hFnn hc s t
      change (d s t : ℝ) ≤ D at hh
      linarith
    obtain ⟨P, hdiam, hbranch⟩ := exists_labelled_partitions_branch_bound
      (fun s t => (d s t : ℝ)) (fun t => by simp [diag])
      (fun s t => by simp only [symm]) (fun s t u => by exact_mod_cast tri s t u)
      F hF hFnn hgrowth hc (by norm_num) (by norm_num) hD hdiamRoot
    let C := 32*D + 128*(3*F Finset.univ/c)
    have hcut (t : T) : Summable (fun n => D *
        (Real.sqrt 2 ^ n * (1/8 : ℝ) ^ (P.cutoff n t))) ∧
        ∑' n, D * (Real.sqrt 2 ^ n * (1/8 : ℝ) ^ (P.cutoff n t)) ≤ C := by
      let lab := fun k => P.label k t
      let L := labelCodeLength lab
      let b := fun j => Real.sqrt (Real.log (lab (j+1) : ℝ))
      have hlab : ∀ k, 0 < lab k := fun k => P.label_pos k t
      have hthreshold (n : ℕ) : (2 : ℝ)^n ≤ L (P.cutoff n t+1) := by
        have hh := P.cutoff_log_bound n t
        rw [P.neg_log_codeMass] at hh
        rw [← labelCodeLength_mul_log_two lab] at hh
        exact (mul_le_mul_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hh
      have hprefix (M : ℕ) : (∑ j ∈ Finset.range M, D * (1/8 : ℝ) ^ (j+1) * b j) ≤
          3*F Finset.univ/c := by
        exact ((hbranch t).1.sum_le_tsum _ (fun j _ => by positivity)).trans
          (hbranch t).2
      obtain ⟨hsum, hbound⟩ := dyadic_cut_cost_le (fun n => P.cutoff n t) L b
        (α := (1/8 : ℝ)) (A := 2) (B := 3*F Finset.univ/c) (D := D)
        (by norm_num) (by norm_num) (by norm_num) hD
        (fun j => Real.sqrt_nonneg _) (labelCodeLength_nonneg lab hlab)
        (labelCodeLength_monotone lab hlab) hthreshold
        (labelCodeLength_sqrt_le lab hlab) hprefix
      refine ⟨hsum, ?_⟩
      convert hbound using 1
      dsimp [C]
      ring
    have hg := P.gamma2_toReal_le_cut_cost d D (1/8) C hD.le (by norm_num) hdiam hcut
    apply hg.trans_eq
    dsimp [C, D, growthChainingConstant]
    field_simp
    ring


/-- A coarse numerical bound for the universal deterministic constant. -/
theorem growthChainingConstant_le_4000 : growthChainingConstant ≤ 4000 := by
  have hs : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hl : (1/2 : ℝ) ≤ Real.sqrt (Real.log 2) := by
    have hsq := Real.sq_sqrt (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hnn := Real.sqrt_nonneg (Real.log 2)
    nlinarith [log_two_ge_half]
  have hd : (2+64*Real.sqrt 2)/Real.sqrt (Real.log 2) ≤ 260 := by
    apply (div_le_iff₀ sqrt_log_two_pos).mpr
    nlinarith
  unfold growthChainingConstant
  nlinarith

/-- A numerical form of local growth implying the admissible-net bound. -/
theorem gamma2_le_of_localGrowth {T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq T] (d : T → T → ℝ≥0) (diag : ∀ t, d t t = 0)
    (symm : ∀ s t, d s t = d t s)
    (tri : ∀ s t u, d s t ≤ d s u + d t u)
    (F : Finset T → ℝ) (hF : Monotone F) (hFnn : ∀ A, 0 ≤ F A)
    {c : ℝ} (hc : 0 < c)
    (hgrowth : HasLocalGrowth (fun s t => (d s t : ℝ)) F c (1/8)) :
    (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal ≤ (4000/c)*F Finset.univ := by
  apply (gamma2_le_of_localGrowth_exact d diag symm tri F hF hFnn hc hgrowth).trans
  apply mul_le_mul_of_nonneg_right _ (hFnn _)
  exact div_le_div_of_nonneg_right growthChainingConstant_le_4000 hc.le

/-- The deterministic constant can be chosen before the finite index set,
distance, functional, and growth coefficient. -/
theorem exists_gamma2_le_of_localGrowth :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : Type*) [Fintype T] [Nonempty T] [DecidableEq T]
      (d : T → T → ℝ≥0) (_ : ∀ t, d t t = 0)
      (_ : ∀ s t, d s t = d t s)
      (_ : ∀ s t u, d s t ≤ d s u + d t u)
      (F : Finset T → ℝ) (_ : Monotone F) (_ : ∀ A, 0 ≤ F A)
      (c : ℝ), 0 < c → HasLocalGrowth (fun s t => (d s t : ℝ)) F c (1/8) →
      (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal ≤ K/c*F Finset.univ := by
  exact ⟨4000, by norm_num,
    fun _ _ _ _ d diag symm tri F hF hFnn c hc hgrowth =>
      gamma2_le_of_localGrowth d diag symm tri F hF hFnn hc hgrowth⟩

end GenericChaining
