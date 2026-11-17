import GenericChaining.FiniteNets

/-!
# Finite approximations of the chaining infimum

On a finite index type one can replace every sufficiently late net by the
whole type.  This only decreases its cost, makes every branch terminate, and
ensures that all the chaining functionals of finite distances are finite.
-/

namespace GenericChaining

open scoped NNReal ENNReal

variable {T : Type*} [Fintype T] [Nonempty T]

/-- A common termination level, independent of the distance and the nets. -/
def finiteCutoff (T : Type*) [Fintype T] : ℕ := Fintype.card T + 1

omit [Nonempty T] in
theorem finiteCutoff_pos : 0 < finiteCutoff T := by simp [finiteCutoff]

theorem card_le_capacity_of_cutoff {k : ℕ} (hk : finiteCutoff T ≤ k) :
    Fintype.card T ≤ capacity k := by
  cases k with
  | zero => simp [finiteCutoff] at hk
  | succ k =>
    change Fintype.card T ≤ 2 ^ (2 ^ (k + 1))
    have h₁ := Nat.lt_two_pow_self (n := k + 1)
    have h₂ := Nat.lt_two_pow_self (n := 2 ^ (k + 1))
    simp only [finiteCutoff] at hk
    omega

/-- Keep the original nets until the fixed termination level and then list
every point. -/
noncomputable def finishNets (N : Nets T) : Nets T := fun k =>
  if hk : finiteCutoff T ≤ k then
    Classical.choose (exists_surjection_fin (capacity k) (card_le_capacity_of_cutoff hk))
  else N k

theorem finishNets_surjective (N : Nets T) {k : ℕ} (hk : finiteCutoff T ≤ k) :
    Function.Surjective (finishNets N k) := by
  simpa [finishNets, hk] using Classical.choose_spec
    (exists_surjection_fin (capacity k) (card_le_capacity_of_cutoff hk))

omit [Fintype T] [Nonempty T] in
theorem netDist_eq_zero_of_surjective (d : T → T → ℝ≥0∞)
    (hdiag : ∀ t, d t t = 0) (N : Nets T) {k : ℕ}
    (hN : Function.Surjective (N k)) (t : T) : netDist d N k t = 0 := by
  obtain ⟨j, hj⟩ := hN t
  apply le_antisymm _ (zero_le _)
  exact (iInf_le _ j).trans (by simp [hj, hdiag])

theorem netDist_finishNets_eq_zero (d : T → T → ℝ≥0∞)
    (hdiag : ∀ t, d t t = 0) (N : Nets T) {k : ℕ}
    (hk : finiteCutoff T ≤ k) (t : T) : netDist d (finishNets N) k t = 0 :=
  netDist_eq_zero_of_surjective d hdiag _ (finishNets_surjective N hk) t

theorem netDist_finishNets_le (d : T → T → ℝ≥0∞)
    (hdiag : ∀ t, d t t = 0) (N : Nets T) (k : ℕ) (t : T) :
    netDist d (finishNets N) k t ≤ netDist d N k t := by
  by_cases hk : finiteCutoff T ≤ k
  · rw [netDist_finishNets_eq_zero d hdiag N hk]
    exact zero_le _
  · simp [netDist, finishNets, hk]

theorem cost_finishNets_le (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞)
    (hdiag : ∀ t, d t t = 0) (N : Nets T) :
    cost w d (finishNets N) ≤ cost w d N := by
  apply iSup_mono
  intro t
  exact ENNReal.tsum_le_tsum fun k => mul_le_mul_left' (netDist_finishNets_le d hdiag N k t) _

omit [Fintype T] [Nonempty T] in
theorem cost_eq_sum_of_terminal (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞)
    (hdiag : ∀ t, d t t = 0) (N : Nets T) (K : ℕ)
    (hN : ∀ k, K ≤ k → Function.Surjective (N k)) :
    cost w d N = ⨆ t, ∑ k ∈ Finset.range K, w k * netDist d N k t := by
  unfold cost
  congr 1
  funext t
  exact tsum_eq_sum (s := Finset.range K) fun k hk => by
    rw [netDist_eq_zero_of_surjective d hdiag N (hN k (by simpa using hk)), mul_zero]

omit [Fintype T] [Nonempty T] in
theorem netDist_ne_top (d : T → T → ℝ≥0∞) (hd : ∀ s t, d s t ≠ ⊤)
    (N : Nets T) (k : ℕ) (t : T) : netDist d N k t ≠ ⊤ := by
  apply ne_top_of_le_ne_top (hd t (N k ⟨0, capacity_pos k⟩))
  exact iInf_le (fun j : Fin (capacity k) => d t (N k j)) ⟨0, capacity_pos k⟩

omit [Fintype T] [Nonempty T] in
/-- The finite infimum defining the distance to a net is attained. -/
theorem exists_nearest_center (d : T → T → ℝ≥0∞) (N : Nets T) (k : ℕ) (t : T) :
    ∃ j, netDist d N k t = d t (N k j) := by
  classical
  haveI : Nonempty (Fin (capacity k)) := ⟨⟨0, capacity_pos k⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image (fun j => d t (N k j))
    Finset.univ_nonempty
  refine ⟨j, le_antisymm (iInf_le _ j) (le_iInf fun i => ?_)⟩
  exact hj i (Finset.mem_univ i)

omit [Nonempty T] in
theorem cost_ne_top_of_terminal (w : ℕ → ℝ≥0∞) (hw : ∀ k, w k ≠ ⊤)
    (d : T → T → ℝ≥0∞) (hd : ∀ s t, d s t ≠ ⊤) (hdiag : ∀ t, d t t = 0)
    (N : Nets T) (K : ℕ) (hN : ∀ k, K ≤ k → Function.Surjective (N k)) :
    cost w d N ≠ ⊤ := by
  rw [cost_eq_sum_of_terminal w d hdiag N K hN]
  classical
  have hsum : (∑ t : T, ∑ k ∈ Finset.range K, w k * netDist d N k t) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro t _
    exact ENNReal.sum_ne_top.mpr fun k hk =>
      ENNReal.mul_ne_top (hw k) (netDist_ne_top d hd N k t)
  apply ne_top_of_le_ne_top hsum
  exact iSup_le fun t => Finset.single_le_sum
    (f := fun t : T => ∑ k ∈ Finset.range K, w k * netDist d N k t)
    (fun _ _ => zero_le _) (Finset.mem_univ t)

theorem gamma_ne_top (w : ℕ → ℝ≥0∞) (hw : ∀ k, w k ≠ ⊤)
    (d : T → T → ℝ≥0∞) (hd : ∀ s t, d s t ≠ ⊤) (hdiag : ∀ t, d t t = 0) :
    gamma w d ≠ ⊤ := by
  let N : Nets T := fun _ _ => Classical.choice ‹Nonempty T›
  exact ne_top_of_le_ne_top
    (cost_ne_top_of_terminal w hw d hd hdiag (finishNets N) (finiteCutoff T)
      (fun _ hk => finishNets_surjective N hk)) (iInf_le _ (finishNets N))

theorem gamma1_ne_top (d : T → T → ℝ≥0) (hdiag : ∀ t, d t t = 0) :
    gamma1 (fun s t => (d s t : ℝ≥0∞)) ≠ ⊤ := by
  apply gamma_ne_top
  · intro k
    exact ENNReal.pow_ne_top (by norm_num)
  · intro s t
    exact ENNReal.coe_ne_top
  · intro t
    simp [hdiag]

theorem gamma2_ne_top (d : T → T → ℝ≥0) (hdiag : ∀ t, d t t = 0) :
    gamma2 (fun s t => (d s t : ℝ≥0∞)) ≠ ⊤ := by
  apply gamma_ne_top
  · intro k
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · intro s t
    exact ENNReal.coe_ne_top
  · intro t
    simp [hdiag]

/-- Choose nets arbitrarily close to the chaining infimum, all of which are
the full index set from the common finite cutoff onward. -/
theorem exists_nets_cost_lt (w : ℕ → ℝ≥0∞) (hw : ∀ k, w k ≠ ⊤)
    (d : T → T → ℝ≥0∞) (hd : ∀ s t, d s t ≠ ⊤) (hdiag : ∀ t, d t t = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Nets T, (∀ k, finiteCutoff T ≤ k → Function.Surjective (N k)) ∧
      cost w d N ≠ ⊤ ∧ (cost w d N).toReal < (gamma w d).toReal + ε := by
  have hγ := gamma_ne_top w hw d hd hdiag
  have hpos : 0 < (gamma w d).toReal + ε :=
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε
  have hlt : gamma w d < ENNReal.ofReal ((gamma w d).toReal + ε) := by
    nth_rw 1 [← ENNReal.ofReal_toReal hγ]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (lt_add_of_pos_right _ hε)
  obtain ⟨N, hN⟩ := iInf_lt_iff.mp hlt
  have hM := (cost_finishNets_le w d hdiag N).trans_lt hN
  have hfinite : cost w d (finishNets N) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM.le
  refine ⟨finishNets N, (fun _ hk => finishNets_surjective N hk), hfinite, ?_⟩
  have hreal := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hM
  simpa only [ENNReal.toReal_ofReal hpos.le] using hreal

omit [Fintype T] [Nonempty T] in
/-- Every finite initial part of every branch is bounded by the real cost. -/
theorem sum_toReal_netDist_le_cost (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞)
    (N : Nets T) (K : ℕ) (t : T) (hcost : cost w d N ≠ ⊤) :
    ∑ k ∈ Finset.range K, (w k).toReal * (netDist d N k t).toReal ≤
      (cost w d N).toReal := by
  have hbranch : (∑' k, w k * netDist d N k t) ≤ cost w d N := by
    exact le_iSup (fun t : T => ∑' k, w k * netDist d N k t) t
  have hterm (k : ℕ) : w k * netDist d N k t ≠ ⊤ :=
    ne_top_of_le_ne_top hcost ((ENNReal.le_tsum k).trans hbranch)
  have hsum : (∑ k ∈ Finset.range K, w k * netDist d N k t) ≤ cost w d N :=
    (ENNReal.sum_le_tsum (Finset.range K)).trans hbranch
  have hreal := ENNReal.toReal_mono hcost hsum
  simpa only [ENNReal.toReal_sum (fun k _ => hterm k), ENNReal.toReal_mul] using hreal

omit [Fintype T] [Nonempty T] in
theorem sum_real_netDist_le_cost (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (d : T → T → ℝ≥0) (N : Nets T) (K : ℕ) (t : T)
    (hcost : cost (fun k => ENNReal.ofReal (w k)) (fun s t => (d s t : ℝ≥0∞)) N ≠ ⊤) :
    ∑ k ∈ Finset.range K, w k * (netDist (fun s t => (d s t : ℝ≥0∞)) N k t).toReal ≤
      (cost (fun k => ENNReal.ofReal (w k)) (fun s t => (d s t : ℝ≥0∞)) N).toReal := by
  have he (k : ℕ) : (ENNReal.ofReal (w k)).toReal = w k := ENNReal.toReal_ofReal (hw k)
  simpa only [he] using sum_toReal_netDist_le_cost
    (fun k => ENNReal.ofReal (w k)) (fun s t => (d s t : ℝ≥0∞)) N K t hcost

end GenericChaining
