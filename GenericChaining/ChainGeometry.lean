import GenericChaining.Link
import GenericChaining.FiniteNets
import GenericChaining.FiniteCost

/-! # The common finite chain for two distances -/

namespace GenericChaining

open scoped NNReal ENNReal

private theorem exists_nearest_index {T : Type*} (d : T → T → ℝ≥0)
    (N : Nets T) (k : ℕ) (t : T) :
    ∃ j : Fin (capacity k),
      (d t (N k j) : ℝ≥0∞) = netDist (fun s t => (d s t : ℝ≥0∞)) N k t := by
  classical
  haveI : Nonempty (Fin (capacity k)) := ⟨⟨0, capacity_pos k⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image (fun i => d t (N k i))
    Finset.univ_nonempty
  refine ⟨j, le_antisymm (le_iInf fun i => ?_) (iInf_le _ j)⟩
  change (d t (N k j) : ℝ≥0∞) ≤ (d t (N k i) : ℝ≥0∞)
  exact_mod_cast hj i (Finset.mem_univ i)

/-- The combined error of two nets at a fixed level, with the weights of
the exponential and Gaussian chaining functionals. -/
noncomputable def approximationError {T : Type*} (d₁ d₂ : T → T → ℝ≥0)
    (N₁ N₂ : Nets T) (k : ℕ) (t : T) : ℝ :=
  2 ^ k * (netDist (fun s t => (d₁ s t : ℝ≥0∞)) N₁ k t).toReal +
    (Real.sqrt 2) ^ k * (netDist (fun s t => (d₂ s t : ℝ≥0∞)) N₂ k t).toReal

theorem approximationError_nonneg {T : Type*} (d₁ d₂ : T → T → ℝ≥0)
    (N₁ N₂ : Nets T) (k : ℕ) (t : T) : 0 ≤ approximationError d₁ d₂ N₁ N₂ k t := by
  unfold approximationError
  positivity

/-- Two finite admissible nets admit a common chain. Its zeroth point is
independent of the branch, its last points are exact, and the number of points
at each level is bounded by the product of the two slot counts. -/
theorem exists_common_chain {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    (d₁ d₂ : T → T → ℝ≥0)
    (diag₁ : ∀ t, d₁ t t = 0) (diag₂ : ∀ t, d₂ t t = 0)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (N₁ N₂ : Nets T) (K : ℕ) (hK : 0 < K)
    (hsurj₁ : ∀ k, K ≤ k → Function.Surjective (N₁ k))
    (_hsurj₂ : ∀ k, K ≤ k → Function.Surjective (N₂ k)) :
    ∃ r : ℕ → T → T,
      (∀ s t, r 0 s = r 0 t) ∧
      (∀ k, K ≤ k → ∀ t, r k t = t) ∧
      (∀ k, (Finset.univ.image (r k)).card ≤ capacity k ^ 2) ∧
      (∀ k t, 2 ^ k * (d₁ t (r k t) : ℝ) + (Real.sqrt 2) ^ k * (d₂ t (r k t) : ℝ)
        ≤ 2 * approximationError d₁ d₂ N₁ N₂ k t) := by
  classical
  choose i₁ hi₁ using exists_nearest_index d₁ N₁
  choose i₂ hi₂ using exists_nearest_index d₂ N₂
  have hrep (k : ℕ) := exists_common_representatives_real d₁ d₂ tri₁ tri₂
    (2 ^ k) ((Real.sqrt 2) ^ k) (by positivity) (by positivity)
    (N₁ k) (N₂ k) (i₁ k) (i₂ k)
  choose R hR using hrep
  let r (k : ℕ) (t : T) := if K ≤ k then t else R k (i₁ k t, i₂ k t)
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro s t
    haveI : Subsingleton (Fin (capacity 0)) := by
      change Subsingleton (Fin 1)
      infer_instance
    have h₁ : i₁ 0 s = i₁ 0 t := Subsingleton.elim _ _
    have h₂ : i₂ 0 s = i₂ 0 t := Subsingleton.elim _ _
    simp only [r, show ¬K ≤ 0 by omega, ↓reduceIte, h₁, h₂]
  · intro k hk t
    simp [r, hk]
  · intro k
    by_cases hk : K ≤ k
    · have hc := Fintype.card_le_of_surjective (N₁ k) (hsurj₁ k hk)
      have hcap : capacity k ≤ capacity k ^ 2 := by
        have := capacity_pos k
        nlinarith
      calc
        (Finset.univ.image (r k)).card ≤ Fintype.card T := by
          simpa using Finset.card_image_le (s := Finset.univ) (f := r k)
        _ ≤ capacity k := by simpa using hc
        _ ≤ capacity k ^ 2 := hcap
    · have hsub : Finset.univ.image (r k) ⊆ Finset.univ.image (R k) := by
        intro t ht
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_image.mpr ⟨(i₁ k s, i₂ k s), Finset.mem_univ _, by simp [r, hk]⟩
      calc
        (Finset.univ.image (r k)).card ≤ (Finset.univ.image (R k)).card :=
          Finset.card_le_card hsub
        _ ≤ Fintype.card (Fin (capacity k) × Fin (capacity k)) := by
          simpa using Finset.card_image_le (s := Finset.univ) (f := R k)
        _ = capacity k ^ 2 := by simp [pow_two]
  · intro k t
    by_cases hk : K ≤ k
    · simp only [r, hk, ↓reduceIte, diag₁, diag₂, NNReal.coe_zero, mul_zero, add_zero]
      exact mul_nonneg (by norm_num) (approximationError_nonneg _ _ _ _ _ _)
    · have hh := (hR k t).2.2
      have he₁ : (netDist (fun s t => (d₁ s t : ℝ≥0∞)) N₁ k t).toReal =
          (d₁ t (N₁ k (i₁ k t)) : ℝ) := by rw [← hi₁]; simp
      have he₂ : (netDist (fun s t => (d₂ s t : ℝ≥0∞)) N₂ k t).toReal =
          (d₂ t (N₂ k (i₂ k t)) : ℝ) := by rw [← hi₂]; simp
      simpa only [r, hk, ↓reduceIte, approximationError, he₁, he₂] using hh

/-- Summing consecutive links loses only a universal factor. -/
theorem chain_length_le_error {T : Type*} (d₁ d₂ : T → T → ℝ≥0)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (symm₁ : ∀ s t, d₁ s t = d₁ t s) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (r : ℕ → T → T) (e : ℕ → T → ℝ)
    (he : ∀ k t, 0 ≤ e k t)
    (hr : ∀ k t, 2 ^ k * (d₁ t (r k t) : ℝ) +
      (Real.sqrt 2) ^ k * (d₂ t (r k t) : ℝ) ≤ 2 * e k t)
    (K : ℕ) (t : T) :
    (∑ k ∈ Finset.range K,
      ((2 : ℝ) ^ (k + 1) * d₁ (r k t) (r (k + 1) t) +
        Real.sqrt 2 ^ (k + 1) * d₂ (r k t) (r (k + 1) t))) ≤
      6 * ∑ k ∈ Finset.range (K + 1), e k t := by
  have hshift : (∑ k ∈ Finset.range K, e (k + 1) t) ≤
      ∑ k ∈ Finset.range (K + 1), e k t := by
    rw [Finset.sum_range_succ']
    linarith [he 0 t]
  have hprefix : (∑ k ∈ Finset.range K, e k t) ≤
      ∑ k ∈ Finset.range (K + 1), e k t := by
    rw [Finset.sum_range_succ]
    linarith [he K t]
  calc
    _ ≤ ∑ k ∈ Finset.range K, (2 * e (k + 1) t + 4 * e k t) :=
      Finset.sum_le_sum fun k _ => weighted_link_bound d₁ d₂ tri₁ tri₂ symm₁ symm₂
        k t (r k t) (r (k + 1) t) (e k t) (e (k + 1) t) (hr k t) (hr (k + 1) t)
    _ = 2 * (∑ k ∈ Finset.range K, e (k + 1) t) +
        4 * (∑ k ∈ Finset.range K, e k t) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by linarith

/-- Each finite sum of the combined errors is bounded by the two net costs. -/
theorem approximationError_sum_le_cost {T : Type*} [Fintype T] [Nonempty T]
    (d₁ d₂ : T → T → ℝ≥0)
    (N₁ N₂ : Nets T) (K : ℕ) (t : T)
    (hcost₁ : cost (fun k => (2 : ℝ≥0∞) ^ k)
      (fun s t => (d₁ s t : ℝ≥0∞)) N₁ ≠ ⊤)
    (hcost₂ : cost (fun k => (ENNReal.ofReal (Real.sqrt 2)) ^ k)
      (fun s t => (d₂ s t : ℝ≥0∞)) N₂ ≠ ⊤) :
    (∑ k ∈ Finset.range K, approximationError d₁ d₂ N₁ N₂ k t) ≤
      (cost (fun k => (2 : ℝ≥0∞) ^ k) (fun s t => (d₁ s t : ℝ≥0∞)) N₁).toReal +
      (cost (fun k => (ENNReal.ofReal (Real.sqrt 2)) ^ k)
        (fun s t => (d₂ s t : ℝ≥0∞)) N₂).toReal := by
  have h₁ := sum_toReal_netDist_le_cost (fun k => (2 : ℝ≥0∞) ^ k)
    (fun s t => (d₁ s t : ℝ≥0∞)) N₁ K t hcost₁
  have h₂ := sum_toReal_netDist_le_cost (fun k => (ENNReal.ofReal (Real.sqrt 2)) ^ k)
    (fun s t => (d₂ s t : ℝ≥0∞)) N₂ K t hcost₂
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h₁
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg 2)] at h₂
  simpa only [approximationError, Finset.sum_add_distrib] using add_le_add h₁ h₂

/-- A chain satisfying the common-representative error bounds has total
weighted length at most six times the sum of its two admissible-net costs. -/
theorem chain_length_le_cost {T : Type*} [Fintype T] [Nonempty T]
    (d₁ d₂ : T → T → ℝ≥0)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (symm₁ : ∀ s t, d₁ s t = d₁ t s) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (N₁ N₂ : Nets T) (r : ℕ → T → T)
    (hr : ∀ k t, 2 ^ k * (d₁ t (r k t) : ℝ) +
      (Real.sqrt 2) ^ k * (d₂ t (r k t) : ℝ) ≤
        2 * approximationError d₁ d₂ N₁ N₂ k t)
    (K : ℕ) (t : T)
    (hcost₁ : cost (fun k => (2 : ℝ≥0∞) ^ k)
      (fun s t => (d₁ s t : ℝ≥0∞)) N₁ ≠ ⊤)
    (hcost₂ : cost (fun k => (ENNReal.ofReal (Real.sqrt 2)) ^ k)
      (fun s t => (d₂ s t : ℝ≥0∞)) N₂ ≠ ⊤) :
    (∑ k ∈ Finset.range K,
      ((2 : ℝ) ^ (k + 1) * d₁ (r k t) (r (k + 1) t) +
        Real.sqrt 2 ^ (k + 1) * d₂ (r k t) (r (k + 1) t))) ≤
      6 * ((cost (fun k => (2 : ℝ≥0∞) ^ k)
        (fun s t => (d₁ s t : ℝ≥0∞)) N₁).toReal +
        (cost (fun k => (ENNReal.ofReal (Real.sqrt 2)) ^ k)
          (fun s t => (d₂ s t : ℝ≥0∞)) N₂).toReal) :=
  (chain_length_le_error d₁ d₂ tri₁ tri₂ symm₁ symm₂ r _
    (approximationError_nonneg _ _ _ _) hr K t).trans
    (mul_le_mul_of_nonneg_left
      (approximationError_sum_le_cost d₁ d₂ N₁ N₂ (K + 1) t hcost₁ hcost₂) (by norm_num))

end GenericChaining
