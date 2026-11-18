import GenericChaining.Dirksen

/-!
# Deterministic facts for the Gaussian chaining functional

Finite scaling commutes with the functional. The singleton net at level zero
also shows that the functional controls every distance. These two elementary
facts absorb the scale and the base-point term in the Gaussian upper bound.
-/

namespace GenericChaining

open MeasureTheory
open scoped NNReal ENNReal

variable {T : Type*} [Nonempty T]

omit [Nonempty T] in
theorem netDist_mul_nnreal (d : T → T → ℝ≥0∞) (c : ℝ≥0) (N : Nets T)
    (k : ℕ) (t : T) :
    netDist (fun s t => (c : ℝ≥0∞) * d s t) N k t =
      (c : ℝ≥0∞) * netDist d N k t := by
  haveI : Nonempty (Fin (capacity k)) := ⟨⟨0, capacity_pos k⟩⟩
  exact (ENNReal.mul_iInf (fun h => (ENNReal.coe_ne_top h).elim)).symm

omit [Nonempty T] in
theorem cost_mul_nnreal (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞)
    (c : ℝ≥0) (N : Nets T) :
    cost w (fun s t => (c : ℝ≥0∞) * d s t) N = (c : ℝ≥0∞) * cost w d N := by
  unfold cost
  simp_rw [netDist_mul_nnreal]
  have he (k : ℕ) (t : T) : w k * ((c : ℝ≥0∞) * netDist d N k t) =
      (c : ℝ≥0∞) * (w k * netDist d N k t) := by ring
  simp_rw [he, ENNReal.tsum_mul_left]
  exact (ENNReal.mul_iSup _ _).symm

theorem gamma_mul_nnreal (w : ℕ → ℝ≥0∞) (d : T → T → ℝ≥0∞) (c : ℝ≥0) :
    gamma w (fun s t => (c : ℝ≥0∞) * d s t) = (c : ℝ≥0∞) * gamma w d := by
  haveI : Nonempty (Nets T) := ⟨fun _ _ => Classical.choice ‹Nonempty T›⟩
  unfold gamma
  simp_rw [cost_mul_nnreal]
  exact (ENNReal.mul_iInf (fun h => (ENNReal.coe_ne_top h).elim)).symm

theorem gamma_zero (w : ℕ → ℝ≥0∞) : gamma (T := T) w (fun _ _ => 0) = 0 := by
  simpa only [ENNReal.coe_zero, zero_mul] using
    gamma_mul_nnreal w (fun _ _ => 0) (0 : ℝ≥0)

theorem gamma1_zero : gamma1 (T := T) (fun _ _ => 0) = 0 := gamma_zero _

theorem gamma2_zero : gamma2 (T := T) (fun _ _ => 0) = 0 := gamma_zero _

theorem gamma2_mul_nnreal (d : T → T → ℝ≥0∞) (c : ℝ≥0) :
    gamma2 (fun s t => (c : ℝ≥0∞) * d s t) = (c : ℝ≥0∞) * gamma2 d :=
  gamma_mul_nnreal _ _ _

theorem gamma2_toReal_mul_nnreal (d : T → T → ℝ≥0) (c : ℝ≥0) :
    (gamma2 (fun s t => ((c * d s t : ℝ≥0) : ℝ≥0∞))).toReal =
      (c : ℝ) * (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal := by
  simp_rw [ENNReal.coe_mul, gamma2_mul_nnreal, ENNReal.toReal_mul, ENNReal.coe_toReal]

omit [Nonempty T] in
theorem netDist_zero_level (d : T → T → ℝ≥0∞) (N : Nets T) (t : T) :
    netDist d N 0 t = d t (N 0 ⟨0, capacity_pos 0⟩) := by
  haveI : Unique (Fin (capacity 0)) := by change Unique (Fin 1); infer_instance
  unfold netDist
  rw [iInf_unique]
  congr 2
  exact Subsingleton.elim _ _

/-- The first net is a singleton, so twice its optimal cost controls every
distance, including for a pseudometric with coincident indices. -/
theorem gamma2_diameter_le [Fintype T] (d : T → T → ℝ≥0)
    (diag : ∀ t, d t t = 0) (tri : ∀ s t c, d s t ≤ d s c + d t c)
    (s t : T) : (d s t : ℝ) ≤ 2 * (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, _, hcost, he⟩ := exists_nets_cost_lt
    (fun k => ENNReal.ofReal (Real.sqrt 2) ^ k)
    (fun _ => ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (fun s t => (d s t : ℝ≥0∞)) (fun _ _ => ENNReal.coe_ne_top)
    (fun t => by simp [diag]) (show 0 < ε/2 by linarith)
  let a : T := N 0 ⟨0, capacity_pos 0⟩
  let C := cost (fun k => ENNReal.ofReal (Real.sqrt 2) ^ k)
    (fun s t => (d s t : ℝ≥0∞)) N
  have hpoint (u : T) : (d u a : ℝ) ≤ C.toReal := by
    have hle : (d u a : ℝ≥0∞) ≤ C := by
      calc
        _ = ENNReal.ofReal (Real.sqrt 2) ^ 0 *
            netDist (fun s t => (d s t : ℝ≥0∞)) N 0 u := by
          simp only [pow_zero, one_mul, netDist_zero_level, a]
        _ ≤ ∑' k, ENNReal.ofReal (Real.sqrt 2) ^ k *
            netDist (fun s t => (d s t : ℝ≥0∞)) N k u := ENNReal.le_tsum 0
        _ ≤ C := le_iSup (fun u : T => ∑' k, ENNReal.ofReal (Real.sqrt 2) ^ k *
            netDist (fun s t => (d s t : ℝ≥0∞)) N k u) u
    simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono hcost hle
  have htri : (d s t : ℝ) ≤ (d s a : ℝ) + (d t a : ℝ) := by
    exact_mod_cast tri s t a
  change C.toReal < (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal + ε/2 at he
  have hs := hpoint s
  have ht := hpoint t
  linarith

/-- A universal factor for the upper bound of a centered Gaussian process. -/
def gaussianExpectationConstant : ℝ := 100

theorem gaussianExpectationConstant_pos : 0 < gaussianExpectationConstant := by
  norm_num [gaussianExpectationConstant]

/-- The Gaussian upper bound uses only the Gaussian-scale mixed tail, the
first absolute moments of the increments, and centering at one index. -/
theorem gaussian_expectation_of_mixedTail [Fintype T] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : T → Ω → ℝ) (d : T → T → ℝ≥0) (c : ℝ≥0) (hc : c ≤ 2)
    (diag : ∀ t, d t t = 0) (symm : ∀ s t, d s t = d t s)
    (tri : ∀ s t u, d s t ≤ d s u + d t u)
    (htail : HasMixedTail μ X (fun _ _ => 0) (fun s t => c * d s t))
    (hInt : ∀ t, Integrable (X t) μ)
    (habs : ∀ s t, ∫ ω, |X s ω - X t ω| ∂μ ≤ (d s t : ℝ))
    (t₀ : T) (hcenter : ∫ ω, X t₀ ω ∂μ = 0) :
    ∫ ω, ⨆ t, X t ω ∂μ ≤
      gaussianExpectationConstant * (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal := by
  have hinc (s t : T) : Integrable (fun ω => X s ω - X t ω) μ := (hInt s).sub (hInt t)
  have hD := dirksen_expectation X (fun _ _ => 0) (fun s t => c * d s t)
    (fun _ => rfl) (fun t => by simp [diag]) (fun _ _ => rfl)
    (fun s t => congrArg (fun z => c * z) (symm s t)) (fun _ _ _ => by simp)
    (fun s t u => by
      rw [← mul_add]
      exact mul_le_mul_left' (tri s t u) c)
    htail hinc t₀
  simp only [ENNReal.coe_zero, gamma1_zero, ENNReal.toReal_zero, add_zero,
    gamma2_toReal_mul_nnreal] at hD
  have hbase : (⨆ t, ∫ ω, |X t ω - X t₀ ω| ∂μ) ≤
      2 * (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal :=
    ciSup_le fun t => (habs t t₀).trans (gamma2_diameter_le d diag tri t t₀)
  have hpoint (ω : Ω) : (⨆ t, X t ω) ≤ incrementMaximum X t₀ ω + X t₀ ω := by
    apply ciSup_le
    intro t
    have ht := (le_abs_self (X t ω - X t₀ ω)).trans (increment_le_maximum X t₀ t ω)
    linarith
  have hmax := integral_mono (integrable_iSup_finite hInt)
    ((integrable_incrementMaximum t₀ hinc).add (hInt t₀)) hpoint
  simp only [Pi.add_apply] at hmax
  rw [integral_add (integrable_incrementMaximum t₀ hinc) (hInt t₀), hcenter,
    add_zero] at hmax
  have hc' : (c : ℝ) ≤ 2 := by exact_mod_cast hc
  have hγ : 0 ≤ (gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal := ENNReal.toReal_nonneg
  have hscale := mul_le_mul_of_nonneg_right hc' hγ
  norm_num [dirksenConstant, gaussianExpectationConstant] at hD ⊢
  nlinarith

end GenericChaining
