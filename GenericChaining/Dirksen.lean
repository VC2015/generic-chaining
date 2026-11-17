import GenericChaining.ChainGeometry
import GenericChaining.ChainingExpectation

/-!
# The finite expectation case of Dirksen's mixed-tail theorem

For finite pseudometrics, the extended chaining costs are finite. Applying
common representatives to two nearly optimal nets gives an exact finite
chain. Its integrated tail bounds the expected maximum by a universal
constant times the sum of the two chaining functionals.
-/

namespace GenericChaining
open MeasureTheory
open scoped NNReal ENNReal

/-- A numerical constant, independent of the index set, metrics, and process. -/
def dirksenConstant : ℝ := 48

theorem dirksenConstant_pos : 0 < dirksenConstant := by norm_num [dirksenConstant]

/-- Finite expectation form of Dirksen's Theorem 3.5. Distances may be
pseudometrics: distinct indices at zero distance are allowed. -/
theorem dirksen_expectation {T Ω : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : T → Ω → ℝ) (d₁ d₂ : T → T → ℝ≥0)
    (diag₁ : ∀ t, d₁ t t = 0) (diag₂ : ∀ t, d₂ t t = 0)
    (symm₁ : ∀ s t, d₁ s t = d₁ t s) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (tri₁ : ∀ s t c, d₁ s t ≤ d₁ s c + d₁ t c)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (htail : HasMixedTail μ X d₁ d₂)
    (hInt : ∀ s t, Integrable (fun ω => X s ω - X t ω) μ) (t₀ : T) :
    ∫ ω, incrementMaximum X t₀ ω ∂μ ≤
      dirksenConstant * ((gamma2 (fun s t => (d₂ s t : ℝ≥0∞))).toReal +
        (gamma1 (fun s t => (d₁ s t : ℝ≥0∞))).toReal) +
      2 * ⨆ t, ∫ ω, |X t ω - X t₀ ω| ∂μ := by
  classical
  -- Finiteness is established before using the real-valued functionals.
  have hγ₁ := gamma1_ne_top d₁ diag₁
  have hγ₂ := gamma2_ne_top d₂ diag₂
  let M : ℝ := ⨆ t, ∫ ω, |X t ω - X t₀ ω| ∂μ
  have hM : 0 ≤ M := (integral_nonneg fun ω => abs_nonneg (X t₀ ω - X t₀ ω)).trans
    (le_ciSup ((Set.finite_range (fun t : T => ∫ ω, |X t ω - X t₀ ω| ∂μ)).bddAbove) t₀)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (2 * dirksenConstant)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) dirksenConstant_pos)
  obtain ⟨N₁, hN₁, hc₁, he₁⟩ := exists_nets_cost_lt (T := T)
    (fun k => (2 : ℝ≥0∞) ^ k) (fun k => ENNReal.pow_ne_top (by norm_num))
    (fun s t => (d₁ s t : ℝ≥0∞)) (fun _ _ => ENNReal.coe_ne_top)
    (fun t => by simp [diag₁]) hδ
  obtain ⟨N₂, hN₂, hc₂, he₂⟩ := exists_nets_cost_lt (T := T)
    (fun k => ENNReal.ofReal (Real.sqrt 2) ^ k)
    (fun k => ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (fun s t => (d₂ s t : ℝ≥0∞)) (fun _ _ => ENNReal.coe_ne_top)
    (fun t => by simp [diag₂]) hδ
  obtain ⟨r, hstart, hend, hcard, herr⟩ := exists_common_chain d₁ d₂
    diag₁ diag₂ tri₁ tri₂ N₁ N₂ (finiteCutoff T) (finiteCutoff_pos (T := T)) hN₁ hN₂
  let a := r 0 t₀
  let c₁ := (cost (fun k => (2 : ℝ≥0∞) ^ k)
    (fun s t => (d₁ s t : ℝ≥0∞)) N₁).toReal
  let c₂ := (cost (fun k => ENNReal.ofReal (Real.sqrt 2) ^ k)
    (fun s t => (d₂ s t : ℝ≥0∞)) N₂).toReal
  have hchain := finite_chain_expectation htail hInt r (finiteCutoff T) a
    (fun t => hstart t t₀) (hend _ le_rfl) hcard
    (B := 6*(c₁+c₂)) (by dsimp [c₁, c₂]; positivity)
    (fun t => chain_length_le_cost d₁ d₂ tri₁ tri₂ symm₁ symm₂ N₁ N₂ r herr
      (finiteCutoff T) t hc₁ hc₂)
  have hpoint (ω : Ω) : incrementMaximum X t₀ ω ≤
      incrementMaximum X a ω + |X a ω - X t₀ ω| := by
    apply incrementMaximum_le
    intro t
    calc
      _ ≤ |X t ω - X a ω| + |X a ω - X t₀ ω| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add_right (increment_le_maximum X a t ω) _
  have hbase : (∫ ω, |X a ω - X t₀ ω| ∂μ) ≤ M :=
    le_ciSup ((Set.finite_range (fun t : T => ∫ ω, |X t ω - X t₀ ω| ∂μ)).bddAbove) a
  have hmax := integral_mono (integrable_incrementMaximum t₀ hInt)
    ((integrable_incrementMaximum a hInt).add (hInt a t₀).abs) hpoint
  simp only [Pi.add_apply] at hmax
  rw [integral_add (integrable_incrementMaximum a hInt) (hInt a t₀).abs] at hmax
  have hnet : dirksenConstant*(c₁+c₂) <
      dirksenConstant*((gamma2 (fun s t => (d₂ s t : ℝ≥0∞))).toReal +
        (gamma1 (fun s t => (d₁ s t : ℝ≥0∞))).toReal)+ε := by
    have hsum : c₁+c₂ <
        (gamma2 (fun s t => (d₂ s t : ℝ≥0∞))).toReal +
        (gamma1 (fun s t => (d₁ s t : ℝ≥0∞))).toReal + 2*δ := by
      change c₁ < (gamma1 _).toReal + δ at he₁
      change c₂ < (gamma2 _).toReal + δ at he₂
      linarith
    have hm := mul_lt_mul_of_pos_left hsum dirksenConstant_pos
    have heq : dirksenConstant*(2*δ) = ε := by
      dsimp [δ, dirksenConstant]
      ring
    nlinarith
  have hcoeff : chainExpectationConstant*(6*(c₁+c₂)) = dirksenConstant*(c₁+c₂) := by
    norm_num [chainExpectationConstant, dirksenConstant]
    ring
  rw [hcoeff] at hchain
  change _ ≤ _ + 2*M + ε
  linarith

end GenericChaining
