import GenericChaining.GaussianSmoothMax
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Differentiating the expected smooth maximum along a square-root interpolation

This analytic step applies to any two finite families of integrable variables.
On a compact subinterval of `(0,1)`, the derivative is dominated by a constant
times the sum of their absolute values. At the endpoints, continuity follows
from the same sum as an envelope for the smooth maximum itself.
-/

namespace GenericChaining

open MeasureTheory Set Filter Metric
open scoped BigOperators Topology

variable {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def sqrtInterpolation (X Y : I → Ω → ℝ) (s : ℝ) (ω : Ω) (i : I) : ℝ :=
  Real.sqrt s * X i ω + Real.sqrt (1 - s) * Y i ω

noncomputable def sqrtInterpolationDeriv (X Y : I → Ω → ℝ) (s : ℝ) (ω : Ω) (i : I) : ℝ :=
  X i ω / (2 * Real.sqrt s) - Y i ω / (2 * Real.sqrt (1 - s))

noncomputable def softMaxInterpolation (β : ℝ) (X Y : I → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  softMax β (sqrtInterpolation X Y s ω)

noncomputable def softMaxInterpolationDeriv (β : ℝ) (X Y : I → Ω → ℝ)
    (s : ℝ) (ω : Ω) : ℝ :=
  ∑ i, softMaxWeight β (sqrtInterpolation X Y s ω) i * sqrtInterpolationDeriv X Y s ω i

omit [Fintype I] [Nonempty I] [MeasurableSpace Ω] in
theorem sqrtInterpolation_hasDerivAt (X Y : I → Ω → ℝ) {s : ℝ} (hs : s ∈ Ioo 0 1)
    (ω : Ω) (i : I) :
    HasDerivAt (fun t => sqrtInterpolation X Y t ω i)
      (sqrtInterpolationDeriv X Y s ω i) s := by
  have h₁ := (Real.hasDerivAt_sqrt hs.1.ne').mul_const (X i ω)
  have h₂ := ((Real.hasDerivAt_sqrt (show 1 - s ≠ 0 by linarith [hs.2])).comp s
    ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))).mul_const (Y i ω)
  convert h₁.add h₂ using 1
  simp only [sqrtInterpolationDeriv]
  ring

omit [MeasurableSpace Ω] in
theorem softMaxInterpolation_hasDerivAt (β : ℝ) (hβ : β ≠ 0) (X Y : I → Ω → ℝ)
    {s : ℝ} (hs : s ∈ Ioo 0 1) (ω : Ω) :
    HasDerivAt (fun t => softMaxInterpolation β X Y t ω)
      (softMaxInterpolationDeriv β X Y s ω) s :=
  hasDerivAt_softMax_comp β hβ (fun i t => sqrtInterpolation X Y t ω i)
    (sqrtInterpolationDeriv X Y s ω) s (sqrtInterpolation_hasDerivAt X Y hs ω)

omit [Fintype I] [Nonempty I] [MeasurableSpace Ω] in
theorem sqrtInterpolation_continuous (X Y : I → Ω → ℝ) (ω : Ω) :
    Continuous (fun s => sqrtInterpolation X Y s ω) := by
  apply continuous_pi
  intro i
  exact (Real.continuous_sqrt.mul continuous_const).add
    ((continuous_const.sub continuous_id).sqrt.mul continuous_const)

omit [MeasurableSpace Ω] in
theorem softMaxInterpolation_continuous (β : ℝ) (X Y : I → Ω → ℝ) (ω : Ω) :
    Continuous (fun s => softMaxInterpolation β X Y s ω) :=
  (continuous_softMax β).comp (sqrtInterpolation_continuous X Y ω)

omit [Fintype I] [Nonempty I] [IsProbabilityMeasure μ] in
lemma sqrtInterpolation_aemeasurable {X Y : I → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) (hY : ∀ i, Integrable (Y i) μ) (s : ℝ) (i : I) :
    AEMeasurable (fun ω => sqrtInterpolation X Y s ω i) μ :=
  ((hX i).aemeasurable.const_mul _).add ((hY i).aemeasurable.const_mul _)

omit [IsProbabilityMeasure μ] in
lemma softMaxInterpolation_aestronglyMeasurable (β : ℝ) {X Y : I → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) (hY : ∀ i, Integrable (Y i) μ) (s : ℝ) :
    AEStronglyMeasurable (softMaxInterpolation β X Y s) μ := by
  apply AEMeasurable.aestronglyMeasurable
  exact (continuous_softMax β).measurable.comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun i => sqrtInterpolation_aemeasurable hX hY s i))

omit [IsProbabilityMeasure μ] in
lemma softMaxInterpolationDeriv_aestronglyMeasurable (β : ℝ) {X Y : I → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) (hY : ∀ i, Integrable (Y i) μ) (s : ℝ) :
    AEStronglyMeasurable (softMaxInterpolationDeriv β X Y s) μ := by
  classical
  apply AEMeasurable.aestronglyMeasurable
  apply Finset.aemeasurable_sum
  intro i _
  have hw := (continuous_softMaxWeight β i).measurable.comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun i => sqrtInterpolation_aemeasurable hX hY s i))
  exact hw.mul (((hX i).aemeasurable.div_const _).sub ((hY i).aemeasurable.div_const _))

theorem softMaxInterpolation_integrable (β : ℝ) (hβ : 0 < β) {X Y : I → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) (hY : ∀ i, Integrable (Y i) μ) (s : ℝ) :
    Integrable (softMaxInterpolation β X Y s) μ := by
  classical
  have hint (i : I) : Integrable (fun ω => sqrtInterpolation X Y s ω i) μ :=
    ((hX i).const_mul _).add ((hY i).const_mul _)
  have hsum : Integrable (fun ω => (∑ i, |sqrtInterpolation X Y s ω i|) +
      Real.log (Fintype.card I) / β) μ :=
    (integrable_finset_sum _ (fun i _ => (hint i).abs)).add (integrable_const _)
  apply hsum.mono' (softMaxInterpolation_aestronglyMeasurable β hX hY s)
  exact Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using abs_softMax_le β hβ (sqrtInterpolation X Y s ω)

omit [Fintype I] [Nonempty I] [MeasurableSpace Ω] in
private lemma abs_sqrtInterpolation_le (X Y : I → Ω → ℝ) {s : ℝ} (hs : s ∈ Icc 0 1)
    (ω : Ω) (i : I) : |sqrtInterpolation X Y s ω i| ≤ |X i ω| + |Y i ω| := by
  have hs₁ : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs.2
  have hs₂ : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [hs.1])
  calc
    _ ≤ |Real.sqrt s * X i ω| + |Real.sqrt (1 - s) * Y i ω| := abs_add_le _ _
    _ = Real.sqrt s * |X i ω| + Real.sqrt (1 - s) * |Y i ω| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_left (abs_nonneg _) hs₁) (mul_le_of_le_one_left (abs_nonneg _) hs₂)

/-- Continuity includes both endpoints, despite singular square-root derivatives there. -/
theorem continuousOn_integral_softMaxInterpolation (β : ℝ) (hβ : 0 < β)
    {X Y : I → Ω → ℝ} (hX : ∀ i, Integrable (X i) μ) (hY : ∀ i, Integrable (Y i) μ) :
    ContinuousOn (fun s => ∫ ω, softMaxInterpolation β X Y s ω ∂μ) (Icc 0 1) := by
  classical
  let B : Ω → ℝ := fun ω => (∑ i, (|X i ω| + |Y i ω|)) + Real.log (Fintype.card I) / β
  have hB : Integrable B μ :=
    (integrable_finset_sum _ (fun i _ => (hX i).abs.add (hY i).abs)).add (integrable_const _)
  apply continuousOn_of_dominated (bound := B)
  · intro s _
    exact softMaxInterpolation_aestronglyMeasurable β hX hY s
  · intro s hs
    apply Eventually.of_forall
    intro ω
    calc
      ‖softMaxInterpolation β X Y s ω‖ ≤ (∑ i, |sqrtInterpolation X Y s ω i|) +
          Real.log (Fintype.card I) / β := by
        simpa only [Real.norm_eq_abs] using abs_softMax_le β hβ (sqrtInterpolation X Y s ω)
      _ ≤ B ω := add_le_add_right
        (Finset.sum_le_sum (fun i _ => abs_sqrtInterpolation_le X Y hs ω i)) _
  · exact hB
  · exact Eventually.of_forall fun ω => (softMaxInterpolation_continuous β X Y ω).continuousOn

omit [Fintype I] [Nonempty I] [MeasurableSpace Ω] in
private lemma abs_sqrtInterpolationDeriv_le (X Y : I → Ω → ℝ)
    {δ s : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) (hs' : δ ≤ 1 - s) (ω : Ω) (i : I) :
    |sqrtInterpolationDeriv X Y s ω i| ≤ (|X i ω| + |Y i ω|) / (2 * Real.sqrt δ) := by
  have hd : 0 < 2 * Real.sqrt δ := by positivity
  have h₁ : 2 * Real.sqrt δ ≤ 2 * Real.sqrt s :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (by norm_num)
  have h₂ : 2 * Real.sqrt δ ≤ 2 * Real.sqrt (1 - s) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs') (by norm_num)
  calc
    _ ≤ |X i ω / (2 * Real.sqrt s)| + |Y i ω / (2 * Real.sqrt (1 - s))| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (X i ω / (2 * Real.sqrt s)) (-(Y i ω / (2 * Real.sqrt (1 - s))))
    _ = |X i ω| / (2 * Real.sqrt s) + |Y i ω| / (2 * Real.sqrt (1 - s)) := by
      rw [abs_div, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt s),
        abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (1 - s))]
    _ ≤ |X i ω| / (2 * Real.sqrt δ) + |Y i ω| / (2 * Real.sqrt δ) :=
      add_le_add (div_le_div_of_nonneg_left (abs_nonneg _) hd h₁)
        (div_le_div_of_nonneg_left (abs_nonneg _) hd h₂)
    _ = _ := (add_div _ _ _).symm

/-- Differentiation under the expectation on the open interpolation interval. -/
theorem hasDerivAt_integral_softMaxInterpolation (β : ℝ) (hβ : 0 < β)
    {X Y : I → Ω → ℝ} (hX : ∀ i, Integrable (X i) μ) (hY : ∀ i, Integrable (Y i) μ)
    {t : ℝ} (ht : t ∈ Ioo 0 1) :
    Integrable (softMaxInterpolationDeriv β X Y t) μ ∧
    HasDerivAt (fun s => ∫ ω, softMaxInterpolation β X Y s ω ∂μ)
      (∫ ω, softMaxInterpolationDeriv β X Y t ω ∂μ) t := by
  classical
  let δ : ℝ := min t (1 - t) / 2
  have hδ : 0 < δ :=
    div_pos (lt_min ht.1 (sub_pos.mpr ht.2)) (by norm_num)
  have hδt : 2 * δ ≤ t := by dsimp [δ]; linarith [min_le_left t (1 - t)]
  have hδt' : 2 * δ ≤ 1 - t := by dsimp [δ]; linarith [min_le_right t (1 - t)]
  have hball (s : ℝ) (hs : s ∈ ball t δ) : δ ≤ s ∧ δ ≤ 1 - s := by
    rw [mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith
  let B : Ω → ℝ := fun ω => ∑ i, (|X i ω| + |Y i ω|) / (2 * Real.sqrt δ)
  have hB : Integrable B μ :=
    integrable_finset_sum _ (fun i _ => ((hX i).abs.add (hY i).abs).div_const _)
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε := δ) (bound := B) hδ
  · exact Eventually.of_forall (softMaxInterpolation_aestronglyMeasurable β hX hY)
  · exact softMaxInterpolation_integrable β hβ hX hY t
  · exact softMaxInterpolationDeriv_aestronglyMeasurable β hX hY t
  · apply Eventually.of_forall
    intro ω s hs
    calc
      ‖softMaxInterpolationDeriv β X Y s ω‖ ≤ ∑ i, |sqrtInterpolationDeriv X Y s ω i| := by
        simpa only [Real.norm_eq_abs] using abs_sum_softMaxWeight_mul_le β
          (sqrtInterpolation X Y s ω) (sqrtInterpolationDeriv X Y s ω)
      _ ≤ B ω := Finset.sum_le_sum fun i _ =>
        abs_sqrtInterpolationDeriv_le X Y hδ (hball s hs).1 (hball s hs).2 ω i
  · exact hB
  · apply Eventually.of_forall
    intro ω s hs
    have hb := hball s hs
    exact softMaxInterpolation_hasDerivAt β hβ.ne' X Y
      ⟨hδ.trans_le hb.1, by linarith [hb.2]⟩ ω

end GenericChaining
