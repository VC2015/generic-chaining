import GenericChaining.MixedTail
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Integrating the simultaneous edge bound

The geometric tail in `HasMixedTail.dyadic_edge_bound` has a fixed integrable
envelope once its parameter is at least one. The estimate here is independent
of the number of edges and levels.
-/

namespace GenericChaining

open MeasureTheory Set

/-- A maximum over a nonempty finite family of integrable real variables is integrable. -/
theorem integrable_iSup_finite {T Ω : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace Ω] {μ : Measure Ω} {f : T → Ω → ℝ}
    (hf : ∀ t, Integrable (f t) μ) : Integrable (fun ω => ⨆ t, f t ω) μ := by
  classical
  have h : Integrable (Finset.univ.sup' Finset.univ_nonempty f) μ := by
    exact Finset.sup'_induction (p := fun g : Ω → ℝ => Integrable g μ)
      Finset.univ_nonempty f
      (fun a ha b hb => ha.sup hb) (fun t _ => hf t)
  have heq : Finset.univ.sup' Finset.univ_nonempty f = (fun ω => ⨆ t, f t ω) := by
    funext ω
    rw [Finset.sup'_apply, Finset.sup'_univ_eq_ciSup]
  rwa [heq] at h

/-- The integral of an exponential envelope for the geometric tail above level one. -/
noncomputable def dyadicTailConstant : ℝ :=
  2 * Real.exp (-1) / (1 - Real.exp (-1))

theorem dyadicTailConstant_nonneg : 0 ≤ dyadicTailConstant := by
  unfold dyadicTailConstant
  have h : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact div_nonneg (by positivity) (sub_nonneg.mpr h.le)

theorem dyadicTailConstant_le_two : dyadicTailConstant ≤ 2 := by
  have hq : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hpos : 0 < Real.exp (-1) := Real.exp_pos _
  have he : 2 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hmul : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hhalf : 2 * Real.exp (-1) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right he hpos.le]
  unfold dyadicTailConstant
  apply (div_le_iff₀ (sub_pos.mpr hq)).mpr
  linarith

/-- A bound for the geometric tail that can be integrated on the positive half-line. -/
theorem dyadic_tail_envelope {t : ℝ} (ht : 0 ≤ t) :
    2 * Real.exp (-(t + 1)) / (1 - Real.exp (-(t + 1))) ≤
      dyadicTailConstant * Real.exp (-t) := by
  have hq : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hexp : Real.exp (-(t + 1)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hden : 0 < 1 - Real.exp (-1) := sub_pos.mpr hq
  calc
    _ ≤ 2 * Real.exp (-(t + 1)) / (1 - Real.exp (-1)) :=
      div_le_div_of_nonneg_left (by positivity) hden (by linarith)
    _ = dyadicTailConstant * Real.exp (-t) := by
      rw [show -(t + 1) = -1 + -t by ring, Real.exp_add]
      unfold dyadicTailConstant
      ring

/-- Integrate the geometric tail bound. The variable need only be integrable;
its negative values can only improve this upper bound. -/
theorem integral_le_of_dyadic_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) (A : ℝ)
    (htail : ∀ v : ℝ, 1 ≤ v →
      μ.real {ω | A + v < Z ω} ≤ 2 * Real.exp (-v) / (1 - Real.exp (-v))) :
    ∫ ω, Z ω ∂μ ≤ A + 1 + dyadicTailConstant := by
  let H : Ω → ℝ := fun ω => max (Z ω - (A + 1)) 0
  have hH : Integrable H μ :=
    (hZ.sub (integrable_const (A + 1))).pos_part
  have hHnn : ∀ ω, 0 ≤ H ω := fun ω => le_max_right _ _
  have hbound (t : ℝ) (ht : 0 < t) :
      μ.real {ω | t < H ω} ≤ dyadicTailConstant * Real.exp (-t) := by
    have heq : {ω | t < H ω} = {ω | A + (t + 1) < Z ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, H, lt_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h
        left
        linarith
    rw [heq]
    exact (htail (t + 1) (by linarith)).trans (dyadic_tail_envelope ht.le)
  have henv : IntegrableOn (fun t : ℝ => dyadicTailConstant * Real.exp (-t)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul dyadicTailConstant
  have hmono : Antitone (fun t : ℝ => μ {ω | t < H ω}) := by
    intro a b hab
    exact measure_mono (fun ω hω => hab.trans_lt hω)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => μ.real {ω | t < H ω})
      (volume.restrict (Ioi 0)) := by
    exact hmono.measurable.ennreal_toReal.aestronglyMeasurable
  have hint : IntegrableOn (fun t : ℝ => μ.real {ω | t < H ω}) (Ioi 0) := by
    apply henv.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound t ht
  have hHint : ∫ ω, H ω ∂μ ≤ dyadicTailConstant := by
    rw [hH.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hHnn)]
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), dyadicTailConstant * Real.exp (-t) := by
        apply integral_mono_ae hint henv
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hbound t ht
      _ = dyadicTailConstant := by
        rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  calc
    ∫ ω, Z ω ∂μ ≤ ∫ ω, (A + 1) + H ω ∂μ := by
      apply integral_mono hZ ((integrable_const (A + 1)).add hH)
      intro ω
      have := le_max_left (Z ω - (A + 1)) (0 : ℝ)
      dsimp [H]
      linarith
    _ = A + 1 + ∫ ω, H ω ∂μ := by
      rw [integral_add (integrable_const (A + 1)) hH, integral_const]
      simp
    _ ≤ _ := add_le_add_left hHint _

/-- A scaled form, useful when the deterministic chaining length is `B`. -/
theorem integral_le_of_scaled_dyadic_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Integrable Y μ) (A : ℝ) {B : ℝ} (hB : 0 < B)
    (htail : ∀ v : ℝ, 1 ≤ v →
      μ.real {ω | (A + v) * B < Y ω} ≤ 2 * Real.exp (-v) / (1 - Real.exp (-v))) :
    ∫ ω, Y ω ∂μ ≤ (A + 1 + dyadicTailConstant) * B := by
  have h := integral_le_of_dyadic_tail (hY.div_const B) A (fun v hv => by
    simpa only [lt_div_iff₀ hB] using htail v hv)
  rw [integral_div] at h
  exact (div_le_iff₀ hB).mp h

/-- A numerical version of the expectation bound. -/
theorem integral_le_of_scaled_dyadic_tail_coarse {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Integrable Y μ) (A : ℝ) {B : ℝ} (hB : 0 < B)
    (htail : ∀ v : ℝ, 1 ≤ v →
      μ.real {ω | (A + v) * B < Y ω} ≤ 2 * Real.exp (-v) / (1 - Real.exp (-v))) :
    ∫ ω, Y ω ∂μ ≤ (A + 3) * B := by
  apply (integral_le_of_scaled_dyadic_tail hY A hB htail).trans
  apply mul_le_mul_of_nonneg_right _ hB.le
  linarith [dyadicTailConstant_le_two]

end GenericChaining
