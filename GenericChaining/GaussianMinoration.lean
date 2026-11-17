import GenericChaining.GaussianWidth
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Lower bounds for standard Gaussian tails

These estimates integrate the Gaussian density over an interval of length one.
They are the scalar input to finite independent Gaussian minoration.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The standard Gaussian density decreases on the nonnegative half-line. -/
theorem standardGaussian_density_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 1 y ≤ gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Integrating the least density on a nonnegative interval gives a lower bound
for its standard Gaussian probability. -/
theorem standardGaussian_interval_lower_bound {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (y - x) * gaussianPDFReal 0 1 y ≤ (gaussianReal 0 1).real (Icc x y) := by
  have hprob : (gaussianReal 0 1).real (Icc x y) =
      ∫ z in Icc x y, gaussianPDFReal 0 1 z := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    exact ENNReal.toReal_ofReal (integral_nonneg fun z => gaussianPDFReal_nonneg 0 1 z)
  rw [hprob]
  have hconst : IntegrableOn (fun _ : ℝ => gaussianPDFReal 0 1 y) (Icc x y) :=
    integrableOn_const.mpr (Or.inr (by simp))
  have hmono := setIntegral_mono_on hconst (integrable_gaussianPDFReal 0 1).integrableOn
    measurableSet_Icc (fun z hz => standardGaussian_density_antitone (hx.trans hz.1) hz.2)
  simpa only [setIntegral_const, Real.volume_real_Icc_of_le hxy, smul_eq_mul] using hmono

/-- A lower bound for a Gaussian upper tail obtained by integrating over
`[x,x+1]`. It remains valid at `x = 0`. -/
theorem standardGaussian_upper_tail_lower_bound {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x + 1) ^ 2 / 2) ≤
      (gaussianReal 0 1).real (Ici x) := by
  calc
    _ = ((x + 1) - x) * gaussianPDFReal 0 1 (x + 1) := by
      simp [gaussianPDFReal]
    _ ≤ (gaussianReal 0 1).real (Icc x (x + 1)) :=
      standardGaussian_interval_lower_bound hx (by linarith)
    _ ≤ (gaussianReal 0 1).real (Ici x) :=
      measureReal_mono (fun _ hz => hz.1)

/-- A simpler lower bound sufficient for logarithmic finite maxima: a fixed
positive constant times `exp (-x²)`. -/
theorem standardGaussian_upper_tail_exp_lower_bound {x : ℝ} (hx : 0 ≤ x) :
    ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) * Real.exp (-x ^ 2) ≤
      (gaussianReal 0 1).real (Ici x) := by
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1 - x ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x + 1) ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (x - 1)]
    _ ≤ _ := standardGaussian_upper_tail_lower_bound hx

/-- The probability that all independent standard Gaussian coordinates lie
below a threshold is the corresponding scalar probability raised to `m`. -/
theorem standardGaussian_all_lt (m : ℕ) (x : ℝ) :
    (standardGaussian m).real {g | ∀ i, g i < x} =
      ((gaussianReal 0 1).real (Iio x)) ^ m := by
  have hset : {g : Fin m → ℝ | ∀ i, g i < x} =
      univ.pi (fun _ : Fin m => Iio x) := by
    ext g
    simp
  rw [hset, standardGaussian, measureReal_def, Measure.pi_pi]
  simp [measureReal_def]

/-- An explicit lower bound for the probability that some independent
standard Gaussian coordinate exceeds a nonnegative threshold. -/
theorem standardGaussian_exists_ge_lower_bound (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    1 - (1 - ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) * Real.exp (-x ^ 2)) ^ m ≤
      (standardGaussian m).real {g | ∃ i, x ≤ g i} := by
  let c := ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) * Real.exp (-x ^ 2)
  have hscalar : (gaussianReal 0 1).real (Iio x) ≤ 1 - c := by
    have hadd := measureReal_add_measureReal_compl (μ := gaussianReal 0 1)
      (s := Iio x) measurableSet_Iio
    have htail := standardGaussian_upper_tail_exp_lower_bound hx
    simp only [compl_Iio, measureReal_univ_eq_one] at hadd
    dsimp [c]
    linarith
  have hpow : ((gaussianReal 0 1).real (Iio x)) ^ m ≤ (1 - c) ^ m :=
    pow_le_pow_left₀ (measureReal_nonneg) hscalar m
  have hcompl : {g : Fin m → ℝ | ∀ i, g i < x}ᶜ = {g | ∃ i, x ≤ g i} := by
    ext g
    simp
  have hm : MeasurableSet {g : Fin m → ℝ | ∀ i, g i < x} := by
    have hs : {g : Fin m → ℝ | ∀ i, g i < x} =
        ⋂ i : Fin m, {g : Fin m → ℝ | g i < x} := by
      ext g
      simp
    rw [hs]
    exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_pi_apply i) measurable_const
  have hadd := measureReal_add_measureReal_compl (μ := standardGaussian m) hm
  rw [hcompl, standardGaussian_all_lt] at hadd
  simp only [measureReal_univ_eq_one] at hadd
  change 1 - (1 - c) ^ m ≤ _
  linarith

/-- An exponential version of the independent-coordinate lower bound. -/
theorem standardGaussian_exists_ge_exp_lower_bound (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    1 - Real.exp (-(m : ℝ) *
      (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) * Real.exp (-x ^ 2))) ≤
      (standardGaussian m).real {g | ∃ i, x ≤ g i} := by
  let p := ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) * Real.exp (-x ^ 2)
  have hp : p ≤ 1 := (standardGaussian_upper_tail_exp_lower_bound hx).trans measureReal_le_one
  have hbase : 1 - p ≤ Real.exp (-p) := by
    linarith [Real.add_one_le_exp (-p)]
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hp) hbase m
  have heq : Real.exp (-p) ^ m = Real.exp (-(m : ℝ) * p) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hpow
  exact (sub_le_sub_left hpow 1).trans (standardGaussian_exists_ge_lower_bound m hx)

/-- The universal probability constant used in the logarithmic lower bound is
strictly positive. -/
theorem standardGaussian_log_threshold_constant_pos :
    0 < 1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2)) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have h : 0 < ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2 := by positivity
  linarith

/-- At the logarithmic threshold, the probability of an exceedance is bounded
below by one fixed positive number, uniformly in the number of coordinates. -/
theorem standardGaussian_log_threshold_probability {m : ℕ} (hm : 1 ≤ m) :
    1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2)) ≤
      (standardGaussian m).real {g | ∃ i, Real.sqrt (Real.log ((m : ℝ) + 1)) ≤ g i} := by
  let c := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  have hlog : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hratio : c / 2 ≤ (m : ℝ) * (c / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc (m : ℝ) c ((m : ℝ) + 1)]
    apply (le_div_iff₀ hpos).mpr
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hmreal)]
  have hprob := standardGaussian_exists_ge_exp_lower_bound m
    (x := Real.sqrt (Real.log ((m : ℝ) + 1))) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hlog, Real.exp_neg (Real.log ((m : ℝ) + 1)), Real.exp_log hpos] at hprob
  change 1 - Real.exp (-(c / 2)) ≤ _
  apply le_trans _ hprob
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  change -(m : ℝ) * (c * ((m : ℝ) + 1)⁻¹) ≤ -(c / 2)
  rw [← div_eq_mul_inv]
  linarith

/-- Taking the maximum with a centered integrable variable raises expectation
at least to the positive part of any fixed level. -/
theorem integral_max_centered_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ : Integrable Z μ)
    (hcenter : ∫ ω, Z ω ∂μ = 0) (a : ℝ) :
    max a 0 ≤ ∫ ω, max a (Z ω) ∂μ := by
  have hmax : Integrable (fun ω => max a (Z ω)) μ := (integrable_const a).sup hZ
  apply max_le
  · have h := integral_mono (integrable_const a) hmax (fun ω => le_max_left a (Z ω))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using h
  · rw [← hcenter]
    exact integral_mono hZ hmax (fun ω => le_max_right a (Z ω))

/-- The independent-variable form of the preceding estimate. It is the step
that replaces an iid maximum by a nonnegative maximum before using its tail. -/
theorem integral_independent_max_ge_positive_part {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} {Y : Ω' → ℝ} (hZ : Integrable Z μ) (hY : Integrable Y ν)
    (hcenter : ∫ ω, Z ω ∂μ = 0) :
    ∫ ω, max (Y ω) 0 ∂ν ≤ ∫ p : Ω × Ω', max (Y p.2) (Z p.1) ∂μ.prod ν := by
  have hZprod : Integrable (fun p : Ω × Ω' => Z p.1) (μ.prod ν) := by
    simpa only [mul_one] using hZ.mul_prod (integrable_const (1 : ℝ) : Integrable _ ν)
  have hYprod : Integrable (fun p : Ω × Ω' => Y p.2) (μ.prod ν) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable _ μ).mul_prod hY
  have hmax : Integrable (fun p : Ω × Ω' => max (Y p.2) (Z p.1)) (μ.prod ν) :=
    hYprod.sup hZprod
  rw [integral_prod_symm _ hmax]
  exact integral_mono hY.pos_part hmax.integral_prod_right
    (fun ω => integral_max_centered_ge hZ hcenter (Y ω))

private theorem gaussianLinear_coordinate {r : ℕ} (i : Fin r) (g : Fin r → ℝ) :
    gaussianLinear ((WithLp.equiv 2 (Fin r → ℝ)).symm (Pi.single i 1)) g = g i := by
  classical
  simp [gaussianLinear, Pi.single_apply, mul_ite]

/-- Coordinate integrability, in the raw product sample space. -/
theorem standardGaussian_coordinate_integrable {r : ℕ} (i : Fin r) :
    Integrable (fun g : Fin r → ℝ => g i) (standardGaussian r) := by
  have heq : gaussianLinear ((WithLp.equiv 2 (Fin r → ℝ)).symm (Pi.single i 1)) =
      (fun g : Fin r → ℝ => g i) := funext (gaussianLinear_coordinate i)
  rw [← heq]
  exact gaussianLinear_integrable _

/-- Coordinates are centered. -/
theorem standardGaussian_coordinate_integral {r : ℕ} (i : Fin r) :
    ∫ g : Fin r → ℝ, g i ∂standardGaussian r = 0 := by
  simpa only [gaussianLinear_coordinate] using
    gaussianLinear_integral ((WithLp.equiv 2 (Fin r → ℝ)).symm (Pi.single i 1))

private theorem standardGaussian_scalar_integrable :
    Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
  rw [← standardGaussian_coordinate_map (0 : Fin 1)]
  exact (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
    (measurable_pi_apply (0 : Fin 1)).aemeasurable).mpr
      (standardGaussian_coordinate_integrable (0 : Fin 1))

private theorem standardGaussian_scalar_integral :
    ∫ z : ℝ, z ∂gaussianReal 0 1 = 0 := by
  rw [← standardGaussian_coordinate_map (0 : Fin 1)]
  rw [integral_map (φ := fun g : Fin 1 → ℝ => g 0) (f := fun z : ℝ => z)
    (measurable_pi_apply (0 : Fin 1)).aemeasurable
      stronglyMeasurable_id.aestronglyMeasurable]
  exact standardGaussian_coordinate_integral (0 : Fin 1)

private theorem ciSup_insert_zero {m : ℕ} [NeZero m] (z : ℝ) (g : Fin m → ℝ) :
    (⨆ i : Fin (m + 1), (0 : Fin (m + 1)).insertNth z g i) = max (⨆ i, g i) z := by
  apply le_antisymm
  · apply ciSup_le
    exact (Fin.forall_iff_succAbove (0 : Fin (m + 1))).mpr
      ⟨by simpa only [Fin.insertNth_apply_same] using le_max_right (⨆ i, g i) z,
       fun j => by
        simp only [Fin.insertNth_apply_succAbove]
        exact (le_ciSup (Finite.bddAbove_range g) j).trans (le_max_left _ _)⟩
  · apply max_le
    · apply ciSup_le
      intro j
      have h := le_ciSup
        (Finite.bddAbove_range ((0 : Fin (m + 1)).insertNth z g))
        ((0 : Fin (m + 1)).succAbove j)
      simpa only [Fin.insertNth_apply_succAbove] using h
    · have h := le_ciSup
        (Finite.bddAbove_range ((0 : Fin (m + 1)).insertNth z g)) (0 : Fin (m + 1))
      simpa only [Fin.insertNth_apply_same] using h

/-- One extra independent centered coordinate pays for replacing a maximum by
its positive part. -/
theorem standardGaussian_iid_max_ge_positive_part (m : ℕ) [NeZero m] :
    ∫ g : Fin m → ℝ, max (⨆ i, g i) 0 ∂standardGaussian m ≤
      ∫ g : Fin (m + 1) → ℝ, (⨆ i, g i) ∂standardGaussian (m + 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hpres : MeasurePreserving e (standardGaussian (m + 1))
      ((gaussianReal 0 1).prod (standardGaussian m)) :=
    measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) 0
  have heq (p : ℝ × (Fin m → ℝ)) : (⨆ i, e.symm p i) = max (⨆ i, p.2 i) p.1 := by
    change (⨆ i, (0 : Fin (m + 1)).insertNth p.1 p.2 i) = _
    exact ciSup_insert_zero p.1 p.2
  have hsym := MeasurePreserving.symm e hpres
  rw [← hsym.integral_comp' (fun g : Fin (m + 1) → ℝ => ⨆ i, g i)]
  simp_rw [heq]
  exact integral_independent_max_ge_positive_part standardGaussian_scalar_integrable
    (integrable_iSup_finite standardGaussian_coordinate_integrable) standardGaussian_scalar_integral

/-- The expected one-sided maximum of `m+1` independent standard Gaussians
grows at least as a fixed positive multiple of `sqrt(log(m+1))`. -/
theorem standardGaussian_iid_max_lower_bound_succ {m : ℕ} (hm : 1 ≤ m) :
    (1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2))) *
        Real.sqrt (Real.log ((m : ℝ) + 1)) ≤
      ∫ g : Fin (m + 1) → ℝ, (⨆ i, g i) ∂standardGaussian (m + 1) := by
  letI : NeZero m := ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)⟩
  let x := Real.sqrt (Real.log ((m : ℝ) + 1))
  let S : Set (Fin m → ℝ) := {g | ∃ i, x ≤ g i}
  let H : (Fin m → ℝ) → ℝ := fun g => max (⨆ i, g i) 0
  have hH : Integrable H (standardGaussian m) :=
    (integrable_iSup_finite standardGaussian_coordinate_integrable).pos_part
  have hS : MeasurableSet S := by
    have heq : S = ⋃ i : Fin m, {g : Fin m → ℝ | x ≤ g i} := by
      ext g
      simp [S]
    rw [heq]
    exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
  calc
    _ = x * (1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2))) :=
      mul_comm _ _
    _ ≤ x * (standardGaussian m).real S :=
      mul_le_mul_of_nonneg_left (standardGaussian_log_threshold_probability hm) (Real.sqrt_nonneg _)
    _ ≤ ∫ g in S, H g ∂standardGaussian m := by
      apply setIntegral_ge_of_const_le hS (measure_ne_top _ _) _ hH.integrableOn
      rintro g ⟨i, hi⟩
      exact hi.trans ((le_ciSup (Finite.bddAbove_range g) i).trans (le_max_left _ _))
    _ ≤ ∫ g, H g ∂standardGaussian m :=
      setIntegral_le_integral hH (Filter.Eventually.of_forall (fun g => le_max_right _ _))
    _ ≤ _ := standardGaussian_iid_max_ge_positive_part m

/-- A universal lower bound for iid standard Gaussian maxima, with the constant
quantified before the number of coordinates. -/
theorem standardGaussian_iid_max_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m →
      c * Real.sqrt (Real.log (m : ℝ)) ≤
        ∫ g : Fin m → ℝ, (⨆ i, g i) ∂standardGaussian m := by
  refine ⟨1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2)),
    standardGaussian_log_threshold_constant_pos, ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := Nat.le_trans (by decide) hm
  have hn : 1 ≤ m - 1 := Nat.le_sub_one_of_lt hm
  have heq : m - 1 + 1 = m := Nat.sub_add_cancel hm1
  have h := standardGaussian_iid_max_lower_bound_succ hn
  have hreal : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast heq
  rw [hreal, heq] at h
  exact h

/-- The explicit iid lower bound also includes one coordinate, where both
sides vanish. -/
theorem standardGaussian_iid_max_explicit_lower_bound {m : ℕ} [NeZero m] :
    (1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2))) *
        Real.sqrt (Real.log (m : ℝ)) ≤
      ∫ g : Fin m → ℝ, (⨆ i, g i) ∂standardGaussian m := by
  by_cases hm : m = 1
  · subst m
    simpa only [Nat.cast_one, Real.log_one, Real.sqrt_zero, mul_zero, ciSup_unique] using
      (standardGaussian_coordinate_integral (0 : Fin 1)).ge
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    have hm2 : 2 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_ne hm1 (Ne.symm hm))
    have hn : 1 ≤ m - 1 := Nat.le_sub_one_of_lt hm2
    have heq : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    have h := standardGaussian_iid_max_lower_bound_succ hn
    have hreal : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast heq
    rw [hreal, heq] at h
    exact h

end GenericChaining
