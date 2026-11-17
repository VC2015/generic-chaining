import GenericChaining.GaussianCore
import GenericChaining.MixedTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Gaussian projections and their mixed-tail bound

The concrete product Gaussian law has independent standard normal coordinates.
Multiplying their moment generating functions gives the exact Gaussian formula
for every Euclidean projection, including vectors of norm zero.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

/-- Each coordinate of the product standard Gaussian has the standard normal law. -/
theorem standardGaussian_coordinate_map {r : ℕ} (i : Fin r) :
    (standardGaussian r).map (fun g => g i) = gaussianReal 0 1 := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  change (Measure.pi (fun _ : Fin r => gaussianReal 0 1)) ((Function.eval i) ⁻¹' s) = _
  rw [← Set.univ_pi_update_univ, Measure.pi_pi]
  have heq : (fun j : Fin r => gaussianReal 0 1 ((Function.update (fun _ => Set.univ) i s) j)) =
      Function.update (fun _ => (1 : ℝ≥0∞)) i (gaussianReal 0 1 s) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h, h]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

/-- The coordinates of the product Gaussian law are independent. -/
theorem standardGaussian_coordinates_indep (r : ℕ) :
    iIndepFun (fun i : Fin r => fun g : Fin r → ℝ => g i) (standardGaussian r) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).2
  simp only [standardGaussian_coordinate_map]
  change (standardGaussian r).map id = standardGaussian r
  exact Measure.map_id

/-- The exact moment generating function of a Gaussian projection. -/
theorem gaussianLinear_mgf {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) (t : ℝ) :
    mgf (gaussianLinear a) (standardGaussian r) t = Real.exp (‖a‖ ^ 2 * t ^ 2 / 2) := by
  let Z : Fin r → (Fin r → ℝ) → ℝ := fun i g => g i * a i
  have hZ : iIndepFun Z (standardGaussian r) :=
    (standardGaussian_coordinates_indep r).comp (fun i x => x * a i)
      (fun i => measurable_mul_const (a i))
  have hm (i : Fin r) : Measurable (Z i) := (measurable_pi_apply i).mul_const _
  have hg (i : Fin r) : mgf (Z i) (standardGaussian r) t =
      Real.exp ((a i) ^ 2 * t ^ 2 / 2) := by
    calc
      _ = mgf (fun g : Fin r → ℝ => g i) (standardGaussian r) (a i * t) := by
        unfold mgf
        apply integral_congr_ae
        filter_upwards [] with g
        change Real.exp (t * (g i * a i)) = Real.exp ((a i * t) * g i)
        congr 1
        ring
      _ = _ := by
        rw [mgf_gaussianReal (p := standardGaussian r)
          (X := fun g : Fin r → ℝ => g i) (standardGaussian_coordinate_map i)]
        congr 1
        simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
        ring
  have hn : ∑ i, (a i) ^ 2 = ‖a‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin r => ℝ) a).symm
  change mgf (fun g => ∑ i, Z i g) (standardGaussian r) t = _
  have hsum := hZ.mgf_sum hm Finset.univ (t := t)
  have hfun : (fun g => ∑ i, Z i g) = ∑ i, Z i := by
    funext g
    simp only [Finset.sum_apply]
  rw [hfun, hsum]
  simp_rw [hg]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, ← Finset.sum_mul, hn]

/-- Exponentials of every linear Gaussian projection are integrable. -/
theorem gaussianLinear_integrable_exp_mul {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) (t : ℝ) :
    Integrable (fun g => Real.exp (t * gaussianLinear a g)) (standardGaussian r) :=
  mgf_pos_iff.mp (by rw [gaussianLinear_mgf]; positivity)

/-- Chernoff's upper-tail bound for the exact centered Gaussian MGF. -/
theorem gaussian_mgf_upper_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Ω → ℝ} (d : ℝ≥0) (hd : 0 < d)
    (hmgf : ∀ t : ℝ, mgf Z μ t = Real.exp ((d : ℝ) ^ 2 * t ^ 2 / 2))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ Z ω} ≤ Real.exp (-ε ^ 2 / (2 * (d : ℝ) ^ 2)) := by
  have hd' : (d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hd)
  have hint : Integrable (fun ω => Real.exp ((ε / (d : ℝ) ^ 2) * Z ω)) μ :=
    mgf_pos_iff.mp (by rw [hmgf]; positivity)
  calc
    _ ≤ Real.exp (-(ε / (d : ℝ) ^ 2) * ε) * mgf Z μ (ε / (d : ℝ) ^ 2) :=
      measure_ge_le_exp_mul_mgf ε (by positivity) hint
    _ = _ := by
      rw [hmgf, ← Real.exp_add]
      congr 1
      field_simp [hd']
      ring

/-- Two-sided Gaussian Chernoff bound at the natural square-root threshold. -/
theorem gaussian_mgf_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Ω → ℝ} (d : ℝ≥0) (hd : 0 < d)
    (hmgf : ∀ t : ℝ, mgf Z μ t = Real.exp ((d : ℝ) ^ 2 * t ^ 2 / 2))
    {u : ℝ} (hu : 0 < u) :
    μ.real {ω | Real.sqrt u * (Real.sqrt 2 * (d : ℝ)) < |Z ω|} ≤
      2 * Real.exp (-u) := by
  let q := Real.sqrt u * (Real.sqrt 2 * (d : ℝ))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : -q ^ 2 / (2 * (d : ℝ) ^ 2) = -u := by
    dsimp [q]
    rw [mul_pow, mul_pow, Real.sq_sqrt hu.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hd' : (d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hd)
    field_simp [hd']
  have hp := gaussian_mgf_upper_tail d hd hmgf hq
  have hneg (v : ℝ) : mgf (fun ω => -Z ω) μ v =
      Real.exp ((d : ℝ) ^ 2 * v ^ 2 / 2) := by
    change mgf (-Z) μ v = _
    rw [mgf_neg, hmgf]
    simp only [neg_sq]
  have hn := gaussian_mgf_upper_tail d hd hneg hq
  rw [he] at hp hn
  have hsub : {ω | q < |Z ω|} ⊆ {ω | q ≤ Z ω} ∪ {ω | q ≤ -Z ω} := by
    intro ω hω
    change q < |Z ω| at hω
    by_cases hz : 0 ≤ Z ω
    · exact Or.inl (by simpa only [abs_of_nonneg hz] using hω.le)
    · exact Or.inr (by simpa only [abs_of_neg (lt_of_not_ge hz)] using hω.le)
  calc
    _ ≤ μ.real ({ω | q ≤ Z ω} ∪ {ω | q ≤ -Z ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | q ≤ Z ω} + μ.real {ω | q ≤ -Z ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-u) := by linarith

/-- Gaussian projections satisfy the mixed-tail condition in their canonical
Euclidean pseudometric. The exponential component is zero. -/
theorem gaussianLinear_hasMixedTail {T : Type*} {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) :
    HasMixedTail (standardGaussian r) (fun t => gaussianLinear (a t))
      (fun _ _ => 0) (fun s t => (Real.sqrt 2).toNNReal * ‖a s - a t‖₊) := by
  intro s t u hu
  by_cases hz : a s - a t = 0
  · have heq : a s = a t := sub_eq_zero.mp hz
    simp only [badIncrement, heq, sub_self, nnnorm_zero, mul_zero, NNReal.coe_zero,
      add_zero, abs_zero, lt_self_iff_false, Set.setOf_false, measureReal_empty]
    positivity
  · have hd : (0 : ℝ≥0) < ‖a s - a t‖₊ := nnnorm_pos.mpr hz
    have hm (v : ℝ) : mgf (gaussianLinear (a s - a t)) (standardGaussian r) v =
        Real.exp ((‖a s - a t‖₊ : ℝ) ^ 2 * v ^ 2 / 2) := gaussianLinear_mgf _ v
    have htail := gaussian_mgf_abs_tail ‖a s - a t‖₊ hd hm hu
    simpa only [badIncrement, NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _),
      NNReal.coe_zero, mul_zero, add_zero, gaussianLinear_sub, coe_nnnorm] using htail

end GenericChaining
