import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

/-!
# A concrete finite standard Gaussian process

The sample space is the product of `r` real lines. Its coordinate law is the
standard real Gaussian law; vectors and their distances use the Euclidean norm.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The concrete product standard Gaussian law in dimension `r`, including `r = 0`. -/
noncomputable def standardGaussian (r : ℕ) : Measure (Fin r → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance standardGaussian_isProbabilityMeasure (r : ℕ) :
    IsProbabilityMeasure (standardGaussian r) := by
  unfold standardGaussian
  infer_instance

/-- Evaluation of a vector against a standard Gaussian sample. -/
noncomputable def gaussianLinear {r : ℕ} (a : EuclideanSpace ℝ (Fin r))
    (g : Fin r → ℝ) : ℝ := ∑ i, g i * a i

/-- The coordinate definition is the usual Euclidean inner-product process. -/
theorem gaussianLinear_eq_inner {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) (g : Fin r → ℝ) :
    gaussianLinear a g = inner (𝕜 := ℝ) ((WithLp.equiv 2 (Fin r → ℝ)).symm g) a := by
  change (∑ i, g i * a i) = ∑ i, a i * g i
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem gaussianLinear_add {r : ℕ} (a b : EuclideanSpace ℝ (Fin r)) (g : Fin r → ℝ) :
    gaussianLinear (a + b) g = gaussianLinear a g + gaussianLinear b g := by
  simp [gaussianLinear, mul_add, Finset.sum_add_distrib]

theorem gaussianLinear_sub {r : ℕ} (a b : EuclideanSpace ℝ (Fin r)) (g : Fin r → ℝ) :
    gaussianLinear (a - b) g = gaussianLinear a g - gaussianLinear b g := by
  simp [gaussianLinear, mul_sub, Finset.sum_sub_distrib]

theorem gaussianLinear_smul {r : ℕ} (c : ℝ) (a : EuclideanSpace ℝ (Fin r)) (g : Fin r → ℝ) :
    gaussianLinear (c • a) g = c * gaussianLinear a g := by
  simp only [gaussianLinear, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

@[simp] theorem gaussianLinear_zero {r : ℕ} (g : Fin r → ℝ) :
    gaussianLinear (0 : EuclideanSpace ℝ (Fin r)) g = 0 := by
  simp [gaussianLinear]

theorem gaussianLinear_measurable {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    Measurable (gaussianLinear a) := by
  unfold gaussianLinear
  exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).mul_const _)

end GenericChaining
