import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Gaussian integration by parts

The scalar integration-by-parts identity is used coordinatewise in the
smooth-maximum interpolation argument. The complete finite comparison
theorem is proved in `GaussianComparison`.
-/
namespace GenericChaining
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The derivative of the standard normal density. -/
theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  have hpdf : gaussianPDFReal 0 1 =
      (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y^2/2)) := by
    funext y
    simp [gaussianPDFReal]
  rw [hpdf]
  convert h using 1
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- Scalar Gaussian integration by parts, stated with density-weighted
integrability assumptions so that no boundary condition is hidden. -/
theorem standardGaussian_stein_density {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable (fun x => f x * gaussianPDFReal 0 1 x))
    (hf' : Integrable (fun x => f' x * gaussianPDFReal 0 1 x))
    (hxf : Integrable (fun x => x * f x * gaussianPDFReal 0 1 x)) :
    (∫ x, f' x * gaussianPDFReal 0 1 x) =
      ∫ x, x * f x * gaussianPDFReal 0 1 x := by
  have hneg : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert hxf.neg using 1
    funext x
    change f x * (-x * gaussianPDFReal 0 1 x) = -(x * f x * gaussianPDFReal 0 1 x)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable hderiv
    hasDerivAt_standardGaussianPDF hneg hf' hf
  have heq : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      (fun x => -(x * f x * gaussianPDFReal 0 1 x)) := by funext x; ring
  rw [heq, integral_neg] at h
  linarith

/-- Rewrite Gaussian integrability as ordinary integrability against the
standard density. -/
theorem integrable_standardGaussian_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall (fun x => gaussianPDF_lt_top))]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    smul_eq_mul, mul_comm]

/-- Stein's identity for the concrete standard normal law. -/
theorem standardGaussian_stein {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) = ∫ x, x * f x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  simpa only [mul_comm (gaussianPDFReal 0 1 _) _] using
    standardGaussian_stein_density hderiv
      (integrable_standardGaussian_iff.mp hf)
      (integrable_standardGaussian_iff.mp hf')
      (integrable_standardGaussian_iff.mp hxf)

end GenericChaining
