import GenericChaining.GaussianWidth
import GenericChaining.GaussianMetric
import GenericChaining.GaussianFunctional
import GenericChaining.GaussianGrowthFunctional
import GenericChaining.GrowthChaining

/-!
# Finite Gaussian majorizing measures

The expected maximum is one-sided and uses the concrete product Gaussian law.
The constants do not depend on dimension, cardinality, or vectors. Local
Gaussian growth gives the lower bound; Dirksen gives the converse.
-/
namespace GenericChaining
open MeasureTheory
open scoped NNReal ENNReal

/-- A fixed positive constant for the Gaussian majorizing-measure lower bound. -/
noncomputable def gaussianMajorizingConstant : ℝ :=
  growthChainingConstant / gaussianGrowthConstant

theorem gaussianMajorizingConstant_pos : 0 < gaussianMajorizingConstant :=
  div_pos growthChainingConstant_pos gaussianGrowthConstant_pos

/-- The direction needed for Lemma C.2: the canonical admissible-net cost is
bounded by the expected one-sided maximum of a concrete finite Gaussian family.
Repeated vectors, zero canonical distances, and arbitrary translations are allowed. -/
theorem gamma2_le_gaussianWidth {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) :
    (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal ≤
      gaussianMajorizingConstant * gaussianWidth a := by
  classical
  have hfinite := gamma2_canonicalDist_ne_top a
  have h := gamma2_le_of_localGrowth_exact (canonicalDist a)
    (canonicalDist_self a) (canonicalDist_symm a) (canonicalDist_triangle a)
    (finiteGaussianWidth a) (fun _ _ hAB => finiteGaussianWidth_mono a hAB)
    (finiteGaussianWidth_nonneg a) gaussianGrowthConstant_pos
    (finiteGaussianWidth_hasLocalGrowth a)
  simpa only [finiteGaussianWidth_univ, gaussianMajorizingConstant] using h

/-- The lower constant is chosen before dimension, index set, and vectors. -/
theorem exists_gamma2_le_gaussianWidth :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (T : Type*) [Fintype T] [Nonempty T]
      (a : T → EuclideanSpace ℝ (Fin r)),
      (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal ≤ C * gaussianWidth a := by
  exact ⟨gaussianMajorizingConstant, gaussianMajorizingConstant_pos,
    fun _ _ _ _ a => gamma2_le_gaussianWidth a⟩

/-- The converse direction of finite Gaussian majorizing measures, obtained
from Dirksen with exponential metric zero and its base-point term absorbed. -/
theorem gaussianWidth_le_gamma2 {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) :
    gaussianWidth a ≤ gaussianExpectationConstant *
      (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal := by
  classical
  let t₀ : T := Classical.choice ‹Nonempty T›
  have hc : (Real.sqrt 2).toNNReal ≤ (2 : ℝ≥0) := by
    apply Real.toNNReal_le_iff_le_coe.mpr
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have habs (s t : T) :
      (∫ g, |gaussianLinear (a s) g - gaussianLinear (a t) g| ∂standardGaussian r) ≤
        (canonicalDist a s t : ℝ) := by
    simpa only [gaussianLinear_sub, canonicalDist, coe_nnnorm] using
      gaussianLinear_integral_abs_le (a s - a t)
  exact gaussian_expectation_of_mixedTail (fun t => gaussianLinear (a t)) (canonicalDist a)
    (Real.sqrt 2).toNNReal hc (canonicalDist_self a) (canonicalDist_symm a)
    (canonicalDist_triangle a) (gaussianLinear_hasMixedTail a)
    (fun t => gaussianLinear_integrable (a t)) habs t₀ (gaussianLinear_integral (a t₀))

/-- The upper constant is chosen before dimension, index set, and vectors. -/
theorem exists_gaussianWidth_le_gamma2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (T : Type*) [Fintype T] [Nonempty T]
      (a : T → EuclideanSpace ℝ (Fin r)), gaussianWidth a ≤
        C * (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal := by
  exact ⟨gaussianExpectationConstant, gaussianExpectationConstant_pos,
    fun _ _ _ _ a => gaussianWidth_le_gamma2 a⟩

/-- Both dimension-free directions with their constants quantified first. -/
theorem finite_gaussian_majorizing_measure :
    ∃ Cₗ Cᵤ : ℝ, 0 < Cₗ ∧ 0 < Cᵤ ∧
      ∀ (r : ℕ) (T : Type*) [Fintype T] [Nonempty T]
        (a : T → EuclideanSpace ℝ (Fin r)),
        (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal ≤ Cₗ * gaussianWidth a ∧
        gaussianWidth a ≤ Cᵤ * (gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞))).toReal := by
  exact ⟨gaussianMajorizingConstant, gaussianExpectationConstant,
    gaussianMajorizingConstant_pos, gaussianExpectationConstant_pos,
    fun _ _ _ _ a => ⟨gamma2_le_gaussianWidth a, gaussianWidth_le_gamma2 a⟩⟩

/-- The singleton canonical chaining cost is zero, as is its Gaussian width. -/
@[simp] theorem gamma2_canonicalDist_singleton {T : Type*} [Fintype T] [Unique T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) :
    gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞)) = 0 := by
  have hzero : (fun s t => (canonicalDist a s t : ℝ≥0∞)) = fun (_ _ : T) => 0 := by
    funext s t
    have hst : s = t := Subsingleton.elim _ _
    simp only [hst, canonicalDist_self, ENNReal.coe_zero]
  rw [hzero]
  exact gamma2_zero

end GenericChaining
