import GenericChaining.GaussianProductStein
import GenericChaining.GaussianSmoothMax
import GenericChaining.GaussianWidth

/-!
# Gaussian integration by parts for soft-maximum weights

The weights and their coordinate derivatives are bounded. Consequently the
coordinate Stein identity applies to them, and summing gives the covariance
contraction used in finite Gaussian comparison.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [Nonempty I] {r : ℕ}

theorem gaussianCoordinate_integrable (k : Fin r) :
    Integrable (fun g : Fin r → ℝ => g k) (standardGaussian r) := by
  have h := gaussianLinear_integrable (EuclideanSpace.single k (1 : ℝ))
  change Integrable (fun g : Fin r → ℝ => ∑ j, g j * (EuclideanSpace.single k (1 : ℝ)) j)
    (standardGaussian r) at h
  simpa [EuclideanSpace.single_apply] using h

theorem gaussianLinear_continuous (a : EuclideanSpace ℝ (Fin r)) :
    Continuous (gaussianLinear a) := by
  unfold gaussianLinear
  exact continuous_finset_sum _ (fun k _ => (continuous_apply k).mul continuous_const)

theorem hasDerivAt_gaussianLinear_update (a : EuclideanSpace ℝ (Fin r))
    (g : Fin r → ℝ) (k : Fin r) (x : ℝ) :
    HasDerivAt (fun z => gaussianLinear a (Function.update g k z)) (a k) x := by
  classical
  have hd (j : Fin r) : HasDerivAt (fun z => Function.update g k z j * a j)
      (if j = k then a j else 0) x := by
    by_cases hj : j = k
    · subst j
      simpa [Function.update_self] using (hasDerivAt_id x).mul_const (a k)
    · simpa only [Function.update_of_ne hj, if_neg hj] using
        hasDerivAt_const x (g j * a j)
  convert HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hd j) using 1
  simp

noncomputable def gaussianSoftMaxWeight (β : ℝ) (c : I → EuclideanSpace ℝ (Fin r))
    (i : I) (g : Fin r → ℝ) : ℝ :=
  softMaxWeight β (fun j => gaussianLinear (c j) g) i

theorem gaussianSoftMaxWeight_continuous (β : ℝ) (c : I → EuclideanSpace ℝ (Fin r))
    (i : I) : Continuous (gaussianSoftMaxWeight β c i) := by
  have hs : Continuous (fun g => softMaxSum β (fun j => gaussianLinear (c j) g)) := by
    unfold softMaxSum
    exact continuous_finset_sum _ (fun j _ => Real.continuous_exp.comp
      (continuous_const.mul (gaussianLinear_continuous (c j))))
  exact (Real.continuous_exp.comp
    (continuous_const.mul (gaussianLinear_continuous (c i)))).div hs
    (fun g => (softMaxSum_pos β (fun j => gaussianLinear (c j) g)).ne')

theorem gaussianSoftMaxWeight_integrable (β : ℝ) (c : I → EuclideanSpace ℝ (Fin r))
    (i : I) : Integrable (gaussianSoftMaxWeight β c i) (standardGaussian r) := by
  apply (integrable_const (1 : ℝ)).mono'
    (gaussianSoftMaxWeight_continuous β c i).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun g => by
    dsimp only [gaussianSoftMaxWeight]
    rw [Real.norm_eq_abs, abs_of_nonneg (softMaxWeight_nonneg _ _ _)]
    exact softMaxWeight_le_one _ _ _

theorem gaussianSoftMaxWeight_mul_integrable (β : ℝ) (c : I → EuclideanSpace ℝ (Fin r))
    (i : I) {f : (Fin r → ℝ) → ℝ} (hf : Integrable f (standardGaussian r)) :
    Integrable (fun g => gaussianSoftMaxWeight β c i g * f g) (standardGaussian r) := by
  apply hf.bdd_mul (gaussianSoftMaxWeight_continuous β c i).aestronglyMeasurable
  refine ⟨1, fun g => ?_⟩
  dsimp only [gaussianSoftMaxWeight]
  rw [Real.norm_eq_abs, abs_of_nonneg (softMaxWeight_nonneg _ _ _)]
  exact softMaxWeight_le_one _ _ _

theorem hasDerivAt_gaussianSoftMaxWeight_update (β : ℝ)
    (c : I → EuclideanSpace ℝ (Fin r)) (i : I) (g : Fin r → ℝ) (k : Fin r) (x : ℝ) :
    HasDerivAt (fun z => gaussianSoftMaxWeight β c i (Function.update g k z))
      (β * gaussianSoftMaxWeight β c i (Function.update g k x) *
        ((c i) k - ∑ j, gaussianSoftMaxWeight β c j (Function.update g k x) * (c j) k)) x :=
  hasDerivAt_softMaxWeight_comp β
    (fun j z => gaussianLinear (c j) (Function.update g k z)) (fun j => (c j) k) x
    (fun j => hasDerivAt_gaussianLinear_update (c j) g k x) i

theorem gaussianSoftMaxWeight_coordinate_derivative_integrable (β : ℝ)
    (c : I → EuclideanSpace ℝ (Fin r)) (i : I) (k : Fin r) :
    Integrable (fun g => β * gaussianSoftMaxWeight β c i g *
      ((c i) k - ∑ j, gaussianSoftMaxWeight β c j g * (c j) k)) (standardGaussian r) := by
  have hs : Integrable (fun g => ∑ j, gaussianSoftMaxWeight β c j g * (c j) k)
      (standardGaussian r) :=
    integrable_finset_sum _ (fun j _ => (gaussianSoftMaxWeight_integrable β c j).mul_const _)
  have hi := gaussianSoftMaxWeight_mul_integrable β c i ((integrable_const ((c i) k)).sub hs)
  simpa only [mul_assoc] using hi.const_mul β

/-- Coordinatewise integration by parts for a soft-maximum probability. -/
theorem gaussianSoftMaxWeight_coordinate_stein (β : ℝ)
    (c : I → EuclideanSpace ℝ (Fin r)) (i : I) (k : Fin r) :
    (∫ g, gaussianSoftMaxWeight β c i g * g k ∂standardGaussian r) =
      ∫ g, β * gaussianSoftMaxWeight β c i g *
        ((c i) k - ∑ j, gaussianSoftMaxWeight β c j g * (c j) k) ∂standardGaussian r := by
  have hxf : Integrable (fun g => g k * gaussianSoftMaxWeight β c i g) (standardGaussian r) := by
    simpa only [mul_comm] using
      gaussianSoftMaxWeight_mul_integrable β c i (gaussianCoordinate_integrable k)
  have h := standardGaussian_stein_coordinate k
    (hasDerivAt_gaussianSoftMaxWeight_update β c i · k ·)
    (gaussianSoftMaxWeight_integrable β c i)
    (gaussianSoftMaxWeight_coordinate_derivative_integrable β c i k) hxf
  simpa only [mul_comm (gaussianSoftMaxWeight β c i _) _] using h.symm

omit [Nonempty I] in
private theorem softMax_stein_algebra (β p : ℝ) (q : I → ℝ)
    (c v : Fin r → ℝ) (a : I → Fin r → ℝ) :
    (∑ k, v k * (β * p * (c k - ∑ j, q j * a j k))) =
      β * (p * ∑ k, v k * c k - ∑ j, p * q j * ∑ k, v k * a j k) := by
  calc
    _ = β * p * (∑ k, v k * c k) -
        β * p * (∑ k, ∑ j, q j * (v k * a j k)) := by
      simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    _ = β * p * (∑ k, v k * c k) -
        β * p * (∑ j, ∑ k, q j * (v k * a j k)) := by rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.mul_sum, mul_sub]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem gaussianSoftMaxWeight_linear_stein (β : ℝ)
    (c : I → EuclideanSpace ℝ (Fin r)) (v : EuclideanSpace ℝ (Fin r)) (i : I) :
    (∫ g, gaussianSoftMaxWeight β c i g * gaussianLinear v g ∂standardGaussian r) =
      ∫ g, β * (gaussianSoftMaxWeight β c i g * (∑ k, v k * (c i) k) -
        ∑ j, gaussianSoftMaxWeight β c i g * gaussianSoftMaxWeight β c j g *
          ∑ k, v k * (c j) k) ∂standardGaussian r := by
  classical
  let P := gaussianSoftMaxWeight β c
  let D := fun (k : Fin r) (g : Fin r → ℝ) => β * P i g *
    ((c i) k - ∑ j, P j g * (c j) k)
  have hP (k : Fin r) : Integrable (fun g => P i g * g k) (standardGaussian r) :=
    gaussianSoftMaxWeight_mul_integrable β c i (gaussianCoordinate_integrable k)
  have hD (k : Fin r) : Integrable (D k) (standardGaussian r) :=
    gaussianSoftMaxWeight_coordinate_derivative_integrable β c i k
  calc
    _ = ∫ g, ∑ k, v k * (P i g * g k) ∂standardGaussian r := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        simp only [gaussianLinear, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by dsimp [P]; ring
    _ = ∑ k, v k * ∫ g, P i g * g k ∂standardGaussian r := by
      rw [integral_finset_sum _ (fun k _ => (hP k).const_mul (v k))]
      simp only [integral_const_mul]
    _ = ∑ k, v k * ∫ g, D k g ∂standardGaussian r := by
      apply Finset.sum_congr rfl
      intro k _
      rw [gaussianSoftMaxWeight_coordinate_stein β c i k]
    _ = ∫ g, ∑ k, v k * D k g ∂standardGaussian r := by
      rw [integral_finset_sum _ (fun k _ => (hD k).const_mul (v k))]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g =>
        softMax_stein_algebra β (P i g) (fun j => P j g) (fun k => (c i) k)
          (fun k => v k) (fun j k => (c j) k)

/-- Summed Gaussian integration by parts gives the precise covariance
contraction for a soft maximum and an arbitrary linear perturbation. -/
theorem gaussianSoftMax_directional_stein (β : ℝ)
    (c v : I → EuclideanSpace ℝ (Fin r)) :
    (∫ g, ∑ i, gaussianSoftMaxWeight β c i g * gaussianLinear (v i) g
      ∂standardGaussian r) =
      β * ∫ g, (∑ i, gaussianSoftMaxWeight β c i g * ∑ k, (v i) k * (c i) k) -
        (∑ i, ∑ j, gaussianSoftMaxWeight β c i g * gaussianSoftMaxWeight β c j g *
          ∑ k, (v i) k * (c j) k) ∂standardGaussian r := by
  classical
  let P := gaussianSoftMaxWeight β c
  let A := fun (i : I) (g : Fin r → ℝ) => P i g * ∑ k, (v i) k * (c i) k
  let B := fun (i j : I) (g : Fin r → ℝ) => P i g * P j g * ∑ k, (v i) k * (c j) k
  have hA (i : I) : Integrable (A i) (standardGaussian r) :=
    (gaussianSoftMaxWeight_integrable β c i).mul_const _
  have hB (i j : I) : Integrable (B i j) (standardGaussian r) :=
    (gaussianSoftMaxWeight_mul_integrable β c i
      (gaussianSoftMaxWeight_integrable β c j)).mul_const _
  have hterm (i : I) : Integrable (fun g => β * (A i g - ∑ j, B i j g))
      (standardGaussian r) :=
    ((hA i).sub (integrable_finset_sum _ (fun j _ => hB i j))).const_mul β
  calc
    _ = ∑ i, ∫ g, P i g * gaussianLinear (v i) g ∂standardGaussian r :=
      integral_finset_sum _ (fun i _ =>
        gaussianSoftMaxWeight_mul_integrable β c i (gaussianLinear_integrable (v i)))
    _ = ∑ i, ∫ g, β * (A i g - ∑ j, B i j g) ∂standardGaussian r := by
      exact Finset.sum_congr rfl fun i _ => gaussianSoftMaxWeight_linear_stein β c (v i) i
    _ = ∫ g, ∑ i, β * (A i g - ∑ j, B i j g) ∂standardGaussian r :=
      (integral_finset_sum _ (fun i _ => hterm i)).symm
    _ = ∫ g, β * ((∑ i, A i g) - ∑ i, ∑ j, B i j g) ∂standardGaussian r := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    _ = _ := integral_const_mul _ _

end GenericChaining
