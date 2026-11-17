import GenericChaining.GaussianWidth
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Orthogonal coordinate blocks for concrete Gaussian processes

Appending Euclidean vectors places them in orthogonal coordinate blocks.
The corresponding standard Gaussian law is the product law under the sample
append equivalence, so appending zeros preserves Gaussian width.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def appendEuclidean {r s : ℕ} (a : EuclideanSpace ℝ (Fin r))
    (b : EuclideanSpace ℝ (Fin s)) : EuclideanSpace ℝ (Fin (r + s)) :=
  (WithLp.equiv 2 (Fin (r + s) → ℝ)).symm (Fin.append a b)

noncomputable def padLeft (s : ℕ) {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℝ (Fin (r + s)) := appendEuclidean a 0

noncomputable def padRight (r : ℕ) {s : ℕ} (b : EuclideanSpace ℝ (Fin s)) :
    EuclideanSpace ℝ (Fin (r + s)) := appendEuclidean 0 b

@[simp] theorem appendEuclidean_left {r s : ℕ} (a : EuclideanSpace ℝ (Fin r))
    (b : EuclideanSpace ℝ (Fin s)) (i : Fin r) :
    appendEuclidean a b (Fin.castAdd s i) = a i := by
  simp [appendEuclidean, Fin.append_left]

@[simp] theorem appendEuclidean_right {r s : ℕ} (a : EuclideanSpace ℝ (Fin r))
    (b : EuclideanSpace ℝ (Fin s)) (i : Fin s) :
    appendEuclidean a b (Fin.natAdd r i) = b i := by
  simp [appendEuclidean, Fin.append_right]

theorem appendEuclidean_norm_sq {r s : ℕ} (a : EuclideanSpace ℝ (Fin r))
    (b : EuclideanSpace ℝ (Fin s)) : ‖appendEuclidean a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add]
  simp only [appendEuclidean_left, appendEuclidean_right]
  rw [← PiLp.norm_sq_eq_of_L2, ← PiLp.norm_sq_eq_of_L2]

theorem appendEuclidean_sub {r s : ℕ} (a c : EuclideanSpace ℝ (Fin r))
    (b d : EuclideanSpace ℝ (Fin s)) :
    appendEuclidean a b - appendEuclidean c d = appendEuclidean (a - c) (b - d) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

@[simp] theorem padLeft_norm {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    ‖padLeft s a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [padLeft, appendEuclidean_norm_sq]

@[simp] theorem padRight_norm {r s : ℕ} (b : EuclideanSpace ℝ (Fin s)) :
    ‖padRight r b‖ = ‖b‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [padRight, appendEuclidean_norm_sq]

theorem padLeft_sub {r s : ℕ} (a c : EuclideanSpace ℝ (Fin r)) :
    padLeft s a - padLeft s c = padLeft s (a - c) := by
  simpa [padLeft] using appendEuclidean_sub a c (0 : EuclideanSpace ℝ (Fin s)) 0

theorem padRight_sub {r s : ℕ} (b d : EuclideanSpace ℝ (Fin s)) :
    padRight r b - padRight r d = padRight r (b - d) := by
  simpa [padRight] using appendEuclidean_sub (0 : EuclideanSpace ℝ (Fin r)) 0 b d

@[simp] theorem padLeft_norm_sub {r s : ℕ} (a c : EuclideanSpace ℝ (Fin r)) :
    ‖padLeft s a - padLeft s c‖ = ‖a - c‖ := by rw [padLeft_sub, padLeft_norm]

@[simp] theorem padRight_norm_sub {r s : ℕ} (b d : EuclideanSpace ℝ (Fin s)) :
    ‖padRight r b - padRight r d‖ = ‖b - d‖ := by rw [padRight_sub, padRight_norm]

theorem inner_padLeft_padRight {r s : ℕ} (a : EuclideanSpace ℝ (Fin r))
    (b : EuclideanSpace ℝ (Fin s)) : inner (𝕜 := ℝ) (padLeft s a) (padRight r b) = 0 := by
  change (∑ i, padRight r b i * padLeft s a i) = 0
  rw [Fin.sum_univ_add]
  simp [padLeft, padRight]

/-- The full process splits into its two independent coordinate blocks. -/
theorem gaussianLinear_append {r s : ℕ} (a : EuclideanSpace ℝ (Fin r))
    (b : EuclideanSpace ℝ (Fin s)) (g : Fin r → ℝ) (h : Fin s → ℝ) :
    gaussianLinear (appendEuclidean a b) (Fin.append g h) =
      gaussianLinear a g + gaussianLinear b h := by
  unfold gaussianLinear
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, appendEuclidean_left, appendEuclidean_right]

noncomputable def gaussianSampleAppendEquiv (r s : ℕ) :
    ((Fin r → ℝ) × (Fin s → ℝ)) ≃ᵐ (Fin (r + s) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin s => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (r + s) => ℝ) finSumFinEquiv)

theorem gaussianSampleAppendEquiv_apply {r s : ℕ} (g : Fin r → ℝ) (h : Fin s → ℝ) :
    gaussianSampleAppendEquiv r s (g, h) = Fin.append g h := by
  ext k
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective k
  cases j with
  | inl i =>
    rw [gaussianSampleAppendEquiv, MeasurableEquiv.trans_apply,
      MeasurableEquiv.piCongrLeft_apply_apply]
    simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply]
  | inr i =>
    rw [gaussianSampleAppendEquiv, MeasurableEquiv.trans_apply,
      MeasurableEquiv.piCongrLeft_apply_apply]
    simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply]

theorem gaussianSampleAppend_measurePreserving (r s : ℕ) :
    MeasurePreserving (gaussianSampleAppendEquiv r s)
      ((standardGaussian r).prod (standardGaussian s)) (standardGaussian (r + s)) := by
  exact (measurePreserving_piCongrLeft (fun _ : Fin (r + s) => gaussianReal 0 1)
    finSumFinEquiv).comp
      (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin r ⊕ Fin s => gaussianReal 0 1))

/-- Appending coefficient blocks rewrites width as an integral under the independent product law. -/
theorem gaussianWidth_append_eq_integral_prod {T : Type*} [Fintype T] [Nonempty T]
    {r s : ℕ} (a : T → EuclideanSpace ℝ (Fin r)) (b : T → EuclideanSpace ℝ (Fin s)) :
    gaussianWidth (fun t => appendEuclidean (a t) (b t)) =
      ∫ p, (⨆ t, gaussianLinear (a t) p.1 + gaussianLinear (b t) p.2)
        ∂(standardGaussian r).prod (standardGaussian s) := by
  rw [gaussianWidth, ← (gaussianSampleAppend_measurePreserving r s).integral_comp
    (gaussianSampleAppendEquiv r s).measurableEmbedding]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  rcases p with ⟨g, h⟩
  simp only [gaussianSampleAppendEquiv_apply, gaussianMaximum, gaussianLinear_append]

@[simp] theorem gaussianWidth_padLeft {T : Type*} [Fintype T] [Nonempty T]
    {r : ℕ} (s : ℕ) (a : T → EuclideanSpace ℝ (Fin r)) :
    gaussianWidth (fun t => padLeft s (a t)) = gaussianWidth a := by
  rw [show (fun t => padLeft s (a t)) = (fun t => appendEuclidean (a t) 0) from rfl,
    gaussianWidth_append_eq_integral_prod]
  simp only [gaussianLinear_zero, add_zero]
  change (∫ p, gaussianMaximum a p.1 ∂(standardGaussian r).prod (standardGaussian s)) = _
  rw [integral_fun_fst]
  simp [gaussianWidth]

@[simp] theorem gaussianWidth_padRight {T : Type*} [Fintype T] [Nonempty T]
    {s : ℕ} (r : ℕ) (b : T → EuclideanSpace ℝ (Fin s)) :
    gaussianWidth (fun t => padRight r (b t)) = gaussianWidth b := by
  rw [show (fun t => padRight r (b t)) = (fun t => appendEuclidean 0 (b t)) from rfl,
    gaussianWidth_append_eq_integral_prod]
  simp only [gaussianLinear_zero, zero_add]
  change (∫ p, gaussianMaximum b p.2 ∂(standardGaussian r).prod (standardGaussian s)) = _
  rw [integral_fun_snd]
  simp [gaussianWidth]

end GenericChaining
