import GenericChaining.GaussianTail
import GenericChaining.GaussianGeometry
import GenericChaining.TailExpectation
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite one-sided Gaussian width

The process is the concrete Euclidean projection from `GaussianCore`. Exact
first and second moments identify its canonical distance. A common translation
adds a centered integrable variable and therefore preserves the expected maximum.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

lemma gaussianLinear_integrableExpSet {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    integrableExpSet (gaussianLinear a) (standardGaussian r) = univ := by
  ext t
  simp only [mem_univ, iff_true]
  exact gaussianLinear_integrable_exp_mul a t

lemma gaussianLinear_zero_mem_interior {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    (0 : ℝ) ∈ interior (integrableExpSet (gaussianLinear a) (standardGaussian r)) := by
  rw [gaussianLinear_integrableExpSet, interior_univ]
  trivial

theorem gaussianLinear_integrable_pow {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) (n : ℕ) :
    Integrable (fun g => gaussianLinear a g ^ n) (standardGaussian r) :=
  integrable_pow_of_mem_interior_integrableExpSet (gaussianLinear_zero_mem_interior a) n

theorem gaussianLinear_integrable {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    Integrable (gaussianLinear a) (standardGaussian r) := by
  simpa only [pow_one] using gaussianLinear_integrable_pow a 1

private lemma projection_mgf_hasDerivAt {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (‖a‖ ^ 2 * s ^ 2 / 2))
      (‖a‖ ^ 2 * t * Real.exp (‖a‖ ^ 2 * t ^ 2 / 2)) t := by
  convert ((((hasDerivAt_id t).pow 2).const_mul (‖a‖ ^ 2)).div_const 2).exp using 1
  simp only [id_eq]
  ring

/-- Every projection is centered, also in dimension zero and for the zero vector. -/
theorem gaussianLinear_integral {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    ∫ g, gaussianLinear a g ∂standardGaussian r = 0 := by
  have hd : deriv (mgf (gaussianLinear a) (standardGaussian r)) 0 = 0 := by
    rw [show mgf (gaussianLinear a) (standardGaussian r) =
      (fun t : ℝ => Real.exp (‖a‖ ^ 2 * t ^ 2 / 2)) from funext (gaussianLinear_mgf a)]
    simpa using (projection_mgf_hasDerivAt a 0).deriv
  rwa [deriv_mgf_zero (gaussianLinear_zero_mem_interior a)] at hd

/-- The canonical second moment of a projection is its squared Euclidean norm. -/
theorem gaussianLinear_integral_sq {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    ∫ g, gaussianLinear a g ^ 2 ∂standardGaussian r = ‖a‖ ^ 2 := by
  have hfirst : deriv (mgf (gaussianLinear a) (standardGaussian r)) =
      (fun t : ℝ => ‖a‖ ^ 2 * t * Real.exp (‖a‖ ^ 2 * t ^ 2 / 2)) := by
    funext t
    rw [show mgf (gaussianLinear a) (standardGaussian r) =
      (fun t : ℝ => Real.exp (‖a‖ ^ 2 * t ^ 2 / 2)) from funext (gaussianLinear_mgf a)]
    exact (projection_mgf_hasDerivAt a t).deriv
  have hsecond : HasDerivAt
      (fun t : ℝ => ‖a‖ ^ 2 * t * Real.exp (‖a‖ ^ 2 * t ^ 2 / 2)) (‖a‖ ^ 2) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul (‖a‖ ^ 2)).mul
      (projection_mgf_hasDerivAt a 0) using 1
    simp
  have hm := iteratedDeriv_mgf_zero (gaussianLinear_zero_mem_interior a) 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hm
  rw [hfirst, hsecond.deriv] at hm
  exact hm.symm

theorem gaussianLinear_integrable_contrast_sq {r : ℕ}
    (a b : EuclideanSpace ℝ (Fin r)) :
    Integrable (fun g => (gaussianLinear a g - gaussianLinear b g) ^ 2)
      (standardGaussian r) := by
  simpa only [gaussianLinear_sub] using gaussianLinear_integrable_pow (a - b) 2

/-- The concrete process has exactly the requested canonical pseudometric. -/
theorem gaussianLinear_canonical_increment {r : ℕ} (a b : EuclideanSpace ℝ (Fin r)) :
    ∫ g, (gaussianLinear a g - gaussianLinear b g) ^ 2 ∂standardGaussian r = ‖a - b‖ ^ 2 := by
  simpa only [gaussianLinear_sub] using gaussianLinear_integral_sq (a - b)

/-- Cauchy--Schwarz for a Gaussian projection, in the form used for a base-point increment. -/
theorem gaussianLinear_integral_abs_le {r : ℕ} (a : EuclideanSpace ℝ (Fin r)) :
    ∫ g, |gaussianLinear a g| ∂standardGaussian r ≤ ‖a‖ := by
  have hint := gaussianLinear_integrable a
  have hsq : Integrable (fun g => |gaussianLinear a g| ^ 2) (standardGaussian r) := by
    simpa only [sq_abs] using gaussianLinear_integrable_pow a 2
  have hl2 := (memLp_two_iff_integrable_sq hint.abs.aestronglyMeasurable).2 hsq
  have hv := variance_nonneg (fun g => |gaussianLinear a g|) (standardGaussian r)
  rw [variance_def' hl2] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  rw [gaussianLinear_integral_sq] at hv
  have hn : 0 ≤ ∫ g, |gaussianLinear a g| ∂standardGaussian r :=
    integral_nonneg (fun _ => abs_nonneg _)
  apply (sq_le_sq₀ hn (norm_nonneg a)).mp
  linarith

/-- The one-sided maximum of a finite Gaussian process. -/
noncomputable def gaussianMaximum {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) (g : Fin r → ℝ) : ℝ :=
  ⨆ t, gaussianLinear (a t) g

/-- The expected one-sided maximum, with no anchoring or absolute value. -/
noncomputable def gaussianWidth {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) : ℝ :=
  ∫ g, gaussianMaximum a g ∂standardGaussian r

theorem gaussianMaximum_measurable {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) : Measurable (gaussianMaximum a) := by
  classical
  have h : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun t => gaussianLinear (a t))) := by
    exact Finset.sup'_induction (p := fun f : (Fin r → ℝ) → ℝ => Measurable f)
      Finset.univ_nonempty (fun t => gaussianLinear (a t))
      (fun f hf g hg => hf.sup hg) (fun t _ => gaussianLinear_measurable (a t))
  have heq : Finset.univ.sup' Finset.univ_nonempty (fun t => gaussianLinear (a t)) =
      gaussianMaximum a := by
    funext g
    rw [Finset.sup'_apply, Finset.sup'_univ_eq_ciSup]
    rfl
  rwa [heq] at h

theorem gaussianMaximum_integrable {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) :
    Integrable (gaussianMaximum a) (standardGaussian r) :=
  integrable_iSup_finite (fun t => gaussianLinear_integrable (a t))

theorem gaussianWidth_nonneg {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) : 0 ≤ gaussianWidth a := by
  classical
  let t := Classical.choice ‹Nonempty T›
  rw [← gaussianLinear_integral (a t)]
  exact integral_mono (gaussianLinear_integrable (a t)) (gaussianMaximum_integrable a)
    (fun g => le_ciSup (Finite.bddAbove_range (fun s => gaussianLinear (a s) g)) t)

theorem gaussianMaximum_translate {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin r)) (g : Fin r → ℝ) :
    gaussianMaximum (fun t => a t + b) g = gaussianMaximum a g + gaussianLinear b g := by
  have h₁ : gaussianMaximum (fun t => a t + b) g ≤ gaussianMaximum a g + gaussianLinear b g := by
    apply ciSup_le
    intro t
    rw [gaussianLinear_add]
    exact add_le_add_right
      (le_ciSup (Finite.bddAbove_range (fun s => gaussianLinear (a s) g)) t)
      (gaussianLinear b g)
  have h₂ : gaussianMaximum a g ≤ gaussianMaximum (fun t => a t + b) g - gaussianLinear b g := by
    apply ciSup_le
    intro t
    have h := le_ciSup (Finite.bddAbove_range (fun t => gaussianLinear (a t + b) g)) t
    rw [gaussianLinear_add] at h
    exact (le_sub_iff_add_le).mpr h
  linarith

/-- A common translation of all vectors preserves their expected one-sided maximum. -/
theorem gaussianWidth_translate {T : Type*} [Fintype T] [Nonempty T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin r)) :
    gaussianWidth (fun t => a t + b) = gaussianWidth a := by
  unfold gaussianWidth
  simp_rw [gaussianMaximum_translate]
  rw [integral_add (gaussianMaximum_integrable a) (gaussianLinear_integrable b),
    gaussianLinear_integral, add_zero]

theorem gaussianWidth_singleton {T : Type*} [Fintype T] [Unique T] {r : ℕ}
    (a : T → EuclideanSpace ℝ (Fin r)) : gaussianWidth a = 0 := by
  unfold gaussianWidth gaussianMaximum
  simpa only [ciSup_unique] using gaussianLinear_integral (a default)

/-- Repeated vector coordinates can be removed using the checked zero-contrast reduction. -/
theorem gaussianMaximum_ae_eq_of_vector_quotient {S T : Type*}
    [Fintype S] [Nonempty S] [Fintype T] [Nonempty T] {r : ℕ}
    (q : S → T) (hq : Function.Surjective q)
    (a : S → EuclideanSpace ℝ (Fin r)) (b : T → EuclideanSpace ℝ (Fin r))
    (hvec : ∀ s, a s = b (q s)) :
    gaussianMaximum a =ᵐ[standardGaussian r] gaussianMaximum b := by
  apply maximum_ae_eq_of_zero_contrasts q hq
  · intro s
    exact gaussianLinear_integrable_contrast_sq (a s) (b (q s))
  · intro s
    rw [gaussianLinear_canonical_increment, hvec s, sub_self, norm_zero, zero_pow (by decide)]

theorem gaussianWidth_of_vector_quotient {S T : Type*}
    [Fintype S] [Nonempty S] [Fintype T] [Nonempty T] {r : ℕ}
    (q : S → T) (hq : Function.Surjective q)
    (a : S → EuclideanSpace ℝ (Fin r)) (b : T → EuclideanSpace ℝ (Fin r))
    (hvec : ∀ s, a s = b (q s)) : gaussianWidth a = gaussianWidth b :=
  integral_congr_ae (gaussianMaximum_ae_eq_of_vector_quotient q hq a b hvec)

end GenericChaining
