import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Smooth maxima for finite Gaussian comparison

These elementary estimates approximate a finite maximum by log-sum-exp and
identify the probability weights in the Gaussian interpolation formula.
-/
namespace GenericChaining
open scoped BigOperators

variable {I : Type*} [Fintype I] [Nonempty I]

/-- The normalizing sum in log-sum-exp. -/
noncomputable def softMaxSum (β : ℝ) (x : I → ℝ) : ℝ := ∑ i, Real.exp (β*x i)

lemma softMaxSum_pos (β : ℝ) (x : I → ℝ) : 0 < softMaxSum β x := by
  classical
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- Log-sum-exp with inverse temperature `β`. -/
noncomputable def softMax (β : ℝ) (x : I → ℝ) : ℝ := Real.log (softMaxSum β x) / β

/-- The probability weights given by the gradient of log-sum-exp. -/
noncomputable def softMaxWeight (β : ℝ) (x : I → ℝ) (i : I) : ℝ :=
  Real.exp (β*x i) / softMaxSum β x

lemma softMaxWeight_nonneg (β : ℝ) (x : I → ℝ) (i : I) : 0 ≤ softMaxWeight β x i :=
  div_nonneg (Real.exp_pos _).le (softMaxSum_pos β x).le

lemma sum_softMaxWeight (β : ℝ) (x : I → ℝ) : ∑ i, softMaxWeight β x i = 1 := by
  simp only [softMaxWeight, ← Finset.sum_div]
  exact div_self (softMaxSum_pos β x).ne'

omit [Nonempty I] in
/-- Log-sum-exp dominates every member of the finite family. -/
lemma le_softMax (β : ℝ) (hβ : 0 < β) (x : I → ℝ) (i : I) : x i ≤ softMax β x := by
  have hterm : Real.exp (β*x i) ≤ softMaxSum β x := by
    apply Finset.single_le_sum (fun j _ => (Real.exp_pos (β*x j)).le) (Finset.mem_univ i)
  have hlog := Real.log_le_log (Real.exp_pos _) hterm
  rw [Real.log_exp] at hlog
  exact (le_div_iff₀ hβ).mpr (by simpa [mul_comm] using hlog)

/-- The error of log-sum-exp is at most `log(card I)/β`. -/
lemma softMax_le_max_add_log_card (β : ℝ) (hβ : 0 < β) (x : I → ℝ) :
    softMax β x ≤ (⨆ i, x i) + Real.log (Fintype.card I) / β := by
  classical
  let M : ℝ := ⨆ i, x i
  have hM (i : I) : x i ≤ M := le_ciSup (Finite.bddAbove_range _) i
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : softMaxSum β x ≤ (Fintype.card I : ℝ) * Real.exp (β*M) := by
    calc
      _ ≤ ∑ _i : I, Real.exp (β*M) :=
        Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hM i) hβ.le)
      _ = _ := by simp
  have hlog := Real.log_le_log (softMaxSum_pos β x) hsum
  rw [Real.log_mul hn.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  change Real.log (softMaxSum β x) / β ≤ M + Real.log (Fintype.card I) / β
  apply (div_le_iff₀ hβ).mpr
  have heq : (M + Real.log (Fintype.card I) / β)*β =
      Real.log (Fintype.card I) + β*M := by field_simp; ring
  simpa only [heq] using hlog

omit [Nonempty I] in
/-- Weighted averaging with the soft-maximum probabilities. -/
lemma sum_softMaxWeight_mul (β : ℝ) (x v : I → ℝ) :
    (∑ i, softMaxWeight β x i * v i) =
      (∑ i, Real.exp (β*x i) * v i) / softMaxSum β x := by
  simp only [softMaxWeight, div_mul_eq_mul_div, ← Finset.sum_div]

lemma softMaxWeight_le_one (β : ℝ) (x : I → ℝ) (i : I) :
    softMaxWeight β x i ≤ 1 := by
  apply (div_le_one (softMaxSum_pos β x)).mpr
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos (β*x j)).le) (Finset.mem_univ i)

lemma abs_sum_softMaxWeight_mul_le (β : ℝ) (x v : I → ℝ) :
    |∑ i, softMaxWeight β x i * v i| ≤ ∑ i, |v i| := by
  calc
    _ ≤ ∑ i, |softMaxWeight β x i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, softMaxWeight β x i * |v i| := by
      simp only [abs_mul, abs_of_nonneg (softMaxWeight_nonneg β x _)]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_of_le_one_left (abs_nonneg _) (softMaxWeight_le_one β x i)

omit [Nonempty I] in
/-- Differentiate the normalizing sum along arbitrary differentiable coordinate paths. -/
theorem hasDerivAt_softMaxSum_comp (β : ℝ) (f : I → ℝ → ℝ) (v : I → ℝ)
    (t : ℝ) (hf : ∀ i, HasDerivAt (f i) (v i) t) :
    HasDerivAt (fun s => softMaxSum β (fun i => f i s))
      (β * ∑ i, Real.exp (β*f i t) * v i) t := by
  classical
  have h := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => ((hf i).const_mul β).exp)
  convert h using 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The derivative of log-sum-exp is its weighted directional average. -/
theorem hasDerivAt_softMax_comp (β : ℝ) (hβ : β ≠ 0)
    (f : I → ℝ → ℝ) (v : I → ℝ) (t : ℝ)
    (hf : ∀ i, HasDerivAt (f i) (v i) t) :
    HasDerivAt (fun s => softMax β (fun i => f i s))
      (∑ i, softMaxWeight β (fun i => f i t) i * v i) t := by
  have hs := hasDerivAt_softMaxSum_comp β f v t hf
  have hh := (hs.log (softMaxSum_pos β (fun i => f i t)).ne').div_const β
  convert hh using 1
  rw [sum_softMaxWeight_mul]
  apply (eq_div_iff hβ).2
  ring

/-- The derivative of a soft-maximum weight, needed for coordinatewise Gaussian Stein. -/
theorem hasDerivAt_softMaxWeight_comp (β : ℝ)
    (f : I → ℝ → ℝ) (v : I → ℝ) (t : ℝ)
    (hf : ∀ i, HasDerivAt (f i) (v i) t) (i : I) :
    HasDerivAt (fun s => softMaxWeight β (fun i => f i s) i)
      (β * softMaxWeight β (fun i => f i t) i *
        (v i - ∑ j, softMaxWeight β (fun j => f j t) j * v j)) t := by
  have hs := hasDerivAt_softMaxSum_comp β f v t hf
  have hh := (((hf i).const_mul β).exp).div hs
    (softMaxSum_pos β (fun i => f i t)).ne'
  convert hh using 1
  rw [sum_softMaxWeight_mul]
  simp only [softMaxWeight]
  field_simp [(softMaxSum_pos β (fun i => f i t)).ne']
  ring

/-- In particular, the affine-direction derivative has the same weights. -/
theorem hasDerivAt_softMax_line (β : ℝ) (hβ : β ≠ 0) (x v : I → ℝ) (t : ℝ) :
    HasDerivAt (fun s => softMax β (fun i => x i+s*v i))
      (∑ i, softMaxWeight β (fun i => x i+t*v i) i * v i) t := by
  apply hasDerivAt_softMax_comp β hβ
  intro i
  simpa using ((hasDerivAt_id t).mul_const (v i)).const_add (x i)

omit [Nonempty I] in
/-- Log-sum-exp and its gradient weights are continuous on a finite product. -/
theorem continuous_softMaxSum (β : ℝ) : Continuous (softMaxSum (I := I) β) := by
  classical
  exact continuous_finset_sum _ (fun i _ => (continuous_const.mul (continuous_apply i)).rexp)

theorem continuous_softMax (β : ℝ) : Continuous (softMax (I := I) β) :=
  ((continuous_softMaxSum β).log (fun x => (softMaxSum_pos β x).ne')).div_const β

theorem continuous_softMaxWeight (β : ℝ) (i : I) :
    Continuous (fun x : I → ℝ => softMaxWeight β x i) :=
  (continuous_const.mul (continuous_apply i)).rexp.div (continuous_softMaxSum β)
    (fun x => (softMaxSum_pos β x).ne')

/-- An integrable absolute envelope for the smooth maximum. -/
theorem abs_softMax_le (β : ℝ) (hβ : 0 < β) (x : I → ℝ) :
    |softMax β x| ≤ (∑ i, |x i|) + Real.log (Fintype.card I) / β := by
  classical
  let R : ℝ := ∑ i, |x i|
  have hR (i : I) : |x i| ≤ R :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have he : 0 ≤ Real.log (Fintype.card I) / β := by
    apply div_nonneg _ hβ.le
    apply Real.log_nonneg
    exact_mod_cast Fintype.card_pos (α := I)
  apply abs_le.mpr
  constructor
  · let i := Classical.choice ‹Nonempty I›
    have hl := le_softMax β hβ x i
    have hn := neg_abs_le (x i)
    change -(R + _) ≤ _
    linarith [hR i]
  · have hm : (⨆ i, x i) ≤ R := ciSup_le fun i => (le_abs_self (x i)).trans (hR i)
    exact (softMax_le_max_add_log_card β hβ x).trans (add_le_add_right hm _)

end GenericChaining
