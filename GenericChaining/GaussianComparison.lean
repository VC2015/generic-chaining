import GenericChaining.GaussianStein
import GenericChaining.GaussianEmbedding
import GenericChaining.GaussianSoftMaxStein
import GenericChaining.GaussianInterpolation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import GenericChaining.GaussianSmoothMax
import GenericChaining.TailExpectation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Basic

namespace GenericChaining
open scoped BigOperators

/-- The covariance contraction of the Hessian of log-sum-exp equals half
the weighted sum of the corresponding increment variances. -/
theorem covariance_contraction_eq_increment_sum {I : Type*} [Fintype I]
    (p : I → ℝ) (hp : ∑ i, p i = 1) (C : I → I → ℝ) :
    (∑ i, p i * C i i) - (∑ i, ∑ j, p i * p j * C i j) =
      (1/2 : ℝ) * ∑ i, ∑ j, p i * p j * (C i i + C j j - 2*C i j) := by
  have h₁ : (∑ i, ∑ j, p i * p j * C i i) = ∑ i, p i * C i i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (p i * C i i) * ∑ j, p j := by rw [Finset.mul_sum]; congr 1; ext j; ring
      _ = _ := by rw [hp, mul_one]
  have h₂ : (∑ i, ∑ j, p i * p j * C j j) = ∑ j, p j * C j j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (∑ i, p i) * (p j * C j j) := by rw [Finset.sum_mul]; congr 1; ext i; ring
      _ = _ := by rw [hp, one_mul]
  have h₃ : (∑ i, ∑ j, p i * p j * (2*C i j)) =
      2 * ∑ i, ∑ j, p i * p j * C i j := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h₁, h₂, h₃]
  ring

/-- Increment variance ordering gives the sign needed by Gaussian
interpolation, for every vector of nonnegative weights summing to one. -/
theorem covariance_contraction_mono {I : Type*} [Fintype I]
    (p : I → ℝ) (hp : ∑ i, p i = 1) (hp0 : ∀ i, 0 ≤ p i)
    (C D : I → I → ℝ)
    (hinc : ∀ i j, C i i + C j j - 2*C i j ≤ D i i + D j j - 2*D i j) :
    (∑ i, p i * C i i) - (∑ i, ∑ j, p i * p j * C i j) ≤
      (∑ i, p i * D i i) - (∑ i, ∑ j, p i * p j * D i j) := by
  rw [covariance_contraction_eq_increment_sum p hp C,
    covariance_contraction_eq_increment_sum p hp D]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hinc i j) (mul_nonneg (hp0 i) (hp0 j))

/-- Independent coefficient families are interpolated by these vectors. -/
noncomputable def gaussianComparisonPath {I E : Type*} [AddCommGroup E]
    [Module ℝ E] (A B : I → E) (s : ℝ) (i : I) : E :=
  Real.sqrt s • A i + Real.sqrt (1-s) • B i

/-- The velocity of the square-root interpolation away from its endpoints. -/
noncomputable def gaussianComparisonVelocity {I E : Type*} [AddCommGroup E]
    [Module ℝ E] (A B : I → E) (s : ℝ) (i : I) : E :=
  (1 / (2*Real.sqrt s)) • A i - (1 / (2*Real.sqrt (1-s))) • B i

/-- Orthogonality of the two independent coefficient families removes all
cross terms in the interpolation covariance derivative. -/
theorem gaussianComparisonVelocity_inner_path {I E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : I → E)
    (horth : ∀ i j, inner (𝕜 := ℝ) (A i) (B j) = 0)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (i j : I) :
    inner (𝕜 := ℝ) (gaussianComparisonVelocity A B s i)
      (gaussianComparisonPath A B s j) =
      (1/2 : ℝ) * (inner (𝕜 := ℝ) (A i) (A j) - inner (𝕜 := ℝ) (B i) (B j)) := by
  have hBA : inner (𝕜 := ℝ) (B i) (A j) = 0 := by
    rw [real_inner_comm, horth]
  have hsq0 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq1 : Real.sqrt (1-s) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  simp only [gaussianComparisonVelocity, gaussianComparisonPath, inner_sub_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, horth, hBA,
    mul_zero, add_zero, zero_add]
  field_simp
  ring

/-- Pairwise distance ordering gives a nonnegative contraction of the
interpolation velocity against the smooth-maximum Hessian. -/
theorem gaussianComparison_contraction_nonneg {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : I → E)
    (horth : ∀ i j, inner (𝕜 := ℝ) (A i) (B j) = 0)
    (hinc : ∀ i j, ‖B i-B j‖^2 ≤ ‖A i-A j‖^2)
    (p : I → ℝ) (hp : ∑ i, p i = 1) (hp0 : ∀ i, 0 ≤ p i)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 ≤ (∑ i, p i * inner (𝕜 := ℝ) (gaussianComparisonVelocity A B s i)
      (gaussianComparisonPath A B s i)) -
      (∑ i, ∑ j, p i*p j * inner (𝕜 := ℝ) (gaussianComparisonVelocity A B s i)
        (gaussianComparisonPath A B s j)) := by
  have hc := covariance_contraction_mono p hp hp0
    (fun i j => inner (𝕜 := ℝ) (B i) (B j))
    (fun i j => inner (𝕜 := ℝ) (A i) (A j)) (fun i j => by
      have hh := hinc i j
      rw [norm_sub_sq_real, norm_sub_sq_real] at hh
      simp only [real_inner_self_eq_norm_sq]
      linarith)
  simp_rw [gaussianComparisonVelocity_inner_path A B horth hs hs1]
  have hdiag : (∑ i, p i*((1/2 : ℝ)*(inner (𝕜 := ℝ) (A i) (A i) -
      inner (𝕜 := ℝ) (B i) (B i)))) =
      (1/2 : ℝ)*((∑ i, p i*inner (𝕜 := ℝ) (A i) (A i)) -
        (∑ i, p i*inner (𝕜 := ℝ) (B i) (B i))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hdouble : (∑ i, ∑ j, p i*p j*((1/2 : ℝ)*(inner (𝕜 := ℝ) (A i) (A j) -
      inner (𝕜 := ℝ) (B i) (B j)))) =
      (1/2 : ℝ)*((∑ i, ∑ j, p i*p j*inner (𝕜 := ℝ) (A i) (A j)) -
        (∑ i, ∑ j, p i*p j*inner (𝕜 := ℝ) (B i) (B j))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hdiag, hdouble]
  linarith

/-- Comparing all smooth maxima compares the expected finite maxima. The
log-sum-exp error tends to zero without any limiting interchange under the
probability integral. -/
theorem integral_max_le_of_softMax_le {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (X Y : I → Ω → ℝ)
    (hX : ∀ i, MeasureTheory.Integrable (X i) μ)
    (hY : ∀ i, MeasureTheory.Integrable (Y i) μ)
    (hsoft : ∀ β : ℝ, 0 < β →
      MeasureTheory.Integrable (fun ω => softMax β (fun i => X i ω)) μ ∧
      MeasureTheory.Integrable (fun ω => softMax β (fun i => Y i ω)) μ ∧
      (∫ ω, softMax β (fun i => X i ω) ∂μ) ≤ ∫ ω, softMax β (fun i => Y i ω) ∂μ) :
    (∫ ω, ⨆ i, X i ω ∂μ) ≤ ∫ ω, ⨆ i, Y i ω ∂μ := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  have hn : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ Real.log (Fintype.card I) := Real.log_nonneg hn
  let β := (Real.log (Fintype.card I)+1) / ε
  have hβ : 0 < β := div_pos (by linarith) hε
  obtain ⟨hsX, hsY, hcomp⟩ := hsoft β hβ
  have hmaxX := integrable_iSup_finite hX
  have hmaxY := integrable_iSup_finite hY
  have hleft : (∫ ω, ⨆ i, X i ω ∂μ) ≤ ∫ ω, softMax β (fun i => X i ω) ∂μ := by
    apply MeasureTheory.integral_mono hmaxX hsX
    intro ω
    exact ciSup_le (fun i => le_softMax β hβ (fun i => X i ω) i)
  have hright : (∫ ω, softMax β (fun i => Y i ω) ∂μ) ≤
      (∫ ω, ⨆ i, Y i ω ∂μ) + Real.log (Fintype.card I)/β := by
    have h := MeasureTheory.integral_mono hsY
      (hmaxY.add (MeasureTheory.integrable_const (Real.log (Fintype.card I)/β)))
      (fun ω => softMax_le_max_add_log_card β hβ (fun i => Y i ω))
    change (∫ ω, softMax β (fun i => Y i ω) ∂μ) ≤
      ∫ ω, (⨆ i, Y i ω) + Real.log (Fintype.card I)/β ∂μ at h
    rw [MeasureTheory.integral_add hmaxY (MeasureTheory.integrable_const _),
      MeasureTheory.integral_const] at h
    simpa using h
  have herr : Real.log (Fintype.card I)/β ≤ ε := by
    apply (div_le_iff₀ hβ).mpr
    have heq : ε*β = Real.log (Fintype.card I)+1 := by
      dsimp [β]
      field_simp
    linarith
  exact hleft.trans (hcomp.trans (hright.trans (add_le_add_left herr _)))

lemma euclidean_sum_mul_eq_inner {r : ℕ} (a b : EuclideanSpace ℝ (Fin r)) :
    (∑ k, a k*b k) = inner (𝕜 := ℝ) a b := by
  change (∑ k, a k*b k) = ∑ k, b k*a k
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma gaussianComparisonPath_linear {I : Type*} {r : ℕ}
    (A B : I → EuclideanSpace ℝ (Fin r)) (s : ℝ) (g : Fin r → ℝ) (i : I) :
    gaussianLinear (gaussianComparisonPath A B s i) g =
      sqrtInterpolation (fun i => gaussianLinear (A i)) (fun i => gaussianLinear (B i)) s g i := by
  simp only [gaussianComparisonPath, gaussianLinear_add, gaussianLinear_smul, sqrtInterpolation]

lemma gaussianComparisonVelocity_linear {I : Type*} {r : ℕ}
    (A B : I → EuclideanSpace ℝ (Fin r)) (s : ℝ) (g : Fin r → ℝ) (i : I) :
    gaussianLinear (gaussianComparisonVelocity A B s i) g =
      sqrtInterpolationDeriv (fun i => gaussianLinear (A i)) (fun i => gaussianLinear (B i)) s g i := by
  simp only [gaussianComparisonVelocity, gaussianLinear_sub, gaussianLinear_smul,
    sqrtInterpolationDeriv, div_eq_mul_inv, one_mul]
  ring

/-- The expected smooth maximum is increasing along the interpolation
between two orthogonal Gaussian coefficient families with ordered increments. -/
theorem gaussian_softMax_interpolation_derivative_nonneg {I : Type*}
    [Fintype I] [Nonempty I] {r : ℕ}
    (A B : I → EuclideanSpace ℝ (Fin r))
    (horth : ∀ i j, inner (𝕜 := ℝ) (A i) (B j) = 0)
    (hinc : ∀ i j, ‖B i-B j‖^2 ≤ ‖A i-A j‖^2)
    (β : ℝ) (hβ : 0 < β) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    0 ≤ ∫ g, softMaxInterpolationDeriv β
      (fun i => gaussianLinear (A i)) (fun i => gaussianLinear (B i)) s g
      ∂standardGaussian r := by
  classical
  let c := gaussianComparisonPath A B s
  let v := gaussianComparisonVelocity A B s
  have hrep (g : Fin r → ℝ) : softMaxInterpolationDeriv β
      (fun i => gaussianLinear (A i)) (fun i => gaussianLinear (B i)) s g =
      ∑ i, gaussianSoftMaxWeight β c i g * gaussianLinear (v i) g := by
    simp only [softMaxInterpolationDeriv, gaussianSoftMaxWeight]
    simp_rw [c, gaussianComparisonPath_linear, v, gaussianComparisonVelocity_linear]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrep),
    gaussianSoftMax_directional_stein]
  apply mul_nonneg hβ.le
  apply MeasureTheory.integral_nonneg
  intro g
  simp_rw [euclidean_sum_mul_eq_inner]
  exact gaussianComparison_contraction_nonneg A B horth hinc
    (fun i => gaussianSoftMaxWeight β c i g)
    (sum_softMaxWeight β (fun i => gaussianLinear (c i) g))
    (fun i => softMaxWeight_nonneg β (fun i => gaussianLinear (c i) g) i) hs.1 hs.2

/-- Finite Sudakov--Fernique comparison for independent (orthogonal)
coefficient families on the same concrete standard Gaussian space. -/
theorem gaussianWidth_mono_of_increment_le_orthogonal {I : Type*}
    [Fintype I] [Nonempty I] {r : ℕ}
    (A B : I → EuclideanSpace ℝ (Fin r))
    (horth : ∀ i j, inner (𝕜 := ℝ) (A i) (B j) = 0)
    (hinc : ∀ i j, ‖B i-B j‖^2 ≤ ‖A i-A j‖^2) :
    gaussianWidth B ≤ gaussianWidth A := by
  classical
  apply integral_max_le_of_softMax_le (fun i => gaussianLinear (B i))
    (fun i => gaussianLinear (A i))
    (fun i => gaussianLinear_integrable (B i)) (fun i => gaussianLinear_integrable (A i))
  intro β hβ
  let X := fun i => gaussianLinear (A i)
  let Y := fun i => gaussianLinear (B i)
  have hX : ∀ i, MeasureTheory.Integrable (X i) (standardGaussian r) :=
    fun i => gaussianLinear_integrable (A i)
  have hY : ∀ i, MeasureTheory.Integrable (Y i) (standardGaussian r) :=
    fun i => gaussianLinear_integrable (B i)
  have hcont := continuousOn_integral_softMaxInterpolation β hβ hX hY
  have hdiff := fun s (hs : s ∈ Set.Ioo (0 : ℝ) 1) =>
    hasDerivAt_integral_softMaxInterpolation β hβ hX hY hs
  have hmono : MonotoneOn (fun s => ∫ g, softMaxInterpolation β X Y s g
      ∂standardGaussian r) (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hdiff s hs).2.hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact gaussian_softMax_interpolation_derivative_nonneg A B horth hinc β hβ hs
  have hend := hmono (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  have hi0 := softMaxInterpolation_integrable β hβ hX hY 0
  have hi1 := softMaxInterpolation_integrable β hβ hX hY 1
  have he0 : softMaxInterpolation β X Y 0 =
      (fun g => softMax β (fun i => gaussianLinear (B i) g)) := by
    funext g
    unfold softMaxInterpolation
    apply congrArg (softMax β)
    funext i
    simp [sqrtInterpolation, X, Y]
  have he1 : softMaxInterpolation β X Y 1 =
      (fun g => softMax β (fun i => gaussianLinear (A i) g)) := by
    funext g
    unfold softMaxInterpolation
    apply congrArg (softMax β)
    funext i
    simp [sqrtInterpolation, X, Y]
  rw [he0] at hi0
  rw [he1] at hi1
  refine ⟨hi0, hi1, ?_⟩
  simpa only [he0, he1] using hend

/-- Finite Sudakov--Fernique comparison for arbitrary dimensions, including
singular covariance matrices and repeated coefficient vectors. -/
theorem gaussianWidth_mono_of_increment_le {I : Type*} [Fintype I] [Nonempty I]
    {r s : ℕ} (A : I → EuclideanSpace ℝ (Fin r)) (B : I → EuclideanSpace ℝ (Fin s))
    (hinc : ∀ i j, ‖B i-B j‖^2 ≤ ‖A i-A j‖^2) : gaussianWidth B ≤ gaussianWidth A := by
  have h := gaussianWidth_mono_of_increment_le_orthogonal
    (fun i => padLeft s (A i)) (fun i => padRight r (B i))
    (fun i j => inner_padLeft_padRight (A i) (B j)) (by simpa using hinc)
  simpa only [gaussianWidth_padLeft, gaussianWidth_padRight] using h

/-- Gaussian width depends only on the canonical distances, even when its
representations have different dimensions or duplicate vectors. -/
theorem gaussianWidth_eq_of_increment_eq {I : Type*} [Fintype I] [Nonempty I]
    {r s : ℕ} (A : I → EuclideanSpace ℝ (Fin r)) (B : I → EuclideanSpace ℝ (Fin s))
    (hinc : ∀ i j, ‖A i-A j‖ = ‖B i-B j‖) : gaussianWidth A = gaussianWidth B := by
  apply le_antisymm
  · exact gaussianWidth_mono_of_increment_le B A (fun i j => by rw [hinc])
  · exact gaussianWidth_mono_of_increment_le A B (fun i j => by rw [hinc])

end GenericChaining
