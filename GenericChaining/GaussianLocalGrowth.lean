import GenericChaining.GaussianMinoration
import GenericChaining.GaussianGrowth
import GenericChaining.GaussianEmbedding
import GenericChaining.GaussianComparison

/-!
# Growth from separated Gaussian blocks

Conditioning on independent offsets and taking expectations in the local
sample first gives the gain from a finite Gaussian maximum. The local samples
may be shared: only their independence from the offsets is needed.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- If every local maximum has mean at least `w`, adding independent offsets
raises the expected overall maximum by at least the expected offset maximum.
No independence between the local variables themselves is required. -/
theorem integral_independent_offsets_growth {I Ω Ω' : Type*}
    [Fintype I] [Nonempty I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : I → Ω → ℝ} {Z : I → Ω' → ℝ}
    (hY : ∀ i, Integrable (Y i) μ) (hZ : ∀ i, Integrable (Z i) ν)
    (w : ℝ) (hw : ∀ i, w ≤ ∫ ω, Y i ω ∂μ) :
    w + (∫ η, (⨆ i, Z i η) ∂ν) ≤
      ∫ p : Ω × Ω', (⨆ i, Y i p.1 + Z i p.2) ∂μ.prod ν := by
  have hprod (i : I) : Integrable (fun p : Ω × Ω' => Y i p.1 + Z i p.2) (μ.prod ν) := by
    have h₁ : Integrable (fun p : Ω × Ω' => Y i p.1) (μ.prod ν) := by
      simpa only [mul_one] using (hY i).mul_prod
        (integrable_const (1 : ℝ) : Integrable _ ν)
    have h₂ : Integrable (fun p : Ω × Ω' => Z i p.2) (μ.prod ν) := by
      simpa only [one_mul] using
        (integrable_const (1 : ℝ) : Integrable _ μ).mul_prod (hZ i)
    exact h₁.add h₂
  have hmax : Integrable (fun p : Ω × Ω' => ⨆ i, Y i p.1 + Z i p.2) (μ.prod ν) :=
    integrable_iSup_finite hprod
  rw [integral_prod_symm _ hmax]
  have hleft : Integrable (fun η => w + ⨆ i, Z i η) ν :=
    (integrable_const w).add (integrable_iSup_finite hZ)
  have hbound (η : Ω') : w + (⨆ i, Z i η) ≤
      ∫ ω, (⨆ i, Y i ω + Z i η) ∂μ := by
    have hslice : Integrable (fun ω => ⨆ j, Y j ω + Z j η) μ :=
      integrable_iSup_finite (f := fun j ω => Y j ω + Z j η)
        (fun j => (hY j).add (integrable_const _))
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => Z i η)
    rw [← hi]
    calc
      _ ≤ (∫ ω, Y i ω ∂μ) + Z i η := add_le_add_right (hw i) _
      _ = ∫ ω, Y i ω + Z i η ∂μ := by
        rw [integral_add (hY i) (integrable_const _), integral_const,
          measureReal_univ_eq_one, one_smul]
      _ ≤ _ := integral_mono ((hY i).add (integrable_const _))
        hslice (fun ω => le_ciSup (Finite.bddAbove_range (fun j => Y j ω + Z j η)) i)
  have h := integral_mono hleft hmax.integral_prod_right hbound
  simpa only [integral_add (integrable_const w) (integrable_iSup_finite hZ),
    integral_const, measureReal_univ_eq_one, one_smul] using h

/-- The shared local sample used above also satisfies the required increment
comparison. This slightly larger variance bound still fits radius `a/8`. -/
theorem shared_local_block_variance_le {E : Type*} [SeminormedAddCommGroup E]
    (c d x y : E) {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (hsmall : ρ ≤ a / 8) (hsep : a ≤ dist c d)
    (hx : dist x c ≤ ρ) (hy : dist y d ≤ ρ) :
    ‖(x - c) - (y - d)‖ ^ 2 + 2 * (a / 4) ^ 2 ≤ dist x y ^ 2 := by
  have hdiff : ‖(x - c) - (y - d)‖ ≤ 2 * ρ := by
    have h := norm_sub_le (x - c) (y - d)
    rw [← dist_eq_norm x c, ← dist_eq_norm y d] at h
    linarith
  have hd := local_block_distance_lower c d x y hsep hx hy
  have hdiff2 : ‖(x - c) - (y - d)‖ ^ 2 ≤ (a / 4) ^ 2 := by
    have hfirst := (sq_le_sq₀ (norm_nonneg ((x - c) - (y - d)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ)).mpr hdiff
    have hsecond : (2 * ρ) ^ 2 ≤ (a / 4) ^ 2 := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      linarith
    exact hfirst.trans hsecond
  have hdist2 : (3 * a / 4) ^ 2 ≤ dist x y ^ 2 := by
    apply (sq_le_sq₀ (by positivity) dist_nonneg).mpr
    linarith
  nlinarith

/-- A scalar offset is represented by one Euclidean coordinate vector. -/
theorem gaussianLinear_single {m : ℕ} (β : ℝ) (i : Fin m) (g : Fin m → ℝ) :
    gaussianLinear (EuclideanSpace.single i β) g = β * g i := by
  classical
  simp [gaussianLinear, EuclideanSpace.single_apply, mul_ite, mul_comm]

/-- Distinct independent scalar offsets contribute two copies of their variance. -/
theorem gaussianOffset_distance_sq {m : ℕ} (β : ℝ) {i j : Fin m} (hij : i ≠ j) :
    ‖EuclideanSpace.single i β - EuclideanSpace.single j β‖ ^ 2 = 2 * β ^ 2 := by
  rw [norm_sub_sq_real, EuclideanSpace.norm_single, EuclideanSpace.norm_single,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp [hij, Real.norm_eq_abs, sq_abs]
  ring

private theorem finite_ciSup_add_const {I : Type*} [Finite I] [Nonempty I]
    (f : I → ℝ) (a : ℝ) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := f)
  apply le_antisymm
  · rw [← hi]
    exact le_ciSup (Finite.bddAbove_range (fun j => f j + a)) i
  · exact ciSup_le (fun j => add_le_add_right (le_ciSup (Finite.bddAbove_range f) j) a)

private theorem finite_ciSup_prod_add {I T : Type*} [Finite I] [Nonempty I]
    [Finite T] [Nonempty T] (f : I → T → ℝ) (z : I → ℝ) :
    (⨆ p : I × T, f p.1 p.2 + z p.1) = ⨆ i, (⨆ t, f i t) + z i := by
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨i, t⟩
    exact (add_le_add_right (le_ciSup (Finite.bddAbove_range (f i)) t) _).trans
      (le_ciSup (Finite.bddAbove_range (fun j => (⨆ t, f j t) + z j)) i)
  · apply ciSup_le
    intro i
    rw [finite_ciSup_add_const]
    exact ciSup_le (fun t => le_ciSup
      (Finite.bddAbove_range (fun p : I × T => f p.1 p.2 + z p.1)) (i, t))

/-- Conditional Jensen's inequality gives the gain from independent scalar
offsets, while the same local Gaussian sample may be used in every block. -/
theorem gaussian_product_local_growth {m r : ℕ} [NeZero m] {T : Type*}
    [Fintype T] [Nonempty T]
    (a : Fin m → T → EuclideanSpace ℝ (Fin r))
    (c : Fin m → EuclideanSpace ℝ (Fin r)) (β : ℝ) (hβ : 0 ≤ β)
    (w : ℝ) (hw : ∀ i, w ≤ gaussianWidth (a i)) :
    w + β * (∫ h : Fin m → ℝ, (⨆ i, h i) ∂standardGaussian m) ≤
      ∫ p : (Fin r → ℝ) × (Fin m → ℝ),
        (⨆ it : Fin m × T, gaussianLinear (a it.1 it.2 - c it.1) p.1 + β * p.2 it.1)
        ∂(standardGaussian r).prod (standardGaussian m) := by
  let Y : Fin m → (Fin r → ℝ) → ℝ := fun i => gaussianMaximum (fun t => a i t - c i)
  let Z : Fin m → (Fin m → ℝ) → ℝ := fun i h => β * h i
  have hY (i : Fin m) : Integrable (Y i) (standardGaussian r) := gaussianMaximum_integrable _
  have hZ (i : Fin m) : Integrable (Z i) (standardGaussian m) :=
    (standardGaussian_coordinate_integrable i).const_mul β
  have hmean (i : Fin m) : w ≤ ∫ g, Y i g ∂standardGaussian r := by
    change w ≤ gaussianWidth (fun t => a i t - c i)
    have htranslate := gaussianWidth_translate (a i) (-c i)
    simp only [sub_eq_add_neg] at *
    rw [htranslate]
    exact hw i
  have h := integral_independent_offsets_growth hY hZ w hmean
  have hoff : (fun h : Fin m → ℝ => ⨆ i, Z i h) = (fun h => β * ⨆ i, h i) := by
    funext h
    exact (Real.mul_iSup_of_nonneg hβ h).symm
  rw [hoff, integral_const_mul] at h
  apply h.trans_eq
  apply integral_congr_ae
  filter_upwards [] with p
  exact (finite_ciSup_prod_add (fun i t => gaussianLinear (a i t - c i) p.1)
    (fun i => β * p.2 i)).symm

/-- The comparison process keeps the centered local vectors in one common
block and uses a separate coordinate for every independent offset. -/
noncomputable def localGaussianVector {m r : ℕ} {T : Type*}
    (a : Fin m → T → EuclideanSpace ℝ (Fin r))
    (c : Fin m → EuclideanSpace ℝ (Fin r)) (β : ℝ) (it : Fin m × T) :
    EuclideanSpace ℝ (Fin (r + m)) :=
  appendEuclidean (a it.1 it.2 - c it.1) (EuclideanSpace.single it.1 β)

/-- Separation of the centers controls every increment of the comparison
process; increments in the same local block are unchanged. -/
theorem localGaussianVector_increment_le {m r : ℕ} {T : Type*}
    (a : Fin m → T → EuclideanSpace ℝ (Fin r))
    (c : Fin m → EuclideanSpace ℝ (Fin r)) {δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ δ / 8)
    (hcent : ∀ i j, i ≠ j → δ ≤ ‖c i - c j‖)
    (hloc : ∀ i t, ‖a i t - c i‖ ≤ ρ) (p q : Fin m × T) :
    ‖localGaussianVector a c (δ / 4) p - localGaussianVector a c (δ / 4) q‖ ^ 2 ≤
      ‖a p.1 p.2 - a q.1 q.2‖ ^ 2 := by
  unfold localGaussianVector
  rw [appendEuclidean_sub, appendEuclidean_norm_sq]
  by_cases hpq : p.1 = q.1
  · rw [hpq, sub_self, norm_zero, zero_pow (by decide), add_zero]
    simp only [sub_sub_sub_cancel_right, le_refl]
  · rw [gaussianOffset_distance_sq _ hpq]
    exact shared_local_block_variance_le (c p.1) (c q.1) (a p.1 p.2) (a q.1 q.2)
      hδ hρ hsmall (by simpa only [dist_eq_norm] using hcent p.1 q.1 hpq)
      (by simpa only [dist_eq_norm] using hloc p.1 p.2)
      (by simpa only [dist_eq_norm] using hloc q.1 q.2)

/-- Jensen's lower bound for the concrete appended comparison process. -/
theorem localGaussianVector_width_lower_bound {m r : ℕ} [NeZero m] {T : Type*}
    [Fintype T] [Nonempty T]
    (a : Fin m → T → EuclideanSpace ℝ (Fin r))
    (c : Fin m → EuclideanSpace ℝ (Fin r)) (β : ℝ) (hβ : 0 ≤ β)
    (b : ℝ) (hb : ∀ i, b ≤ gaussianWidth (a i)) :
    b + β * (∫ h : Fin m → ℝ, (⨆ i, h i) ∂standardGaussian m) ≤
      gaussianWidth (localGaussianVector a c β) := by
  unfold localGaussianVector
  rw [gaussianWidth_append_eq_integral_prod]
  simp_rw [gaussianLinear_single]
  exact gaussian_product_local_growth a c β hβ b hb

/-- A fixed positive growth coefficient, independent of the dimension and
the number or cardinalities of the local sets. -/
noncomputable def gaussianGrowthConstant : ℝ :=
  (1 - Real.exp (-(((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)) / 2))) / 4

theorem gaussianGrowthConstant_pos : 0 < gaussianGrowthConstant :=
  div_pos standardGaussian_log_threshold_constant_pos (by norm_num)

/-- Gaussian local width growth for centers separated by `δ`, with every local
point in the closed ball of radius `ρ ≤ δ/8` about its center. -/
theorem gaussian_local_growth {m r : ℕ} [NeZero m] {T : Type*}
    [Fintype T] [Nonempty T]
    (a : Fin m → T → EuclideanSpace ℝ (Fin r))
    (c : Fin m → EuclideanSpace ℝ (Fin r)) {δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ δ / 8)
    (hcent : ∀ i j, i ≠ j → δ ≤ ‖c i - c j‖)
    (hloc : ∀ i t, ‖a i t - c i‖ ≤ ρ)
    (b : ℝ) (hb : ∀ i, b ≤ gaussianWidth (a i)) :
    b + gaussianGrowthConstant * δ * Real.sqrt (Real.log (m : ℝ)) ≤
      gaussianWidth (fun it : Fin m × T => a it.1 it.2) := by
  have hiid := standardGaussian_iid_max_explicit_lower_bound (m := m)
  have hscale := mul_le_mul_of_nonneg_left hiid (show 0 ≤ δ / 4 by positivity)
  have hgain : gaussianGrowthConstant * δ * Real.sqrt (Real.log (m : ℝ)) ≤
      (δ / 4) * (∫ h : Fin m → ℝ, (⨆ i, h i) ∂standardGaussian m) := by
    convert hscale using 1
    dsimp [gaussianGrowthConstant]
    ring
  have hcomp := gaussianWidth_mono_of_increment_le
    (fun it : Fin m × T => a it.1 it.2) (localGaussianVector a c (δ / 4))
    (localGaussianVector_increment_le a c hδ hρ hsmall hcent hloc)
  exact (add_le_add_left hgain b).trans
    ((localGaussianVector_width_lower_bound a c (δ / 4) (by positivity) b hb).trans hcomp)

end GenericChaining
