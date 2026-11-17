import GenericChaining.GaussianCore
import GenericChaining.GaussianStein
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration by parts in a coordinate of a Gaussian product

The scalar Stein identity is applied on almost every coordinate section.
Global integrability supplies all three scalar integrability conditions by
Fubini; thus no uniform domination condition on the sections is needed.
-/

namespace GenericChaining

open MeasureTheory ProbabilityTheory

/-- Splitting off any coordinate of the finite standard Gaussian measure is
a measure-preserving equivalence with a scalar Gaussian and the remaining
standard Gaussian coordinates. -/
theorem standardGaussian_split_coordinate {r : ℕ} (j : Fin (r + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) j).symm
      ((gaussianReal 0 1).prod (standardGaussian r)) (standardGaussian (r + 1)) := by
  simpa only [standardGaussian] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => gaussianReal 0 1) j).symm _

/-- Product Gaussian integration by parts, with the coordinate sections
written using insertion of one scalar coordinate. -/
theorem standardGaussian_stein_insertNth {r : ℕ} (j : Fin (r + 1))
    {f f' : (Fin (r + 1) → ℝ) → ℝ}
    (hderiv : ∀ (y : Fin r → ℝ) (x : ℝ),
      HasDerivAt (fun z => f (j.insertNth z y)) (f' (j.insertNth x y)) x)
    (hf : Integrable f (standardGaussian (r + 1)))
    (hf' : Integrable f' (standardGaussian (r + 1)))
    (hxf : Integrable (fun g => g j * f g) (standardGaussian (r + 1))) :
    (∫ g, f' g ∂standardGaussian (r + 1)) =
      ∫ g, g j * f g ∂standardGaussian (r + 1) := by
  let e : ℝ × (Fin r → ℝ) ≃ᵐ (Fin (r + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) j).symm
  have he : MeasurePreserving e ((gaussianReal 0 1).prod (standardGaussian r))
      (standardGaussian (r + 1)) := standardGaussian_split_coordinate j
  have hfe : Integrable (fun z => f (e z))
      ((gaussianReal 0 1).prod (standardGaussian r)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hf'e : Integrable (fun z => f' (e z))
      ((gaussianReal 0 1).prod (standardGaussian r)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hf'
  have hxfe : Integrable (fun z => (e z) j * f (e z))
      ((gaussianReal 0 1).prod (standardGaussian r)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hxf
  have hsection : ∀ᵐ y ∂standardGaussian r,
      (∫ x, f' (e (x, y)) ∂gaussianReal 0 1) =
        ∫ x, (e (x, y)) j * f (e (x, y)) ∂gaussianReal 0 1 := by
    filter_upwards [hfe.prod_left_ae, hf'e.prod_left_ae, hxfe.prod_left_ae]
      with y hy hy' hyxf
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply] at hy hy' hyxf ⊢
    simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same]
      at hy hy' hyxf ⊢
    exact standardGaussian_stein (hderiv y) hy hy' hyxf
  calc
    _ = ∫ z, f' (e z) ∂((gaussianReal 0 1).prod (standardGaussian r)) :=
      (he.integral_comp' f').symm
    _ = ∫ y, ∫ x, f' (e (x, y)) ∂gaussianReal 0 1 ∂standardGaussian r :=
      integral_prod_symm _ hf'e
    _ = ∫ y, ∫ x, (e (x, y)) j * f (e (x, y)) ∂gaussianReal 0 1
        ∂standardGaussian r := integral_congr_ae hsection
    _ = ∫ z, (e z) j * f (e z) ∂((gaussianReal 0 1).prod (standardGaussian r)) :=
      (integral_prod_symm _ hxfe).symm
    _ = _ := he.integral_comp' (fun g => g j * f g)

/-- Product Gaussian Stein identity for an arbitrary finite dimension and
coordinate. The derivative assumption states exactly the partial derivative
in that coordinate. -/
theorem standardGaussian_stein_coordinate {r : ℕ} (j : Fin r)
    {f f' : (Fin r → ℝ) → ℝ}
    (hderiv : ∀ (g : Fin r → ℝ) (x : ℝ),
      HasDerivAt (fun z => f (Function.update g j z))
        (f' (Function.update g j x)) x)
    (hf : Integrable f (standardGaussian r))
    (hf' : Integrable f' (standardGaussian r))
    (hxf : Integrable (fun g => g j * f g) (standardGaussian r)) :
    (∫ g, f' g ∂standardGaussian r) = ∫ g, g j * f g ∂standardGaussian r := by
  cases r with
  | zero => exact Fin.elim0 j
  | succ r =>
    apply standardGaussian_stein_insertNth j ?_ hf hf' hxf
    intro y x
    simpa only [Fin.update_insertNth] using hderiv (j.insertNth 0 y) x

end GenericChaining
