import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Removing duplicate indices of a Gaussian process

In the canonical Gaussian pseudometric the squared distance is a second
moment. A zero second moment therefore identifies two coordinates almost
surely. This reduction uses only square integrability and hence also applies
to finite processes that need not be Gaussian.
-/

namespace GenericChaining

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A zero second moment of a square-integrable contrast gives almost-sure equality. -/
theorem ae_eq_of_zero_contrast {X Y : Ω → ℝ}
    (hint : Integrable (fun ω => (X ω - Y ω) ^ 2) μ)
    (hzero : ∫ ω, (X ω - Y ω) ^ 2 ∂μ = 0) : X =ᵐ[μ] Y := by
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X ω - Y ω)) hint).mp hzero
  filter_upwards [hz] with ω hω
  have hs : (X ω - Y ω) ^ 2 = 0 := hω
  exact sub_eq_zero.mp (pow_eq_zero hs)

/-- A finite maximum agrees almost surely with the maximum over its quotient
if each index and its representative have zero canonical squared distance. -/
theorem maximum_ae_eq_of_zero_contrasts {S T : Type*} [Fintype S] [Nonempty S]
    [Fintype T] [Nonempty T] (q : S → T) (hq : Function.Surjective q)
    (X : S → Ω → ℝ) (Y : T → Ω → ℝ)
    (hint : ∀ s, Integrable (fun ω => (X s ω - Y (q s) ω) ^ 2) μ)
    (hzero : ∀ s, ∫ ω, (X s ω - Y (q s) ω) ^ 2 ∂μ = 0) :
    (fun ω => ⨆ s, X s ω) =ᵐ[μ] (fun ω => ⨆ t, Y t ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ s, X s ω = Y (q s) ω :=
    ae_all_iff.mpr fun s => ae_eq_of_zero_contrast (hint s) (hzero s)
  filter_upwards [hall] with ω hω
  change sSup (Set.range (fun s => X s ω)) = sSup (Set.range (fun t => Y t ω))
  congr 1
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨q s, (hω s).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hq t
    exact ⟨s, hω s⟩

end GenericChaining
