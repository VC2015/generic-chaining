import GenericChaining.FiniteCost
import Mathlib.Analysis.Normed.Group.Basic

/-!
# The canonical distance of a finite vector family

The distance is a pseudometric: repeated vectors remain separate indices.
Translation and surjective reindexing preserve the chaining functional.
-/
namespace GenericChaining
open scoped NNReal ENNReal

variable {T S E : Type*} [SeminormedAddCommGroup E]

/-- Canonical increment distance of a vector family. -/
def canonicalDist (a : T → E) (s t : T) : ℝ≥0 := ‖a s - a t‖₊

@[simp] theorem canonicalDist_self (a : T → E) (t : T) :
    canonicalDist a t t = 0 := by simp [canonicalDist]

theorem canonicalDist_symm (a : T → E) (s t : T) :
    canonicalDist a s t = canonicalDist a t s := by
  simpa only [canonicalDist, nndist_eq_nnnorm] using nndist_comm (a s) (a t)

theorem canonicalDist_triangle (a : T → E) (s t c : T) :
    canonicalDist a s t ≤ canonicalDist a s c + canonicalDist a t c := by
  simpa only [canonicalDist, nndist_eq_nnnorm] using nndist_triangle_right (a s) (a t) (a c)

@[simp] theorem canonicalDist_translate (a : T → E) (b : E) :
    canonicalDist (fun t => a t + b) = canonicalDist a := by
  funext s t
  simp [canonicalDist]

/-- Finiteness is available before converting the extended functional to a real value. -/
theorem gamma2_canonicalDist_ne_top [Fintype T] [Nonempty T] (a : T → E) :
    gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞)) ≠ ⊤ :=
  gamma2_ne_top _ (canonicalDist_self a)

@[simp] theorem gamma2_canonicalDist_translate (a : T → E) (b : E) :
    gamma2 (fun s t => (canonicalDist (fun t => a t + b) s t : ℝ≥0∞)) =
      gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞)) := by
  rw [canonicalDist_translate]

/-- Collapsing repeated vectors uses the existing surjective pullback theorem. -/
theorem gamma2_canonicalDist_pullback (a : T → E) (q : S → T)
    (hq : Function.Surjective q) :
    gamma2 (fun s t => (canonicalDist (a ∘ q) s t : ℝ≥0∞)) =
      gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞)) :=
  gamma_pullback (fun k => ENNReal.ofReal (Real.sqrt 2) ^ k)
    (fun s t => (canonicalDist a s t : ℝ≥0∞)) q hq

/-- In particular, the canonical chaining cost depends only on the image of the vectors. -/
theorem gamma2_canonicalDist_range (a : T → E) :
    gamma2 (fun s t => (canonicalDist a s t : ℝ≥0∞)) =
      gamma2 (fun s t : Set.range a => (canonicalDist (fun s : Set.range a => s.val) s t : ℝ≥0∞)) := by
  let q : T → Set.range a := fun t => ⟨a t, ⟨t, rfl⟩⟩
  have hq : Function.Surjective q := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  exact gamma2_canonicalDist_pullback (fun s : Set.range a => s.val) q hq

end GenericChaining
