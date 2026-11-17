import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith

/-!
# Geometry of separated local Gaussian blocks

For points in small balls around separated centers, independent centered local
copies plus independent scalar Gaussian offsets have smaller increment
variances than the original process. Finite Sudakov--Fernique comparison can
therefore give the local width growth inequality without a concentration
estimate for the local maxima.
-/
namespace GenericChaining

/-- Points in radius `r` balls around `a`-separated centers remain separated
by at least `a - 2*r`. -/
theorem local_block_distance_lower {E : Type*} [PseudoMetricSpace E]
    (c d x y : E) {a r : ℝ} (hsep : a ≤ dist c d)
    (hx : dist x c ≤ r) (hy : dist y d ≤ r) :
    a - 2*r ≤ dist x y := by
  have htri := dist_triangle4 c x y d
  rw [dist_comm c x] at htri
  linarith

/-- The increment variance of two independent centered local blocks with
independent scalar offsets of standard deviation `a/4` is dominated by the
original squared distance. Radius `r ≤ a/8` is sufficient. -/
theorem independent_local_block_variance_le {E : Type*} [PseudoMetricSpace E]
    (c d x y : E) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hsmall : r ≤ a/8) (hsep : a ≤ dist c d)
    (hx : dist x c ≤ r) (hy : dist y d ≤ r) :
    dist x c ^ 2 + dist y d ^ 2 + 2*(a/4)^2 ≤ dist x y ^ 2 := by
  have hd := local_block_distance_lower c d x y hsep hx hy
  have hx0 := dist_nonneg (x := x) (y := c)
  have hy0 := dist_nonneg (x := y) (y := d)
  have hxy0 := dist_nonneg (x := x) (y := y)
  have hx2 : dist x c ^ 2 ≤ r^2 := sq_le_sq₀ hx0 hr |>.mpr hx
  have hy2 : dist y d ^ 2 ≤ r^2 := sq_le_sq₀ hy0 hr |>.mpr hy
  have hr2 : r^2 ≤ (a/8)^2 := sq_le_sq₀ hr (by positivity) |>.mpr hsmall
  have ha2 : (3*a/4)^2 ≤ dist x y ^ 2 := by
    apply (sq_le_sq₀ (by positivity) hxy0).mpr
    linarith
  nlinarith

end GenericChaining
