import ThetaTrial.Paper.Definitions
import Mathlib.Tactic

/-!
# Real and complex normalization of the theta series

`ThetaSeries` uses half the density of the paper. These results identify each
complex mode on the real axis with twice the corresponding real mode, and pass
to the sum. Evenness follows from Jacobi's transformation.
-/

noncomputable section

namespace ThetaTrial.Paper

open ThetaTrial.ThetaSeries

theorem complexThetaMode_ofReal (n : ℕ) (u : ℝ) :
    complexThetaMode n (u : ℂ) = 2 * (thetaPhiTerm n u : ℂ) := by
  unfold complexThetaMode thetaPhiTerm
  push_cast
  ring

theorem complexThetaMode_summable_real (u : ℝ) :
    Summable (fun n : ℕ => complexThetaMode n (u : ℂ)) := by
  simp_rw [complexThetaMode_ofReal]
  exact (Complex.summable_ofReal.mpr (thetaPhiTerm_summable u)).mul_left 2

theorem complexThetaDensity_eq_twice_thetaPhi (u : ℝ) :
    complexThetaDensity (u : ℂ) = 2 * (thetaPhi u : ℂ) := by
  simp_rw [complexThetaDensity, complexThetaMode_ofReal]
  rw [tsum_mul_left, ← Complex.ofReal_tsum]
  rfl

theorem complexThetaDensity_ofReal_nonneg {u : ℝ} (hu : 0 ≤ u) :
    complexThetaDensity (u : ℂ) = (thetaDensity u : ℂ) := by
  rw [complexThetaDensity_eq_twice_thetaPhi, thetaDensity_eq_of_nonneg hu]
  push_cast
  rfl

private theorem thetaBPrime_reflection_all (u : ℝ) :
    thetaBPrime u + thetaBPrime (-u) =
      -(Real.exp (-u / 2) + Real.exp (u / 2)) / 4 := by
  have hl := (thetaB_hasDerivAt_series u).sub
    ((thetaB_hasDerivAt_series (-u)).comp u (hasDerivAt_id u).neg)
  have hr : HasDerivAt
      (fun v : ℝ => (Real.exp (-v / 2) - Real.exp (v / 2)) / 2)
      (-(Real.exp (-u / 2) + Real.exp (u / 2)) / 4) u := by
    convert ((((hasDerivAt_id u).neg.div_const 2).exp).sub
      (((hasDerivAt_id u).div_const 2).exp)).div_const 2 using 1 <;>
      first | rfl | (dsimp; ring)
  have heq : (fun v : ℝ => thetaB v - thetaB (-v)) =
      (fun v : ℝ => (Real.exp (-v / 2) - Real.exp (v / 2)) / 2) :=
    funext thetaB_reflection
  change HasDerivAt (fun v : ℝ => thetaB v - thetaB (-v)) _ u at hl
  rw [heq] at hl
  have h := hl.unique hr
  linarith

/-- Real evenness of the infinite density series, derived by twice
differentiating the established theta reflection identity. -/
theorem thetaPhi_neg (u : ℝ) : thetaPhi (-u) = thetaPhi u := by
  have hl := (thetaBPrime_hasDerivAt_series u).add
    ((thetaBPrime_hasDerivAt_series (-u)).comp u (hasDerivAt_id u).neg)
  have hr : HasDerivAt
      (fun v : ℝ => -(Real.exp (-v / 2) + Real.exp (v / 2)) / 4)
      ((Real.exp (-u / 2) - Real.exp (u / 2)) / 8) u := by
    convert (((((hasDerivAt_id u).neg.div_const 2).exp).add
      (((hasDerivAt_id u).div_const 2).exp)).neg).div_const 4 using 1 <;>
      first | rfl | (dsimp; ring)
  have heq : (fun v : ℝ => thetaBPrime v + thetaBPrime (-v)) =
      (fun v : ℝ => -(Real.exp (-v / 2) + Real.exp (v / 2)) / 4) :=
    funext thetaBPrime_reflection_all
  change HasDerivAt (fun v : ℝ => thetaBPrime v + thetaBPrime (-v)) _ u at hl
  rw [heq] at hl
  have h := hl.unique hr
  have hreflection := thetaB_reflection u
  linarith

theorem thetaPhi_abs (u : ℝ) : thetaPhi |u| = thetaPhi u := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu, thetaPhi_neg]

/-- The paper's even-extension definition equals the same convergent series
on the entire real axis, not just the defining nonnegative half-line. -/
theorem thetaDensity_eq_twice_thetaPhi (u : ℝ) :
    thetaDensity u = 2 * thetaPhi u := by
  rw [thetaDensity, thetaPhi_abs]

theorem complexThetaDensity_ofReal (u : ℝ) :
    complexThetaDensity (u : ℂ) = (thetaDensity u : ℂ) := by
  rw [complexThetaDensity_eq_twice_thetaPhi, thetaDensity_eq_twice_thetaPhi]
  push_cast
  rfl

theorem complexThetaDensity_even_real (u : ℝ) :
    complexThetaDensity ((-u : ℝ) : ℂ) = complexThetaDensity (u : ℂ) := by
  simp only [complexThetaDensity_ofReal, thetaDensity_neg]

theorem complexThetaDensity_im_real (u : ℝ) :
    (complexThetaDensity (u : ℂ)).im = 0 := by
  rw [complexThetaDensity_ofReal]
  rfl

theorem complexThetaDensity_re_pos (u : ℝ) :
    0 < (complexThetaDensity (u : ℂ)).re := by
  rw [complexThetaDensity_ofReal]
  exact thetaDensity_pos u

end ThetaTrial.Paper
