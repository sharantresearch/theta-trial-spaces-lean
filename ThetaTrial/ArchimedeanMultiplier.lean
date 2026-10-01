import ThetaTrial.Imported.Zeta23.GammaFacts.StirlingVert
import Mathlib.Topology.Order.Compact

/-!
# The archimedean multiplier and logarithmic growth

The multiplier `Re ψ(1/4 + ir/2) - log π` is `2π` times the function `mu` from the
imported analytic library. The global bound includes the compact interval
around zero, where the vertical Stirling estimate alone does not apply.
-/

namespace ThetaTrial.ArchimedeanMultiplier

open scoped ContDiff

noncomputable def multiplier (t : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re - Real.log Real.pi

theorem multiplier_eq_two_pi_mu (t : ℝ) :
    multiplier t = (2 * Real.pi) * Zeta23.mu t := by
  unfold multiplier Zeta23.mu
  field_simp [Real.pi_ne_zero]

theorem multiplier_smooth : ContDiff ℝ ∞ multiplier := by
  have he : multiplier = fun t => (2 * Real.pi) * Zeta23.mu t := by
    funext t
    exact multiplier_eq_two_pi_mu t
  rw [he]
  exact contDiff_const.mul Zeta23.mu_smooth

theorem multiplier_continuous : Continuous multiplier := multiplier_smooth.continuous

theorem multiplier_large_bound (t : ℝ) (ht : 2 ≤ |t|) :
    |multiplier t| ≤ Real.log (2 + |t|) + |Real.log Real.pi| + 20 := by
  have ht2 : (1 / 2 : ℝ) ≤ |t / 2| := by
    rw [abs_div]
    norm_num
    linarith
  have hst := Zeta23.StirlingVert.re_digamma_stirling'
    (show (0 : ℝ) < 1 / 4 by norm_num) (show (1 / 4 : ℝ) ≤ 1 by norm_num) ht2
  have he : ((1 / 4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) =
      1 / 4 + Complex.I * (t : ℂ) / 2 := by push_cast; ring
  rw [he] at hst
  have hsq : 1 ≤ (t / 2) ^ 2 := by
    have hab : (1 : ℝ) ≤ |t / 2| := by rw [abs_div]; norm_num; linarith
    nlinarith [sq_abs (t / 2)]
  have hrem : 5 / (t / 2) ^ 2 ≤ (20 : ℝ) := by
    apply (div_le_iff₀ (show 0 < (t / 2) ^ 2 by linarith)).mpr
    linarith
  have hlogpos : 0 ≤ Real.log (|t / 2|) := by
    apply Real.log_nonneg
    rw [abs_div]
    norm_num
    linarith
  have hlog : Real.log (|t / 2|) ≤ Real.log (2 + |t|) := by
    apply Real.log_le_log
    · rw [abs_div]
      positivity
    · rw [abs_div]
      norm_num
      linarith
  calc
    _ = |((Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re -
        Real.log (|t / 2|)) + (Real.log (|t / 2|) - Real.log Real.pi)| := by
      unfold multiplier
      congr 1
      ring
    _ ≤ |(Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re -
        Real.log (|t / 2|)| + |Real.log (|t / 2|) - Real.log Real.pi| := abs_add_le _ _
    _ ≤ 20 + (Real.log (|t / 2|) + |Real.log Real.pi|) := by
      apply add_le_add (hst.trans hrem)
      simpa only [abs_of_nonneg hlogpos] using abs_sub (Real.log (|t / 2|)) (Real.log Real.pi)
    _ ≤ _ := by linarith

end ThetaTrial.ArchimedeanMultiplier
