/-
The Mellin representation of xi in the logarithmic coordinate, before
integration by parts. Convergence follows from Mathlib's Mellin construction
of the completed zeta function.
-/
import ThetaTrial.ThetaSeries.Mellin

noncomputable section

open Complex MeasureTheory Set

namespace ThetaTrial.ThetaSeries

/-- Auxiliary kernel for the two integrations by parts, using the theta tail. -/
def thetaB (u : ℝ) : ℝ := Real.exp (u / 2) * thetaTail (Real.exp (2 * u))

def thetaExpIntegrand (w : ℂ) (u : ℝ) : ℂ :=
  (Real.exp (2 * u) : ℂ) ^ w * ((thetaKernel (Real.exp (2 * u)) : ℂ) - 1)

theorem ofReal_exp_cpow (a : ℝ) (w : ℂ) :
    (Real.exp a : ℂ) ^ w = Complex.exp ((a : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero a)),
    ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp]

theorem thetaExpIntegrand_eq_jacobian (w : ℂ) (u : ℝ) :
    thetaExpIntegrand w u = Real.exp (2 * u) •
      ((Real.exp (2 * u) : ℂ) ^ (w - 1) *
        ((thetaKernel (Real.exp (2 * u)) : ℂ) - 1)) := by
  rw [thetaExpIntegrand, Complex.real_smul, ← mul_assoc]
  have he : (Real.exp (2 * u) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hpow : (Real.exp (2 * u) : ℂ) ^ w =
      (Real.exp (2 * u) : ℂ) * (Real.exp (2 * u) : ℂ) ^ (w - 1) := by
    calc
      _ = (Real.exp (2 * u) : ℂ) ^ ((1 : ℂ) + (w - 1)) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ he, Complex.cpow_one]
  rw [hpow]

theorem thetaExpIntegrand_integrable (w : ℂ) :
    IntegrableOn (thetaExpIntegrand w) (Ioi 0) := by
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (w - 1) * ((thetaKernel t : ℂ) - 1)
  have hg : IntegrableOn g (Ioi (Real.exp 0)) := by
    simpa [g] using upperMellin_integrable w
  have hexp := (integrableOn_comp_exp_Ioi g 0).mpr hg
  have hscale : IntegrableOn (fun u : ℝ => Real.exp (2 * u) • g (Real.exp (2 * u)))
      (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp u • g (Real.exp u)) 0 (show (0 : ℝ) < 2 by norm_num)).mpr
    simpa using hexp
  exact hscale.congr_fun (fun u _ => (thetaExpIntegrand_eq_jacobian w u).symm)
    measurableSet_Ioi

theorem upperMellin_eq_exp_integral (w : ℂ) :
    upperMellin w = 2 * ∫ u : ℝ in Ioi 0, thetaExpIntegrand w u := by
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (w - 1) * ((thetaKernel t : ℂ) - 1)
  have hexp := integral_comp_exp_Ioi g 0
  have hscale := integral_comp_mul_left_Ioi'
    (fun u : ℝ => Real.exp u • g (Real.exp u)) 0 (show (0 : ℝ) < 2 by norm_num)
  calc
    upperMellin w = ∫ t : ℝ in Ioi (Real.exp 0), g t := by
      simpa [g] using upperMellin_eq_integral w
    _ = ∫ u : ℝ in Ioi 0, Real.exp u • g (Real.exp u) := hexp.symm
    _ = (2 : ℝ) • ∫ u : ℝ in Ioi 0, Real.exp (2 * u) • g (Real.exp (2 * u)) := by
      simpa using hscale.symm
    _ = _ := by
      rw [Complex.real_smul]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      exact (thetaExpIntegrand_eq_jacobian w u).symm

theorem thetaExpIntegrand_pair (z : ℂ) (u : ℝ) :
    thetaExpIntegrand (1 / 4 + z / 2) u + thetaExpIntegrand (1 / 4 - z / 2) u =
      4 * ((thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z)) := by
  simp only [thetaExpIntegrand]
  rw [ofReal_exp_cpow, ofReal_exp_cpow]
  simp only [thetaB, thetaTail,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_exp]
  have hp : (2 * (u : ℂ)) * (1 / 4 + z / 2) = (u : ℂ) / 2 + (u : ℂ) * z := by ring
  have hm : (2 * (u : ℂ)) * (1 / 4 - z / 2) = (u : ℂ) / 2 + -((u : ℂ) * z) := by ring
  rw [hp, hm, Complex.exp_add, Complex.exp_add, Complex.cosh]
  ring

/-- Absolute integrability before either integration by parts. -/
theorem thetaB_cosh_integrable (z : ℂ) :
    IntegrableOn (fun u : ℝ => (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z)) (Ioi 0) := by
  have hi : IntegrableOn (fun u =>
      (thetaExpIntegrand (1 / 4 + z / 2) u + thetaExpIntegrand (1 / 4 - z / 2) u) /
        (4 : ℂ)) (Ioi 0) := ((thetaExpIntegrand_integrable (1 / 4 + z / 2)).add
    (thetaExpIntegrand_integrable (1 / 4 - z / 2))).div_const (4 : ℂ)
  exact hi.congr_fun (fun u _ => by dsimp only; rw [thetaExpIntegrand_pair]; ring)
    measurableSet_Ioi

theorem upperMellin_pair_eq_thetaB (z : ℂ) :
    upperMellin (1 / 4 + z / 2) + upperMellin (1 / 4 - z / 2) =
      8 * ∫ u : ℝ in Ioi 0, (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z) := by
  rw [upperMellin_eq_exp_integral, upperMellin_eq_exp_integral, ← mul_add,
    ← integral_add (thetaExpIntegrand_integrable (1 / 4 + z / 2))
      (thetaExpIntegrand_integrable (1 / 4 - z / 2))]
  simp_rw [thetaExpIntegrand_pair]
  rw [integral_const_mul]
  ring

/-- Horizontal-centered xi and its convergent pre-IBP theta integral. -/
theorem xi_centered_eq_thetaB (z : ℂ) :
    ThetaTrial.xi (1 / 2 + z) = 1 / 2 + 2 * (z ^ 2 - 1 / 4) *
      ∫ u : ℝ in Ioi 0, (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z) := by
  rw [xi_centered_eq_upperMellin, upperMellin_pair_eq_thetaB]
  ring

end ThetaTrial.ThetaSeries
