/- The representation of xi as an integral of the theta density `Φ`. -/
import ThetaTrial.ThetaSeries.Weighted
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology

namespace ThetaTrial.ThetaSeries

theorem hasDerivAt_cosh_real_mul (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.cosh ((v : ℂ) * z))
      (z * Complex.sinh ((u : ℂ) * z)) u := by
  have hc := (Complex.hasDerivAt_cosh ((u : ℂ) * z)).comp (u : ℂ)
    ((hasDerivAt_id (u : ℂ)).mul_const z)
  convert hc.comp_ofReal using 1 <;> first | rfl | ring

theorem hasDerivAt_z_sinh_real_mul (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => z * Complex.sinh ((v : ℂ) * z))
      (z ^ 2 * Complex.cosh ((u : ℂ) * z)) u := by
  have hc := (Complex.hasDerivAt_sinh ((u : ℂ) * z)).comp (u : ℂ)
    ((hasDerivAt_id (u : ℂ)).mul_const z)
  convert hc.comp_ofReal.const_mul z using 1 <;> first | rfl | ring

theorem thetaPhi_cosh_integrable (z : ℂ) :
    IntegrableOn (fun u : ℝ => (thetaPhi u : ℂ) * Complex.cosh ((u : ℂ) * z)) (Ioi 0) :=
  thetaPhi_mul_integrable ‖z‖ (by fun_prop) (fun _ hu => norm_cosh_mul_ofReal_le z hu)

theorem thetaBPrime_sinh_integrable (z : ℂ) :
    IntegrableOn (fun u : ℝ => (thetaBPrime u : ℂ) * Complex.sinh ((u : ℂ) * z)) (Ioi 0) :=
  thetaBPrime_mul_integrable ‖z‖ (by fun_prop) (fun _ hu => norm_sinh_mul_ofReal_le z hu)

theorem thetaBPrime_cosh_boundary_zero (z : ℂ) :
    Tendsto (fun u : ℝ => (thetaBPrime u : ℂ) * Complex.cosh ((u : ℂ) * z))
      atTop (𝓝 0) :=
  thetaBPrime_mul_tendsto ‖z‖ (fun _ hu => norm_cosh_mul_ofReal_le z hu)

theorem thetaB_sinh_boundary_zero (z : ℂ) :
    Tendsto (fun u : ℝ => (thetaB u : ℂ) * Complex.sinh ((u : ℂ) * z))
      atTop (𝓝 0) :=
  thetaB_mul_tendsto ‖z‖ (fun _ hu => norm_sinh_mul_ofReal_le z hu)

/-- The two improper integrations by parts, including their boundary terms. -/
theorem thetaPhi_integral_eq (z : ℂ) :
    2 * (∫ u : ℝ in Ioi 0, (thetaPhi u : ℂ) * Complex.cosh ((u : ℂ) * z)) =
      1 / 4 + (z ^ 2 - 1 / 4) *
        (∫ u : ℝ in Ioi 0, (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z)) := by
  have hB := thetaB_cosh_integrable z
  have hP := thetaPhi_cosh_integrable z
  have hS := thetaBPrime_sinh_integrable z
  have hC : IntegrableOn (fun u : ℝ =>
      (thetaBPrime u : ℂ) * (z * Complex.sinh ((u : ℂ) * z))) (Ioi 0) := by
    have hh : IntegrableOn (fun u : ℝ =>
        z * ((thetaBPrime u : ℂ) * Complex.sinh ((u : ℂ) * z))) (Ioi 0) := hS.const_mul z
    exact hh.congr_fun (fun _ _ => by dsimp only; ring) measurableSet_Ioi
  have hD : IntegrableOn (fun u : ℝ =>
      ((thetaB u / 4 + 2 * thetaPhi u : ℝ) : ℂ) *
        Complex.cosh ((u : ℂ) * z)) (Ioi 0) := by
    have hh : IntegrableOn (fun u : ℝ =>
        (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z) / 4 +
        2 * ((thetaPhi u : ℂ) * Complex.cosh ((u : ℂ) * z))) (Ioi 0) :=
      (hB.div_const (4 : ℂ)).add (hP.const_mul (2 : ℂ))
    exact hh.congr_fun (fun _ _ => by dsimp only; push_cast; ring) measurableSet_Ioi
  have hE : IntegrableOn (fun u : ℝ =>
      (thetaB u : ℂ) * (z ^ 2 * Complex.cosh ((u : ℂ) * z))) (Ioi 0) := by
    have hh : IntegrableOn (fun u : ℝ =>
        z ^ 2 * ((thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z))) (Ioi 0) := hB.const_mul (z ^ 2)
    exact hh.congr_fun (fun _ _ => by dsimp only; ring) measurableSet_Ioi
  have hb0 : Tendsto (fun u : ℝ =>
      (thetaBPrime u : ℂ) * Complex.cosh ((u : ℂ) * z)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(1 / 4 : ℂ))) := by
    have hc : ContinuousAt (fun u : ℝ =>
        (thetaBPrime u : ℂ) * Complex.cosh ((u : ℂ) * z)) 0 :=
      ((thetaBPrime_hasDerivAt_series 0).ofReal_comp.continuousAt).mul (by fun_prop)
    simpa [thetaBPrime_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hb1 : Tendsto (fun u : ℝ =>
      (thetaB u : ℂ) * (z * Complex.sinh ((u : ℂ) * z))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun u : ℝ =>
        (thetaB u : ℂ) * (z * Complex.sinh ((u : ℂ) * z))) 0 :=
      ((thetaB_hasDerivAt_series 0).ofReal_comp.continuousAt).mul (by fun_prop)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hb_atTop : Tendsto (fun u : ℝ =>
      (thetaB u : ℂ) * (z * Complex.sinh ((u : ℂ) * z))) atTop (𝓝 0) := by
    have hh := (thetaB_sinh_boundary_zero z).const_mul z
    convert hh using 1 <;> first | simp | (funext u; ring)
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => (thetaBPrime u : ℂ))
    (u' := fun u : ℝ => ((thetaB u / 4 + 2 * thetaPhi u : ℝ) : ℂ))
    (v := fun u : ℝ => Complex.cosh ((u : ℂ) * z))
    (v' := fun u : ℝ => z * Complex.sinh ((u : ℂ) * z))
    (fun u _ => (thetaBPrime_hasDerivAt_series u).ofReal_comp)
    (fun u _ => hasDerivAt_cosh_real_mul z u) hC hD hb0 (thetaBPrime_cosh_boundary_zero z)
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => (thetaB u : ℂ))
    (u' := fun u : ℝ => (thetaBPrime u : ℂ))
    (v := fun u : ℝ => z * Complex.sinh ((u : ℂ) * z))
    (v' := fun u : ℝ => z ^ 2 * Complex.cosh ((u : ℂ) * z))
    (fun u _ => (thetaB_hasDerivAt_series u).ofReal_comp)
    (fun u _ => hasDerivAt_z_sinh_real_mul z u) hE hC hb1 hb_atTop
  have hDi : (∫ u : ℝ in Ioi 0,
      ((thetaB u / 4 + 2 * thetaPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * z)) =
      (∫ u : ℝ in Ioi 0, (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z)) / 4 +
        2 * (∫ u : ℝ in Ioi 0, (thetaPhi u : ℂ) * Complex.cosh ((u : ℂ) * z)) := by
    calc
      _ = ∫ u : ℝ in Ioi 0,
          (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z) / 4 +
          2 * ((thetaPhi u : ℂ) * Complex.cosh ((u : ℂ) * z)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        dsimp only
        push_cast
        ring
      _ = _ := by
        rw [integral_add (hB.div_const (4 : ℂ)) (hP.const_mul (2 : ℂ)),
          integral_div, integral_const_mul]
  have hEi : (∫ u : ℝ in Ioi 0,
      (thetaB u : ℂ) * (z ^ 2 * Complex.cosh ((u : ℂ) * z))) =
      z ^ 2 * (∫ u : ℝ in Ioi 0, (thetaB u : ℂ) * Complex.cosh ((u : ℂ) * z)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    ring
  rw [hDi] at hfirst
  rw [hEi] at hsecond
  linear_combination hfirst - hsecond

/-- The horizontal-centered xi function has the exact positive-Phi representation. -/
theorem xi_centered_eq_thetaPhi (z : ℂ) :
    ThetaTrial.xi (1 / 2 + z) =
      4 * ∫ u : ℝ in Ioi 0, (thetaPhi u : ℂ) * Complex.cosh ((u : ℂ) * z) := by
  rw [xi_centered_eq_thetaB]
  linear_combination -2 * thetaPhi_integral_eq z

end ThetaTrial.ThetaSeries
