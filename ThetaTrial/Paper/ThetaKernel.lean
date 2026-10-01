import ThetaTrial.Paper.ThetaFourier
import ThetaTrial.Paper.ThetaStripDecay
import ThetaTrial.ThetaSeries.XiComparison

/-! Lemma `pre:theta`: normalization, convergence and holomorphy of the theta
series, its Fourier transform, the derivative estimates, and an interval on
which `Xi` does not vanish. -/

noncomputable section
open Complex Set Filter Metric
open scoped Topology

namespace ThetaTrial.Paper

theorem xiFunction_zero_re_pos : 0 < (xiFunction 0).re := by
  have h := ThetaTrial.ThetaSeries.two_xi_half_re_ge_76_div_77
  simp only [xiFunction, mul_zero, add_zero]
  linarith

theorem xiFunction_zero_im : (xiFunction 0).im = 0 := by
  rw [← paperFourier_theta 0]
  simp only [paperFourier, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal]
  rfl

theorem xiFunction_continuous : Continuous xiFunction := by
  have he : xiFunction = ThetaTrial.Xi := funext xiFunction_eq_weilFormula
  rw [he]
  exact ThetaTrial.Xi_entire.continuous

theorem xiFunction_fixed_lower_interval :
    ∃ d > 0, ∃ c > 0, ∀ r : ℝ, |r| ≤ d → c ≤ ‖xiFunction (r : ℂ)‖ := by
  let c := (xiFunction 0).re / 2
  have hc : 0 < c := div_pos xiFunction_zero_re_pos (by norm_num)
  have hcont : Continuous (fun r : ℝ => (xiFunction (r : ℂ)).re) := by
    exact Complex.continuous_re.comp (xiFunction_continuous.comp Complex.continuous_ofReal)
  have hnh : (fun r : ℝ => (xiFunction (r : ℂ)).re) ⁻¹' Ioi c ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt (Ioi_mem_nhds (by
      simp only [Complex.ofReal_zero]
      dsimp [c]
      linarith [xiFunction_zero_re_pos]))
  obtain ⟨d, hd, hsub⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨d / 2, by linarith, c, hc, ?_⟩
  intro r hr
  have hrball : r ∈ ball (0 : ℝ) d := by
    simp only [mem_ball, Real.dist_eq, sub_zero]
    linarith
  exact (hsub hrball).le.trans (Complex.re_le_norm _)

theorem theta_all_substrip_derivative_decay {b : ℝ} (hb : b < Real.pi / 4) :
    ∃ c > 0, ∀ j : ℕ, ∃ C > 0, ∀ z : ℂ, |z.im| ≤ b →
      ‖iteratedDeriv j complexThetaDensity z‖ ≤
        C * Real.exp (((9 / 2 : ℝ) + 2 * (j : ℝ)) * |z.re|) *
          Real.exp (-c * Real.exp (2 * |z.re|)) := by
  by_cases hb0 : 0 ≤ b
  · exact complexThetaDensity_iteratedDeriv_closed_strip_decay hb0 hb
  · refine ⟨1, by norm_num, fun j => ⟨1, by norm_num, ?_⟩⟩
    intro z hz
    exact False.elim (hb0 ((abs_nonneg z.im).trans hz))

/-- Full content of the paper's preliminary theta lemma.
The last decay assertion is slightly stronger: all real parts are allowed. -/
def ThetaKernelStatement : Prop :=
  (∀ u : ℝ, 0 < thetaDensity u) ∧
  (∀ u : ℝ, thetaDensity (-u) = thetaDensity u) ∧
  (∀ u : ℝ, complexThetaDensity (u : ℂ) = (thetaDensity u : ℂ)) ∧
  (∀ z ∈ thetaStrip, Summable (fun n : ℕ => complexThetaMode n z)) ∧
  DifferentiableOn ℂ complexThetaDensity thetaStrip ∧
  (∀ z : ℂ, paperFourier (fun u => (thetaDensity u : ℂ)) z = xiFunction z) ∧
  (∀ b : ℝ, b < Real.pi / 4 → ∃ c > 0, ∀ j : ℕ, ∃ C > 0,
    ∀ z : ℂ, |z.im| ≤ b →
      ‖iteratedDeriv j complexThetaDensity z‖ ≤
        C * Real.exp (((9 / 2 : ℝ) + 2 * (j : ℝ)) * |z.re|) *
          Real.exp (-c * Real.exp (2 * |z.re|))) ∧
  0 < (xiFunction 0).re ∧
  (xiFunction 0).im = 0 ∧
  (∃ d > 0, ∃ c > 0, ∀ r : ℝ, |r| ≤ d → c ≤ ‖xiFunction (r : ℂ)‖)

theorem theta_kernel : ThetaKernelStatement := by
  exact ⟨thetaDensity_pos, thetaDensity_neg, complexThetaDensity_ofReal,
    fun _ hz => complexThetaMode_summable_strip hz,
    complexThetaDensity_differentiableOn_strip, paperFourier_theta,
    fun _ hb => theta_all_substrip_derivative_decay hb,
    xiFunction_zero_re_pos, xiFunction_zero_im, xiFunction_fixed_lower_interval⟩

end ThetaTrial.Paper
