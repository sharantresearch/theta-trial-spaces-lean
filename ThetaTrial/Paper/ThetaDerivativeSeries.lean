import ThetaTrial.Paper.TrialFourier
import ThetaTrial.Paper.RadicalApproximation
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! All orders of termwise differentiation of the full theta series.
Normal convergence is differentiated locally uniformly, preserving the
infinite mode sum before restriction to the real axis. -/

noncomputable section
open Complex MeasureTheory Set Filter Polynomial
open scoped Topology

namespace ThetaTrial.Paper

theorem complexThetaMode_iterated_analytic (j n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv j (complexThetaMode n)) univ := by
  induction j with
  | zero =>
    simpa using (complexThetaMode_differentiable n).differentiableOn.analyticOnNhd isOpen_univ
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem complexThetaDensity_hasSum_iteratedDeriv (j : ℕ) {z : ℂ}
    (hz : z ∈ thetaStrip) :
    HasSum (fun n => iteratedDeriv j (complexThetaMode n) z)
      (iteratedDeriv j complexThetaDensity z) := by
  obtain ⟨U, hU, hzU, M, hM, hbound⟩ := complexThetaDensity_local_majorant
    (exp_two_re_pos_of_mem_thetaStrip hz)
  have hc : TendstoLocallyUniformlyOn
      (fun s : Finset ℕ => fun w => ∑ n ∈ s, complexThetaMode n w)
      complexThetaDensity atTop U :=
    (tendstoUniformlyOn_tsum hM hbound).tendstoLocallyUniformlyOn
  have hall (k : ℕ) : TendstoLocallyUniformlyOn
      (fun s : Finset ℕ => iteratedDeriv k (fun w => ∑ n ∈ s, complexThetaMode n w))
      (iteratedDeriv k complexThetaDensity) atTop U := by
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      have hdiff : ∀ s : Finset ℕ,
          DifferentiableOn ℂ (iteratedDeriv k (fun w => ∑ n ∈ s, complexThetaMode n w)) U := by
        intro s
        have hs : iteratedDeriv k (fun v => ∑ n ∈ s, complexThetaMode n v) =
            fun w => ∑ n ∈ s, iteratedDeriv k (complexThetaMode n) w := by
          funext w
          exact iteratedDeriv_fun_sum (fun n hn =>
            ((complexThetaMode_differentiable n).analyticAt w).contDiffAt)
        rw [hs]
        exact DifferentiableOn.fun_sum (fun n hn =>
          fun w hw => (complexThetaMode_iterated_analytic k n w (mem_univ w)).differentiableAt.differentiableWithinAt)
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (Eventually.of_forall hdiff) hU
  rw [HasSum, SummationFilter.unconditional_filter]
  convert (hall j).tendsto_at hzU using 1
  funext s
  exact (iteratedDeriv_fun_sum (fun n hn =>
    ((complexThetaMode_differentiable n).analyticAt z).contDiffAt)).symm

theorem thetaMode_real_iteratedDeriv (j n : ℕ) (u : ℝ) :
    iteratedDeriv j (fun v : ℝ => complexThetaMode n (v : ℂ)) u =
      iteratedDeriv j (complexThetaMode n) (u : ℂ) := by
  induction j generalizing u with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, funext ih]
    exact ((complexThetaMode_iterated_analytic j n (u : ℂ) (mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal).deriv

theorem thetaDensity_hasSum_real_iteratedDeriv (j : ℕ) (u : ℝ) :
    HasSum (fun n : ℕ => iteratedDeriv j (fun v => (paperThetaMode n v : ℂ)) u)
      (iteratedDeriv j (fun v => (thetaDensity v : ℂ)) u) := by
  have hm (n : ℕ) : (fun v : ℝ => (paperThetaMode n v : ℂ)) =
      (fun v : ℝ => complexThetaMode n (v : ℂ)) := by
    funext v
    exact paperThetaMode_eq_complexThetaMode n v
  simp_rw [hm, thetaMode_real_iteratedDeriv]
  rw [RadicalApproximation.theta_real_iteratedDeriv]
  exact complexThetaDensity_hasSum_iteratedDeriv j
    (RadicalApproximation.real_mem_thetaStrip u)

theorem thetaDensity_hasSum_polynomialDerivative (P : ℂ[X]) (u : ℝ) :
    HasSum (fun n : ℕ => polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u)
      (polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u) := by
  unfold polynomialDerivative
  simp_rw [differentialOperator_iterate]
  exact hasSum_sum (fun j hj =>
    ((thetaDensity_hasSum_real_iteratedDeriv j u).mul_left ((-I)^j)).mul_left (P.coeff j))

/-- Theta sum, all complex polynomial coefficients and all real coordinates. -/
theorem polynomialDerivative_thetaDensity_eq_tsum (P : ℂ[X]) (u : ℝ) :
    polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u =
      ∑' n : ℕ, polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u :=
  (thetaDensity_hasSum_polynomialDerivative P u).tsum_eq.symm

end ThetaTrial.Paper

