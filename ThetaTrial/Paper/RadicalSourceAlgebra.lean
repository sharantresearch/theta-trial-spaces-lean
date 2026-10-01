import ThetaTrial.Paper.RadicalSource
import ThetaTrial.Paper.TrialFourier

/-! Complex linear closure of the source class used by the full
explicit formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Polynomial
open scoped Topology ContDiff

namespace ThetaTrial.Paper.RadicalSource

theorem weighted_norm_add_integrable {F G : ℝ → ℂ} (hF : Continuous F)
    (hG : Continuous G) (R : ℝ)
    (hfi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖F u‖))
    (hgi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖G u‖)) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖(F + G) u‖) := by
  apply (hfi.add hgi).mono'
    (((by fun_prop : Continuous (fun u : ℝ => Real.exp (R * |u|))).mul
      (hF.add hG).norm).aestronglyMeasurable)
  filter_upwards [] with u
  change ‖Real.exp (R * |u|) * ‖F u + G u‖‖ ≤
    Real.exp (R * |u|) * ‖F u‖ + Real.exp (R * |u|) * ‖G u‖
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  simpa only [Pi.add_apply, mul_add] using!
    mul_le_mul_of_nonneg_left (norm_add_le (F u) (G u)) (Real.exp_pos _).le

theorem RegularSource.zero : RegularSource (0 : ℝ → ℂ) := by
  refine ⟨contDiff_const, ?_, ?_, ?_, ?_⟩
  · intro R
    simp
  · intro R
    simp
  · intro R
    simp
  · intro R
    refine ⟨1, by norm_num, ?_⟩
    intro u
    simp only [Pi.zero_apply, norm_zero, one_mul]
    exact (Real.exp_pos _).le

theorem RegularSource.add {F G : ℝ → ℂ} (hF : RegularSource F)
    (hG : RegularSource G) : RegularSource (F + G) := by
  have hdF : Differentiable ℝ F := hF.smooth.differentiable (by norm_num)
  have hdG : Differentiable ℝ G := hG.smooth.differentiable (by norm_num)
  have hd2F : Differentiable ℝ (deriv F) := hF.smooth.differentiable_deriv_two
  have hd2G : Differentiable ℝ (deriv G) := hG.smooth.differentiable_deriv_two
  have hc2F : Continuous (deriv (deriv F)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hF.smooth.continuous_iteratedDeriv 2 (by norm_num)
  have hc2G : Continuous (deriv (deriv G)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hG.smooth.continuous_iteratedDeriv 2 (by norm_num)
  have hder : deriv (F + G) = deriv F + deriv G :=
    funext (fun u => deriv_add (hdF u) (hdG u))
  have hder2 : deriv (deriv (F + G)) = deriv (deriv F) + deriv (deriv G) := by
    rw [hder]
    exact funext (fun u => deriv_add (hd2F u) (hd2G u))
  refine ⟨hF.smooth.add hG.smooth, ?_, ?_, ?_, ?_⟩
  · intro R
    exact weighted_norm_add_integrable hF.smooth.continuous hG.smooth.continuous R
      (hF.weight0 R) (hG.weight0 R)
  · intro R
    rw [hder]
    exact weighted_norm_add_integrable hd2F.continuous hd2G.continuous R
      (hF.weight1 R) (hG.weight1 R)
  · intro R
    rw [hder2]
    exact weighted_norm_add_integrable hc2F hc2G R (hF.weight2 R) (hG.weight2 R)
  · intro R
    obtain ⟨M, hM, hbF⟩ := hF.exponential R
    obtain ⟨N, hN, hbG⟩ := hG.exponential R
    refine ⟨M + N, add_pos hM hN, ?_⟩
    intro u
    exact (norm_add_le _ _).trans (by
      simpa only [add_mul] using add_le_add (hbF u) (hbG u))

theorem weighted_norm_const_mul_integrable {F : ℝ → ℂ} (c : ℂ) (R : ℝ)
    (hfi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖F u‖)) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖c * F u‖) := by
  simpa only [norm_mul, mul_assoc, mul_left_comm] using hfi.const_mul ‖c‖

theorem RegularSource.const_mul {F : ℝ → ℂ} (hF : RegularSource F) (c : ℂ) :
    RegularSource (fun u => c * F u) := by
  refine ⟨contDiff_const.mul hF.smooth, ?_, ?_, ?_, ?_⟩
  · intro R
    exact weighted_norm_const_mul_integrable c R (hF.weight0 R)
  · intro R
    rw [deriv_const_mul_field']
    exact weighted_norm_const_mul_integrable c R (hF.weight1 R)
  · intro R
    rw [deriv_const_mul_field', deriv_const_mul_field']
    exact weighted_norm_const_mul_integrable c R (hF.weight2 R)
  · intro R
    obtain ⟨M, hM, hb⟩ := hF.exponential R
    refine ⟨‖c‖ * M + 1, by positivity, ?_⟩
    intro u
    rw [norm_mul]
    calc
      _ ≤ ‖c‖ * (M * Real.exp (-(R * |u|))) :=
        mul_le_mul_of_nonneg_left (hb u) (norm_nonneg _)
      _ ≤ (‖c‖ * M + 1) * Real.exp (-(R * |u|)) := by
        nlinarith [Real.exp_pos (-(R * |u|))]

theorem RegularSource.smul {F : ℝ → ℂ} (hF : RegularSource F) (c : ℂ) :
    RegularSource (c • F) := by
  simpa only [Pi.smul_def, smul_eq_mul] using hF.const_mul c

theorem RegularSource.neg {F : ℝ → ℂ} (hF : RegularSource F) : RegularSource (-F) := by
  simpa only [neg_one_mul, Pi.neg_apply] using! hF.const_mul (-1)

theorem RegularSource.sub {F G : ℝ → ℂ} (hF : RegularSource F)
    (hG : RegularSource G) : RegularSource (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem RegularSource.finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ s, RegularSource (F i)) : RegularSource (fun u => ∑ i ∈ s, F i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! RegularSource.zero
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have hiF := hF i (Finset.mem_insert_self i s)
    simpa only [Finset.sum_insert hi, Pi.add_apply] using! hiF.add hs

/-- Each finite summand already belongs to the source class, so no separate
smoothness hypothesis is needed. -/
theorem regularSource_polynomialDerivative {F : ℝ → ℂ}
    (hF : ∀ j : ℕ, RegularSource (iteratedDeriv j F)) (P : ℂ[X]) :
    RegularSource (polynomialDerivative P F) := by
  have hs := RegularSource.finset_sum P.support
    (fun j u => (P.coeff j * (-I) ^ j) * iteratedDeriv j F u)
    (fun j _hj => (hF j).const_mul (P.coeff j * (-I) ^ j))
  unfold polynomialDerivative
  simp_rw [differentialOperator_iterate]
  simpa only [mul_assoc] using! hs

end ThetaTrial.Paper.RadicalSource
