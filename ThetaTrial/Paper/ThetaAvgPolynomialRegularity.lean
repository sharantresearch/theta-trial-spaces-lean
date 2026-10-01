import ThetaTrial.Paper.ThetaAvgTail
import ThetaTrial.Paper.TrialFourier
import ThetaTrial.Paper.RadicalSource

/-! Regularity and integrability of every polynomial derivative of the
shifted theta average, with arbitrary complex coefficients. -/

noncomputable section
open Complex MeasureTheory Set Filter Polynomial
open scoped Topology ContDiff

namespace ThetaTrial.Paper

theorem shiftedAverage_real_iteratedDeriv_fun {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (j : ℕ) :
    iteratedDeriv j (fun u : ℝ => shiftedAverage a (u : ℂ)) = thetaAvgTrialDerivative a j :=
  funext (shiftedAverage_real_iteratedDeriv hZ j)

theorem thetaAvgTrialDerivative_contDiff {a : ℝ} (hZ : 16 ≤ scaleZ a) (j : ℕ) :
    ContDiff ℝ ⊤ (thetaAvgTrialDerivative a j) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have hu : |(u : ℂ).im| < 1 / scaleZ a := by
    simp only [Complex.ofReal_im, abs_zero]
    exact one_div_pos.mpr (scaleZ_pos a)
  have hc : ContDiffAt ℝ ⊤ (iteratedDeriv j (shiftedAverage a)) (u : ℂ) :=
    (shiftedAverage_iteratedDeriv_analytic hZ j (u : ℂ) hu).contDiffAt.restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, thetaAvgTrialDerivative] using!
    hc.comp u Complex.ofRealCLM.contDiff.contDiffAt

theorem shiftedAverage_real_contDiff {a : ℝ} (hZ : 16 ≤ scaleZ a) :
    ContDiff ℝ ⊤ (fun u : ℝ => shiftedAverage a (u : ℂ)) := by
  simpa only [thetaAvgTrialDerivative, iteratedDeriv_zero] using! thetaAvgTrialDerivative_contDiff hZ 0

/-- The exact polynomial differential operator, in terms of contour derivatives. -/
theorem polynomialDerivative_shiftedAverage_eq {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) :
    polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)) =
      fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a j u := by
  funext u
  simp only [polynomialDerivative, differentialOperator_iterate,
    shiftedAverage_real_iteratedDeriv hZ, thetaAvgTrialDerivative, mul_assoc]

theorem polynomialDerivative_shiftedAverage_contDiff {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) :
    ContDiff ℝ ⊤ (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))) := by
  rw [polynomialDerivative_shiftedAverage_eq hZ P]
  exact ContDiff.sum (fun j _hj => contDiff_const.mul (thetaAvgTrialDerivative_contDiff hZ j))

theorem polynomialDerivative_shiftedAverage_hasDerivAt {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) (u : ℝ) :
    HasDerivAt (polynomialDerivative P (fun v : ℝ => shiftedAverage a (v : ℂ)))
      (∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + 1) u) u := by
  rw [polynomialDerivative_shiftedAverage_eq hZ P]
  exact HasDerivAt.fun_sum (fun j _hj =>
    (thetaAvgTrialDerivative_hasDerivAt hZ j u).const_mul (P.coeff j * (-I) ^ j))

theorem polynomialDerivative_shiftedAverage_deriv {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) :
    deriv (polynomialDerivative P (fun v : ℝ => shiftedAverage a (v : ℂ))) =
      fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + 1) u :=
  funext (fun u => (polynomialDerivative_shiftedAverage_hasDerivAt hZ P u).deriv)

theorem polynomialDerivative_shiftedAverage_iteratedDeriv {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) (r : ℕ) :
    iteratedDeriv r (polynomialDerivative P (fun v : ℝ => shiftedAverage a (v : ℂ))) =
      fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + r) u := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero, Nat.add_zero] using
      polynomialDerivative_shiftedAverage_eq hZ P
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have hd := HasDerivAt.fun_sum (u := P.support) (fun j _hj =>
      (thetaAvgTrialDerivative_hasDerivAt hZ (j + r) u).const_mul (P.coeff j * (-I) ^ j))
    simpa only [Nat.add_assoc] using hd.deriv

theorem thetaAvgPolynomialSum_all_weights_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (r : ℕ) (R : ℝ) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile R
      (fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + r) u)) := by
  have he : ThetaTrial.PrimeContinuity.weightedProfile R
      (fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + r) u) =
      fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) *
        ThetaTrial.PrimeContinuity.weightedProfile R (thetaAvgTrialDerivative a (j + r)) u := by
    funext u
    simp only [ThetaTrial.PrimeContinuity.weightedProfile, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  apply integrable_finsetSum
  intro j hj
  exact (thetaAvgTrialDerivative_all_weights_integrable ha hZ (j + r) R).const_mul
    (P.coeff j * (-I) ^ j)

theorem shiftedAverage_real_iteratedDeriv_all_weights_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (j : ℕ) (R : ℝ) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile R
      (iteratedDeriv j (fun u : ℝ => shiftedAverage a (u : ℂ)))) := by
  rw [shiftedAverage_real_iteratedDeriv_fun hZ j]
  exact thetaAvgTrialDerivative_all_weights_integrable ha hZ j R

theorem polynomialDerivative_shiftedAverage_iteratedDeriv_all_weights_integrable
    {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (r : ℕ) (R : ℝ) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile R
      (iteratedDeriv r (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))))) := by
  rw [polynomialDerivative_shiftedAverage_iteratedDeriv hZ P r]
  exact thetaAvgPolynomialSum_all_weights_integrable ha hZ P r R

/-- Every real exponential weight is integrable for the polynomial trial. -/
theorem polynomialDerivative_shiftedAverage_all_weights_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (R : ℝ) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile R
      (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)))) := by
  rw [polynomialDerivative_shiftedAverage_eq hZ P]
  simpa only [Nat.add_zero] using thetaAvgPolynomialSum_all_weights_integrable ha hZ P 0 R

theorem polynomialDerivative_shiftedAverage_deriv_all_weights_integrable {a : ℝ}
    (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (R : ℝ) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile R
      (deriv (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))))) := by
  rw [polynomialDerivative_shiftedAverage_deriv hZ P]
  exact thetaAvgPolynomialSum_all_weights_integrable ha hZ P 1 R

theorem polynomialDerivative_shiftedAverage_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    Integrable (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))) := by
  exact integrableOn_univ.mp (integrableOn_of_weightedProfile_one
    (polynomialDerivative_shiftedAverage_all_weights_integrable ha hZ P 1).integrableOn)

theorem polynomialDerivative_shiftedAverage_deriv_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    Integrable (deriv (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)))) := by
  exact integrableOn_univ.mp (integrableOn_of_weightedProfile_one
    (polynomialDerivative_shiftedAverage_deriv_all_weights_integrable ha hZ P 1).integrableOn)

theorem polynomialDerivative_shiftedAverage_boundedVariation {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    BoundedVariationOn (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)))
      univ := by
  have hd := (polynomialDerivative_shiftedAverage_contDiff hZ P).differentiable (by simp)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (variation_le_integral_deriv ordConnected_univ (fun u _hu => (hd u).hasDerivAt)
      (polynomialDerivative_shiftedAverage_deriv_integrable ha hZ P).integrableOn)

/-- Whole-line `L²` membership, from the integrable derivative and the BV
bound. -/
theorem polynomialDerivative_shiftedAverage_memLp_two {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    MemLp (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))) 2 volume :=
  memLp_two_of_integrable_bv (polynomialDerivative_shiftedAverage_integrable ha hZ P)
    (polynomialDerivative_shiftedAverage_boundedVariation ha hZ P)

theorem thetaAvgContourEnvelope_weighted_identity (a R u : ℝ) :
    Real.exp (R * |u|) * thetaAvgContourEnvelope a u =
      (thetaAvgContourConstant * (scaleZ a) ^ (13 / 4 : ℝ) * Real.exp (-2 * scaleZ a)) *
        ThetaTrial.ThetaSeries.doubleExpEnvelope (R + 9 / 2) (Real.exp (-2 * a)) |u| := by
  have he : Real.exp (2 * (|u| - a)) = Real.exp (-2 * a) * Real.exp (2 * |u|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaAvgContourEnvelope ThetaTrial.ThetaSeries.doubleExpEnvelope
  rw [he, Real.exp_sub]
  rw [show Real.exp (-2 * scaleZ a) /
      Real.exp (Real.exp (-2 * a) * Real.exp (2 * |u|)) =
      Real.exp (-2 * scaleZ a) *
        Real.exp (-Real.exp (-2 * a) * Real.exp (2 * |u|)) by
      simp only [neg_mul, Real.exp_neg, div_eq_mul_inv]]
  rw [add_mul, Real.exp_add]
  ring_nf

/-- Every derivative has pointwise decay at every exponential rate. -/
theorem thetaAvgTrialDerivative_exponential_bound {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (j : ℕ) (R : ℝ) :
    ∃ M > 0, ∀ u : ℝ,
      ‖thetaAvgTrialDerivative a j u‖ ≤ M * Real.exp (-(R * |u|)) := by
  obtain ⟨B, hB, henv⟩ := RadicalApproximation.doubleExpEnvelope_bounded
    (R + 9 / 2) (Real.exp_pos (-2 * a))
  let K := (j.factorial : ℝ) * (scaleZ a) ^ (2 * j) *
    (thetaAvgContourConstant * (scaleZ a) ^ (13 / 4 : ℝ) * Real.exp (-2 * scaleZ a))
  have hK : 0 ≤ K := by
    have hzpos := scaleZ_pos a
    have hcpos := thetaAvgContourConstant_pos
    dsimp [K]
    positivity
  have hc : Continuous (fun u : ℝ => Real.exp (R * |u|) * ‖thetaAvgTrialDerivative a j u‖) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (R * |u|))).mul
      (thetaAvgTrialDerivative_continuous hZ j).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-a) a)).bddAbove_image hc.continuousOn
  let M := |C| + K * B + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro u
  have hw : Real.exp (R * |u|) * ‖thetaAvgTrialDerivative a j u‖ ≤ M := by
    by_cases hu : u ∈ Icc (-a) a
    · have hh := hC (mem_image_of_mem _ hu)
      dsimp [M]
      nlinarith [le_abs_self C, mul_nonneg hK hB.le]
    · have hd := thetaAvg_contour_derivative_bound ha hZ (le_abs_of_mem_exterior hu) j
      change ‖thetaAvgTrialDerivative a j u‖ ≤ _ at hd
      calc
        _ ≤ Real.exp (R * |u|) *
            ((j.factorial : ℝ) * (scaleZ a) ^ (2 * j) * thetaAvgContourEnvelope a u) :=
          mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
        _ = K * ThetaTrial.ThetaSeries.doubleExpEnvelope (R + 9 / 2) (Real.exp (-2 * a)) |u| := by
          rw [show Real.exp (R * |u|) *
            ((j.factorial : ℝ) * (scaleZ a) ^ (2 * j) * thetaAvgContourEnvelope a u) =
            ((j.factorial : ℝ) * (scaleZ a) ^ (2 * j)) *
              (Real.exp (R * |u|) * thetaAvgContourEnvelope a u) by ring,
            thetaAvgContourEnvelope_weighted_identity]
          dsimp [K]
          ring
        _ ≤ K * B := mul_le_mul_of_nonneg_left (henv |u| (abs_nonneg u)) hK
        _ ≤ M := by dsimp [M]; linarith [abs_nonneg C]
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hw

theorem polynomialDerivative_shiftedAverage_exponential_bound {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (R : ℝ) :
    ∃ M > 0, ∀ u : ℝ,
      ‖polynomialDerivative P (fun v : ℝ => shiftedAverage a (v : ℂ)) u‖ ≤
        M * Real.exp (-(R * |u|)) := by
  classical
  choose M hM hb using fun j : ℕ => thetaAvgTrialDerivative_exponential_bound ha hZ j R
  let S := ∑ j ∈ P.support, ‖P.coeff j * (-I) ^ j‖ * M j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _hj => mul_nonneg (norm_nonneg _) (hM j).le)
  refine ⟨S + 1, by positivity, ?_⟩
  intro u
  rw [polynomialDerivative_shiftedAverage_eq hZ P]
  calc
    _ ≤ ∑ j ∈ P.support, ‖(P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a j u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ P.support,
        (‖P.coeff j * (-I) ^ j‖ * M j) * Real.exp (-(R * |u|)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb j u) (norm_nonneg _)
    _ = S * Real.exp (-(R * |u|)) := by rw [Finset.sum_mul]
    _ ≤ (S + 1) * Real.exp (-(R * |u|)) := by nlinarith [Real.exp_pos (-(R * |u|))]

theorem polynomialDerivative_shiftedAverage_norm_weighted_integrable {a : ℝ}
    (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (r : ℕ) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) *
      ‖iteratedDeriv r (polynomialDerivative P (fun v : ℝ => shiftedAverage a (v : ℂ))) u‖) := by
  have h := (polynomialDerivative_shiftedAverage_iteratedDeriv_all_weights_integrable
    ha hZ P r R).norm
  simpa only [ThetaTrial.PrimeContinuity.weightedProfile_norm] using h

/-- The polynomial trial functions satisfy all the hypotheses of the source
class used for the explicit formula. -/
theorem polynomialDerivative_shiftedAverage_regularSource {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    RadicalSource.RegularSource
      (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))) := by
  refine ⟨(polynomialDerivative_shiftedAverage_contDiff hZ P).of_le le_top,
    ?_, ?_, ?_, polynomialDerivative_shiftedAverage_exponential_bound ha hZ P⟩
  · intro R
    simpa only [iteratedDeriv_zero] using
      polynomialDerivative_shiftedAverage_norm_weighted_integrable ha hZ P 0 R
  · intro R
    simpa only [iteratedDeriv_one] using
      polynomialDerivative_shiftedAverage_norm_weighted_integrable ha hZ P 1 R
  · intro R
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      polynomialDerivative_shiftedAverage_norm_weighted_integrable ha hZ P 2 R

end ThetaTrial.Paper
