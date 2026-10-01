import ThetaTrial.Paper.ThetaDerivSourceLocalization
import ThetaTrial.Paper.ThetaDerivPolynomialRegularity
import ThetaTrial.Paper.ThetaDerivScalarAbsorption

/-!
# Theorem `deriv:main`: positivity on truncated theta derivatives

Quantitative lower bound for the Weil form on the sharp truncation of
`P(D)Φ`, under explicit size conditions on the degree and the cutoff.
-/

noncomputable section
open MeasureTheory Set Polynomial
open scoped Polynomial

namespace ThetaTrial.Paper

def thetaDerivInteractionConstant : ℝ := thetaDerivL1Constant / (1 - Real.exp (-4))

theorem thetaDerivInteractionConstant_pos : 0 < thetaDerivInteractionConstant := by
  apply div_pos thetaDerivL1Constant_pos
  have h := Real.exp_lt_one_iff.mpr (show (-4 : ℝ) < 0 by norm_num)
  linarith

def thetaDerivSectorConstant : ℝ :=
  2 + archimedeanConstant + |Real.log (Real.pi / thetaDerivL1Constant)| +
    thetaDerivInteractionConstant + thetaDerivArithmeticConstant

theorem thetaDerivSectorConstant_pos : 0 < thetaDerivSectorConstant := by
  unfold thetaDerivSectorConstant
  have hA := archimedeanConstant_nonneg
  have hI := thetaDerivInteractionConstant_pos
  have hR := thetaDerivArithmeticConstant_pos
  positivity

theorem thetaDeriv_log_width (d : ℕ) (a : ℝ) :
    Real.log (Real.pi / (thetaDerivL1Constant * thetaDerivTailWidth d a)) =
      Real.log (scaleT a) - Real.log ((d : ℝ) + 2) + Real.log (Real.pi / thetaDerivL1Constant) := by
  have hM : (d : ℝ) + 2 ≠ 0 := by positivity
  rw [Real.log_div Real.pi_ne_zero (mul_ne_zero thetaDerivL1Constant_pos.ne' (thetaDerivTailWidth_pos d a).ne'),
    Real.log_mul thetaDerivL1Constant_pos.ne' (thetaDerivTailWidth_pos d a).ne']
  unfold thetaDerivTailWidth
  rw [Real.log_div hM (thetaDeriv_scaleT_pos a).ne', Real.log_div Real.pi_ne_zero thetaDerivL1Constant_pos.ne']
  ring

theorem thetaDeriv_interaction_bound (d : ℕ) (a : ℝ) (ha1 : 1 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a) :
    (thetaDerivL1Constant * thetaDerivTailWidth d a) * (Real.exp (-a) / (1 - Real.exp (-4))) ≤
      thetaDerivInteractionConstant * ((d : ℝ) + 2) * a * Real.exp (-a) := by
  have hM : 0 ≤ (d : ℝ) + 2 := by positivity
  have hw : thetaDerivTailWidth d a ≤ ((d : ℝ) + 2) * a := by
    have hw' : thetaDerivTailWidth d a ≤ (d : ℝ) + 2 :=
      div_le_self hM (by linarith [thetaDeriv_scaleT_ge_four ha])
    exact hw'.trans (le_mul_of_one_le_right hM ha1)
  have h := mul_le_mul_of_nonneg_right hw
    (mul_nonneg thetaDerivInteractionConstant_pos.le (Real.exp_pos (-a)).le)
  convert! h using 1 <;> unfold thetaDerivInteractionConstant <;> ring

theorem thetaDerivTails_archimedean_lower (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha1 : 1 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    (Real.log (Real.pi / (thetaDerivL1Constant * thetaDerivTailWidth d a)) - 1 - archimedeanConstant -
      (thetaDerivL1Constant * thetaDerivTailWidth d a) * (Real.exp (-a) / (1 - Real.exp (-4)))) *
      squaredNorm (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) ≤
      archimedeanEnergy (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) := by
  obtain ⟨hfi, hfc⟩ := thetaDerivRightTail_l1 d P hP hdegree a ha hsize
  obtain ⟨hgi, hgc⟩ := thetaDerivLeftTail_l1 d P hP hdegree a ha hsize
  exact archimedeanEnergy_two_tail_concentration_exp hfi hgi
    (thetaDerivRightTail_boundedVariation P a) (thetaDerivLeftTail_boundedVariation P a) ha1
    (mul_pos thetaDerivL1Constant_pos (thetaDerivTailWidth_pos d a))
    (thetaDerivRightTail_zero P a) (thetaDerivLeftTail_zero P a) hfc hgc

theorem thetaDerivTails_fullForm_lower (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha1 : 1 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hslog : 40 * thetaDerivTailWidth d a ≤ Real.log 2) :
    (Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - thetaDerivSectorConstant -
      thetaDerivSectorConstant * ((d : ℝ) + 2) * a * Real.exp (-a)) *
      squaredNorm (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) ≤
      fullWeilForm (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) := by
  let t : ℝ → ℂ := fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u
  have hN : 0 ≤ squaredNorm t := integral_nonneg (fun u => sq_nonneg _)
  have hA := thetaDerivTails_archimedean_lower d P hP hdegree a ha1 ha hsize
  have hR := thetaDerivTails_pole_prime_bound d P hP hdegree a ha1 ha hsize hslog
  have hI := thetaDeriv_interaction_bound d a ha1 ha
  rw [thetaDeriv_log_width] at hA
  have hcoeff :
      Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - thetaDerivSectorConstant -
        thetaDerivSectorConstant * ((d : ℝ) + 2) * a * Real.exp (-a) ≤
      Real.log (scaleT a) - Real.log ((d : ℝ) + 2) + Real.log (Real.pi / thetaDerivL1Constant) -
        1 - archimedeanConstant -
        (thetaDerivL1Constant * thetaDerivTailWidth d a) * (Real.exp (-a) / (1 - Real.exp (-4))) -
        thetaDerivArithmeticConstant * ((d : ℝ) + 2) * a * Real.exp (-a) := by
    have hlog := neg_abs_le (Real.log (Real.pi / thetaDerivL1Constant))
    have hC0 : 1 + archimedeanConstant - Real.log (Real.pi / thetaDerivL1Constant) ≤
        thetaDerivSectorConstant := by
      unfold thetaDerivSectorConstant
      linarith [thetaDerivInteractionConstant_pos, thetaDerivArithmeticConstant_pos]
    have hC1 : thetaDerivInteractionConstant + thetaDerivArithmeticConstant ≤ thetaDerivSectorConstant := by
      unfold thetaDerivSectorConstant
      linarith [archimedeanConstant_nonneg, abs_nonneg (Real.log (Real.pi / thetaDerivL1Constant))]
    have hm : 0 ≤ ((d : ℝ) + 2) * a * Real.exp (-a) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hC1 hm
    nlinarith [hI, hmul]
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN
  have hp := neg_abs_le (poleContribution t)
  have hr := le_abs_self (primeContribution t)
  have he : fullWeilForm t = archimedeanEnergy t + poleContribution t - primeContribution t := rfl
  change _ ≤ fullWeilForm t
  rw [he]
  change _ ≤ archimedeanEnergy t at hA
  change |poleContribution t| + |primeContribution t| ≤ _ at hR
  nlinarith [hA, hR, hmul, hp, hr]

/-- The quantitative lower bound of Theorem `deriv:main`. -/
theorem thetaDeriv_quantitative_lower (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha1 : 1 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hslog : 40 * thetaDerivTailWidth d a ≤ Real.log 2) :
    fullWeilForm (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) =
      fullWeilForm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ∧
    (Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - thetaDerivSectorConstant -
      thetaDerivSectorConstant * ((d : ℝ) + 2) * a * Real.exp (-a)) *
      squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ≤
      fullWeilForm (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) := by
  have ha0 : 0 ≤ a := by linarith
  refine ⟨polynomialDerivative_thetaDensity_hardCutoff P ha0, ?_⟩
  rw [polynomialDerivative_thetaDensity_hardCutoff P ha0, thetaDeriv_exteriorTail_eq_sum P a ha0]
  exact thetaDerivTails_fullForm_lower d P hP hdegree a ha1 ha hsize hslog

#print axioms thetaDeriv_quantitative_lower

/-- Theorem `deriv:main` for every complex polynomial of degree at most
`c e^a`; the exterior norm is strictly positive. -/
theorem thetaDeriv_main :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧
      ∀ a : ℝ, a₀ ≤ a → ∀ d : ℕ, (d : ℝ) ≤ c * Real.exp a →
      ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d →
      fullWeilForm (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) =
        fullWeilForm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ∧
      (Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - C -
        C * ((d : ℝ) + 2) * a * Real.exp (-a)) *
        squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ≤
        fullWeilForm (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ∧
      (a / 4) * squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ≤
        (Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - C -
          C * ((d : ℝ) + 2) * a * Real.exp (-a)) *
          squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ∧
      0 < (a / 4) * squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) := by
  obtain ⟨c, hc, a₀, ha₀, hall⟩ := thetaDeriv_scalar_absorption thetaDerivSectorConstant thetaDerivSectorConstant_pos
  refine ⟨c, hc, thetaDerivSectorConstant, thetaDerivSectorConstant_pos, a₀, ha₀, ?_⟩
  intro a haa d hd P hP hdegree
  obtain ⟨ha1, ha, hsize, hslog, hbracket⟩ := hall a haa d hd
  obtain ⟨heq, hquant⟩ := thetaDeriv_quantitative_lower d P hP hdegree a ha1 ha hsize hslog
  have hnorm := thetaDeriv_exteriorTail_square_pos d P hP hdegree a (by linarith) ha hsize
  exact ⟨heq, hquant, mul_le_mul_of_nonneg_right hbracket hnorm.le,
    mul_pos (by linarith) hnorm⟩

/-- Strict positivity in the same degree range. -/
theorem thetaDeriv_positive_sector :
    ∃ c : ℝ, 0 < c ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧
      ∀ a : ℝ, a₀ ≤ a → ∀ d : ℕ, (d : ℝ) ≤ c * Real.exp a →
      ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d →
        0 < fullWeilForm (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) := by
  obtain ⟨c, hc, C, hC, a₀, ha₀, hall⟩ := thetaDeriv_main
  refine ⟨c, hc, a₀, ha₀, ?_⟩
  intro a haa d hd P hP hdegree
  obtain ⟨heq, hquant, hquarter, hpos⟩ := hall a haa d hd P hP hdegree
  exact hpos.trans_le (hquarter.trans hquant)

theorem thetaDeriv_sqrt_scaleT (a : ℝ) :
    Real.sqrt (scaleT a) = Real.sqrt (2 * Real.pi) * Real.exp a := by
  have he : scaleT a = (2 * Real.pi) * (Real.exp a) ^ 2 := by
    unfold scaleT scaleZ
    rw [← Real.exp_nat_mul]
    norm_num
    <;> ring
  rw [he, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos a)]

/-- Exact conversion of the two degree-range conventions in the paper. -/
theorem thetaDeriv_rescaled_degree_factor (c a : ℝ) :
    (c / Real.sqrt (2 * Real.pi)) * Real.sqrt (scaleT a) = c * Real.exp a := by
  rw [thetaDeriv_sqrt_scaleT]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

theorem thetaDeriv_main_sqrtT :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧
      ∀ a : ℝ, a₀ ≤ a → ∀ d : ℕ, (d : ℝ) ≤ c * Real.sqrt (scaleT a) →
      ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d →
      fullWeilForm (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) =
        fullWeilForm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ∧
      (Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - C -
        C * ((d : ℝ) + 2) * a * Real.exp (-a)) *
        squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ≤
        fullWeilForm (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ∧
      (a / 4) * squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ≤
        (Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - C -
          C * ((d : ℝ) + 2) * a * Real.exp (-a)) *
          squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) ∧
      0 < (a / 4) * squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) := by
  obtain ⟨c, hc, C, hC, a₀, ha₀, hall⟩ := thetaDeriv_main
  refine ⟨c / Real.sqrt (2 * Real.pi), div_pos hc (Real.sqrt_pos.mpr (by positivity)),
    C, hC, a₀, ha₀, ?_⟩
  intro a haa d hd P hP hdegree
  rw [thetaDeriv_rescaled_degree_factor] at hd
  exact hall a haa d hd P hP hdegree

#print axioms thetaDeriv_main
#print axioms thetaDeriv_positive_sector
#print axioms thetaDeriv_main_sqrtT

end ThetaTrial.Paper
