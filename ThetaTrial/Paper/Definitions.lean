import ThetaTrial.ThetaSeries.PhiIntegral
import ThetaTrial.FourierNormalization
import Mathlib.Algebra.Polynomial.Basic

/-!
Basic objects for the paper "Explicit theta trial spaces for the truncated Weil
quadratic form": the complex theta series and its real density, the Fourier
transform, the Weil form and its form domain.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper

/-- The paper uses the standard xi normalization, with the factor `1/2`. -/
def xiFunction (z : ℂ) : ℂ := ThetaTrial.xi (1 / 2 + I * z)

/-- The theta density of the paper, extended evenly. -/
def thetaDensity (u : ℝ) : ℝ := 2 * ThetaTrial.ThetaSeries.thetaPhi |u|

/-- All positive theta modes, indexed by `n+1`, on the complex strip. -/
def complexThetaMode (n : ℕ) (w : ℂ) : ℂ :=
  (4 * (Real.pi : ℂ) ^ 2 * ((n : ℂ) + 1) ^ 4 * Complex.exp (9 * w / 2)
    - 6 * (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * Complex.exp (5 * w / 2)) *
    Complex.exp (-(Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * Complex.exp (2 * w))

def complexThetaDensity (w : ℂ) : ℂ := ∑' n : ℕ, complexThetaMode n w

/-- The Fourier transform `∫ f(u) exp(-izu) du` of the paper (no `2π`
normalization). -/
def paperFourier (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, f u * Complex.exp (-I * z * (u : ℂ))

def gammaWeight (r : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + I * (r : ℂ) / 2)).re - Real.log Real.pi

def correlation (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, f u * conj (f (u - x))

/-- Full form: gamma, positive paired polar contribution, and every prime power. -/
def fullWeilForm (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r))
  + 2 * (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re
  - 2 * ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re

def squaredNorm (f : ℝ → ℂ) : ℝ := ∫ u : ℝ, ‖f u‖ ^ 2

def windowCut (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Icc (-a) a).indicator f

def exteriorTail (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Icc (-a) a)ᶜ.indicator f

/-- Logarithmic Fourier form domain; no zero trace imposed. -/
def InWindowFormDomain (a : ℝ) (f : ℝ → ℂ) : Prop :=
  Function.support f ⊆ Icc (-a) a ∧ MemLp f 2 volume ∧
    Integrable (fun r : ℝ => Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2)

def scaleZ (a : ℝ) : ℝ := Real.pi * Real.exp (2 * a)
def scaleT (a : ℝ) : ℝ := 2 * scaleZ a
def shiftWidth (a : ℝ) : ℝ := Real.pi / 4 - (scaleZ a)⁻¹
def shiftWeight (a y : ℝ) : ℝ := Real.exp (-2 * scaleZ a * (1 - Real.cos (2 * y)))

def shiftedAverage (a : ℝ) (u : ℂ) : ℂ :=
  ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
    (shiftWeight a y : ℂ) * complexThetaDensity (u + I * (y : ℂ))

def differentialOperator (f : ℝ → ℂ) : ℝ → ℂ := fun u => -I * deriv f u

def polynomialDerivative (P : Polynomial ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => ∑ j ∈ P.support, P.coeff j * ((differentialOperator^[j]) f) u

@[simp] theorem thetaDensity_neg (u : ℝ) : thetaDensity (-u) = thetaDensity u := by
  simp [thetaDensity]

theorem thetaDensity_eq_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    thetaDensity u = 2 * ThetaTrial.ThetaSeries.thetaPhi u := by
  simp [thetaDensity, abs_of_nonneg hu]

theorem thetaDensity_pos (u : ℝ) : 0 < thetaDensity u := by
  exact mul_pos (by norm_num) (ThetaTrial.ThetaSeries.thetaPhi_pos (abs_nonneg u))

theorem xiFunction_eq_weilFormula (z : ℂ) : xiFunction z = ThetaTrial.Xi z := by
  have h : (1 / 2 + I * z : ℂ) = 1 - (1 / 2 - I * z) := by ring
  rw [xiFunction, h, ThetaTrial.xi_one_sub]
  rfl

theorem paperFourier_eq_source (f : ℝ → ℂ) (z : ℂ) :
    paperFourier f z = Zeta23.paperFT f (-z) := by
  simp only [paperFourier, Zeta23.paperFT, mul_neg, neg_mul]

theorem window_add_tail (a : ℝ) (f : ℝ → ℂ) :
    windowCut a f + exteriorTail a f = f := by
  ext u
  by_cases hu : u ∈ Icc (-a) a <;> simp [windowCut, exteriorTail, hu]

theorem window_eq_sub_tail (a : ℝ) (f : ℝ → ℂ) :
    windowCut a f = f - exteriorTail a f := by
  exact eq_sub_iff_add_eq.mpr (window_add_tail a f)

end ThetaTrial.Paper
