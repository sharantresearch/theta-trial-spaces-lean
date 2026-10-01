import ThetaTrial.GammaEnergy.Multiplier
import ThetaTrial.GammaEnergy.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import ThetaTrial.ArchimedeanMultiplier
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

/-!
# The gamma shift-energy identity

The multiplier is the quarter-line digamma multiplier. The Fourier
transform is the shared unitary angular-frequency transform. All integrals,
including the two-variable integral that exchanges frequency and shift,
are proved integrable for Schwartz functions, hence for compact smooth tests.
-/

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace ThetaTrial.GammaEnergy

noncomputable def physicalShiftSq (f : ℝ → ℂ) (h : ℝ) : ℝ :=
  ∫ u : ℝ, ‖f (u + h) - f u‖ ^ 2

noncomputable def shiftEnergy (f : ℝ → ℂ) : ℝ :=
  ∫ h : ℝ in Ioi 0, shiftKernel h * physicalShiftSq f h

theorem shiftKernel_measurable : Measurable shiftKernel := by
  unfold shiftKernel
  fun_prop

end ThetaTrial.GammaEnergy
