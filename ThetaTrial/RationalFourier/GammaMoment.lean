import ThetaTrial.RationalFourier.GammaMean
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import ThetaTrial.ZetaDefinitions
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
/-! Measurability of the gamma multiplier. -/

open Set MeasureTheory Filter
open scoped Topology

namespace ThetaTrial.RationalFourier
open ThetaTrial.GammaEnergy

theorem gammaMultiplier_aestronglyMeasurable : AEStronglyMeasurable gammaMultiplier := by
  have hi := (gamma_cauchy_integrable (H := 1) (by norm_num)).aestronglyMeasurable
  have hm := hi.mul (show AEStronglyMeasurable (fun x : ℝ => (1 : ℝ) ^ 2 + x ^ 2) by fun_prop)
  apply hm.congr
  filter_upwards [] with x
  dsimp
  exact div_mul_cancel₀ _ (by positivity)

end ThetaTrial.RationalFourier
