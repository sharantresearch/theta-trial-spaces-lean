import ThetaTrial.Imported.Zeta23.GammaFacts.Complete

/-!
# Digamma facts from the imported analytic library

Statements about Mathlib's Gamma and digamma functions, taken from the
imported `Zeta23` modules (see `PROVENANCE.md`). The partial-fraction series
is proved on `Complex.integerComplement`, i.e. away from the poles.
-/

namespace ThetaTrial

/-- Partial fractions for digamma, away from the nonpositive integers. -/
theorem digamma_partial_fractions {z : ℂ}
    (hz : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) :=
  Zeta23.DigammaSeries.digamma_series hz

end ThetaTrial
