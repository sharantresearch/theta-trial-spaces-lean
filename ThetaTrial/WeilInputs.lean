import ThetaTrial.Imported.Zeta23.WeilEF.Main
import ThetaTrial.Imported.Zeta23.ExplicitFormula.Bridge
import ThetaTrial.Imported.Zeta23.GammaFacts.Complete

/-!
The Weil explicit formula from the imported library (anthropics/formal-math,
tag v1.0, Apache-2.0; see `PROVENANCE.md`).

The imported library uses `paperFT k z = ∫ k(u) exp(i z u) du` and
`gammaOf ρ = (ρ - 1/2)/i`. Zeros are the nontrivial zeros of Mathlib's zeta
function, with analytic multiplicities. These statements are for compactly
supported `C²` tests.
-/

noncomputable section

namespace ThetaTrial

/-- The explicit formula, as proved in the imported library. -/
theorem weil_literature_formula : Zeta23.EF.EF_lit Zeta23.zetaZeroConfig :=
  Zeta23.WeilEF.EF_lit_zetaZeroConfig

/-- Exact pole, von Mangoldt, and digamma formula in the Fourier convention of the
imported library. -/
theorem weil_compact_formula {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ) =
      Zeta23.EF.literatureRHS k :=
  (weil_literature_formula k hk hkc).2

/-- The gamma integral is integrable, using the proved gamma package. -/
theorem weil_archimedean_integrable {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    MeasureTheory.Integrable (fun t : ℝ => Zeta23.paperFT k t * (Zeta23.mu t : ℂ)) :=
  Zeta23.EF.integrable_paperFT_mul_mu hk hkc Zeta23.gammaFacts

end ThetaTrial
