import ThetaTrial.WeilFormula.Arithmetic

noncomputable section

namespace ThetaTrial.WeilFormula

open Complex MeasureTheory Set
open scoped ComplexConjugate
open ThetaTrial.FourierNormalization

/-- The summand, indexed by the zeros of zeta. -/
def zetaSummand (f : ℝ → ℂ) (ρ : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
    fourier f (spectralCoord ρ) * conj (fourier f (conj (spectralCoord ρ)))

/-- The explicit formula in the unitary normalization, indexed by the zeros of
zeta; `WeilFormula` transfers it to the zeros of `Xi`. -/
theorem source_compact_sampling {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    Summable (zetaSummand f) ∧
    Integrable (fun t : ℝ => (Zeta23.EF.gammaBracket t : ℂ) *
      (Complex.normSq (fourier f t) : ℂ)) ∧
    fullForm a f = (2 * Real.pi : ℂ) * ∑' ρ, zetaSummand f ρ := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hk := Zeta23.EF.weilTest_contDiff hf hf.continuous hfc
  have hkc := Zeta23.EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨hs, heq⟩ := ThetaTrial.weil_literature_formula _ hk hkc
  have ht : (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (Zeta23.EF.weilTest f f) (Zeta23.gammaOf ρ)) =
      fun ρ => (2 * Real.pi : ℂ) * zetaSummand f ρ := by
    funext ρ
    rw [Zeta23.EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc,
      paperFT_pair_spectralCoord]
    unfold zetaSummand
    ring
  rw [ht] at hs heq
  have htwo : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine ⟨(summable_mul_left_iff htwo).mp hs, gamma_integrable hf hfc, ?_⟩
  rw [tsum_mul_left, literatureRHS_eq_fullForm hf.continuous hfs] at heq
  exact heq.symm

end ThetaTrial.WeilFormula
