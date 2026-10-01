import ThetaTrial.WeilFormula.SourceSampling
import ThetaTrial.XiZeros
import ThetaTrial.WeilFormula.Arithmetic

/-!
# The explicit formula in the unitary normalization

The explicit formula for compactly supported `C²` tests, written with the
unitary Fourier transform of `FourierNormalization` and summed over the zeros
of `Xi` (`XiZeros`) with their analytic multiplicities. The other side is the
pole, gamma and prime expression `fullForm`.
-/

noncomputable section

namespace ThetaTrial.WeilFormula

open Complex MeasureTheory Set
open scoped ComplexConjugate
open ThetaTrial.FourierNormalization

/-- The summand at a zero. -/
def xiSummand (f : ℝ → ℂ) (z : XiZeros) : ℂ :=
  (XiMultiplicity z : ℂ) * fourier f z * conj (fourier f (conj z))

theorem xiSummand_equiv (f : ℝ → ℂ) (ρ : Zeta23.zetaZeroConfig.carrier) :
    xiSummand f (zetaZeroEquivXiZeros ρ) = zetaSummand f ρ := by
  unfold xiSummand
  rw [zetaZeroEquivXiZeros_multiplicity]
  rfl

/-- The explicit formula for `C²` tests with compact support, summed over the
zeros of `Xi` with their analytic multiplicities. -/
theorem compact_signed_sampling {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    Summable (xiSummand f) ∧
    Integrable (fun t : ℝ => (Zeta23.EF.gammaBracket t : ℂ) *
      (Complex.normSq (fourier f t) : ℂ)) ∧
    fullForm a f = (2 * Real.pi : ℂ) * ∑' z : XiZeros, xiSummand f z := by
  obtain ⟨hs, hi, heq⟩ := source_compact_sampling hf hfs
  have hsum : (∑' ρ : Zeta23.zetaZeroConfig.carrier, zetaSummand f ρ) =
      ∑' z : XiZeros, xiSummand f z := by
    simpa only [xiSummand_equiv] using zetaZeroEquivXiZeros.tsum_eq (xiSummand f)
  refine ⟨?_, hi, heq.trans (congrArg ((2 * Real.pi : ℂ) * ·) hsum)⟩
  rw [← zetaZeroEquivXiZeros.summable_iff]
  simpa only [Function.comp_def, xiSummand_equiv] using hs

end ThetaTrial.WeilFormula
