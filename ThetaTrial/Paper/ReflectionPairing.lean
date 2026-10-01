import ThetaTrial.Paper.Reflection
import ThetaTrial.Paper.RadicalCutoff
import ThetaTrial.Paper.FullPairingAlgebra
import ThetaTrial.Paper.WindowFormBounds

/-! Invariance of the Weil pairing under simultaneous reflection of both
arguments, proved directly from the formula for the pairing. -/

noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper
open Radical RadicalCorrelation

theorem paperFT_reflect (k : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT (reflect k) z = Zeta23.paperFT k (-z) := by
  simpa only [ThetaTrial.Paper.paperFourier_eq_source, neg_neg] using
    ThetaTrial.Paper.paperFourier_reflect k (-z)

theorem fullWeil_reflect (k : ℝ → ℂ) : fullWeil (reflect k) = fullWeil k := by
  have hp (n : ℕ) : primeTerm (reflect k) n = primeTerm k n := by
    simp only [primeTerm, reflect_apply, neg_neg, add_comm]
  have hg : (∫ r : ℝ, gammaTerm (reflect k) r) = ∫ r : ℝ, gammaTerm k r := by
    rw [← integral_neg_eq_self (gammaTerm k) volume]
    apply integral_congr_ae
    filter_upwards with r
    simp only [gammaTerm, paperFT_reflect, Complex.ofReal_neg,
      ThetaTrial.WeilFormula.gammaBracket_neg]
  change Zeta23.paperFT (reflect k) (I / 2) + Zeta23.paperFT (reflect k) (-I / 2) -
    ∑' n, primeTerm (reflect k) n + (1 / (2 * Real.pi) : ℂ) * ∫ r, gammaTerm (reflect k) r = _
  simp only [paperFT_reflect, neg_div, neg_neg, hp]
  rw [hg]
  change _ = Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2) -
    ∑' n, primeTerm k n + (1 / (2 * Real.pi) : ℂ) * ∫ r, gammaTerm k r
  ring

theorem weilTest_reflect (f h : ℝ → ℂ) :
    Zeta23.EF.weilTest (reflect f) (reflect h) = reflect (Zeta23.EF.weilTest f h) := by
  funext x
  simp only [reflect_apply, weilTest_eq_integral]
  rw [← integral_neg_eq_self (fun u : ℝ => f u * conj (h (u - -x))) volume]
  apply integral_congr_ae
  filter_upwards with u
  congr 3 <;> ring

theorem fullPairing_reflect (f h : ℝ → ℂ) :
    fullPairing (reflect f) (reflect h) = fullPairing f h := by
  unfold fullPairing
  rw [weilTest_reflect, fullWeil_reflect]

/-- The even and odd subspaces are orthogonal for the pairing on the form
domain. -/
theorem fullPairing_even_odd_eq_zero {a : ℝ} {f h : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (hh : InWindowFormDomain a h)
    (he : Function.Even f) (ho : Function.Odd h) : fullPairing f h = 0 := by
  have hef : reflect f = f := funext he
  have hoh : reflect h = (-1 : ℂ) • h := by
    funext u
    simp only [reflect_apply, ho u, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  have hr := fullPairing_reflect f h
  rw [hef, hoh,
    RadicalCutoff.fullPairing_smul_right (WindowFormBounds.mixed_domain hf hh)] at hr
  simp only [map_neg, map_one, neg_one_smul] at hr
  exact neg_eq_self.mp hr

theorem fullPairing_odd_even_eq_zero {a : ℝ} {f h : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (hh : InWindowFormDomain a h)
    (ho : Function.Odd f) (he : Function.Even h) : fullPairing f h = 0 := by
  rw [RadicalCutoff.fullPairing_hermitian,
    fullPairing_even_odd_eq_zero hh hf he ho, map_zero]

end ThetaTrial.Paper
