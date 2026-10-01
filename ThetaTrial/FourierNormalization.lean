import ThetaTrial.Imported.Zeta23.ExplicitFormula

/-!
# A unitary Fourier convention

The transform `(2π)^(-1/2) ∫ f(x) exp(-izx) dx`, defined at complex arguments,
and its relation to the plus-sign transform of the imported library, keeping
every factor of `2π`.
-/

noncomputable section

namespace ThetaTrial.FourierNormalization

open Complex MeasureTheory Set
open scoped ComplexConjugate FourierTransform

/-- The unitary minus-sign Fourier transform. -/
def fourier (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  Zeta23.paperFT f (-z) / (Real.sqrt (2 * Real.pi) : ℂ)

theorem sqrt_two_pi_ne_zero : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

theorem sqrt_two_pi_sq : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = 2 * Real.pi := by
  exact_mod_cast Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)

theorem paperFT_eq_fourier (f : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT f z = (Real.sqrt (2 * Real.pi) : ℂ) * fourier f (-z) := by
  simp only [fourier, neg_neg]
  field_simp [sqrt_two_pi_ne_zero]

/-- The transform at a complex argument. -/
theorem paperFT_pair_eq (f g : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT f z * conj (Zeta23.paperFT g (conj z)) =
      (2 * Real.pi : ℂ) * (fourier f (-z) * conj (fourier g (conj (-z)))) := by
  rw [paperFT_eq_fourier f z, paperFT_eq_fourier g (conj z)]
  simp only [map_mul, conj_ofReal, map_neg]
  calc
    _ = (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 *
        (fourier f (-z) * conj (fourier g (-conj z))) := by ring
    _ = _ := by rw [sqrt_two_pi_sq]

/-- The spectral coordinate corresponding to a point of the zeta plane. -/
def spectralCoord (ρ : ℂ) : ℂ := I * (ρ - 1 / 2)

theorem spectralCoord_eq_neg_gammaOf (ρ : ℂ) :
    spectralCoord ρ = -Zeta23.gammaOf ρ := by
  unfold spectralCoord Zeta23.gammaOf
  rw [← neg_div]
  apply (eq_div_iff I_ne_zero).2
  calc
    (I * (ρ - 1 / 2)) * I = (I * I) * (ρ - 1 / 2) := by ring
    _ = -(ρ - 1 / 2) := by rw [I_mul_I]; ring

theorem zetaCoord_spectralCoord (ρ : ℂ) :
    1 / 2 - I * spectralCoord ρ = ρ := by
  unfold spectralCoord
  calc
    _ = 1 / 2 - (I * I) * (ρ - 1 / 2) := by ring
    _ = ρ := by rw [I_mul_I]; ring

theorem spectralCoord_zetaCoord (z : ℂ) :
    spectralCoord (1 / 2 - I * z) = z := by
  unfold spectralCoord
  calc
    _ = -(I * I) * z := by ring
    _ = z := by rw [I_mul_I]; ring

theorem paperFT_pair_spectralCoord (f g : ℝ → ℂ) (ρ : ℂ) :
    Zeta23.paperFT f (Zeta23.gammaOf ρ) *
        conj (Zeta23.paperFT g (conj (Zeta23.gammaOf ρ))) =
      (2 * Real.pi : ℂ) *
        (fourier f (spectralCoord ρ) * conj (fourier g (conj (spectralCoord ρ)))) := by
  rw [spectralCoord_eq_neg_gammaOf, paperFT_pair_eq]

end ThetaTrial.FourierNormalization

