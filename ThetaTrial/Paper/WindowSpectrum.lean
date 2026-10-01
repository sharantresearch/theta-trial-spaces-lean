import ThetaTrial.Paper.WindowOperator
import ThetaTrial.Paper.WindowInfiniteDimension
import ThetaTrial.Paper.FormMinMax

/-!
# The window Weil spectrum and the min–max principle

Indices are zero-based: `windowEigenvalue a n` is `λ_{n+1}(a)` in the paper.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Set Filter
open scoped InnerProductSpace Topology

namespace ThetaTrial.Paper

open FormDomain WindowFormAssembly CoerciveFormRepresentation FormMinMax

def windowSpectralData (a : ℝ) (ha : 0 < a) :
    FormSpectralData (windowInclusion a) (windowFormOperator a) :=
  Classical.choice (exists_formSpectralData (windowInclusion a) (windowInclusion_injective a)
    (windowInclusion_denseRange a) (windowInclusion_isCompactOperator a)
    (windowL2_not_finiteDimensional ha) (windowFormOperator a)
    (windowFormOperator_coercive a) (windowFormOperator_symmetric a))

/-- The increasing eigenvalue sequence; the value at nonpositive
window sizes is irrelevant to the positive-window spectral theorems. -/
def windowEigenvalue (a : ℝ) (n : ℕ) : ℝ :=
  if ha : 0 < a then (windowSpectralData a ha).value n - shiftConstant a else 0

def windowEigenbasis (a : ℝ) (ha : 0 < a) : HilbertBasis ℕ ℂ (windowL2 a) :=
  (windowSpectralData a ha).basis

theorem windowEigenvalue_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    windowEigenvalue a n = (windowSpectralData a ha).value n - shiftConstant a := by
  simp only [windowEigenvalue, dif_pos ha]

theorem windowEigenvalue_monotone (a : ℝ) : Monotone (windowEigenvalue a) := by
  by_cases ha : 0 < a
  · intro i j hij
    simp only [windowEigenvalue_eq ha]
    exact sub_le_sub_right ((windowSpectralData a ha).monotone hij) _
  · intro i j hij
    simp only [windowEigenvalue, dif_neg ha, le_refl]

theorem windowEigenvalue_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (windowEigenvalue a) atTop atTop := by
  change Tendsto (fun n => windowEigenvalue a n) atTop atTop
  simp_rw [windowEigenvalue_eq ha, sub_eq_add_neg]
  exact
    tendsto_atTop_add_const_right atTop (-shiftConstant a) (windowSpectralData a ha).divergent

theorem windowEigenvalue_lower {a : ℝ} (ha : 0 < a) (n : ℕ) :
    -shiftConstant a < windowEigenvalue a n := by
  rw [windowEigenvalue_eq ha]
  have := (windowSpectralData a ha).positive n
  linarith

theorem windowEigenbasis_operator {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ hn : windowEigenbasis a ha n ∈ (windowWeilOperator a).domain,
      windowWeilOperator a ⟨windowEigenbasis a ha n, hn⟩ =
        (windowEigenvalue a n : ℂ) • windowEigenbasis a ha n := by
  simpa only [windowWeilOperator, windowEigenbasis, windowEigenvalue_eq ha] using
    spectral_operator_eigenvector (windowSpectralData a ha) (windowInclusion_injective a)
      (windowInclusion_denseRange a) (windowFormOperator_coercive a) (shiftConstant a) n

theorem windowFormOperator_nonneg (a : ℝ) (v : windowFormGraph a) :
    0 ≤ (inner ℂ (windowFormOperator a v) v).re := by
  obtain ⟨m, hm, hc⟩ := windowFormOperator_coercive a
  exact (mul_nonneg hm.le (sq_nonneg _)).trans (hc v)

theorem window_formRayleigh (a : ℝ) (v : windowFormGraph a) :
    formRayleigh (windowInclusion a) (windowFormOperator a) (shiftConstant a) v =
      fullWeilForm (representative a v) / ‖windowInclusion a v‖ ^ 2 := by
  rw [formRayleigh, windowFormOperator_diagonal]

theorem windowEigenvalue_minmax_isLeast {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IsLeast (trialUpperBounds (windowInclusion a) (windowFormOperator a) (shiftConstant a) n)
      (windowEigenvalue a n) := by
  rw [windowEigenvalue_eq ha]
  exact minmax_isLeast (windowSpectralData a ha) (windowInclusion_injective a)
    (windowFormOperator_symmetric a) (windowFormOperator_nonneg a) (shiftConstant a) n

theorem windowEigenvalue_minmax {a : ℝ} (ha : 0 < a) (n : ℕ) :
    sInf (trialUpperBounds (windowInclusion a) (windowFormOperator a) (shiftConstant a) n) =
      windowEigenvalue a n :=
  (windowEigenvalue_minmax_isLeast ha n).csInf_eq

/-- The Weil form bound on a finite graph-space trial
space implies the corresponding eigenvalue bound. -/
theorem windowEigenvalue_le_of_form_trial {a : ℝ} (ha : 0 < a)
    (S : Submodule ℂ (windowFormGraph a)) [FiniteDimensional ℂ S]
    (n : ℕ) (hdim : n < Module.finrank ℂ S) (L : ℝ)
    (hbound : ∀ v ∈ S, fullWeilForm (representative a v) ≤ L * ‖windowInclusion a v‖ ^ 2) :
    windowEigenvalue a n ≤ L := by
  rw [windowEigenvalue_eq ha]
  apply eigenvalue_le_of_trial_bound (windowSpectralData a ha) (windowInclusion_injective a)
    (windowFormOperator_symmetric a) (windowFormOperator_nonneg a) S n hdim (shiftConstant a) L
  simpa only [windowFormOperator_diagonal] using hbound

end ThetaTrial.Paper
