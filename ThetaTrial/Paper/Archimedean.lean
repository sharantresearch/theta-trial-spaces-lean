import ThetaTrial.Paper.LogUncertainty
import ThetaTrial.Paper.FullForm
import ThetaTrial.Paper.BV
import ThetaTrial.GammaEnergy.Multiplier
import ThetaTrial.Imported.Zeta23.GammaFacts.StirlingVert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The archimedean lower estimate

A global lower bound for the digamma multiplier, proved from the Stirling
estimate and the cosine-difference identity, and the resulting lower bound
for the gamma energy via Plancherel.
-/

noncomputable section
open MeasureTheory Set

namespace ThetaTrial.Paper

/-- A fixed, coarse constant. -/
def archimedeanConstant : ℝ :=
  21 + |Real.log 2| + |Real.log Real.pi| + |ThetaTrial.GammaEnergy.gammaBase|

lemma archimedeanConstant_nonneg : 0 ≤ archimedeanConstant := by
  unfold archimedeanConstant
  positivity

lemma gammaWeight_ge_base (r : ℝ) : ThetaTrial.GammaEnergy.gammaBase ≤ gammaWeight r := by
  have h := ThetaTrial.GammaEnergy.gammaMultiplier_sub_base_nonneg r
  rw [← gammaWeight_eq_weilFormula] at h
  linarith

/-- The Stirling estimate on the two unbounded frequency rays. -/
lemma gammaWeight_ge_log_of_one_le_abs {r : ℝ} (hr : 1 ≤ |r|) :
    Real.log |r| - (20 + Real.log 2 + Real.log Real.pi) ≤ gammaWeight r := by
  have ht : (1 : ℝ) / 2 ≤ |r / 2| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hs := Zeta23.StirlingVert.re_digamma_stirling'
    (a := 1 / 4) (by norm_num) (by norm_num) ht
  have hsq : (1 : ℝ) / 4 ≤ (r / 2) ^ 2 := by
    have ha := sq_abs r
    nlinarith [sq_nonneg (|r| - 1)]
  have he : 5 / (r / 2) ^ 2 ≤ (20 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < (r / 2) ^ 2)).mpr
    nlinarith
  have hr0 : |r| ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hl : Real.log |r / 2| = Real.log |r| - Real.log 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_div hr0 (by norm_num : (2 : ℝ) ≠ 0)]
  have hlo := (abs_le.mp hs).1
  rw [hl] at hlo
  rw [gammaWeight_eq_weilFormula]
  unfold ThetaTrial.GammaEnergy.gammaMultiplier
  push_cast at hlo ⊢
  linarith

/-- The global pointwise lower bound. At zero this uses Lean's convention
`Real.log 0 = 0`; the logarithmic integral is unaffected by this single point. -/
theorem gammaWeight_ge_log (r : ℝ) :
    Real.log |r| - archimedeanConstant ≤ gammaWeight r := by
  by_cases hr : 1 ≤ |r|
  · have h := gammaWeight_ge_log_of_one_le_abs hr
    unfold archimedeanConstant
    linarith [le_abs_self (Real.log 2), le_abs_self (Real.log Real.pi),
      abs_nonneg ThetaTrial.GammaEnergy.gammaBase]
  · have hl : Real.log |r| ≤ 0 := Real.log_nonpos (abs_nonneg r) (le_of_not_ge hr)
    have hb := gammaWeight_ge_base r
    unfold archimedeanConstant
    linarith [neg_le_abs ThetaTrial.GammaEnergy.gammaBase, abs_nonneg (Real.log 2),
      abs_nonneg (Real.log Real.pi)]

/-- Identification of the two already proved paper Fourier definitions. -/
lemma paperFourier_real_eq_uncertainty (f : ℝ → ℂ) (r : ℝ) :
    paperFourier f r = LogUncertainty.paperFourier f r :=
  paperFourier_eq_mathlib f r

/-- The gamma part of the form, with its factor `1/(2*pi)`. -/
def archimedeanEnergy (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)

lemma uncertainty_fourier_sq_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    Integrable (fun r : ℝ => ‖LogUncertainty.paperFourier f r‖ ^ 2) :=
  ((LogUncertainty.ordinary_fourier_memLp hf hf2).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)).comp_div (by positivity : 2 * Real.pi ≠ 0)

/-- Finite gamma energy implies logarithmic integrability, by the lower bound
for the multiplier and finiteness of the negative logarithmic moment. -/
lemma log_term_integrable_of_gamma {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r))) :
    Integrable (fun r : ℝ => Real.log |r| *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
  have hgv : Integrable (fun r : ℝ => gammaWeight r *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    simpa only [← Complex.sq_norm, paperFourier_real_eq_uncertainty] using hg
  have hv := uncertainty_fourier_sq_integrable hf hf2
  have hpos : Integrable (fun r : ℝ => LogUncertainty.positiveLogWeight r *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    apply (hgv.norm.add (hv.const_mul archimedeanConstant)).mono'
      (LogUncertainty.positiveLogDensity_measurable hf).aestronglyMeasurable
    filter_upwards [] with r
    have hweight : LogUncertainty.positiveLogWeight r ≤
        |gammaWeight r| + archimedeanConstant := by
      apply max_le
      · linarith [gammaWeight_ge_log r, le_abs_self (gammaWeight r)]
      · exact add_nonneg (abs_nonneg _) archimedeanConstant_nonneg
    have hv0 := sq_nonneg ‖LogUncertainty.paperFourier f r‖
    have hp0 : 0 ≤ LogUncertainty.positiveLogWeight r := le_max_right _ _
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hv0, abs_of_nonneg (mul_nonneg hp0 hv0)]
    nlinarith [mul_le_mul_of_nonneg_right hweight hv0]
  apply (hpos.sub (LogUncertainty.negativeLogDensity_integrable hf)).congr
  filter_upwards [] with r
  change LogUncertainty.positiveLogWeight r * ‖LogUncertainty.paperFourier f r‖ ^ 2 -
    LogUncertainty.negativeLogWeight r * ‖LogUncertainty.paperFourier f r‖ ^ 2 = _
  rw [← sub_mul, LogUncertainty.log_weight_split]

/-- A gamma-energy lower bound for arbitrary nonzero L1 and L2
sources whose gamma integral is finite. No continuity is required. -/
theorem archimedeanEnergy_lower {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) (hne : ¬ f =ᵐ[volume] 0)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r))) :
    (Real.log (Real.pi * squaredNorm f / (∫ u : ℝ, ‖f u‖) ^ 2) -
      1 - archimedeanConstant) * squaredNorm f ≤ archimedeanEnergy f := by
  have hlog := log_term_integrable_of_gamma hf hf2 hg
  have hv := uncertainty_fourier_sq_integrable hf hf2
  have hgv : Integrable (fun r : ℝ => gammaWeight r *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    simpa only [← Complex.sq_norm, paperFourier_real_eq_uncertainty] using hg
  have hsub : Integrable (fun r : ℝ =>
      (Real.log |r| - archimedeanConstant) * ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    apply (hlog.sub (hv.const_mul archimedeanConstant)).congr
    filter_upwards [] with r
    change Real.log |r| * ‖LogUncertainty.paperFourier f r‖ ^ 2 -
      archimedeanConstant * ‖LogUncertainty.paperFourier f r‖ ^ 2 = _
    ring
  have hcmp := integral_mono_ae hsub hgv (ae_of_all _ (fun r =>
    mul_le_mul_of_nonneg_right (gammaWeight_ge_log r) (sq_nonneg _)))
  simp only [sub_mul] at hcmp
  rw [integral_sub hlog (hv.const_mul archimedeanConstant), integral_const_mul,
    LogUncertainty.paperFourier_mass hf hf2] at hcmp
  have hu := LogUncertainty.fourier_log_uncertainty_of_ne_zero hf hf2 hne hlog
  have hc := mul_le_mul_of_nonneg_left hcmp
    (by positivity : 0 ≤ (1 : ℝ) / (2 * Real.pi))
  have hcancel : (1 / (2 * Real.pi)) *
      (archimedeanConstant * ((2 * Real.pi) * ∫ u : ℝ, ‖f u‖ ^ 2)) =
      archimedeanConstant * ∫ u : ℝ, ‖f u‖ ^ 2 := by field_simp
  rw [mul_sub, hcancel] at hc
  unfold archimedeanEnergy squaredNorm
  simp only [← Complex.sq_norm, paperFourier_real_eq_uncertainty]
  nlinarith [hu, hc]

/-- The paper's gamma integral is finite for integrable BV
inputs. The proved Cauchy envelope includes every jump. -/
theorem gamma_term_integrable_of_bv {f : ℝ → ℂ}
    (hf : Integrable f) (hfv : BoundedVariationOn f univ) :
    Integrable (fun r : ℝ => gammaWeight r * Complex.normSq (paperFourier f r)) :=
  gamma_term_integrable_of_fourier_decay
    (paperFourier_continuous_real hf).aestronglyMeasurable
    (paperFourier_sq_le_cauchy_of_bv hf hfv)

/-- Unconditional source-domain version for nonzero integrable BV inputs:
both L2 membership and gamma-integral convergence are consequences. -/
theorem archimedeanEnergy_lower_of_bv {f : ℝ → ℂ}
    (hf : Integrable f) (hfv : BoundedVariationOn f univ) (hne : ¬ f =ᵐ[volume] 0) :
    (Real.log (Real.pi * squaredNorm f / (∫ u : ℝ, ‖f u‖) ^ 2) -
      1 - archimedeanConstant) * squaredNorm f ≤ archimedeanEnergy f :=
  archimedeanEnergy_lower hf (memLp_two_of_integrable_bv hf hfv) hne
    (gamma_term_integrable_of_bv hf hfv)

lemma squaredNorm_eq_zero_of_ae_zero {f : ℝ → ℂ} (hf : f =ᵐ[volume] 0) :
    squaredNorm f = 0 := by
  unfold squaredNorm
  have heq : (fun u : ℝ => ‖f u‖ ^ 2) =ᵐ[volume] 0 := by
    filter_upwards [hf] with u hu
    simp [hu]
  rw [integral_congr_ae heq]
  simp

lemma archimedeanEnergy_eq_zero_of_ae_zero {f : ℝ → ℂ} (hf : f =ᵐ[volume] 0) :
    archimedeanEnergy f = 0 := by
  have hft (r : ℝ) : paperFourier f r = 0 := by
    unfold paperFourier
    have heq : (fun u : ℝ => f u * Complex.exp (-Complex.I * (r : ℂ) * (u : ℂ)))
        =ᵐ[volume] 0 := by
      filter_upwards [hf] with u hu
      simp [hu]
    rw [integral_congr_ae heq]
    simp
  unfold archimedeanEnergy
  simp [hft]

/-- An L1/L2 concentration bound gives a lower bound for the gamma energy.
This version allows one of the two edges to vanish. -/
theorem archimedeanEnergy_lower_of_concentration {f : ℝ → ℂ} {ρ : ℝ}
    (hf : Integrable f) (hfv : BoundedVariationOn f univ) (hρ : 0 < ρ)
    (hcon : (∫ u : ℝ, ‖f u‖) ^ 2 ≤ ρ * squaredNorm f) :
    (Real.log (Real.pi / ρ) - 1 - archimedeanConstant) * squaredNorm f ≤
      archimedeanEnergy f := by
  by_cases hz : f =ᵐ[volume] 0
  · rw [squaredNorm_eq_zero_of_ae_zero hz, archimedeanEnergy_eq_zero_of_ae_zero hz]
    simp
  have hL : 0 < ∫ u : ℝ, ‖f u‖ := by
    by_contra h
    have he : (∫ u : ℝ, ‖f u‖) = 0 :=
      le_antisymm (le_of_not_gt h) (integral_nonneg (fun u => norm_nonneg (f u)))
    have hzae := (integral_eq_zero_iff_of_nonneg
      (fun u => norm_nonneg (f u)) hf.norm).mp he
    apply hz
    filter_upwards [hzae] with u hu
    exact norm_eq_zero.mp hu
  have hA : 0 ≤ squaredNorm f := integral_nonneg (fun u => sq_nonneg ‖f u‖)
  have hratio : Real.pi / ρ ≤ Real.pi * squaredNorm f / (∫ u : ℝ, ‖f u‖) ^ 2 := by
    apply (div_le_div_iff₀ hρ (sq_pos_of_pos hL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcon Real.pi_pos.le]
  have hlog := Real.log_le_log (div_pos Real.pi_pos hρ) hratio
  have hlow := archimedeanEnergy_lower_of_bv hf hfv hz
  have hmul := mul_le_mul_of_nonneg_right hlog hA
  nlinarith

#print axioms gammaWeight_ge_log
#print axioms archimedeanEnergy_lower
#print axioms archimedeanEnergy_lower_of_bv
#print axioms archimedeanEnergy_lower_of_concentration

end ThetaTrial.Paper
