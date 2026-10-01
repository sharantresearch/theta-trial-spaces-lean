import ThetaTrial.Paper.FormDomain
import ThetaTrial.Imported.Zeta23.GammaFacts

/-! Reflection invariance of the Weil form. -/

noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper

/-- Physical reflection, without complex conjugation. -/
def reflect (f : ℝ → ℂ) (u : ℝ) : ℂ := f (-u)

@[simp] theorem reflect_apply (f : ℝ → ℂ) (u : ℝ) : reflect f u = f (-u) := rfl

@[simp] theorem reflect_reflect (f : ℝ → ℂ) : reflect (reflect f) = f := by
  funext u
  simp [reflect]

theorem paperFourier_reflect (f : ℝ → ℂ) (z : ℂ) :
    paperFourier (reflect f) z = paperFourier f (-z) := by
  unfold paperFourier reflect
  rw [← integral_neg_eq_self (fun u : ℝ => f u * Complex.exp (-I * -z * (u : ℂ))) volume]
  apply integral_congr_ae
  filter_upwards with u
  congr 2
  push_cast
  ring

@[simp] theorem gammaWeight_neg (r : ℝ) : gammaWeight (-r) = gammaWeight r := by
  have he : (1 / 4 + I * ((-r : ℝ) : ℂ) / 2 : ℂ) =
      conj (1 / 4 + I * (r : ℂ) / 2) := by
    apply Complex.ext <;> simp [map_ofNat]
  unfold gammaWeight
  rw [he, Zeta23.digamma_conj]
  simp

theorem correlation_reflect (f : ℝ → ℂ) (x : ℝ) :
    correlation (reflect f) x = correlation f (-x) := by
  unfold correlation reflect
  rw [← integral_neg_eq_self (fun u : ℝ => f u * conj (f (u - -x))) volume]
  apply integral_congr_ae
  filter_upwards with u
  congr 3 <;> ring

theorem correlation_neg (f : ℝ → ℂ) (x : ℝ) :
    correlation f (-x) = conj (correlation f x) := by
  simp only [correlation_eq_weilFormula, ThetaTrial.WeilFormula.correlation_neg]

@[simp] theorem correlation_reflect_re (f : ℝ → ℂ) (x : ℝ) :
    (correlation (reflect f) x).re = (correlation f x).re := by
  rw [correlation_reflect, correlation_neg, Complex.conj_re]

theorem squaredNorm_reflect (f : ℝ → ℂ) : squaredNorm (reflect f) = squaredNorm f := by
  exact integral_neg_eq_self (fun u : ℝ => ‖f u‖ ^ 2) volume

theorem fullWeilForm_reflect (f : ℝ → ℂ) : fullWeilForm (reflect f) = fullWeilForm f := by
  have hg : (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier (reflect f) r)) =
      ∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r) := by
    simp only [paperFourier_reflect]
    rw [← integral_neg_eq_self
      (fun r : ℝ => gammaWeight r * Complex.normSq (paperFourier f r)) volume]
    apply integral_congr_ae
    filter_upwards with r
    simp
  have hp : (paperFourier (reflect f) (I / 2) *
      conj (paperFourier (reflect f) (-I / 2))).re =
      (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re := by
    simp only [paperFourier_reflect, neg_div, neg_neg]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  unfold fullWeilForm
  rw [hg, hp]
  simp only [correlation_reflect_re]

theorem memLp_reflect {f : ℝ → ℂ} {p : ENNReal} (hf : MemLp f p) :
    MemLp (reflect f) p :=
  hf.comp_measurePreserving (Measure.measurePreserving_neg volume)

theorem InWindowFormDomain.reflect {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) : InWindowFormDomain a (reflect f) := by
  refine ⟨?_, memLp_reflect hf.2.1, ?_⟩
  · intro u hu
    have hh := hf.1 (show -u ∈ Function.support f from hu)
    simp only [mem_Icc] at hh ⊢
    constructor <;> linarith [hh.1, hh.2]
  · have hi := hf.2.2.comp_neg
    apply hi.congr
    filter_upwards with r
    simp [paperFourier_reflect]

theorem inWindowFormDomain_reflect_iff {a : ℝ} {f : ℝ → ℂ} :
    InWindowFormDomain a (reflect f) ↔ InWindowFormDomain a f := by
  constructor
  · intro hf
    simpa using hf.reflect
  · exact InWindowFormDomain.reflect

end ThetaTrial.Paper
