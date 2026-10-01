import ThetaTrial.Paper.WindowTrial
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Supported BV functions belong to the window form domain

Bounded variation and bounded support imply the integrability hypothesis of
`supported_integrableBV_inDomain`. No boundary condition is needed.
-/

noncomputable section
open Complex MeasureTheory Set

namespace ThetaTrial.Paper

private theorem real_bv_measurable {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) : Measurable f := by
  obtain ⟨p, q, hp, hq, hf⟩ :=
    hv.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  rw [hf]
  exact (monotoneOn_univ.mp hp).measurable.sub (monotoneOn_univ.mp hq).measurable

/-- A complex-valued BV function is measurable, including at its jumps. -/
theorem complex_bv_measurable {f : ℝ → ℂ}
    (hv : BoundedVariationOn f univ) : Measurable f := by
  have hr : Measurable (fun x => (f x).re) := real_bv_measurable
    (Complex.reCLM.lipschitz.comp_boundedVariationOn hv)
  have hi : Measurable (fun x => (f x).im) := real_bv_measurable
    (Complex.imCLM.lipschitz.comp_boundedVariationOn hv)
  have h := (Complex.continuous_ofReal.measurable.comp hr).add
    ((Complex.continuous_ofReal.measurable.comp hi).mul_const Complex.I)
  convert h using 1
  funext x
  exact (Complex.re_add_im (f x)).symm

/-- Bounded support and bounded variation alone imply ordinary L¹
integrability. The interval can include jumps at either endpoint. -/
theorem supported_bv_integrable {a : ℝ} {f : ℝ → ℂ}
    (hs : Function.support f ⊆ Icc (-a) a)
    (hv : BoundedVariationOn f univ) : Integrable f := by
  have hb (x : ℝ) : ‖f x‖ ≤ ‖f 0‖ + (eVariationOn f univ).toReal := by
    have hd := hv.dist_le (mem_univ x) (mem_univ 0)
    have hn := norm_sub_norm_le (f x) (f 0)
    rw [dist_eq_norm] at hd
    linarith
  have hi : IntegrableOn f (Icc (-a) a) :=
    IntegrableOn.of_bound measure_Icc_lt_top
      (complex_bv_measurable hv).aestronglyMeasurable
      (‖f 0‖ + (eVariationOn f univ).toReal) (Filter.Eventually.of_forall hb)
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hi

/-- The BV assertion of `pre:form`: a BV function supported in the window
belongs to the form domain. No boundary condition is needed. -/
theorem supportedBV_inDomain {a : ℝ} {f : ℝ → ℂ}
    (hs : Function.support f ⊆ Icc (-a) a)
    (hv : BoundedVariationOn f univ) : InWindowFormDomain a f :=
  supported_integrableBV_inDomain hs (supported_bv_integrable hs hv) hv

end ThetaTrial.Paper
