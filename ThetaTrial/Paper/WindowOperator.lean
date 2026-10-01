import ThetaTrial.Paper.WindowFormAssembly
import ThetaTrial.Paper.CompactFormSpectrum

/-! The operator and resolvent associated with the localized Weil form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace ComplexConjugate Topology
namespace ThetaTrial.Paper
open FormDomain WindowFormAssembly CoerciveFormRepresentation

def windowFormOperator (a : ℝ) : windowFormGraph a →L[ℂ] windowFormGraph a :=
  formOperator (shiftedForm a)

theorem windowFormOperator_coercive (a : ℝ) : IsCoerciveOperator (windowFormOperator a) :=
  formOperator_coercive (shiftedForm a) (shiftedForm_coercive a)

theorem windowFormOperator_symmetric (a : ℝ) (v w : windowFormGraph a) :
    inner ℂ (windowFormOperator a v) w = inner ℂ v (windowFormOperator a w) :=
  formOperator_symmetric (shiftedForm a) (shiftedForm_hermitian a) v w

theorem windowFormOperator_inner (a : ℝ) (v w : windowFormGraph a) :
    inner ℂ (windowFormOperator a v) w =
      Radical.fullPairing (representative a w) (representative a v) +
        (shiftConstant a : ℂ) * inner ℂ (windowInclusion a v) (windowInclusion a w) := by
  rw [windowFormOperator, formOperator_inner, shiftedForm_apply]
  rfl

theorem windowFormOperator_diagonal (a : ℝ) (v : windowFormGraph a) :
    (inner ℂ (windowFormOperator a v) v).re - shiftConstant a * ‖windowInclusion a v‖ ^ 2 =
      fullWeilForm (representative a v) := by
  have hi : (inner ℂ (windowInclusion a v) (windowInclusion a v)).re =
      ‖windowInclusion a v‖ ^ 2 := by
    simpa only [pow_two, RCLike.re_eq_complex_re] using
      (inner_self_eq_norm_mul_norm (𝕜 := ℂ) (windowInclusion a v))
  rw [windowFormOperator, formOperator_inner, shiftedForm_apply, rawForm_diagonal]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero, hi]
  ring

def windowResolvent (a : ℝ) : windowL2 a →L[ℂ] windowL2 a :=
  coerciveResolvent (windowInclusion a) (windowFormOperator a) (windowFormOperator_coercive a)

theorem windowResolvent_injective (a : ℝ) : Function.Injective (windowResolvent a) :=
  coerciveResolvent_injective (windowInclusion a) (windowInclusion_injective a)
    (windowInclusion_denseRange a) (windowFormOperator a) (windowFormOperator_coercive a)

theorem windowResolvent_compact (a : ℝ) : IsCompactOperator (windowResolvent a) :=
  coerciveResolvent_compact (windowInclusion a) (windowInclusion_isCompactOperator a)
    (windowFormOperator a) (windowFormOperator_coercive a)

theorem windowResolvent_symmetric (a : ℝ) : (windowResolvent a).IsSymmetric :=
  coerciveResolvent_symmetric (windowInclusion a) (windowFormOperator a)
    (windowFormOperator_coercive a) (windowFormOperator_symmetric a)

theorem windowResolvent_nonneg (a : ℝ) (f : windowL2 a) :
    0 ≤ (inner ℂ f (windowResolvent a f)).re :=
  coerciveResolvent_nonneg (windowInclusion a) (windowFormOperator a)
    (windowFormOperator_coercive a) f

def windowWeilOperator (a : ℝ) : windowL2 a →ₗ.[ℂ] windowL2 a :=
  coerciveAssociatedOperator (windowInclusion a) (windowInclusion_injective a)
    (windowInclusion_denseRange a) (windowFormOperator a) (windowFormOperator_coercive a)
    (shiftConstant a)

theorem windowWeilOperator_selfAdjoint (a : ℝ) : IsSelfAdjoint (windowWeilOperator a) :=
  coerciveAssociatedOperator_selfAdjoint (windowInclusion a) (windowInclusion_injective a)
    (windowInclusion_denseRange a) (windowFormOperator a) (windowFormOperator_coercive a)
    (windowFormOperator_symmetric a) (shiftConstant a)

theorem windowWeilOperator_closed (a : ℝ) : (windowWeilOperator a).IsClosed :=
  (windowWeilOperator_selfAdjoint a).isClosed

theorem windowWeilOperator_domain (a : ℝ) :
    (windowWeilOperator a).domain = (windowResolvent a).range := rfl

theorem windowWeilOperator_right_resolvent (a : ℝ) (f : windowL2 a) :
    windowWeilOperator a ⟨windowResolvent a f, ⟨f, rfl⟩⟩ +
      (shiftConstant a : ℂ) • windowResolvent a f = f :=
  coerciveAssociatedOperator_resolvent_identity (windowInclusion a) (windowInclusion_injective a)
    (windowInclusion_denseRange a) (windowFormOperator a) (windowFormOperator_coercive a)
    (shiftConstant a) f

theorem windowWeilOperator_left_resolvent (a : ℝ) (v : (windowWeilOperator a).domain) :
    windowResolvent a (windowWeilOperator a v + (shiftConstant a : ℂ) • (v : windowL2 a)) = v :=
  coerciveAssociatedOperator_left_resolvent (windowInclusion a) (windowInclusion_injective a)
    (windowInclusion_denseRange a) (windowFormOperator a) (windowFormOperator_coercive a)
    (shiftConstant a) v

theorem windowWeilOperator_weak (a : ℝ) (v : windowFormGraph a) (f : windowL2 a) :
    (∀ w : windowFormGraph a,
      Radical.fullPairing (representative a w) (representative a v) =
        inner ℂ f (windowInclusion a w)) ↔
      ∃ hv : windowInclusion a v ∈ (windowWeilOperator a).domain,
        windowWeilOperator a ⟨windowInclusion a v, hv⟩ = f := by
  simpa only [windowFormOperator_inner, add_sub_cancel_right, windowWeilOperator] using
    coerciveAssociatedOperator_eq_iff (windowInclusion a) (windowInclusion_injective a)
      (windowInclusion_denseRange a) (windowFormOperator a) (windowFormOperator_coercive a)
      (shiftConstant a) v f

theorem windowWeilOperator_semibounded (a : ℝ) (v : (windowWeilOperator a).domain) :
    -shiftConstant a * ‖(v : windowL2 a)‖ ^ 2 ≤
      (inner ℂ (windowWeilOperator a v) (v : windowL2 a)).re :=
  coerciveAssociatedOperator_semibounded (windowInclusion a) (windowInclusion_injective a)
    (windowInclusion_denseRange a) (windowFormOperator a) (windowFormOperator_coercive a)
    (shiftConstant a) v

end ThetaTrial.Paper
