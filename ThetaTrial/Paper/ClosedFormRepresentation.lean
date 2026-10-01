import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Tactic

/-!
# Representation of a densely embedded closed form

Let `V` be the Hilbert space of a strictly positive shift of a closed
Hermitian form, and `J : V →L[ℂ] H` its dense injective embedding in the
ambient Hilbert space. Riesz representation gives the bounded resolvent
`J ∘L J.adjoint`. We construct the associated unbounded operator on the
range of that resolvent, and prove that it is self-adjoint and satisfies the
weak form identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Complex Set
open scoped InnerProductSpace

namespace ThetaTrial.Paper.ClosedFormRepresentation

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Riesz solution in the form Hilbert space, followed by its embedding. -/
def formResolvent (J : V →L[ℂ] H) : H →L[ℂ] H := J.comp J.adjoint

@[simp] theorem formResolvent_apply (J : V →L[ℂ] H) (f : H) :
    formResolvent J f = J (J.adjoint f) := rfl

@[simp] theorem formResolvent_adjoint (J : V →L[ℂ] H) :
    (formResolvent J).adjoint = formResolvent J := by
  simp [formResolvent]

theorem formResolvent_inner (J : V →L[ℂ] H) (f g : H) :
    inner ℂ f (formResolvent J g) = inner ℂ (J.adjoint f) (J.adjoint g) := by
  exact (J.adjoint_inner_left (J.adjoint g) f).symm

theorem formResolvent_symmetric (J : V →L[ℂ] H) (f g : H) :
    inner ℂ (formResolvent J f) g = inner ℂ f (formResolvent J g) := by
  rw [← ContinuousLinearMap.adjoint_inner_left, formResolvent_adjoint]

theorem formResolvent_nonneg (J : V →L[ℂ] H) (f : H) :
    0 ≤ (inner ℂ f (formResolvent J f)).re := by
  rw [formResolvent_inner]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem adjoint_injective_of_dense (J : V →L[ℂ] H) (hJ : DenseRange J) :
    Function.Injective J.adjoint := by
  intro f g hfg
  apply hJ.eq_of_inner_left ℂ
  intro v
  rw [← J.adjoint_inner_left, ← J.adjoint_inner_left, hfg]

theorem formResolvent_injective (J : V →L[ℂ] H) (hJ : DenseRange J) :
    Function.Injective (formResolvent J) := by
  exact J.self_comp_adjoint_injective_iff.mpr (adjoint_injective_of_dense J hJ)

theorem formResolvent_denseRange (J : V →L[ℂ] H) (hJ : DenseRange J) :
    DenseRange (formResolvent J) := by
  change Dense ((formResolvent J).range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range, formResolvent_adjoint,
    LinearMap.ker_eq_bot.mpr (formResolvent_injective J hJ)]
  exact Submodule.bot_orthogonal_eq_top

theorem formResolvent_compact (J : V →L[ℂ] H) (hJ : IsCompactOperator J) :
    IsCompactOperator (formResolvent J) := hJ.comp_clm J.adjoint

/-- The shifted form, with conjugate linearity in its first variable. -/
def shiftedForm (J : V →L[ℂ] H) (c : ℝ) (v w : V) : ℂ :=
  inner ℂ v w - (c : ℂ) * inner ℂ (J v) (J w)

/-- The Riesz solution is characterized by the form inner product. -/
theorem riesz_solution_iff (J : V →L[ℂ] H) (f : H) (v : V) :
    (∀ w : V, inner ℂ v w = inner ℂ f (J w)) ↔ v = J.adjoint f := by
  constructor
  · intro h
    apply ext_inner_right ℂ
    intro w
    exact (h w).trans (J.adjoint_inner_left w f).symm
  · rintro rfl w
    exact J.adjoint_inner_left w f


/-- Algebraic inverse of an injective bounded operator on its range. -/
def inverseOnRange (R : H →L[ℂ] H) (hR : Function.Injective R) : R.range →ₗ[ℂ] H :=
  (LinearEquiv.ofInjective R.toLinearMap hR).symm.toLinearMap

@[simp] theorem apply_inverseOnRange (R : H →L[ℂ] H) (hR : Function.Injective R)
    (x : R.range) : R (inverseOnRange R hR x) = (x : H) := by
  exact LinearEquiv.ofInjective_symm_apply R.toLinearMap x

@[simp] theorem inverseOnRange_apply (R : H →L[ℂ] H) (hR : Function.Injective R)
    (f : H) : inverseOnRange R hR ⟨R f, ⟨f, rfl⟩⟩ = f := by
  exact (LinearEquiv.ofInjective R.toLinearMap hR).symm_apply_apply f

/-- The inverse resolvent minus a real scalar, as a partial linear map. -/
def operatorOfResolvent (R : H →L[ℂ] H) (hR : Function.Injective R) (c : ℝ) :
    H →ₗ.[ℂ] H where
  domain := R.range
  toFun := inverseOnRange R hR - (c : ℂ) • R.range.subtype

@[simp] theorem operatorOfResolvent_domain (R : H →L[ℂ] H)
    (hR : Function.Injective R) (c : ℝ) :
    (operatorOfResolvent R hR c).domain = R.range := rfl

@[simp] theorem operatorOfResolvent_apply (R : H →L[ℂ] H)
    (hR : Function.Injective R) (c : ℝ) (x : R.range) :
    operatorOfResolvent R hR c x = inverseOnRange R hR x - (c : ℂ) • (x : H) := rfl

@[simp] theorem operatorOfResolvent_resolvent (R : H →L[ℂ] H)
    (hR : Function.Injective R) (c : ℝ) (f : H) :
    operatorOfResolvent R hR c ⟨R f, ⟨f, rfl⟩⟩ = f - (c : ℂ) • R f := by
  rw [operatorOfResolvent_apply, inverseOnRange_apply]

theorem operatorOfResolvent_symmetric (R : H →L[ℂ] H)
    (hR : Function.Injective R) (c : ℝ)
    (hsym : ∀ f g : H, inner ℂ (R f) g = inner ℂ f (R g)) :
    (operatorOfResolvent R hR c).IsFormalAdjoint (operatorOfResolvent R hR c) := by
  intro x y
  change inner ℂ (inverseOnRange R hR x - (c : ℂ) • (x : H)) (y : H) =
    inner ℂ (x : H) (inverseOnRange R hR y - (c : ℂ) • (y : H))
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  congr 1
  nth_rw 1 [← apply_inverseOnRange R hR y]
  rw [← hsym, apply_inverseOnRange]

/-- An injective bounded symmetric operator with dense range has a
self-adjoint inverse on its range, also after subtracting a real scalar. -/
theorem operatorOfResolvent_selfAdjoint (R : H →L[ℂ] H)
    (hR : Function.Injective R) (c : ℝ)
    (hd : DenseRange R)
    (hsym : ∀ f g : H, inner ℂ (R f) g = inner ℂ f (R g)) :
    IsSelfAdjoint (operatorOfResolvent R hR c) := by
  let A := operatorOfResolvent R hR c
  have hAd : Dense (A.domain : Set H) := hd
  have hAform : A.IsFormalAdjoint A := operatorOfResolvent_symmetric R hR c hsym
  have hle : A ≤ A.adjoint := hAform.le_adjoint hAd
  have hrev : A.adjoint.domain ≤ A.domain := by
    intro x hx
    let y : A.adjoint.domain := ⟨x, hx⟩
    have heq : R (A.adjoint y + (c : ℂ) • x) = x := by
      apply ext_inner_right ℂ
      intro f
      have h := LinearPMap.adjoint_isFormalAdjoint hAd y
        (⟨R f, ⟨f, rfl⟩⟩ : A.domain)
      change inner ℂ (A.adjoint y) (R f) =
        inner ℂ x (operatorOfResolvent R hR c ⟨R f, ⟨f, rfl⟩⟩) at h
      rw [operatorOfResolvent_resolvent, inner_sub_right, inner_smul_right] at h
      rw [map_add, map_smul, inner_add_left, inner_smul_left, Complex.conj_ofReal,
        hsym, hsym]
      linear_combination h
    exact ⟨A.adjoint y + (c : ℂ) • x, heq⟩
  change A.adjoint = A
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hrev)).symm

/-- The self-adjoint operator represented by a densely embedded shifted
form Hilbert space. -/
def associatedOperator (J : V →L[ℂ] H) (hJ : DenseRange J) (c : ℝ) : H →ₗ.[ℂ] H :=
  operatorOfResolvent (formResolvent J) (formResolvent_injective J hJ) c

theorem associatedOperator_selfAdjoint (J : V →L[ℂ] H) (hJ : DenseRange J) (c : ℝ) :
    IsSelfAdjoint (associatedOperator J hJ c) :=
  operatorOfResolvent_selfAdjoint _ _ c (formResolvent_denseRange J hJ)
    (formResolvent_symmetric J)

theorem associatedOperator_closed (J : V →L[ℂ] H) (hJ : DenseRange J) (c : ℝ) :
    (associatedOperator J hJ c).IsClosed :=
  (associatedOperator_selfAdjoint J hJ c).isClosed


/-- The form-domain vector represented by an operator-domain vector. -/
def operatorFormVector (J : V →L[ℂ] H) (hJ : DenseRange J) (c : ℝ)
    (x : (associatedOperator J hJ c).domain) : V :=
  J.adjoint (inverseOnRange (formResolvent J) (formResolvent_injective J hJ) x)

@[simp] theorem operatorFormVector_embedding (J : V →L[ℂ] H)
    (hJ : DenseRange J) (c : ℝ) (x : (associatedOperator J hJ c).domain) :
    J (operatorFormVector J hJ c x) = (x : H) :=
  apply_inverseOnRange (formResolvent J) (formResolvent_injective J hJ) x

/-- The complete weak representation identity, including all cross terms. -/
theorem associatedOperator_represents (J : V →L[ℂ] H) (hJ : DenseRange J)
    (c : ℝ) (x : (associatedOperator J hJ c).domain) (v : V) :
    inner ℂ (associatedOperator J hJ c x) (J v) =
      shiftedForm J c (operatorFormVector J hJ c x) v := by
  change inner ℂ (inverseOnRange (formResolvent J) (formResolvent_injective J hJ) x -
    (c : ℂ) • (x : H)) (J v) = _
  rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal]
  unfold shiftedForm
  rw [operatorFormVector_embedding]
  unfold operatorFormVector
  rw [J.adjoint_inner_left]

/-- Exact characterization of the operator domain by representability of
the shifted form against all form-domain tests. -/
theorem associatedOperator_domain_iff (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J) (c : ℝ) (v : V) :
    J v ∈ (associatedOperator J hJ c).domain ↔
      ∃ f : H, ∀ w : V, shiftedForm J c v w = inner ℂ f (J w) := by
  constructor
  · intro hv
    let x : (associatedOperator J hJ c).domain := ⟨J v, hv⟩
    have hx : operatorFormVector J hJ c x = v :=
      hJi (operatorFormVector_embedding J hJ c x)
    refine ⟨associatedOperator J hJ c x, fun w => ?_⟩
    rw [← hx]
    exact (associatedOperator_represents J hJ c x w).symm
  · rintro ⟨f, hf⟩
    have hv : v = J.adjoint (f + (c : ℂ) • J v) := by
      apply (riesz_solution_iff J _ v).mp
      intro w
      have h := hf w
      unfold shiftedForm at h
      rw [inner_add_left, inner_smul_left, Complex.conj_ofReal]
      linear_combination h
    change J v ∈ (formResolvent J).range
    refine ⟨f + (c : ℂ) • J v, ?_⟩
    exact congrArg J hv.symm

theorem associatedOperator_representer_unique (J : V →L[ℂ] H)
    (hJ : DenseRange J) (c : ℝ) (v : V) {f g : H}
    (hf : ∀ w : V, shiftedForm J c v w = inner ℂ f (J w))
    (hg : ∀ w : V, shiftedForm J c v w = inner ℂ g (J w)) : f = g := by
  exact hJ.eq_of_inner_left ℂ (fun w => (hf w).symm.trans (hg w))

/-- The inverse relation holds on every ambient vector. -/
theorem associatedOperator_resolvent_identity (J : V →L[ℂ] H)
    (hJ : DenseRange J) (c : ℝ) (f : H) :
    associatedOperator J hJ c ⟨formResolvent J f, ⟨f, rfl⟩⟩ +
      (c : ℂ) • formResolvent J f = f := by
  change operatorOfResolvent _ _ c _ + _ = _
  rw [operatorOfResolvent_resolvent, sub_add_cancel]

/-- Exact energy identity on the operator domain. -/
theorem associatedOperator_energy (J : V →L[ℂ] H) (hJ : DenseRange J)
    (c : ℝ) (x : (associatedOperator J hJ c).domain) :
    (inner ℂ (associatedOperator J hJ c x) (x : H)).re =
      ‖operatorFormVector J hJ c x‖ ^ 2 - c * ‖(x : H)‖ ^ 2 := by
  nth_rw 1 [← operatorFormVector_embedding J hJ c x]
  rw [associatedOperator_represents]
  unfold shiftedForm
  rw [operatorFormVector_embedding]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem associatedOperator_semibounded (J : V →L[ℂ] H) (hJ : DenseRange J)
    (c : ℝ) (x : (associatedOperator J hJ c).domain) :
    -c * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (associatedOperator J hJ c x) (x : H)).re := by
  rw [associatedOperator_energy]
  nlinarith [sq_nonneg ‖operatorFormVector J hJ c x‖]

/-- The operator domain is also dense in the form norm. -/
theorem adjoint_denseRange_of_injective (J : V →L[ℂ] H)
    (hJ : Function.Injective J) : DenseRange J.adjoint := by
  change Dense (J.adjoint.range : Set V)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← J.orthogonal_ker, LinearMap.ker_eq_bot.mpr hJ]
  exact Submodule.bot_orthogonal_eq_top

end ThetaTrial.Paper.ClosedFormRepresentation
