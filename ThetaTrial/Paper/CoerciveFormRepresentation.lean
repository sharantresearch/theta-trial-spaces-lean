import ThetaTrial.Paper.ClosedFormRepresentation

/-!
# Coercive complex forms on a given form domain

The graph norm of the form domain need not be the norm of the positive
shifted form. This file constructs the complex Lax–Milgram inverse in the
given Hilbert topology, and then the resolvent `J B⁻¹ J*`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Complex Set
open scoped InnerProductSpace ComplexConjugate NNReal

namespace ThetaTrial.Paper.CoerciveFormRepresentation
open ClosedFormRepresentation

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strict positivity uniformly in the original Hilbert norm. -/
def IsCoerciveOperator (B : V →L[ℂ] V) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ v : V, m * ‖v‖ ^ 2 ≤ (inner ℂ (B v) v).re

theorem coercive_bounded_below {B : V →L[ℂ] V} (hB : IsCoerciveOperator B) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : V, m * ‖v‖ ≤ ‖B v‖ := by
  obtain ⟨m, hm, hb⟩ := hB
  refine ⟨m, hm, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hi := re_inner_le_norm (𝕜 := ℂ) (B v) v
    change (inner ℂ (B v) v).re ≤ ‖B v‖ * ‖v‖ at hi
    have hc := hb v
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith only [hc, hi]

theorem coercive_antilipschitz {B : V →L[ℂ] V} (hB : IsCoerciveOperator B) :
    ∃ K : ℝ≥0, AntilipschitzWith K B := by
  obtain ⟨m, hm, hb⟩ := coercive_bounded_below hB
  refine ⟨m⁻¹.toNNReal, B.antilipschitz_of_bound ?_⟩
  simp only [Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hm.le)]
  intro v
  exact (le_inv_mul_iff₀ hm).mpr (hb v)

theorem coercive_injective {B : V →L[ℂ] V} (hB : IsCoerciveOperator B) :
    Function.Injective B := by
  obtain ⟨K, hK⟩ := coercive_antilipschitz hB
  exact hK.injective

theorem coercive_range_closed {B : V →L[ℂ] V} (hB : IsCoerciveOperator B) :
    IsClosed (B.range : Set V) := by
  obtain ⟨K, hK⟩ := coercive_antilipschitz hB
  exact hK.isClosed_range B.uniformContinuous

/-- Coercivity alone, without symmetry, gives surjectivity in the complex
Hilbert space. This supplies the missing complex Lax–Milgram step. -/
theorem coercive_range_top {B : V →L[ℂ] V} (hB : IsCoerciveOperator B) :
    B.range = ⊤ := by
  have := (coercive_range_closed hB).completeSpace_coe
  rw [← B.range.orthogonal_orthogonal, Submodule.eq_top_iff']
  intro v w hw
  obtain ⟨m, hm, hc⟩ := hB
  have hzero : w = 0 := by
    have hi : inner ℂ (B w) w = 0 := hw (B w) ⟨w, rfl⟩
    have hb := hc w
    rw [hi] at hb
    have hn : ‖w‖ = 0 := by
      simp only [zero_re] at hb
      have hz : m * ‖w‖ ^ 2 = 0 :=
        le_antisymm hb (mul_nonneg hm.le (sq_nonneg _))
      exact sq_eq_zero_iff.mp (Or.resolve_left (mul_eq_zero.mp hz) hm.ne')
    exact norm_eq_zero.mp hn
  simp [hzero]

def coerciveEquiv (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) : V ≃L[ℂ] V :=
  ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr (coercive_injective hB)) (coercive_range_top hB)

def coerciveInverse (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) : V →L[ℂ] V :=
  (coerciveEquiv B hB).symm.toContinuousLinearMap

@[simp] theorem coercive_apply_inverse (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (v : V) : B (coerciveInverse B hB v) = v :=
  (coerciveEquiv B hB).apply_symm_apply v

@[simp] theorem coercive_inverse_apply (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (v : V) : coerciveInverse B hB (B v) = v :=
  (coerciveEquiv B hB).symm_apply_apply v

theorem coerciveInverse_symmetric (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) (v w : V) :
    inner ℂ (coerciveInverse B hB v) w = inner ℂ v (coerciveInverse B hB w) := by
  simpa only [coercive_apply_inverse] using
    (hsym (coerciveInverse B hB v) (coerciveInverse B hB w)).symm

/-- Bounded positive shifted form represented by Riesz on the given
Hilbert graph space. -/
def formOperator (q : V →L⋆[ℂ] V →L[ℂ] ℂ) : V →L[ℂ] V :=
  InnerProductSpace.continuousLinearMapOfBilin q

@[simp] theorem formOperator_inner (q : V →L⋆[ℂ] V →L[ℂ] ℂ) (v w : V) :
    inner ℂ (formOperator q v) w = q v w :=
  InnerProductSpace.continuousLinearMapOfBilin_apply q v w

theorem formOperator_coercive (q : V →L⋆[ℂ] V →L[ℂ] ℂ)
    (hq : ∃ m : ℝ, 0 < m ∧ ∀ v : V, m * ‖v‖ ^ 2 ≤ (q v v).re) :
    IsCoerciveOperator (formOperator q) := by
  simpa only [IsCoerciveOperator, formOperator_inner] using hq

theorem formOperator_symmetric (q : V →L⋆[ℂ] V →L[ℂ] ℂ)
    (hq : ∀ v w : V, conj (q w v) = q v w) (v w : V) :
    inner ℂ (formOperator q v) w = inner ℂ v (formOperator q w) := by
  rw [formOperator_inner, ← inner_conj_symm, formOperator_inner, hq]


/-- Resolvent constructed from the original graph-space Riesz operator. -/
def coerciveResolvent (J : V →L[ℂ] H) (B : V →L[ℂ] V)
    (hB : IsCoerciveOperator B) : H →L[ℂ] H :=
  J.comp ((coerciveInverse B hB).comp J.adjoint)

@[simp] theorem coerciveResolvent_apply (J : V →L[ℂ] H) (B : V →L[ℂ] V)
    (hB : IsCoerciveOperator B) (f : H) :
    coerciveResolvent J B hB f = J (coerciveInverse B hB (J.adjoint f)) := rfl

theorem coerciveResolvent_injective (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) :
    Function.Injective (coerciveResolvent J B hB) :=
  hJi.comp ((coerciveEquiv B hB).symm.injective.comp (adjoint_injective_of_dense J hJ))

theorem coerciveResolvent_symmetric (J : V →L[ℂ] H)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) (f g : H) :
    inner ℂ (coerciveResolvent J B hB f) g =
      inner ℂ f (coerciveResolvent J B hB g) := by
  change inner ℂ (J (coerciveInverse B hB (J.adjoint f))) g =
    inner ℂ f (J (coerciveInverse B hB (J.adjoint g)))
  rw [← J.adjoint_inner_right, coerciveInverse_symmetric B hB hsym,
    J.adjoint_inner_left]

theorem coerciveResolvent_denseRange (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) :
    DenseRange (coerciveResolvent J B hB) := by
  let R := coerciveResolvent J B hB
  have hstar : R.adjoint = R :=
    ((ContinuousLinearMap.eq_adjoint_iff R R).mpr
      (coerciveResolvent_symmetric J B hB hsym)).symm
  change Dense (R.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range, hstar,
    LinearMap.ker_eq_bot.mpr (coerciveResolvent_injective J hJi hJ B hB)]
  exact Submodule.bot_orthogonal_eq_top

theorem coerciveResolvent_compact (J : V →L[ℂ] H) (hJ : IsCompactOperator J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) :
    IsCompactOperator (coerciveResolvent J B hB) :=
  hJ.comp_clm ((coerciveInverse B hB).comp J.adjoint)

theorem coerciveResolvent_selfAdjoint (J : V →L[ℂ] H)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) :
    IsSelfAdjoint (coerciveResolvent J B hB) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact coerciveResolvent_symmetric J B hB hsym

theorem coerciveResolvent_nonneg (J : V →L[ℂ] H)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (f : H) :
    0 ≤ (inner ℂ f (coerciveResolvent J B hB f)).re := by
  rw [coerciveResolvent_apply, ← J.adjoint_inner_left]
  obtain ⟨m, hm, hc⟩ := hB
  have h := hc (coerciveInverse B ⟨m, hm, hc⟩ (J.adjoint f))
  rw [coercive_apply_inverse] at h
  exact (mul_nonneg hm.le (sq_nonneg _)).trans h

/-- Operator construction for a coercive perturbation of the graph
inner product. -/
def coerciveAssociatedOperator (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ) : H →ₗ.[ℂ] H :=
  operatorOfResolvent (coerciveResolvent J B hB)
    (coerciveResolvent_injective J hJi hJ B hB) c

theorem coerciveAssociatedOperator_selfAdjoint (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) (c : ℝ) :
    IsSelfAdjoint (coerciveAssociatedOperator J hJi hJ B hB c) :=
  operatorOfResolvent_selfAdjoint _ _ c (coerciveResolvent_denseRange J hJi hJ B hB hsym)
    (coerciveResolvent_symmetric J B hB hsym)

theorem coerciveAssociatedOperator_closed (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) (c : ℝ) :
    (coerciveAssociatedOperator J hJi hJ B hB c).IsClosed :=
  (coerciveAssociatedOperator_selfAdjoint J hJi hJ B hB hsym c).isClosed

def coerciveOperatorFormVector (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ)
    (x : (coerciveAssociatedOperator J hJi hJ B hB c).domain) : V :=
  coerciveInverse B hB (J.adjoint (inverseOnRange (coerciveResolvent J B hB)
    (coerciveResolvent_injective J hJi hJ B hB) x))

@[simp] theorem coerciveOperatorFormVector_embedding (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ)
    (x : (coerciveAssociatedOperator J hJi hJ B hB c).domain) :
    J (coerciveOperatorFormVector J hJi hJ B hB c x) = (x : H) :=
  apply_inverseOnRange (coerciveResolvent J B hB)
    (coerciveResolvent_injective J hJi hJ B hB) x

/-- Weak identity on every original graph-space test, without taking a
closure or deleting any term of the form. -/
theorem coerciveAssociatedOperator_represents (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ)
    (x : (coerciveAssociatedOperator J hJi hJ B hB c).domain) (w : V) :
    inner ℂ (coerciveAssociatedOperator J hJi hJ B hB c x) (J w) =
      inner ℂ (B (coerciveOperatorFormVector J hJi hJ B hB c x)) w -
        (c : ℂ) * inner ℂ (x : H) (J w) := by
  change inner ℂ (inverseOnRange (coerciveResolvent J B hB)
    (coerciveResolvent_injective J hJi hJ B hB) x - (c : ℂ) • (x : H)) (J w) = _
  rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal]
  unfold coerciveOperatorFormVector
  rw [coercive_apply_inverse, J.adjoint_inner_left]

/-- Precise domain of the represented operator. -/
theorem coerciveAssociatedOperator_domain_iff (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ) (v : V) :
    J v ∈ (coerciveAssociatedOperator J hJi hJ B hB c).domain ↔
      ∃ f : H, ∀ w : V, inner ℂ (B v) w - (c : ℂ) * inner ℂ (J v) (J w) =
        inner ℂ f (J w) := by
  constructor
  · intro hv
    let x : (coerciveAssociatedOperator J hJi hJ B hB c).domain := ⟨J v, hv⟩
    have hx : coerciveOperatorFormVector J hJi hJ B hB c x = v :=
      hJi (coerciveOperatorFormVector_embedding J hJi hJ B hB c x)
    refine ⟨coerciveAssociatedOperator J hJi hJ B hB c x, fun w => ?_⟩
    simpa only [hx] using (coerciveAssociatedOperator_represents J hJi hJ B hB c x w).symm
  · rintro ⟨f, hf⟩
    have hv : B v = J.adjoint (f + (c : ℂ) • J v) := by
      apply (riesz_solution_iff J _ (B v)).mp
      intro w
      have h := hf w
      rw [inner_add_left, inner_smul_left, Complex.conj_ofReal]
      linear_combination h
    change J v ∈ (coerciveResolvent J B hB).range
    refine ⟨f + (c : ℂ) • J v, ?_⟩
    change J (coerciveInverse B hB (J.adjoint (f + (c : ℂ) • J v))) = J v
    rw [← hv, coercive_inverse_apply]

theorem coerciveAssociatedOperator_resolvent_identity (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ) (f : H) :
    coerciveAssociatedOperator J hJi hJ B hB c
        ⟨coerciveResolvent J B hB f, ⟨f, rfl⟩⟩ +
      (c : ℂ) • coerciveResolvent J B hB f = f := by
  change operatorOfResolvent _ _ c _ + _ = _
  rw [operatorOfResolvent_resolvent, sub_add_cancel]

theorem coerciveAssociatedOperator_semibounded (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ)
    (x : (coerciveAssociatedOperator J hJi hJ B hB c).domain) :
    -c * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ (coerciveAssociatedOperator J hJi hJ B hB c x) (x : H)).re := by
  let v := coerciveOperatorFormVector J hJi hJ B hB c x
  have hv : J v = (x : H) := coerciveOperatorFormVector_embedding J hJi hJ B hB c x
  have h := coerciveAssociatedOperator_represents J hJi hJ B hB c x v
  rw [hv] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inner_self_eq_norm_sq_to_K] at hr
  norm_cast at hr
  change (inner ℂ (coerciveAssociatedOperator J hJi hJ B hB c x) (x : H)).re =
    (inner ℂ (B v) v).re - c * ‖(x : H)‖ ^ 2 at hr
  obtain ⟨m, hm, hc⟩ := hB
  have hc' := hc v
  nlinarith [mul_nonneg hm.le (sq_nonneg ‖v‖)]


/-- The weak equation characterizes both membership and the operator value, rather than only the operator domain. -/
theorem coerciveAssociatedOperator_eq_iff (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ) (v : V) (f : H) :
    (∀ w : V, inner ℂ (B v) w - (c : ℂ) * inner ℂ (J v) (J w) = inner ℂ f (J w)) ↔
      ∃ hv : J v ∈ (coerciveAssociatedOperator J hJi hJ B hB c).domain,
        coerciveAssociatedOperator J hJi hJ B hB c ⟨J v, hv⟩ = f := by
  constructor
  · intro hf
    have hv := (coerciveAssociatedOperator_domain_iff J hJi hJ B hB c v).mpr ⟨f, hf⟩
    refine ⟨hv, ?_⟩
    have hx : coerciveOperatorFormVector J hJi hJ B hB c ⟨J v, hv⟩ = v :=
      hJi (coerciveOperatorFormVector_embedding J hJi hJ B hB c ⟨J v, hv⟩)
    apply hJ.eq_of_inner_left ℂ
    intro w
    rw [coerciveAssociatedOperator_represents, hx]
    exact hf w
  · rintro ⟨hv, hval⟩ w
    have hx : coerciveOperatorFormVector J hJi hJ B hB c ⟨J v, hv⟩ = v :=
      hJi (coerciveOperatorFormVector_embedding J hJi hJ B hB c ⟨J v, hv⟩)
    have h := coerciveAssociatedOperator_represents J hJi hJ B hB c ⟨J v, hv⟩ w
    simpa only [hx, hval] using h.symm

theorem coerciveAssociatedOperator_left_resolvent (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J)
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B) (c : ℝ)
    (x : (coerciveAssociatedOperator J hJi hJ B hB c).domain) :
    coerciveResolvent J B hB
      (coerciveAssociatedOperator J hJi hJ B hB c x + (c : ℂ) • (x : H)) = (x : H) := by
  change coerciveResolvent J B hB
    ((inverseOnRange (coerciveResolvent J B hB)
      (coerciveResolvent_injective J hJi hJ B hB) x - (c : ℂ) • (x : H)) +
      (c : ℂ) • (x : H)) = _
  rw [sub_add_cancel, apply_inverseOnRange]

/-- Closed-form representation with compact resolvent on a given complete
graph space: the operator and both inverse identities are constructed from
hypotheses on the form and its embedding. -/
theorem exists_compact_form_representation
    (J : V →L[ℂ] H) (hJi : Function.Injective J) (hJ : DenseRange J)
    (hJcompact : IsCompactOperator J) (q : V →L⋆[ℂ] V →L[ℂ] ℂ)
    (hqHermitian : ∀ v w : V, conj (q w v) = q v w)
    (hqCoercive : ∃ m : ℝ, 0 < m ∧ ∀ v : V, m * ‖v‖ ^ 2 ≤ (q v v).re)
    (c : ℝ) :
    ∃ (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H),
      IsSelfAdjoint A ∧ A.IsClosed ∧ IsCompactOperator R ∧
      A.domain = R.range ∧
      (∀ f : H, ∃ x : A.domain, (x : H) = R f ∧ A x + (c : ℂ) • (x : H) = f) ∧
      (∀ x : A.domain, R (A x + (c : ℂ) • (x : H)) = (x : H)) ∧
      (∀ v : V, ∀ f : H,
        (∀ w : V, q v w - (c : ℂ) * inner ℂ (J v) (J w) = inner ℂ f (J w)) ↔
          ∃ hv : J v ∈ A.domain, A ⟨J v, hv⟩ = f) ∧
      (∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (A x) (x : H)).re) := by
  let B := formOperator q
  have hB : IsCoerciveOperator B := formOperator_coercive q hqCoercive
  have hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w) :=
    formOperator_symmetric q hqHermitian
  let A := coerciveAssociatedOperator J hJi hJ B hB c
  let R := coerciveResolvent J B hB
  refine ⟨A, R, coerciveAssociatedOperator_selfAdjoint J hJi hJ B hB hsym c,
    coerciveAssociatedOperator_closed J hJi hJ B hB hsym c,
    coerciveResolvent_compact J hJcompact B hB, rfl, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨⟨R f, ⟨f, rfl⟩⟩, rfl, coerciveAssociatedOperator_resolvent_identity J hJi hJ B hB c f⟩
  · exact coerciveAssociatedOperator_left_resolvent J hJi hJ B hB c
  · intro v f
    simpa only [B, formOperator_inner] using
      coerciveAssociatedOperator_eq_iff J hJi hJ B hB c v f
  · exact coerciveAssociatedOperator_semibounded J hJi hJ B hB c

end ThetaTrial.Paper.CoerciveFormRepresentation
