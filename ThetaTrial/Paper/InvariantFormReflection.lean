import ThetaTrial.Paper.CoerciveFormRepresentation

/-!
# Unitary symmetries of the operator represented by a coercive form

Form invariance forces commutation of the Riesz operator and its inverse.
Together with the intertwining of the form embedding, this proves that
the resolvent and its associated unbounded operator commute with
the symmetry. In particular, this applies to reflection involutions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open scoped InnerProductSpace

namespace ThetaTrial.Paper.InvariantFormReflection
open CoerciveFormRepresentation ClosedFormRepresentation

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Invariance of the form implies commutation of its Riesz operator. -/
theorem formOperator_commutes (RV : V ≃ₗᵢ[ℂ] V)
    (q : V →L⋆[ℂ] V →L[ℂ] ℂ)
    (hq : ∀ v w : V, q (RV v) (RV w) = q v w) (v : V) :
    formOperator q (RV v) = RV (formOperator q v) := by
  apply ext_inner_right ℂ
  intro w
  obtain ⟨w, rfl⟩ := RV.surjective w
  rw [formOperator_inner, hq, RV.inner_map_map, formOperator_inner]

/-- The adjoint embedding intertwines the same unitary symmetries. -/
theorem adjoint_intertwines (RV : V ≃ₗᵢ[ℂ] V) (R_H : H ≃ₗᵢ[ℂ] H)
    (J : V →L[ℂ] H) (hJ : ∀ v : V, J (RV v) = R_H (J v)) (f : H) :
    J.adjoint (R_H f) = RV (J.adjoint f) := by
  apply ext_inner_right ℂ
  intro w
  obtain ⟨w, rfl⟩ := RV.surjective w
  rw [J.adjoint_inner_left, hJ, R_H.inner_map_map, RV.inner_map_map,
    J.adjoint_inner_left]

theorem coerciveInverse_commutes (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (R : V →ₗ[ℂ] V) (hR : ∀ v : V, B (R v) = R (B v)) (v : V) :
    coerciveInverse B hB (R v) = R (coerciveInverse B hB v) := by
  apply coercive_injective hB
  rw [coercive_apply_inverse, hR, coercive_apply_inverse]

/-- The inverse commutation follows from invariance of the form. -/
theorem formInverse_commutes (RV : V ≃ₗᵢ[ℂ] V)
    (q : V →L⋆[ℂ] V →L[ℂ] ℂ) (hB : IsCoerciveOperator (formOperator q))
    (hq : ∀ v w : V, q (RV v) (RV w) = q v w) (v : V) :
    coerciveInverse (formOperator q) hB (RV v) =
      RV (coerciveInverse (formOperator q) hB v) :=
  coerciveInverse_commutes (formOperator q) hB RV.toLinearEquiv.toLinearMap
    (formOperator_commutes RV q hq) v

theorem coerciveResolvent_commutes (RV : V ≃ₗᵢ[ℂ] V) (R_H : H ≃ₗᵢ[ℂ] H)
    (J : V →L[ℂ] H) (hJ : ∀ v : V, J (RV v) = R_H (J v))
    (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hBR : ∀ v : V, B (RV v) = RV (B v)) (f : H) :
    coerciveResolvent J B hB (R_H f) = R_H (coerciveResolvent J B hB f) := by
  have hinv (v : V) : coerciveInverse B hB (RV v) = RV (coerciveInverse B hB v) :=
    coerciveInverse_commutes B hB RV.toLinearEquiv.toLinearMap hBR v
  rw [coerciveResolvent_apply, adjoint_intertwines RV R_H J hJ,
    hinv, hJ, coerciveResolvent_apply]

/-- The form resolvent commutes with the ambient symmetry. -/
theorem formResolvent_commutes (RV : V ≃ₗᵢ[ℂ] V) (R_H : H ≃ₗᵢ[ℂ] H)
    (J : V →L[ℂ] H) (hJ : ∀ v : V, J (RV v) = R_H (J v))
    (q : V →L⋆[ℂ] V →L[ℂ] ℂ) (hB : IsCoerciveOperator (formOperator q))
    (hq : ∀ v w : V, q (RV v) (RV w) = q v w) (f : H) :
    coerciveResolvent J (formOperator q) hB (R_H f) =
      R_H (coerciveResolvent J (formOperator q) hB f) :=
  coerciveResolvent_commutes RV R_H J hJ (formOperator q) hB
    (formOperator_commutes RV q hq) f

/-- Commutation preserves the range domain of the inverse resolvent. -/
theorem operatorOfResolvent_domain_invariant (R : H →L[ℂ] H)
    (hRi : Function.Injective R) (c : ℝ) (U : H →ₗ[ℂ] H)
    (hU : ∀ f : H, R (U f) = U (R f)) {x : H}
    (hx : x ∈ (operatorOfResolvent R hRi c).domain) :
    U x ∈ (operatorOfResolvent R hRi c).domain := by
  obtain ⟨f, rfl⟩ := hx
  exact ⟨U f, hU f⟩

theorem inverseOnRange_commutes (R : H →L[ℂ] H)
    (hRi : Function.Injective R) (U : H →ₗ[ℂ] H)
    (hU : ∀ f : H, R (U f) = U (R f)) (x : R.range) :
    inverseOnRange R hRi
        ⟨U x, operatorOfResolvent_domain_invariant R hRi 0 U hU x.property⟩ =
      U (inverseOnRange R hRi x) := by
  apply hRi
  rw [apply_inverseOnRange, hU, apply_inverseOnRange]

/-- The unbounded operator itself commutes, including its precise domain. -/
theorem operatorOfResolvent_commutes (R : H →L[ℂ] H)
    (hRi : Function.Injective R) (c : ℝ) (U : H →ₗ[ℂ] H)
    (hU : ∀ f : H, R (U f) = U (R f))
    (x : (operatorOfResolvent R hRi c).domain) :
    operatorOfResolvent R hRi c
        ⟨U x, operatorOfResolvent_domain_invariant R hRi c U hU x.property⟩ =
      U (operatorOfResolvent R hRi c x) := by
  change inverseOnRange R hRi _ - (c : ℂ) • U (x : H) =
    U (inverseOnRange R hRi x - (c : ℂ) • (x : H))
  rw [map_sub, map_smul, inverseOnRange_commutes R hRi U hU]

theorem formAssociatedOperator_domain_invariant
    (RV : V ≃ₗᵢ[ℂ] V) (R_H : H ≃ₗᵢ[ℂ] H)
    (J : V →L[ℂ] H) (hJi : Function.Injective J) (hJd : DenseRange J)
    (hJ : ∀ v : V, J (RV v) = R_H (J v))
    (q : V →L⋆[ℂ] V →L[ℂ] ℂ) (hB : IsCoerciveOperator (formOperator q))
    (hq : ∀ v w : V, q (RV v) (RV w) = q v w) (c : ℝ) {x : H}
    (hx : x ∈ (coerciveAssociatedOperator J hJi hJd (formOperator q) hB c).domain) :
    R_H x ∈ (coerciveAssociatedOperator J hJi hJd (formOperator q) hB c).domain :=
  operatorOfResolvent_domain_invariant _ _ c R_H.toLinearEquiv.toLinearMap
    (formResolvent_commutes RV R_H J hJ q hB hq) hx

theorem formAssociatedOperator_commutes
    (RV : V ≃ₗᵢ[ℂ] V) (R_H : H ≃ₗᵢ[ℂ] H)
    (J : V →L[ℂ] H) (hJi : Function.Injective J) (hJd : DenseRange J)
    (hJ : ∀ v : V, J (RV v) = R_H (J v))
    (q : V →L⋆[ℂ] V →L[ℂ] ℂ) (hB : IsCoerciveOperator (formOperator q))
    (hq : ∀ v w : V, q (RV v) (RV w) = q v w) (c : ℝ)
    (x : (coerciveAssociatedOperator J hJi hJd (formOperator q) hB c).domain) :
    coerciveAssociatedOperator J hJi hJd (formOperator q) hB c
        ⟨R_H x, formAssociatedOperator_domain_invariant RV R_H J hJi hJd hJ q hB hq c
          x.property⟩ =
      R_H (coerciveAssociatedOperator J hJi hJd (formOperator q) hB c x) :=
  operatorOfResolvent_commutes _ _ c R_H.toLinearEquiv.toLinearMap
    (formResolvent_commutes RV R_H J hJ q hB hq) x

end ThetaTrial.Paper.InvariantFormReflection
