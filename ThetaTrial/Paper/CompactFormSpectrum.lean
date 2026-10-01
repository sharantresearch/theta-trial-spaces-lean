import ThetaTrial.Paper.CoerciveFormRepresentation
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Cardinal.Order

/-!
# Spectral consequences of a compact form resolvent

This file constructs spectral data from a positive, injective compact
self-adjoint resolvent. No eigenbasis or variational characterization is
an input. The represented unbounded operator is the inverse resolvent
minus the shift constructed in `ClosedFormRepresentation`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Complex Set Module.End Filter
open scoped InnerProductSpace ComplexConjugate Topology

namespace ThetaTrial.Paper.CompactFormSpectrum

open ClosedFormRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem eigenspace_zero_of_injective (R : H →L[ℂ] H) (hR : Function.Injective R) :
    eigenspace R.toLinearMap 0 = ⊥ := by
  rw [eigenspace_zero]
  exact LinearMap.ker_eq_bot.mpr hR

theorem finite_eigenspace (R : H →L[ℂ] H) (hR : Function.Injective R)
    (hcompact : IsCompactOperator R) (r : ℝ) :
    FiniteDimensional ℂ (eigenspace R.toLinearMap (r : ℂ)) := by
  by_cases hr : r = 0
  · subst r
    rw [Complex.ofReal_zero, eigenspace_zero_of_injective R hR]
    infer_instance
  · exact R.finite_dimensional_eigenspace hcompact _ (Complex.ofReal_ne_zero.mpr hr)

theorem eigenvalue_positive (R : H →L[ℂ] H) (hR : Function.Injective R)
    (hpos : ∀ x : H, 0 ≤ (inner ℂ x (R x)).re) {r : ℝ}
    (hr : HasEigenvalue R.toLinearMap (r : ℂ)) : 0 < r := by
  have hn : 0 ≤ r := eigenvalue_nonneg_of_nonneg hr hpos
  have hne : r ≠ 0 := by
    intro he
    subst r
    exact hr (by simpa using eigenspace_zero_of_injective R hR)
  exact lt_of_le_of_ne hn hne.symm

theorem real_eigenspaces_total (R : H →L[ℂ] H)
    (hcompact : IsCompactOperator R) (hsym : R.IsSymmetric) :
    (⨆ r : ℝ, eigenspace R.toLinearMap (r : ℂ))ᗮ = ⊥ := by
  have htotal := R.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsym
  have heq : (⨆ r : ℝ, eigenspace R.toLinearMap (r : ℂ)) =
      ⨆ z : ℂ, eigenspace R.toLinearMap z := by
    apply le_antisymm
    · exact iSup_le fun r => le_iSup _ (r : ℂ)
    · refine iSup_le fun z => ?_
      by_cases hz : HasEigenvalue R.toLinearMap z
      · have hzreal : (z.re : ℂ) = z :=
          Complex.conj_eq_iff_re.mp (hsym.conj_eigenvalue_eq_self hz)
        exact hzreal ▸ le_iSup (fun r : ℝ => eigenspace R.toLinearMap (r : ℂ)) z.re
      · have hz' : eigenspace R.toLinearMap z = ⊥ :=
          not_ne_iff.mp (hasEigenvalue_iff.not.mp hz)
        rw [hz']
        exact bot_le
  rwa [heq]

/-- The complete Hilbert eigenbasis, assembled from the finite-dimensional
eigenspaces. The index set includes multiplicity. -/
theorem exists_hilbert_eigenbasis (R : H →L[ℂ] H)
    (hR : Function.Injective R) (hcompact : IsCompactOperator R)
    (hsym : R.IsSymmetric) (hpos : ∀ x : H, 0 ≤ (inner ℂ x (R x)).re) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ H) (r : ι → ℝ),
      (∀ i, 0 < r i) ∧ (∀ i, R (b i) = (r i : ℂ) • b i) := by
  let E : ℝ → Submodule ℂ H := fun r => eigenspace R.toLinearMap (r : ℂ)
  letI (r : ℝ) : FiniteDimensional ℂ (E r) := finite_eigenspace R hR hcompact r
  let B (r : ℝ) := stdOrthonormalBasis ℂ (E r)
  let ι := Σ r : ℝ, Fin (Module.finrank ℂ (E r))
  let v : ι → H := fun i => (B i.1 i.2 : H)
  have horth : Orthonormal ℂ v := by
    exact (hsym.orthogonalFamily_eigenspaces.comp Complex.ofReal_injective).orthonormal_sigma_orthonormal
      (fun r => (B r).orthonormal)
  have hle (r : ℝ) : E r ≤ Submodule.span ℂ (range v) := by
    intro x hx
    let y : E r := ⟨x, hx⟩
    have hy := congrArg (fun z : E r => (z : H)) ((B r).sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hy
    change (y : H) ∈ _
    rw [← hy]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨r, i⟩, rfl⟩)
  have htotal : (Submodule.span ℂ (range v))ᗮ = ⊥ := by
    apply le_antisymm
    · have h := Submodule.orthogonal_le (iSup_le hle)
      exact h.trans (real_eigenspaces_total R hcompact hsym).le
    · exact bot_le
  let b := HilbertBasis.mkOfOrthogonalEqBot horth htotal
  have hb : ⇑b = v := HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  refine ⟨ι, b, fun i => i.1, ?_, ?_⟩
  · intro i
    apply eigenvalue_positive R hR hpos
    exact hasEigenvalue_of_hasEigenvector ⟨(B i.1 i.2).property, horth.ne_zero i⟩
  · intro i
    rw [hb]
    exact mem_eigenspace_iff.mp (B i.1 i.2).property

/-- Compactness controls multiplicity as well as distinct eigenvalues:
only finitely many orthonormal eigenvectors can have eigenvalue norm
bounded below by a positive number. -/
theorem finite_large_eigenvectors (R : H →L[ℂ] H) (hcompact : IsCompactOperator R)
    {ι : Type*} (b : ι → H) (hb : Orthonormal ℂ b) (r : ι → ℂ)
    (heigen : ∀ i, R (b i) = r i • b i) {ε : ℝ} (hε : 0 < ε) :
    {i : ι | ε ≤ ‖r i‖}.Finite := by
  classical
  let S := {i : ι | ε ≤ ‖r i‖}
  obtain ⟨K, hK, hRK⟩ := hcompact.image_closedBall_subset_compact 1
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (ε / 2) (by positivity)
  have hnear : ∀ i : S, ∃ y : t, dist (R (b i)) (y : H) < ε / 2 := by
    intro i
    have hiK : R (b i) ∈ K := hRK ⟨b i, by simp [hb.1 i], rfl⟩
    have hi := hcover hiK
    simp only [Set.mem_iUnion, Metric.mem_ball] at hi
    obtain ⟨y, hyt, hy⟩ := hi
    exact ⟨⟨y, hyt⟩, hy⟩
  choose center hcenter using hnear
  have hcenter_inj : Function.Injective center := by
    intro i j hij
    by_contra hne
    have hne' : (i : ι) ≠ (j : ι) := fun h => hne (Subtype.ext h)
    have hinner : inner ℂ (b i) (R (b i) - R (b j)) = r i := by
      rw [inner_sub_right, heigen, heigen, inner_smul_right, inner_smul_right,
        hb.inner_eq_zero hne', inner_self_eq_norm_sq_to_K, hb.1]
      simp
    have hnorm := norm_inner_le_norm (𝕜 := ℂ) (b i) (R (b i) - R (b j))
    rw [hinner, hb.1, one_mul] at hnorm
    have hsep : ε ≤ dist (R (b i)) (R (b j)) := by
      rw [dist_eq_norm]
      exact i.property.trans hnorm
    have htri := dist_triangle (R (b i)) (center i : H) (R (b j))
    have hi := hcenter i
    have hj := hcenter j
    rw [← hij] at hj
    rw [dist_comm (R (b j))] at hj
    linarith
  letI : Finite t := ht.fintype.finite
  haveI : Finite S := Finite.of_injective center hcenter_inj
  exact Set.toFinite S

/-- A positive family with finite superlevel sets can be enumerated in
decreasing order, with repetitions. -/
theorem exists_antitone_enumeration {ι : Type*} [Infinite ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hfinite : ∀ ε : ℝ, 0 < ε → {i : ι | ε ≤ r i}.Finite) :
    ∃ e : ℕ ≃ ι, Antitone (fun n => r (e n)) := by
  classical
  let oldOrder : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder ι := oldOrder
  let key : ι → ℝ ×ₗ ι := fun i => toLex (-r i, i)
  have hkey : Function.Injective key := by
    intro i j h
    exact congrArg (fun p : ℝ ×ₗ ι => (ofLex p).2) h
  let keyOrder : LinearOrder (ℝ ×ₗ ι) := inferInstance
  letI : LinearOrder ι := @LinearOrder.lift' ι (ℝ ×ₗ ι) keyOrder key hkey
  have hanti : Antitone r := by
    intro i j hij
    have h := @Prod.Lex.monotone_fst ℝ ι _ oldOrder.toLE (key i) (key j) hij
    change -r i ≤ -r j at h
    linarith
  have hIic (i : ι) : (Iic i).Finite := (hfinite (r i) (hr i)).subset
    (fun j hj => hanti hj)
  letI : LocallyFiniteOrder ι := LocallyFiniteOrder.ofFiniteIcc
    (fun i j => (hIic j).subset Icc_subset_Iic_self)
  let i₀ : ι := Classical.choice (Infinite.nonempty ι)
  obtain ⟨m, hm, hmin⟩ := (hIic i₀).toFinset.exists_min_image id
    ⟨i₀, by simp⟩
  have hmle : ∀ i : ι, m ≤ i := by
    intro i
    rcases le_total i i₀ with hi | hi
    · exact hmin i (by simpa using hi)
    · exact (by simpa using hm : m ≤ i₀).trans hi
  letI : OrderBot ι := { bot := m, bot_le := hmle }
  letI : NoMaxOrder ι := ⟨fun i => by
    by_contra! hi
    have hfin : (univ : Set ι).Finite := (hIic i).subset (fun j _ => hi j)
    exact Set.infinite_univ hfin⟩
  letI : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  letI : PredOrder ι := LinearLocallyFiniteOrder.predOrder ι
  let e := (orderIsoNatOfLinearSuccPredArch (ι := ι)).symm
  exact ⟨e.toEquiv, hanti.comp_monotone e.monotone⟩

theorem tendsto_zero_of_finite_superlevels (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hfinite : ∀ ε : ℝ, 0 < ε → {n : ℕ | ε ≤ r n}.Finite) :
    Tendsto r atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := (hfinite ε hε).bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (hr n)]
  by_contra! h
  have := hN h
  omega

/-- Ordered complete spectral data for an infinite-dimensional ambient
space. Every value is repeated once for each orthonormal eigenvector. -/
theorem exists_ordered_hilbert_eigenbasis (R : H →L[ℂ] H)
    (hH : ¬ FiniteDimensional ℂ H)
    (hR : Function.Injective R) (hcompact : IsCompactOperator R)
    (hsym : R.IsSymmetric) (hpos : ∀ x : H, 0 ≤ (inner ℂ x (R x)).re) :
    ∃ (b : HilbertBasis ℕ ℂ H) (r : ℕ → ℝ),
      (∀ n, 0 < r n) ∧ Antitone r ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, R (b n) = (r n : ℂ) • b n) := by
  classical
  obtain ⟨ι, b, r, hr, heigen⟩ := exists_hilbert_eigenbasis R hR hcompact hsym hpos
  haveI : Infinite ι := (finite_or_infinite ι).resolve_left (fun hfin => by
    letI := hfin
    letI := Fintype.ofFinite ι
    exact hH b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite)
  have hfinite (ε : ℝ) (hε : 0 < ε) : {i : ι | ε ≤ r i}.Finite := by
    have h := finite_large_eigenvectors R hcompact b b.orthonormal
      (fun i => (r i : ℂ)) heigen hε
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr _)] using h
  obtain ⟨e, he⟩ := exists_antitone_enumeration r hr hfinite
  have ho : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e e.injective
  have hd : (Submodule.span ℂ (range (b ∘ e))).topologicalClosure = ⊤ := by
    rw [e.surjective.range_comp]
    exact b.dense_span
  let b' := HilbertBasis.mk ho hd.ge
  have hb' : ⇑b' = b ∘ e := HilbertBasis.coe_mk _ _
  refine ⟨b', r ∘ e, fun n => hr (e n), he, ?_, ?_⟩
  · apply tendsto_zero_of_finite_superlevels _ (fun n => hr (e n))
    intro ε hε
    exact Set.Finite.preimage (f := e) e.injective.injOn (hfinite ε hε)
  · intro n
    simp only [hb', Function.comp_apply]
    exact heigen (e n)

theorem eigenvector_mem_range (R : H →L[ℂ] H) {r : ℝ} (hr : r ≠ 0) {x : H}
    (hx : R x = (r : ℂ) • x) : x ∈ R.range := by
  refine ⟨(r : ℂ)⁻¹ • x, ?_⟩
  change R ((r : ℂ)⁻¹ • x) = x
  rw [map_smul, hx, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hr)]

theorem operatorOfResolvent_eigenvector (R : H →L[ℂ] H)
    (hR : Function.Injective R) (c : ℝ) {r : ℝ} (hr : r ≠ 0) {x : H}
    (hx : R x = (r : ℂ) • x) :
    operatorOfResolvent R hR c ⟨x, eigenvector_mem_range R hr hx⟩ =
      ((r⁻¹ - c : ℝ) : ℂ) • x := by
  have hinv : inverseOnRange R hR ⟨x, eigenvector_mem_range R hr hx⟩ =
      (r : ℂ)⁻¹ • x := by
    apply hR
    rw [apply_inverseOnRange, map_smul, hx,
      inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hr)]
  rw [operatorOfResolvent_apply, hinv]
  simp [sub_smul]

/-- The represented unbounded operator has an increasing eigenvalue
sequence tending to positive infinity and a complete Hilbert eigenbasis. -/
theorem exists_discrete_operator_spectrum (R : H →L[ℂ] H)
    (hH : ¬ FiniteDimensional ℂ H)
    (hR : Function.Injective R) (hcompact : IsCompactOperator R)
    (hsym : R.IsSymmetric) (hpos : ∀ x : H, 0 ≤ (inner ℂ x (R x)).re) (c : ℝ) :
    ∃ (b : HilbertBasis ℕ ℂ H) (value : ℕ → ℝ),
      Monotone value ∧ Tendsto value atTop atTop ∧ (∀ n, -c < value n) ∧
      ∀ n, ∃ hn : b n ∈ (operatorOfResolvent R hR c).domain,
        operatorOfResolvent R hR c ⟨b n, hn⟩ = (value n : ℂ) • b n := by
  obtain ⟨b, r, hr, hanti, hzero, heigen⟩ :=
    exists_ordered_hilbert_eigenbasis R hH hR hcompact hsym hpos
  refine ⟨b, fun n => (r n)⁻¹ - c, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact sub_le_sub_right (inv_le_inv₀ (hr i) (hr j) |>.mpr (hanti hij)) c
  · have hwithin : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hr⟩
    simpa only [sub_eq_add_neg, Function.comp_apply, Pi.inv_apply] using
      tendsto_atTop_add_const_right atTop (-c) hwithin.inv_tendsto_nhdsGT_zero
  · intro n
    have := inv_pos.mpr (hr n)
    linarith
  · intro n
    exact ⟨eigenvector_mem_range R (hr n).ne' (heigen n),
      operatorOfResolvent_eigenvector R hR c (hr n).ne' (heigen n)⟩

end ThetaTrial.Paper.CompactFormSpectrum
