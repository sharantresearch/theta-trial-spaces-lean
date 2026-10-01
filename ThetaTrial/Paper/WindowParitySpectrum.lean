import ThetaTrial.Paper.WindowParity
import ThetaTrial.Paper.WindowSpectrum
import ThetaTrial.Paper.ThetaAvgSpaceVectors
import ThetaTrial.Paper.ThetaAvgMain

/-! The Weil spectrum on even and odd functions, and the bound for the first
even eigenvalue from Theorem `avg:main`. The parity form domains are obtained by
restricting the reflection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
open Complex Set Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace ThetaTrial.Paper

open FormDomain WindowFormAssembly WindowParity CoerciveFormRepresentation FormMinMax

attribute [local irreducible] ParityFormEmbedding.sector
  graphReflectionCLM windowReflectionCLM parityInclusion

def parityFormOperator (a : ℝ) (ε : ℂ) : graphSector a ε →L[ℂ] graphSector a ε :=
  @formOperator (graphSector a ε) inferInstance inferInstance inferInstance (parityShiftedForm a ε)

theorem parityFormOperator_coercive (a : ℝ) (ε : ℂ) :
    @IsCoerciveOperator (graphSector a ε) inferInstance inferInstance (parityFormOperator a ε) :=
  @formOperator_coercive (graphSector a ε) inferInstance inferInstance inferInstance
    (parityShiftedForm a ε) (parityShiftedForm_coercive a ε)

theorem parityFormOperator_symmetric (a : ℝ) (ε : ℂ) (v w : graphSector a ε) :
    inner ℂ (parityFormOperator a ε v) w = inner ℂ v (parityFormOperator a ε w) :=
  @formOperator_symmetric (graphSector a ε) inferInstance inferInstance inferInstance
    (parityShiftedForm a ε) (parityShiftedForm_hermitian a ε) v w

theorem parityFormOperator_nonneg (a : ℝ) (ε : ℂ) (v : graphSector a ε) :
    0 ≤ (inner ℂ (parityFormOperator a ε v) v).re := by
  obtain ⟨m, hm, hc⟩ := parityFormOperator_coercive a ε
  exact (mul_nonneg hm.le (sq_nonneg _)).trans (hc v)

theorem parityInclusion_norm (a : ℝ) (ε : ℂ) (v : graphSector a ε) :
    ‖parityInclusion a ε v‖ = ‖windowInclusion a v.val‖ := by
  unfold parityInclusion
  rfl

theorem parityFormOperator_diagonal (a : ℝ) (ε : ℂ) (v : graphSector a ε) :
    (inner ℂ (parityFormOperator a ε v) v).re - shiftConstant a * ‖parityInclusion a ε v‖ ^ 2 =
      fullWeilForm (representative a v.val) := by
  have h : inner ℂ (parityFormOperator a ε v) v =
      inner ℂ (windowFormOperator a v.val) v.val := by
    calc
      _ = parityShiftedForm a ε v v :=
        @formOperator_inner (graphSector a ε) inferInstance inferInstance inferInstance
          (parityShiftedForm a ε) v v
      _ = shiftedForm a v.val v.val := parityShiftedForm_apply a ε v v
      _ = _ := (formOperator_inner (shiftedForm a) v.val v.val).symm
  rw [h, parityInclusion_norm]
  exact windowFormOperator_diagonal a v.val

theorem physicalSector_not_finiteDimensional {a : ℝ} (ha : 0 < a) (ε : ℂ)
    (hε : ε ^ 2 = 1) : ¬ FiniteDimensional ℂ (physicalSector a ε) := by
  intro hfin
  letI := hfin
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · exact evenWindowL2_not_finiteDimensional ha
      (FiniteDimensional.of_injective (evenSectorEquiv a).toLinearEquiv.toLinearMap
        (evenSectorEquiv a).injective)
  · exact oddWindowL2_not_finiteDimensional ha
      (FiniteDimensional.of_injective (oddSectorEquiv a).toLinearEquiv.toLinearMap
        (oddSectorEquiv a).injective)

def paritySpectralData (a : ℝ) (ha : 0 < a) (ε : ℂ) (hε : ε ^ 2 = 1) :
    @FormSpectralData (graphSector a ε) (physicalSector a ε)
      inferInstance inferInstance inferInstance inferInstance
      (parityInclusion a ε) (parityFormOperator a ε) :=
  Classical.choice (@exists_formSpectralData (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityInclusion_injective a ε)
    (parityInclusion_denseRange a ε hε) (parityInclusion_isCompactOperator a ε)
    (physicalSector_not_finiteDimensional ha ε hε) (parityFormOperator a ε)
    (parityFormOperator_coercive a ε) (parityFormOperator_symmetric a ε))

def parityEigenvalue (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) (n : ℕ) : ℝ :=
  if ha : 0 < a then (paritySpectralData a ha ε hε).value n - shiftConstant a else 0

def evenWindowEigenvalue (a : ℝ) (n : ℕ) : ℝ := parityEigenvalue a 1 (by norm_num) n

def oddWindowEigenvalue (a : ℝ) (n : ℕ) : ℝ := parityEigenvalue a (-1) (by norm_num) n

theorem parityEigenvalue_eq {a : ℝ} (ha : 0 < a) (ε : ℂ) (hε : ε ^ 2 = 1) (n : ℕ) :
    parityEigenvalue a ε hε n = (paritySpectralData a ha ε hε).value n - shiftConstant a := by
  simp only [parityEigenvalue, dif_pos ha]

theorem parityEigenvalue_monotone (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    Monotone (parityEigenvalue a ε hε) := by
  by_cases ha : 0 < a
  · intro i j hij
    simp only [parityEigenvalue_eq ha]
    exact sub_le_sub_right ((paritySpectralData a ha ε hε).monotone hij) _
  · intro i j hij
    simp only [parityEigenvalue, dif_neg ha, le_refl]

theorem parityEigenvalue_tendsto {a : ℝ} (ha : 0 < a) (ε : ℂ) (hε : ε ^ 2 = 1) :
    Tendsto (parityEigenvalue a ε hε) atTop atTop := by
  change Tendsto (fun n => parityEigenvalue a ε hε n) atTop atTop
  simp_rw [parityEigenvalue_eq ha, sub_eq_add_neg]
  exact tendsto_atTop_add_const_right atTop (-shiftConstant a)
    (paritySpectralData a ha ε hε).divergent

def parityWeilOperator (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    physicalSector a ε →ₗ.[ℂ] physicalSector a ε :=
  @coerciveAssociatedOperator (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityInclusion_injective a ε)
    (parityInclusion_denseRange a ε hε) (parityFormOperator a ε)
    (parityFormOperator_coercive a ε) (shiftConstant a)

theorem parityWeilOperator_selfAdjoint (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    IsSelfAdjoint (parityWeilOperator a ε hε) :=
  @coerciveAssociatedOperator_selfAdjoint (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityInclusion_injective a ε)
    (parityInclusion_denseRange a ε hε) (parityFormOperator a ε)
    (parityFormOperator_coercive a ε) (parityFormOperator_symmetric a ε) (shiftConstant a)

theorem parityEigenvalue_operator {a : ℝ} (ha : 0 < a) (ε : ℂ) (hε : ε ^ 2 = 1) (n : ℕ) :
    ∃ hn : (paritySpectralData a ha ε hε).basis n ∈ (parityWeilOperator a ε hε).domain,
      parityWeilOperator a ε hε ⟨(paritySpectralData a ha ε hε).basis n, hn⟩ =
        (parityEigenvalue a ε hε n : ℂ) • (paritySpectralData a ha ε hε).basis n := by
  simpa only [parityWeilOperator, parityEigenvalue_eq ha] using
    spectral_operator_eigenvector (V := graphSector a ε) (H := physicalSector a ε)
      (paritySpectralData a ha ε hε) (parityInclusion_injective a ε)
      (parityInclusion_denseRange a ε hε) (parityFormOperator_coercive a ε) (shiftConstant a) n

theorem parityEigenvalue_minmax {a : ℝ} (ha : 0 < a) (ε : ℂ) (hε : ε ^ 2 = 1) (n : ℕ) :
    IsLeast (trialUpperBounds (V := graphSector a ε) (H := physicalSector a ε)
      (parityInclusion a ε) (parityFormOperator a ε) (shiftConstant a) n)
      (parityEigenvalue a ε hε n) := by
  rw [parityEigenvalue_eq ha]
  exact minmax_isLeast (V := graphSector a ε) (H := physicalSector a ε)
    (paritySpectralData a ha ε hε) (parityInclusion_injective a ε)
    (parityFormOperator_symmetric a ε) (parityFormOperator_nonneg a ε) (shiftConstant a) n

theorem parity_first_eigenvalue_mul_le {a : ℝ} (ha : 0 < a) (ε : ℂ) (hε : ε ^ 2 = 1)
    (v : graphSector a ε) :
    parityEigenvalue a ε hε 0 * ‖parityInclusion a ε v‖ ^ 2 ≤
      fullWeilForm (representative a v.val) := by
  have h := form_lower_bound_of_orthogonal (V := graphSector a ε) (H := physicalSector a ε)
    (paritySpectralData a ha ε hε)
    (parityFormOperator_symmetric a ε) (parityFormOperator_nonneg a ε) 0 v
    (fun i hi => (Nat.not_lt_zero i hi).elim)
  rw [parityEigenvalue_eq ha, ← parityFormOperator_diagonal a ε v]
  nlinarith

/-- An even unit-norm form-domain function is an admissible trial
for the even-sector first eigenvalue. Its Fourier graph parity
follows from injectivity of the physical inclusion and reflection. -/
theorem even_first_eigenvalue_le_of_unit_trial {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : InWindowFormDomain a f) (heven : Function.Even f)
    (hnorm : squaredNorm f = 1) :
    evenWindowEigenvalue a 0 ≤ fullWeilForm f := by
  obtain ⟨g, hg⟩ := InWindowFormDomain.exists_graph hf
  let p : windowFormGraph a := ⟨WithLp.toLp 2 (hf.2.1.toLp f, g), hg⟩
  have hevenLp : hf.2.1.toLp f ∈ evenL2 := by
    apply (mem_evenL2_iff_ae _).mpr
    have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      hf.2.1.coeFn_toLp
    filter_upwards [hf.2.1.coeFn_toLp, hn] with x hx hnx
    rw [hx, hnx]
    exact heven x
  have hp : p ∈ graphSector a 1 := by
    rw [ParityFormEmbedding.mem_sector]
    unfold graphReflectionCLM
    change graphReflection a p = (1 : ℂ) • p
    rw [one_smul]
    apply physicalInclusion_injective a
    change l2Reflection (hf.2.1.toLp f) = hf.2.1.toLp f
    exact (mem_evenL2_iff _).mp hevenLp
  let v : graphSector a 1 := ⟨p, hp⟩
  have hrep : representative a p =ᵐ[volume] f :=
    (windowRepresentative_ae_eq p.property.2).trans hf.2.1.coeFn_toLp
  have hvnorm : ‖parityInclusion a 1 v‖ ^ 2 = 1 := by
    rw [parityInclusion_norm]
    change ‖hf.2.1.toLp f‖ ^ 2 = 1
    rw [← squaredNorm_eq_norm_toLp_sq hf.2.1]
    exact hnorm
  have h := parity_first_eigenvalue_mul_le ha 1 (by norm_num) v
  rw [hvnorm, mul_one] at h
  change evenWindowEigenvalue a 0 ≤ fullWeilForm (representative a p) at h
  rwa [fullWeilForm_congr_ae hrep] at h

/-- The paper's first-even-eigenvalue corollary with the complete
form and the proved exponent `-2 T_a + 34 a`. -/
theorem thetaAvg_even_first_eigenvalue :
    ∃ C > 0, ∃ a₀ : ℝ, 16 ≤ a₀ ∧ ∀ a ≥ a₀,
      evenWindowEigenvalue a 0 ≤ C * Real.exp (-2 * scaleT a + 34 * a) := by
  obtain ⟨C, hC, a₀, ha₀, hmain⟩ := thetaAvg_main
  refine ⟨C, hC, a₀, ha₀, ?_⟩
  intro a haa
  obtain ⟨hdom, hmem, heven, hreal, hnorm, henergy⟩ := hmain a haa
  exact (even_first_eigenvalue_le_of_unit_trial (by linarith : 0 < a) hdom heven hnorm).trans
    ((le_abs_self _).trans henergy)

/-- Restricting the form to a reflection sector cannot lower
the first eigenvalue. The test used here is the sector's normalized
first eigenvector in its form domain. -/
theorem window_first_eigenvalue_le_parity {a : ℝ} (ha : 0 < a)
    (ε : ℂ) (hε : ε ^ 2 = 1) :
    windowEigenvalue a 0 ≤ parityEigenvalue a ε hε 0 := by
  let D := paritySpectralData a ha ε hε
  let v := D.vector 0
  have hn : ‖parityInclusion a ε v‖ = 1 := by
    rw [show parityInclusion a ε v = D.basis 0 from D.embedding 0]
    exact D.basis.orthonormal.1 0
  have hn' : ‖windowInclusion a v.val‖ = 1 := by rwa [parityInclusion_norm] at hn
  have h := form_lower_bound_of_orthogonal (windowSpectralData a ha)
    (windowFormOperator_symmetric a) (windowFormOperator_nonneg a) 0 v.val
    (fun i hi => (Nat.not_lt_zero i hi).elim)
  have hlower : windowEigenvalue a 0 ≤ fullWeilForm (representative a v.val) := by
    rw [windowEigenvalue_eq ha, ← windowFormOperator_diagonal a v.val]
    rw [hn', one_pow] at h ⊢
    linarith
  have hr := spectral_vector_rayleigh (V := graphSector a ε) (H := physicalSector a ε)
    D (shiftConstant a) 0
  change @formRayleigh (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityFormOperator a ε) (shiftConstant a) v =
    D.value 0 - shiftConstant a at hr
  rw [formRayleigh, parityFormOperator_diagonal, hn, one_pow, div_one] at hr
  exact hlower.trans_eq (hr.trans (parityEigenvalue_eq ha ε hε 0).symm)

/-- The bound of Theorem `avg:main` for the first eigenvalue of the window
operator. -/
theorem thetaAvg_first_eigenvalue :
    ∃ C > 0, ∃ a₀ : ℝ, 16 ≤ a₀ ∧ ∀ a ≥ a₀,
      windowEigenvalue a 0 ≤ C * Real.exp (-2 * scaleT a + 34 * a) := by
  obtain ⟨C, hC, a₀, ha₀, hmain⟩ := thetaAvg_even_first_eigenvalue
  refine ⟨C, hC, a₀, ha₀, ?_⟩
  intro a haa
  exact (window_first_eigenvalue_le_parity (by linarith : 0 < a) 1 (by norm_num)).trans
    (hmain a haa)

end ThetaTrial.Paper
