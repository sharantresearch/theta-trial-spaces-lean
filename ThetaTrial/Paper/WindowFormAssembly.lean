import ThetaTrial.Paper.WindowFormBounds
import ThetaTrial.Paper.FullPairingAlgebra
import ThetaTrial.Paper.SesquilinearBound
import ThetaTrial.Paper.CoerciveFormRepresentation

/-! The Weil form on its supported logarithmic graph.
The first argument is conjugate-linear to match the Hilbert inner product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped ComplexConjugate

namespace ThetaTrial.Paper.WindowFormAssembly
open FormDomain WindowFormBounds Radical RadicalCorrelation RadicalCutoff

def representative (a : ℝ) (p : windowFormGraph a) : ℝ → ℂ :=
  windowRepresentative a p.val.fst

theorem representative_domain (a : ℝ) (p : windowFormGraph a) :
    InWindowFormDomain a (representative a p) :=
  windowRepresentative_inDomain (show WithLp.toLp 2 (p.val.fst, p.val.snd) ∈
    windowFormGraph a from p.property)

theorem representative_add (a : ℝ) (p q : windowFormGraph a) :
    representative a (p + q) =ᵐ[volume] representative a p + representative a q := by
  filter_upwards [Lp.coeFn_add p.val.fst q.val.fst] with u hu
  change (Icc (-a) a).indicator (fun u => (p.val.fst + q.val.fst) u) u = _
  by_cases hin : u ∈ Icc (-a) a
  · simpa only [representative, windowRepresentative, Set.indicator_of_mem hin, Pi.add_apply] using hu
  · simp [representative, windowRepresentative, hin]

theorem representative_smul (a : ℝ) (c : ℂ) (p : windowFormGraph a) :
    representative a (c • p) =ᵐ[volume] c • representative a p := by
  filter_upwards [Lp.coeFn_smul c p.val.fst] with u hu
  change (Icc (-a) a).indicator (fun u => (c • p.val.fst) u) u = _
  by_cases hin : u ∈ Icc (-a) a
  · simpa only [representative, windowRepresentative, Set.indicator_of_mem hin, Pi.smul_apply] using hu
  · simp [representative, windowRepresentative, hin]

theorem fullPairing_congr {f f' h h' : ℝ → ℂ}
    (hf : f =ᵐ[volume] f') (hh : h =ᵐ[volume] h') : fullPairing f h = fullPairing f' h' := by
  unfold fullPairing
  congr 1
  funext x
  simp only [weilTest_eq_integral]
  apply integral_congr_ae
  have ht := (measurePreserving_add_right volume (-x)).quasiMeasurePreserving.ae_eq_comp hh
  filter_upwards [hf, ht] with u hu hv
  change h (u - x) = h' (u - x) at hv
  rw [hu, hv]

def rawPair (a : ℝ) (p q : windowFormGraph a) : ℂ :=
  fullPairing (representative a q) (representative a p)

theorem rawPair_add_left (a : ℝ) (p q r : windowFormGraph a) :
    rawPair a (p + q) r = rawPair a p r + rawPair a q r := by
  unfold rawPair
  rw [fullPairing_congr ae_eq_rfl (representative_add a p q)]
  exact fullPairing_add_right (representative_domain a r).2.1
    (representative_domain a p).2.1 (representative_domain a q).2.1
    (mixed_domain (representative_domain a r) (representative_domain a p))
    (mixed_domain (representative_domain a r) (representative_domain a q))

theorem rawPair_smul_left (a : ℝ) (c : ℂ) (p q : windowFormGraph a) :
    rawPair a (c • p) q = conj c • rawPair a p q := by
  unfold rawPair
  rw [fullPairing_congr ae_eq_rfl (representative_smul a c p)]
  exact fullPairing_smul_right
    (mixed_domain (representative_domain a q) (representative_domain a p)) c

theorem rawPair_add_right (a : ℝ) (p q r : windowFormGraph a) :
    rawPair a p (q + r) = rawPair a p q + rawPair a p r := by
  unfold rawPair
  rw [fullPairing_congr (representative_add a q r) ae_eq_rfl]
  exact fullPairing_add_left (representative_domain a q).2.1
    (representative_domain a r).2.1 (representative_domain a p).2.1
    (mixed_domain (representative_domain a q) (representative_domain a p))
    (mixed_domain (representative_domain a r) (representative_domain a p))

theorem rawPair_smul_right (a : ℝ) (c : ℂ) (p q : windowFormGraph a) :
    rawPair a p (c • q) = c • rawPair a p q := by
  unfold rawPair
  rw [fullPairing_congr (representative_smul a c q) ae_eq_rfl]
  exact fullPairing_smul_left
    (mixed_domain (representative_domain a q) (representative_domain a p)) c

def rawForm (a : ℝ) : windowFormGraph a →ₗ⋆[ℂ] windowFormGraph a →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (rawPair a)
    (rawPair_add_left a) (rawPair_smul_left a) (rawPair_add_right a) (rawPair_smul_right a)

theorem rawForm_hermitian (a : ℝ) : (rawForm a).IsSymm := by
  constructor
  intro p q
  exact (fullPairing_hermitian (representative a q) (representative a p)).symm

theorem rawForm_diagonal (a : ℝ) (p : windowFormGraph a) :
    rawForm a p p = (fullWeilForm (representative a p) : ℂ) :=
  fullPairing_self_eq (representative_domain a p)

def gammaPerturbationConstant : ℝ := Classical.choose fullForm_log_bounded_perturbation

def perturbationConstant (a : ℝ) : ℝ :=
  gammaPerturbationConstant + poleWindowBound a + primeWindowBound a

theorem perturbationConstant_pos (a : ℝ) : 0 < perturbationConstant a := by
  have hc := (Classical.choose_spec fullForm_log_bounded_perturbation).1
  change 0 < gammaPerturbationConstant at hc
  have hp : 0 ≤ poleWindowBound a := by unfold poleWindowBound; positivity
  have hq := primeWindowBound_nonneg a
  unfold perturbationConstant
  linarith

theorem rawForm_graph_comparison (a : ℝ) (p : windowFormGraph a) :
    |(rawForm a p p).re - (‖p‖ ^ 2 - ‖windowInclusion a p‖ ^ 2)| ≤
      perturbationConstant a * ‖windowInclusion a p‖ ^ 2 := by
  have h := (Classical.choose_spec fullForm_log_bounded_perturbation).2 a
    (representative a p) (representative_domain a p)
  have hn := windowFormGraph_norm_sq a p
  have hs := windowRepresentative_squaredNorm (show p.val.fst ∈ windowL2 a from p.property.2)
  rw [rawForm_diagonal, Complex.ofReal_re]
  change squaredNorm (representative a p) = ‖windowInclusion a p‖ ^ 2 at hs
  change ‖p‖ ^ 2 = squaredNorm (representative a p) + _ at hn
  rw [hs] at hn h
  have he : (1 / (2 * Real.pi)) *
      (∫ r : ℝ, Real.log (2 + |r|) *
        ‖ThetaTrial.Paper.paperFourier (representative a p) r‖ ^ 2) =
      ‖p‖ ^ 2 - ‖windowInclusion a p‖ ^ 2 := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    dsimp only [representative]
    linarith
  simpa only [he, perturbationConstant, gammaPerturbationConstant] using h

theorem rawForm_diagonal_bound (a : ℝ) (p : windowFormGraph a) :
    |(rawForm a p p).re| ≤ (perturbationConstant a + 1) * ‖p‖ ^ 2 := by
  have hc := rawForm_graph_comparison a p
  have hp := physicalInclusion_norm_le a p
  change ‖windowInclusion a p‖ ≤ ‖p‖ at hp
  have hn : ‖windowInclusion a p‖ ^ 2 ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hD := (perturbationConstant_pos a).le
  rcases abs_le.mp hc with ⟨hl, hu⟩
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hn hD, sq_nonneg ‖windowInclusion a p‖]

theorem rawForm_shifted_coercive (a : ℝ) (p : windowFormGraph a) :
    ‖p‖ ^ 2 ≤ (rawForm a p p).re +
      (perturbationConstant a + 1) * ‖windowInclusion a p‖ ^ 2 := by
  have hc := (abs_le.mp (rawForm_graph_comparison a p)).1
  linarith

def continuousForm (a : ℝ) : windowFormGraph a →L⋆[ℂ] windowFormGraph a →L[ℂ] ℂ :=
  (rawForm a).mkContinuous₂ (4 * (perturbationConstant a + 1))
    (sesquilinear_norm_le_of_diagonal (rawForm a) (rawForm_hermitian a)
      (by linarith [perturbationConstant_pos a]) (rawForm_diagonal_bound a))

@[simp] theorem continuousForm_apply (a : ℝ) (p q : windowFormGraph a) :
    continuousForm a p q = fullPairing (representative a q) (representative a p) := rfl

def physicalInnerForm (a : ℝ) : windowFormGraph a →L⋆[ℂ] windowFormGraph a →L[ℂ] ℂ :=
  (ContinuousLinearMap.toSesqForm (windowInclusion a)).comp (windowInclusion a)

@[simp] theorem physicalInnerForm_apply (a : ℝ) (p q : windowFormGraph a) :
    physicalInnerForm a p q = inner ℂ (windowInclusion a p) (windowInclusion a q) := rfl

def shiftConstant (a : ℝ) : ℝ := perturbationConstant a + 1

theorem shiftConstant_pos (a : ℝ) : 0 < shiftConstant a := by
  unfold shiftConstant
  linarith [perturbationConstant_pos a]

def shiftedForm (a : ℝ) : windowFormGraph a →L⋆[ℂ] windowFormGraph a →L[ℂ] ℂ :=
  continuousForm a + (shiftConstant a : ℂ) • physicalInnerForm a

theorem shiftedForm_apply (a : ℝ) (p q : windowFormGraph a) :
    shiftedForm a p q = rawForm a p q +
      (shiftConstant a : ℂ) * inner ℂ (windowInclusion a p) (windowInclusion a q) := rfl

theorem shiftedForm_hermitian (a : ℝ) (p q : windowFormGraph a) :
    conj (shiftedForm a q p) = shiftedForm a p q := by
  simp only [shiftedForm_apply, map_add, map_mul, conj_ofReal, inner_conj_symm]
  congr 1
  exact (rawForm_hermitian a).eq q p

theorem shiftedForm_coercive (a : ℝ) : ∃ m : ℝ, 0 < m ∧
    ∀ p : windowFormGraph a, m * ‖p‖ ^ 2 ≤ (shiftedForm a p p).re := by
  refine ⟨1, zero_lt_one, fun p => ?_⟩
  have hi : (inner ℂ (windowInclusion a p) (windowInclusion a p)).re =
      ‖windowInclusion a p‖ ^ 2 := by
    simpa only [pow_two, RCLike.re_eq_complex_re] using
      (inner_self_eq_norm_mul_norm (𝕜 := ℂ) (windowInclusion a p))
  rw [one_mul, shiftedForm_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hi]
  exact rawForm_shifted_coercive a p

/-- Representation of the full Weil form, including both poles
and every Mangoldt coefficient, on the supported logarithmic domain.
The compact resolvent and its two inverse identities are constructed from
the proved graph embedding and shifted coercive comparison. -/
theorem exists_form_representation (a : ℝ) :
    ∃ (A : windowL2 a →ₗ.[ℂ] windowL2 a) (R : windowL2 a →L[ℂ] windowL2 a),
      IsSelfAdjoint A ∧ A.IsClosed ∧ IsCompactOperator R ∧
      A.domain = R.range ∧
      (∀ f : windowL2 a, ∃ x : A.domain,
        (x : windowL2 a) = R f ∧ A x + (shiftConstant a : ℂ) • (x : windowL2 a) = f) ∧
      (∀ x : A.domain, R (A x + (shiftConstant a : ℂ) • (x : windowL2 a)) = (x : windowL2 a)) ∧
      (∀ v : windowFormGraph a, ∀ f : windowL2 a,
        (∀ w : windowFormGraph a,
          fullPairing (representative a w) (representative a v) =
            inner ℂ f (windowInclusion a w)) ↔
          ∃ hv : windowInclusion a v ∈ A.domain, A ⟨windowInclusion a v, hv⟩ = f) ∧
      (∀ x : A.domain, -shiftConstant a * ‖(x : windowL2 a)‖ ^ 2 ≤
        (inner ℂ (A x) (x : windowL2 a)).re) := by
  obtain ⟨A, R, hA, hclosed, hcompact, hdomain, hright, hleft, hweak, hlower⟩ :=
    CoerciveFormRepresentation.exists_compact_form_representation
      (windowInclusion a) (windowInclusion_injective a) (windowInclusion_denseRange a)
      (windowInclusion_isCompactOperator a) (shiftedForm a)
      (shiftedForm_hermitian a) (shiftedForm_coercive a) (shiftConstant a)
  refine ⟨A, R, hA, hclosed, hcompact, hdomain, hright, hleft, ?_, hlower⟩
  intro v f
  simpa only [shiftedForm_apply, add_sub_cancel_right, rawForm,
    LinearMap.mk₂'ₛₗ_apply, rawPair] using hweak v f

#print axioms continuousForm
#print axioms shiftedForm_hermitian
#print axioms shiftedForm_coercive
#print axioms exists_form_representation

end ThetaTrial.Paper.WindowFormAssembly
