import ThetaTrial.Paper.ThetaAvgSpaces
import ThetaTrial.Paper.ThetaDerivTrialSpace

/-!
# Estimates for every vector in the theta-average trial space

The canonical window representative satisfies the pointwise support condition
of the paper. The energy is also stated for the `Lp` representative, since the
form does not change under almost-everywhere equality.
-/

noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped Polynomial Topology

namespace ThetaTrial.Paper

theorem thetaAvgTrialSpace_vector_polynomial {a : ℝ} {ha : 0 ≤ a}
    {hZ : 16 ≤ scaleZ a} {k : ℕ} {v : Lp ℂ 2 (volume : Measure ℝ)}
    (hv : v ∈ thetaAvgTrialSpace a ha hZ k) :
    ∃ P : ℂ[X], P.natDegree ≤ k ∧ v = thetaAvgWindowL2LinearMap a ha hZ P := by
  obtain ⟨P, rfl⟩ := hv
  refine ⟨P, ?_, rfl⟩
  by_cases hp : (P : ℂ[X]) = 0
  · simp only [hp, natDegree_zero, Nat.zero_le]
  · exact Nat.lt_succ_iff.mp ((Polynomial.natDegree_lt_iff_degree_lt hp).mpr
      (Polynomial.mem_degreeLT.mp P.property))

theorem thetaAvgTrialSpace_mem_windowL2 {a : ℝ} {ha : 0 ≤ a}
    {hZ : 16 ≤ scaleZ a} {k : ℕ} {v : Lp ℂ 2 (volume : Measure ℝ)}
    (hv : v ∈ thetaAvgTrialSpace a ha hZ k) : v ∈ FormDomain.windowL2 a := by
  obtain ⟨P, hp, rfl⟩ := thetaAvgTrialSpace_vector_polynomial hv
  filter_upwards [thetaAvgWindowL2LinearMap_coeFn ha hZ P] with u hu
  intro hout
  rw [hu]
  simp [thetaAvgWindowProfile, windowCut, hout]

theorem thetaAvgTrialSpace_representative_ae {a : ℝ} {ha : 0 ≤ a}
    {hZ : 16 ≤ scaleZ a} {k : ℕ} {v : Lp ℂ 2 (volume : Measure ℝ)}
    (hv : v ∈ thetaAvgTrialSpace a ha hZ k) :
    FormDomain.windowRepresentative a v =ᵐ[volume] (fun u => v u) :=
  FormDomain.windowRepresentative_ae_eq (thetaAvgTrialSpace_mem_windowL2 hv)

theorem thetaAvgTrialSpace_representative_squaredNorm {a : ℝ} {ha : 0 ≤ a}
    {hZ : 16 ≤ scaleZ a} {k : ℕ} {v : Lp ℂ 2 (volume : Measure ℝ)}
    (hv : v ∈ thetaAvgTrialSpace a ha hZ k) :
    squaredNorm (FormDomain.windowRepresentative a v) = ‖v‖ ^ 2 :=
  FormDomain.windowRepresentative_squaredNorm (thetaAvgTrialSpace_mem_windowL2 hv)

theorem thetaAvgTrialSpace_vector_inDomain {a : ℝ} {ha : 0 ≤ a}
    {hZ : 16 ≤ scaleZ a} {k : ℕ} {v : Lp ℂ 2 (volume : Measure ℝ)}
    (hv : v ∈ thetaAvgTrialSpace a ha hZ k) :
    InWindowFormDomain a (FormDomain.windowRepresentative a v) := by
  obtain ⟨P, hp, he⟩ := thetaAvgTrialSpace_vector_polynomial hv
  have hcoe : (fun u => v u) =ᵐ[volume] thetaAvgWindowProfile a P := by
    rw [he]
    exact thetaAvgWindowL2LinearMap_coeFn ha hZ P
  have hrep := (thetaAvgTrialSpace_representative_ae hv).trans hcoe
  have hdom := thetaAvg_polynomial_window_domain ha hZ P
  refine ⟨FormDomain.windowRepresentative_support a v,
    FormDomain.windowRepresentative_memLp a v, ?_⟩
  have hfour (r : ℝ) : paperFourier (FormDomain.windowRepresentative a v) r =
      paperFourier (thetaAvgWindowProfile a P) r := by
    unfold paperFourier
    apply integral_congr_ae
    filter_upwards [hrep] with u hu
    rw [hu]
  apply hdom.2.2.congr
  filter_upwards [] with r
  rw [hfour]
  rfl

theorem thetaAvgTrialSpace_vector_energy_of_polynomials {a E : ℝ} {ha : 0 ≤ a}
    {hZ : 16 ≤ scaleZ a} {k : ℕ}
    (hbound : ∀ P : ℂ[X], P.natDegree ≤ k →
      |fullWeilForm (thetaAvgWindowProfile a P)| ≤ E * squaredNorm (thetaAvgWindowProfile a P))
    {v : Lp ℂ 2 (volume : Measure ℝ)} (hv : v ∈ thetaAvgTrialSpace a ha hZ k) :
    |fullWeilForm (FormDomain.windowRepresentative a v)| ≤ E * ‖v‖ ^ 2 ∧
      |fullWeilForm (fun u => v u)| ≤ E * ‖v‖ ^ 2 := by
  obtain ⟨P, hp, he⟩ := thetaAvgTrialSpace_vector_polynomial hv
  have hcoe : (fun u => v u) =ᵐ[volume] thetaAvgWindowProfile a P := by
    rw [he]
    exact thetaAvgWindowL2LinearMap_coeFn ha hZ P
  have hrep := (thetaAvgTrialSpace_representative_ae hv).trans hcoe
  have hnorm : squaredNorm (thetaAvgWindowProfile a P) = ‖v‖ ^ 2 := by
    rw [← thetaAvgTrialSpace_representative_squaredNorm hv]
    unfold squaredNorm
    apply integral_congr_ae
    filter_upwards [hrep] with u hu
    rw [hu]
  have hb := hbound P hp
  rw [hnorm] at hb
  constructor
  · rw [fullWeilForm_congr_ae hrep]
    exact hb
  · rw [fullWeilForm_congr_ae hcoe]
    exact hb

/-- The growing-dimensional space theorem, quantified over every
complex L² vector of the image, with the exact window domain. -/
theorem thetaAvg_spaces_L2 :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ a₁ : ℝ, 1 ≤ a₁ ∧
      ∀ a ≥ a₁, ∃ ha : 0 ≤ a, ∃ hZ : 16 ≤ scaleZ a,
        ∀ k : ℕ,
          (k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) + C₁ * ((k : ℝ) + a) ≤ scaleT a →
          Module.finrank ℂ (thetaAvgTrialSpace a ha hZ k) = k + 1 ∧
          ∀ v : Lp ℂ 2 (volume : Measure ℝ), v ∈ thetaAvgTrialSpace a ha hZ k →
            InWindowFormDomain a (FormDomain.windowRepresentative a v) ∧
            FormDomain.windowRepresentative a v =ᵐ[volume] (fun u => v u) ∧
            |fullWeilForm (FormDomain.windowRepresentative a v)| ≤
              Real.exp (-2 * scaleT a + 8 * (k : ℝ) * a +
                2 * (k : ℝ) * Real.log ((k : ℝ) + 1) + C₂ * ((k : ℝ) + a)) * ‖v‖ ^ 2 ∧
            |fullWeilForm (fun u => v u)| ≤
              Real.exp (-2 * scaleT a + 8 * (k : ℝ) * a +
                2 * (k : ℝ) * Real.log ((k : ℝ) + 1) + C₂ * ((k : ℝ) + a)) * ‖v‖ ^ 2 := by
  obtain ⟨C₁, hC₁, C₂, hC₂, a₁, ha₁, hall⟩ := thetaAvg_spaces
  refine ⟨C₁, hC₁, C₂, hC₂, a₁, ha₁, ?_⟩
  intro a haa
  obtain ⟨ha, hZ, hspace⟩ := hall a haa
  refine ⟨ha, hZ, ?_⟩
  intro k hk
  obtain ⟨hdim, hpoly⟩ := hspace k hk
  refine ⟨hdim, ?_⟩
  intro v hv
  exact ⟨thetaAvgTrialSpace_vector_inDomain hv, thetaAvgTrialSpace_representative_ae hv,
    thetaAvgTrialSpace_vector_energy_of_polynomials (fun P hp => (hpoly P hp).2.2) hv⟩

/-- The explicit floor-degree space and homogeneous full-form estimate on
every vector, including zero, rather than only a polynomial parameterization. -/
theorem thetaAvg_large_space_L2 :
    ∀ᶠ a : ℝ in atTop, ∃ ha : 0 ≤ a, ∃ hZ : 16 ≤ scaleZ a,
      Module.finrank ℂ (thetaAvgTrialSpace a ha hZ (TrialBounds.selectedDegree a)) =
        TrialBounds.selectedDegree a + 1 ∧
      ∀ v : Lp ℂ 2 (volume : Measure ℝ),
        v ∈ thetaAvgTrialSpace a ha hZ (TrialBounds.selectedDegree a) →
        InWindowFormDomain a (FormDomain.windowRepresentative a v) ∧
        FormDomain.windowRepresentative a v =ᵐ[volume] (fun u => v u) ∧
        |fullWeilForm (FormDomain.windowRepresentative a v)| ≤ Real.exp (-scaleT a) * ‖v‖ ^ 2 ∧
        |fullWeilForm (fun u => v u)| ≤ Real.exp (-scaleT a) * ‖v‖ ^ 2 := by
  filter_upwards [thetaAvg_large_space] with a ha
  obtain ⟨ha0, hZ, hdim, hpoly⟩ := ha
  refine ⟨ha0, hZ, hdim, ?_⟩
  intro v hv
  exact ⟨thetaAvgTrialSpace_vector_inDomain hv, thetaAvgTrialSpace_representative_ae hv,
    thetaAvgTrialSpace_vector_energy_of_polynomials (fun P hp => (hpoly P hp).2.2) hv⟩

#print axioms thetaAvg_spaces_L2
#print axioms thetaAvg_large_space_L2

end ThetaTrial.Paper
