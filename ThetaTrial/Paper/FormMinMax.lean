import ThetaTrial.Paper.CompactFormSpectrum

/-!
# The variational principle on the form domain

Eigenvectors are first constructed from the compact resolvent and lifted
to the form space. Positivity of the shifted form proves Bessel's energy
inequality on arbitrary form-domain vectors; thus trial spaces need not
belong to the operator domain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Complex Set Filter
open scoped InnerProductSpace ComplexConjugate Topology

namespace ThetaTrial.Paper.FormMinMax

open CoerciveFormRepresentation CompactFormSpectrum

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral data in the original form space, including the weak
eigenvector equation. Existence is proved below from compact embedding. -/
structure FormSpectralData (J : V →L[ℂ] H) (B : V →L[ℂ] V) where
  basis : HilbertBasis ℕ ℂ H
  vector : ℕ → V
  value : ℕ → ℝ
  embedding : ∀ n, J (vector n) = basis n
  positive : ∀ n, 0 < value n
  monotone : Monotone value
  divergent : Tendsto value atTop atTop
  weak : ∀ n v, inner ℂ (B (vector n)) v = (value n : ℂ) * inner ℂ (basis n) (J v)

theorem exists_formSpectralData (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J) (hJcompact : IsCompactOperator J)
    (hH : ¬ FiniteDimensional ℂ H) (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) :
    Nonempty (FormSpectralData J B) := by
  obtain ⟨b, value, hmono, hdiv, hpos, heigen⟩ := exists_discrete_operator_spectrum
    (coerciveResolvent J B hB) hH (coerciveResolvent_injective J hJi hJ B hB)
    (coerciveResolvent_compact J hJcompact B hB)
    (coerciveResolvent_symmetric J B hB hsym) (coerciveResolvent_nonneg J B hB) 0
  choose hmem hval using heigen
  let v (n : ℕ) := coerciveOperatorFormVector J hJi hJ B hB 0 ⟨b n, hmem n⟩
  refine ⟨⟨b, v, value, ?_, ?_, hmono, hdiv, ?_⟩⟩
  · intro n
    exact coerciveOperatorFormVector_embedding J hJi hJ B hB 0 ⟨b n, hmem n⟩
  · simpa only [neg_zero] using hpos
  · intro n w
    have h := coerciveAssociatedOperator_represents J hJi hJ B hB 0 ⟨b n, hmem n⟩ w
    change inner ℂ (ClosedFormRepresentation.operatorOfResolvent _ _ 0 _) (J w) = _ at h
    rw [hval n, inner_smul_left, Complex.conj_ofReal] at h
    simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using h.symm

theorem basis_mass_hasSum {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (b.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  convert! h using 1
  · ext i
    change ‖inner ℂ (b i) x‖ ^ 2 = (inner ℂ x (b i) * inner ℂ (b i) x).re
    rw [← inner_conj_symm x (b i), RCLike.conj_mul]
    norm_cast
  · change ‖x‖ ^ 2 = (inner ℂ x x).re
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm

variable {J : V →L[ℂ] H} {B : V →L[ℂ] V}

/-- Finite spectral energy is bounded by the full shifted form energy. -/
theorem finite_energy_le (D : FormSpectralData J B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w))
    (hpos : ∀ v : V, 0 ≤ (inner ℂ (B v) v).re) (s : Finset ℕ) (v : V) :
    ∑ i ∈ s, D.value i * ‖inner ℂ (D.basis i) (J v)‖ ^ 2 ≤ (inner ℂ (B v) v).re := by
  classical
  let a : ℕ → ℂ := fun i => inner ℂ (D.basis i) (J v)
  let p : V := ∑ i ∈ s, a i • D.vector i
  let energy : ℝ := ∑ i ∈ s, D.value i * ‖a i‖ ^ 2
  have hJp : J p = ∑ i ∈ s, a i • D.basis i := by
    simp only [p, map_sum, map_smul, D.embedding]
  have hpw (w : V) : inner ℂ (B p) w =
      ∑ i ∈ s, conj (a i) * ((D.value i : ℂ) * inner ℂ (D.basis i) (J w)) := by
    simp only [p, map_sum, map_smul, sum_inner, inner_smul_left, D.weak]
  have hpv : inner ℂ (B p) v = (energy : ℂ) := by
    rw [hpw]
    simp only [energy, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i hi
    change conj (a i) * ((D.value i : ℂ) * a i) = _
    rw [mul_left_comm, RCLike.conj_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal]
  have hpp : inner ℂ (B p) p = (energy : ℂ) := by
    rw [hpw]
    simp only [energy, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hJp, D.basis.orthonormal.inner_right_sum a hi, mul_left_comm, RCLike.conj_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal]
  have hvp : inner ℂ (B v) p = (energy : ℂ) := by
    rw [hsym, ← inner_conj_symm, hpv, Complex.conj_ofReal]
  have hrem := hpos (v - p)
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hpv, hpp, hvp] at hrem
  simp only [Complex.sub_re, Complex.ofReal_re] at hrem
  change energy ≤ _
  linarith

/-- The lower Rayleigh bound after removing the first `n` spectral
coordinates holds on the whole form domain. -/
theorem form_lower_bound_of_orthogonal (D : FormSpectralData J B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w))
    (hpos : ∀ v : V, 0 ≤ (inner ℂ (B v) v).re) (n : ℕ) (v : V)
    (horth : ∀ i < n, inner ℂ (D.basis i) (J v) = 0) :
    D.value n * ‖J v‖ ^ 2 ≤ (inner ℂ (B v) v).re := by
  have hsum := (basis_mass_hasSum D.basis (J v)).mul_left (D.value n)
  apply le_of_tendsto hsum
  filter_upwards [] with s
  rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ s, D.value i * ‖inner ℂ (D.basis i) (J v)‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rcases lt_or_ge i n with hin | hin
      · simp [horth i hin]
      · exact mul_le_mul_of_nonneg_right (D.monotone hin) (sq_nonneg _)
    _ ≤ _ := finite_energy_le D hsym hpos s v

/-- The Rayleigh quotient of the form after subtracting its
positive shift. -/
def formRayleigh (J : V →L[ℂ] H) (B : V →L[ℂ] V) (c : ℝ) (v : V) : ℝ :=
  ((inner ℂ (B v) v).re - c * ‖J v‖ ^ 2) / ‖J v‖ ^ 2

/-- Every trial space of dimension greater than `n` contains a nonzero
vector orthogonal to the first `n` eigenvectors. -/
theorem trial_orthogonal_vector (D : FormSpectralData J B) (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] (n : ℕ) (hdim : n < Module.finrank ℂ S) :
    ∃ v ∈ S, v ≠ 0 ∧ ∀ i < n, inner ℂ (D.basis i) (J v) = 0 := by
  let F : S →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi fun i =>
    (((innerSL ℂ (D.basis i)).toLinearMap.comp J.toLinearMap).comp S.subtype)
  have hdim' : Module.finrank ℂ (Fin n → ℂ) < Module.finrank ℂ S := by
    simpa using hdim
  obtain ⟨x, hx, hxne⟩ := (LinearMap.ker F).ne_bot_iff.mp
    (LinearMap.ker_ne_bot_of_finrank_lt hdim')
  refine ⟨(x : V), x.property, ?_, ?_⟩
  · intro he
    exact hxne (Subtype.ext he)
  · intro i hi
    have h := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
    exact h

/-- The trial-space half of Courant--Fischer, for arbitrary form-domain
trials. Index `n` corresponds to the paper's eigenvalue `n+1`. -/
theorem trial_rayleigh_ge (D : FormSpectralData J B)
    (hJi : Function.Injective J)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w))
    (hpos : ∀ v : V, 0 ≤ (inner ℂ (B v) v).re)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] (n : ℕ)
    (hdim : n < Module.finrank ℂ S) (c : ℝ) :
    ∃ v ∈ S, v ≠ 0 ∧ D.value n - c ≤ formRayleigh J B c v := by
  obtain ⟨v, hvS, hv, horth⟩ := trial_orthogonal_vector D S n hdim
  have hJv : J v ≠ 0 := fun h => hv (hJi (h.trans J.map_zero.symm))
  have hnorm : 0 < ‖J v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hJv)
  refine ⟨v, hvS, hv, ?_⟩
  rw [formRayleigh, le_div_iff₀ hnorm]
  have h := form_lower_bound_of_orthogonal D hsym hpos n v horth
  nlinarith

theorem spectral_vectors_linearIndependent (D : FormSpectralData J B) :
    LinearIndependent ℂ D.vector := by
  apply LinearIndependent.of_comp J.toLinearMap
  have heq : J.toLinearMap ∘ D.vector = D.basis := funext D.embedding
  rw [heq]
  exact D.basis.orthonormal.linearIndependent

/-- The finite spectral trial space that attains the min--max value. -/
def spectralTrial (D : FormSpectralData J B) (n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ (range (fun i : Fin (n + 1) => D.vector i))

theorem spectralTrial_finrank (D : FormSpectralData J B) (n : ℕ) :
    Module.finrank ℂ (spectralTrial D n) = n + 1 := by
  unfold spectralTrial
  simpa only [Function.comp_def, Fintype.card_fin] using
    finrank_span_eq_card ((spectral_vectors_linearIndependent D).comp
      (fun i : Fin (n + 1) => (i : ℕ)) Fin.val_injective)

theorem spectral_sum_energy (D : FormSpectralData J B) (n : ℕ)
    (a : Fin (n + 1) → ℂ) :
    (inner ℂ (B (∑ i, a i • D.vector i)) (∑ i, a i • D.vector i)).re =
      ∑ i : Fin (n + 1), D.value i * ‖a i‖ ^ 2 := by
  have ho : Orthonormal ℂ (fun i : Fin (n + 1) => D.basis i) :=
    D.basis.orthonormal.comp (fun i : Fin (n + 1) => (i : ℕ)) Fin.val_injective
  have hcomplex : inner ℂ (B (∑ i, a i • D.vector i)) (∑ i, a i • D.vector i) =
      ((∑ i : Fin (n + 1), D.value i * ‖a i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [map_sum, map_smul, sum_inner, inner_smul_left, D.weak,
      D.embedding, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ho.inner_right_fintype a i, mul_left_comm, RCLike.conj_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal]
  simpa only [Complex.ofReal_re] using congrArg Complex.re hcomplex

theorem spectral_sum_norm (D : FormSpectralData J B) (n : ℕ)
    (a : Fin (n + 1) → ℂ) :
    ‖J (∑ i, a i • D.vector i)‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  have ho : Orthonormal ℂ (fun i : Fin (n + 1) => D.basis i) :=
    D.basis.orthonormal.comp (fun i : Fin (n + 1) => (i : ℕ)) Fin.val_injective
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [map_sum, map_smul, D.embedding]
  rw [ho.inner_sum a a Finset.univ]
  simp only [RCLike.conj_mul, map_sum]
  norm_cast

theorem spectralTrial_rayleigh_le (D : FormSpectralData J B)
    (hJi : Function.Injective J) (n : ℕ) (c : ℝ) {v : V}
    (hvS : v ∈ spectralTrial D n) (hv : v ≠ 0) :
    formRayleigh J B c v ≤ D.value n - c := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hvS
  have hJv : J (∑ i, a i • D.vector i) ≠ 0 :=
    fun h => hv (hJi (h.trans J.map_zero.symm))
  have hnorm : 0 < ‖J (∑ i, a i • D.vector i)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hJv)
  rw [formRayleigh, div_le_iff₀ hnorm, spectral_sum_energy, spectral_sum_norm]
  have hle : (∑ i : Fin (n + 1), D.value i * ‖a i‖ ^ 2) ≤
      D.value n * ∑ i, ‖a i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (D.monotone (by omega : (i : ℕ) ≤ n)) (sq_nonneg _)
  nlinarith

/-- Upper bounds achieved on a trial space of dimension `n+1`. Taking
the infimum of this set is exactly the infimum of the trial Rayleigh
suprema, without introducing an artificial boundedness convention. -/
def trialUpperBounds (J : V →L[ℂ] H) (B : V →L[ℂ] V) (c : ℝ) (n : ℕ) : Set ℝ :=
  {L | ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ Module.finrank ℂ S = n + 1 ∧
    ∀ v ∈ S, v ≠ 0 → formRayleigh J B c v ≤ L}

/-- The exact Courant--Fischer min--max principle, with attainment by
the first `n+1` spectral vectors in the form domain. -/
theorem minmax_isLeast (D : FormSpectralData J B)
    (hJi : Function.Injective J)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w))
    (hpos : ∀ v : V, 0 ≤ (inner ℂ (B v) v).re) (c : ℝ) (n : ℕ) :
    IsLeast (trialUpperBounds J B c n) (D.value n - c) := by
  constructor
  · refine ⟨spectralTrial D n, ?_, spectralTrial_finrank D n, ?_⟩
    · exact FiniteDimensional.of_finrank_eq_succ (spectralTrial_finrank D n)
    · intro v hv hvne
      exact spectralTrial_rayleigh_le D hJi n c hv hvne
  · intro L hL
    obtain ⟨S, hS, hdim, hbound⟩ := hL
    letI := hS
    obtain ⟨v, hvS, hvne, hge⟩ := trial_rayleigh_ge D hJi hsym hpos S n
      (by omega) c
    exact hge.trans (hbound v hvS hvne)

theorem minmax_eq_sInf (D : FormSpectralData J B)
    (hJi : Function.Injective J)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w))
    (hpos : ∀ v : V, 0 ≤ (inner ℂ (B v) v).re) (c : ℝ) (n : ℕ) :
    sInf (trialUpperBounds J B c n) = D.value n - c :=
  (minmax_isLeast D hJi hsym hpos c n).csInf_eq

/-- The frequently used trial-space consequence in homogeneous form. -/
theorem eigenvalue_le_of_trial_bound (D : FormSpectralData J B)
    (hJi : Function.Injective J)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w))
    (hpos : ∀ v : V, 0 ≤ (inner ℂ (B v) v).re)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] (n : ℕ)
    (hdim : n < Module.finrank ℂ S) (c L : ℝ)
    (hbound : ∀ v ∈ S, (inner ℂ (B v) v).re - c * ‖J v‖ ^ 2 ≤ L * ‖J v‖ ^ 2) :
    D.value n - c ≤ L := by
  obtain ⟨v, hvS, hv, horth⟩ := trial_orthogonal_vector D S n hdim
  have hJv : J v ≠ 0 := fun h => hv (hJi (h.trans J.map_zero.symm))
  have hnorm : 0 < ‖J v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hJv)
  have hlow := form_lower_bound_of_orthogonal D hsym hpos n v horth
  have hupp := hbound v hvS
  have hmul : (D.value n - c) * ‖J v‖ ^ 2 ≤ L * ‖J v‖ ^ 2 := by nlinarith
  nlinarith

/-- All the variational data and identities are constructed from the
coercive form and its compact, dense, injective embedding. -/
theorem exists_form_minmax (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJ : DenseRange J) (hJcompact : IsCompactOperator J)
    (hH : ¬ FiniteDimensional ℂ H) (B : V →L[ℂ] V) (hB : IsCoerciveOperator B)
    (hsym : ∀ v w : V, inner ℂ (B v) w = inner ℂ v (B w)) (c : ℝ) :
    ∃ D : FormSpectralData J B,
      ∀ n, IsLeast (trialUpperBounds J B c n) (D.value n - c) := by
  obtain ⟨D⟩ := exists_formSpectralData J hJi hJ hJcompact hH B hB hsym
  have hpos (v : V) : 0 ≤ (inner ℂ (B v) v).re := by
    obtain ⟨m, hm, hc⟩ := hB
    exact (mul_nonneg hm.le (sq_nonneg _)).trans (hc v)
  exact ⟨D, minmax_isLeast D hJi hsym hpos c⟩

/-- The min–max values are eigenvalues of the operator. -/
theorem spectral_operator_eigenvector (D : FormSpectralData J B)
    (hJi : Function.Injective J) (hJ : DenseRange J) (hB : IsCoerciveOperator B)
    (c : ℝ) (n : ℕ) :
    ∃ hn : D.basis n ∈ (coerciveAssociatedOperator J hJi hJ B hB c).domain,
      coerciveAssociatedOperator J hJi hJ B hB c ⟨D.basis n, hn⟩ =
        ((D.value n - c : ℝ) : ℂ) • D.basis n := by
  have hweak (w : V) :
      inner ℂ (B (D.vector n)) w - (c : ℂ) * inner ℂ (J (D.vector n)) (J w) =
        inner ℂ (((D.value n - c : ℝ) : ℂ) • D.basis n) (J w) := by
    rw [D.weak, D.embedding, inner_smul_left, Complex.conj_ofReal, Complex.ofReal_sub]
    ring
  obtain ⟨hn, he⟩ := (coerciveAssociatedOperator_eq_iff J hJi hJ B hB c
    (D.vector n) (((D.value n - c : ℝ) : ℂ) • D.basis n)).mp hweak
  have hres : ∃ hx : J (D.vector n) ∈ (coerciveAssociatedOperator J hJi hJ B hB c).domain,
      coerciveAssociatedOperator J hJi hJ B hB c ⟨J (D.vector n), hx⟩ =
        ((D.value n - c : ℝ) : ℂ) • D.basis n := ⟨hn, he⟩
  simpa only [D.embedding] using hres

theorem spectral_vector_rayleigh (D : FormSpectralData J B) (c : ℝ) (n : ℕ) :
    formRayleigh J B c (D.vector n) = D.value n - c := by
  rw [formRayleigh, D.weak, D.embedding, inner_self_eq_norm_sq_to_K,
    D.basis.orthonormal.1 n]
  simp

end ThetaTrial.Paper.FormMinMax
