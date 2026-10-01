import ThetaTrial.Paper.TailVariation
import ThetaTrial.Paper.FullForm

/-!
The full hard-tail Weil-form bound, with gamma, both polar evaluations, and
the Mangoldt sum. Analytic membership and decay of the hard tail
are derived from ordinary weighted integrability of F and its derivative.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open ThetaTrial.PrimeContinuity
open scoped ComplexConjugate Topology

namespace ThetaTrial.Paper

def gammaCauchyMass : ℝ := ∫ r : ℝ, |gammaWeight r| / (1 + r ^ 2)

theorem gammaCauchyMass_nonneg : 0 ≤ gammaCauchyMass :=
  integral_nonneg (fun _ => by positivity)

def tailFormConstant : ℝ :=
  (1 / (2 * Real.pi)) * gammaCauchyMass * (1 + Real.pi / 2) ^ 2 +
    3 + 2 * logMajorantSum 1

theorem tailFormConstant_pos : 0 < tailFormConstant := by
  have hg := gammaCauchyMass_nonneg
  have hp := logMajorantSum_nonneg 1
  unfold tailFormConstant
  positivity

/-- The ordinary exponential weight controls Fourier-Laplace integrands on
the full closed strip needed for both pole evaluations. -/
theorem paperFourier_integrand_norm_le_weighted (f : ℝ → ℂ) {z : ℂ}
    (hz : |z.im| ≤ 1) (u : ℝ) :
    ‖f u * Complex.exp (-I * z * (u : ℂ))‖ ≤ ‖weightedProfile 1 f u‖ := by
  rw [norm_mul, Complex.norm_exp, weightedProfile_norm, one_mul]
  have hre : (-I * z * (u : ℂ)).re = z.im * u := by simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hex : z.im * u ≤ |u| := calc
    _ ≤ |z.im * u| := le_abs_self _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ 1 * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
    _ = _ := one_mul _
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (norm_nonneg (f u))

theorem paperFourier_integrable_of_weighted {f : ℝ → ℂ} (hf : Integrable f)
    (hw : Integrable (weightedProfile 1 f)) {z : ℂ} (hz : |z.im| ≤ 1) :
    Integrable (fun u : ℝ => f u * Complex.exp (-I * z * (u : ℂ))) := by
  apply hw.norm.mono'
    (hf.aestronglyMeasurable.mul (show Continuous (fun u : ℝ =>
      Complex.exp (-I * z * (u : ℂ))) by fun_prop).aestronglyMeasurable)
  exact Eventually.of_forall (paperFourier_integrand_norm_le_weighted f hz)

theorem paperFourier_norm_le_weighted_l1 {f : ℝ → ℂ} (hf : Integrable f)
    (hw : Integrable (weightedProfile 1 f)) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖paperFourier f z‖ ≤ ∫ u : ℝ, ‖weightedProfile 1 f u‖ := by
  apply (norm_integral_le_integral_norm _).trans
  exact integral_mono (paperFourier_integrable_of_weighted hf hw hz).norm hw.norm
    (paperFourier_integrand_norm_le_weighted f hz)

theorem gamma_integral_abs_le_of_fourier_decay {f : ℝ → ℂ} {M : ℝ}
    (hm : AEStronglyMeasurable (fun r : ℝ => paperFourier f r))
    (hb : ∀ r : ℝ, ‖paperFourier f r‖ ^ 2 ≤ M ^ 2 / (1 + r ^ 2)) :
    |∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)| ≤
      M ^ 2 * gammaCauchyMass := by
  have hi := gamma_term_integrable_of_fourier_decay hm hb
  calc
    _ ≤ ∫ r : ℝ, ‖gammaWeight r * Complex.normSq (paperFourier f r)‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun r : ℝ => gammaWeight r * Complex.normSq (paperFourier f r))
    _ ≤ ∫ r : ℝ, M ^ 2 * (|gammaWeight r| / (1 + r ^ 2)) := by
      apply integral_mono hi.norm (gamma_cauchy_integrable.const_mul _)
      intro r
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _),
        ← Complex.sq_norm]
      calc
        _ ≤ |gammaWeight r| * (M ^ 2 / (1 + r ^ 2)) :=
          mul_le_mul_of_nonneg_left (hb r) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

theorem fullPrime_abs_le_weightedNorm {f : ℝ → ℂ} (hf : WeightedL2 1 f) :
    |∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re| ≤ logMajorantSum 1 * (weightedNorm 1 f) ^ 2 := by
  have hz : WeightedL2 1 (0 : ℝ → ℂ) := by
    have he : weightedProfile 1 (0 : ℝ → ℂ) = 0 := by
      funext x
      simp [weightedProfile]
    change MemLp (weightedProfile 1 (0 : ℝ → ℂ)) 2 volume
    rw [he]
    exact MemLp.zero
  have h := fullPrime_continuous_bound (a := 1) (by norm_num) hf hz
  simpa [correlation, weightedNorm, weightedProfile, sq, mul_assoc] using h

private theorem square_cauchy_bound {g : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ r, ‖g r‖ * (1 + |r|) ≤ M) (r : ℝ) :
    ‖g r‖ ^ 2 ≤ M ^ 2 / (1 + r ^ 2) := by
  have hs := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (by positivity)) hM).2 (hb r)
  have hr : 1 + r ^ 2 ≤ (1 + |r|) ^ 2 := by nlinarith [sq_abs r, abs_nonneg r]
  have hp := mul_le_mul_of_nonneg_left hr (sq_nonneg ‖g r‖)
  rw [mul_pow] at hs
  exact (le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)).2 (hp.trans hs)

theorem exteriorTail_fourier_square_bound {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) (r : ℝ) :
    ‖paperFourier (exteriorTail a F) r‖ ^ 2 ≤
      ((1 + Real.pi / 2) * hardTailBudget F F' a) ^ 2 / (1 + r ^ 2) := by
  apply square_cauchy_bound (g := fun r : ℝ => paperFourier (exteriorTail a F) r)
    (mul_nonneg (by positivity) (hardTailBudget_nonneg F F' a))
  exact exteriorTail_fourier_bound hc ha hd hi hi'

/-- Every integral and the prime series in the form of the hard tail converge
absolutely. -/
theorem exteriorTail_fullForm_converges {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier (exteriorTail a F) r)) ∧
    Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation (exteriorTail a F) (Real.log n)).re|) ∧
    (∀ z : ℂ, |z.im| ≤ 1 → Integrable (fun u : ℝ =>
      exteriorTail a F u * Complex.exp (-I * z * (u : ℂ)))) := by
  have hf := exteriorTail_integrable (integrableOn_of_weightedProfile_one hi)
  have hw : Integrable (weightedProfile 1 (exteriorTail a F)) := by
    rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  refine ⟨gamma_term_integrable_of_fourier_decay
    (paperFourier_continuous_real hf).aestronglyMeasurable
    (exteriorTail_fourier_square_bound hc ha hd hi hi'), ?_, ?_⟩
  · exact fullPrime_absolutely_summable (by norm_num : (1 / 2 : ℝ) < 1)
      (exteriorTail_weightedL2 hc ha hd hi hi')
  · intro z hz
    exact paperFourier_integrable_of_weighted hf hw hz

/-- Each correlation integral in the prime term converges absolutely. -/
theorem exteriorTail_correlation_integrable {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) (v : ℝ) :
    Integrable (fun u : ℝ => exteriorTail a F u * conj (exteriorTail a F (u - v))) := by
  have hw := exteriorTail_weightedL2 hc ha hd hi hi'
  have hh := (ThetaTrial.PrimeContinuity.correlation_integrable (by norm_num : (0 : ℝ) ≤ 1)
    hw hw v).comp_add_right (-v)
  simpa only [← sub_eq_add_neg, sub_add_cancel] using hh

private theorem fullWeilForm_abs_le_terms (f : ℝ → ℂ) :
    |fullWeilForm f| ≤
      (1 / (2 * Real.pi)) * |∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)| +
      2 * |(paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re| +
      2 * |∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re| := by
  unfold fullWeilForm
  calc
    _ ≤ |(1 / (2 * Real.pi)) *
          (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)) +
        2 * (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re| +
        |2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation f (Real.log n)).re| := abs_sub _ _
    _ ≤ |(1 / (2 * Real.pi)) *
          (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r))| +
        |2 * (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re| +
        |2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation f (Real.log n)).re| := add_le_add (abs_add_le _ _) le_rfl
    _ = _ := by
      simp only [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
      norm_num

/-- The weighted-BV form bound of the paper, for hard tails. -/
theorem exteriorTail_fullWeilForm_abs_le {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    |fullWeilForm (exteriorTail a F)| ≤ tailFormConstant * (hardTailBudget F F' a) ^ 2 := by
  let f := exteriorTail a F
  let M := hardTailBudget F F' a
  have hM : 0 ≤ M := hardTailBudget_nonneg F F' a
  have hf : Integrable f := exteriorTail_integrable (integrableOn_of_weightedProfile_one hi)
  have hw : Integrable (weightedProfile 1 f) := by
    dsimp [f]
    rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  have hl1 : (∫ u : ℝ, ‖weightedProfile 1 f u‖) ≤ M := weighted_exteriorTail_l1_le hi hi'
  have hplus : ‖paperFourier f (I / 2)‖ ≤ M :=
    (paperFourier_norm_le_weighted_l1 hf hw (by norm_num)).trans hl1
  have hminus : ‖paperFourier f (-I / 2)‖ ≤ M :=
    (paperFourier_norm_le_weighted_l1 hf hw (by norm_num)).trans hl1
  have hpoles : |(paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re| ≤ M ^ 2 := by
    calc
      _ ≤ ‖paperFourier f (I / 2) * conj (paperFourier f (-I / 2))‖ := Complex.abs_re_le_norm _
      _ = ‖paperFourier f (I / 2)‖ * ‖paperFourier f (-I / 2)‖ := by rw [norm_mul, norm_conj]
      _ ≤ M * M := mul_le_mul hplus hminus (norm_nonneg _) hM
      _ = _ := (sq M).symm
  have hprimes : |∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re| ≤ logMajorantSum 1 * M ^ 2 := by
    apply (fullPrime_abs_le_weightedNorm (exteriorTail_weightedL2 hc ha hd hi hi')).trans
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (weightedNorm_nonneg 1 f) hM).2 (exteriorTail_weightedNorm_le hc ha hd hi hi'))
      (logMajorantSum_nonneg 1)
  have hgamma : |∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)| ≤
      ((1 + Real.pi / 2) * M) ^ 2 * gammaCauchyMass :=
    gamma_integral_abs_le_of_fourier_decay (paperFourier_continuous_real hf).aestronglyMeasurable
      (exteriorTail_fourier_square_bound hc ha hd hi hi')
  apply (fullWeilForm_abs_le_terms f).trans
  calc
    _ ≤ (1 / (2 * Real.pi)) * (((1 + Real.pi / 2) * M) ^ 2 * gammaCauchyMass) +
        2 * M ^ 2 + 2 * (logMajorantSum 1 * M ^ 2) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hgamma (by positivity))
          (mul_le_mul_of_nonneg_left hpoles (by norm_num)))
        (mul_le_mul_of_nonneg_left hprimes (by norm_num))
    _ ≤ tailFormConstant * M ^ 2 := by
      unfold tailFormConstant
      nlinarith [sq_nonneg M]

end ThetaTrial.Paper
