import ThetaTrial.Paper.ThetaAvgContour
import ThetaTrial.ThetaSeries.DecayTools

/-! Pointwise envelopes for the hard tails of the theta average. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology

namespace ThetaTrial.Paper

def thetaAvgTailProfile (s : ℝ) : ℝ :=
  Real.exp ((11 / 2 : ℝ) * s) * Real.exp (-Real.exp (2 * s))

theorem thetaAvgTailProfile_pos (s : ℝ) : 0 < thetaAvgTailProfile s := by
  unfold thetaAvgTailProfile
  positivity

theorem thetaAvgTailProfile_continuous : Continuous thetaAvgTailProfile := by
  unfold thetaAvgTailProfile
  fun_prop

theorem thetaAvgTailProfile_integrable : Integrable thetaAvgTailProfile := by
  have hp : IntegrableOn thetaAvgTailProfile (Ioi 0) := by
    unfold thetaAvgTailProfile
    have hh := ThetaTrial.ThetaSeries.doubleExpEnvelope_integrable (11 / 2) (by norm_num : (0 : ℝ) < 1)
    unfold ThetaTrial.ThetaSeries.doubleExpEnvelope at hh
    simpa only [neg_mul, one_mul] using hh
  have hn : IntegrableOn thetaAvgTailProfile (Iic 0) := by
    apply (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 11 / 2) 0).mono'
      thetaAvgTailProfile_continuous.aestronglyMeasurable
    filter_upwards [] with s
    rw [Real.norm_of_nonneg (thetaAvgTailProfile_pos s).le]
    unfold thetaAvgTailProfile
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le))
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

def thetaAvgTailProfileMass : ℝ := ∫ s : ℝ, thetaAvgTailProfile s

theorem thetaAvgTailProfileMass_nonneg : 0 ≤ thetaAvgTailProfileMass :=
  integral_nonneg (fun s => (thetaAvgTailProfile_pos s).le)

def thetaAvgWeightedScale (a : ℝ) : ℝ :=
  thetaAvgContourConstant * (scaleZ a) ^ (13 / 4 : ℝ) *
    Real.exp (11 * a / 2 - 2 * scaleZ a)

theorem thetaAvgWeightedScale_pos (a : ℝ) : 0 < thetaAvgWeightedScale a := by
  exact mul_pos (mul_pos thetaAvgContourConstant_pos (Real.rpow_pos_of_pos (scaleZ_pos a) _))
    (Real.exp_pos _)

theorem thetaAvg_weighted_envelope_identity (a x : ℝ) :
    Real.exp |x| * thetaAvgContourEnvelope a x =
      thetaAvgWeightedScale a * thetaAvgTailProfile (|x| - a) := by
  unfold thetaAvgContourEnvelope thetaAvgWeightedScale thetaAvgTailProfile
  have he : Real.exp |x| * Real.exp (9 * |x| / 2) *
      Real.exp (-2 * scaleZ a - Real.exp (2 * (|x| - a))) =
      Real.exp (11 * a / 2 - 2 * scaleZ a) *
        (Real.exp (11 / 2 * (|x| - a)) * Real.exp (-Real.exp (2 * (|x| - a)))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (thetaAvgContourConstant * (scaleZ a) ^ (13 / 4 : ℝ)) *
        (Real.exp |x| * Real.exp (9 * |x| / 2) *
          Real.exp (-2 * scaleZ a - Real.exp (2 * (|x| - a)))) := by ring
    _ = _ := by rw [he]; ring

theorem thetaAvg_abs_profile_le (a x : ℝ) :
    thetaAvgTailProfile (|x| - a) ≤
      thetaAvgTailProfile (x - a) + thetaAvgTailProfile (-x - a) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (thetaAvgTailProfile_pos _).le
  · rw [abs_of_nonpos hx]
    exact le_add_of_nonneg_left (thetaAvgTailProfile_pos _).le

theorem thetaAvg_abs_profile_integrable (a : ℝ) :
    Integrable (fun x : ℝ => thetaAvgTailProfile (|x| - a)) := by
  have hp := thetaAvgTailProfile_integrable.comp_add_right (-a)
  have hn := hp.comp_neg
  have hc : Continuous (fun x : ℝ => thetaAvgTailProfile (|x| - a)) :=
    thetaAvgTailProfile_continuous.comp (by fun_prop)
  apply (hp.add hn).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (thetaAvgTailProfile_pos _).le]
  simpa only [sub_eq_add_neg, Pi.add_apply] using thetaAvg_abs_profile_le a x

theorem thetaAvg_abs_profile_integral_le (a : ℝ) :
    (∫ x : ℝ, thetaAvgTailProfile (|x| - a)) ≤ 2 * thetaAvgTailProfileMass := by
  have hp := thetaAvgTailProfile_integrable.comp_add_right (-a)
  have hn := hp.comp_neg
  have hsum : Integrable (fun x : ℝ => thetaAvgTailProfile (x - a) + thetaAvgTailProfile (-x - a)) := by
    convert hp.add hn using 1
    · rfl
    · rfl
  calc
    _ ≤ ∫ x : ℝ, thetaAvgTailProfile (x - a) + thetaAvgTailProfile (-x - a) := by
      apply integral_mono (thetaAvg_abs_profile_integrable a) hsum
      exact thetaAvg_abs_profile_le a
    _ = 2 * thetaAvgTailProfileMass := by
      rw [integral_add (by simpa only [sub_eq_add_neg] using hp)
        (by simpa only [sub_eq_add_neg] using hn)]
      have hp' : (∫ x : ℝ, thetaAvgTailProfile (x - a)) = thetaAvgTailProfileMass := by
        simpa only [sub_eq_add_neg, thetaAvgTailProfileMass] using
          integral_add_right_eq_self thetaAvgTailProfile (-a)
      have hn' : (∫ x : ℝ, thetaAvgTailProfile (-x - a)) = thetaAvgTailProfileMass := by
        rw [← hp']
        simpa only using integral_neg_eq_self (fun x : ℝ => thetaAvgTailProfile (x - a)) volume
      rw [hp', hn']
      ring

theorem thetaAvg_weighted_envelope_integrable (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp |x| * thetaAvgContourEnvelope a x) := by
  simp_rw [thetaAvg_weighted_envelope_identity]
  exact (thetaAvg_abs_profile_integrable a).const_mul _

theorem thetaAvg_weighted_envelope_integral_le (a : ℝ) :
    (∫ x : ℝ, Real.exp |x| * thetaAvgContourEnvelope a x) ≤
      thetaAvgWeightedScale a * (2 * thetaAvgTailProfileMass) := by
  simp_rw [thetaAvg_weighted_envelope_identity]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (thetaAvg_abs_profile_integral_le a)
    (thetaAvgWeightedScale_pos a).le

theorem thetaAvg_doubleExp_abs_integrable (p : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => ThetaTrial.ThetaSeries.doubleExpEnvelope p c |x|) := by
  let g : ℝ → ℝ := fun x => ThetaTrial.ThetaSeries.doubleExpEnvelope p c |x|
  have hp : IntegrableOn g (Ioi 0) := by
    apply (ThetaTrial.ThetaSeries.doubleExpEnvelope_integrable p hc).congr_fun _ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    simp only [g, abs_of_pos hx]
  have hn : IntegrableOn g (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, g, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hp
  simpa only [Iic_union_Ioi, integrableOn_univ, g] using hn.union hp

/-- Every fixed exponential weight is integrable against the contour
envelope, for use in noncompact explicit-formula approximation. -/
theorem thetaAvg_envelope_all_weights_integrable (a R : ℝ) :
    Integrable (fun x : ℝ => Real.exp (R * |x|) * thetaAvgContourEnvelope a x) := by
  have hg := thetaAvg_doubleExp_abs_integrable (R + 9 / 2) (Real.exp_pos (-2 * a))
  have he (x : ℝ) : Real.exp (R * |x|) * thetaAvgContourEnvelope a x =
      (thetaAvgContourConstant * (scaleZ a) ^ (13 / 4 : ℝ) * Real.exp (-2 * scaleZ a)) *
        ThetaTrial.ThetaSeries.doubleExpEnvelope (R + 9 / 2) (Real.exp (-2 * a)) |x| := by
    have hi : Real.exp (2 * (|x| - a)) = Real.exp (-2 * a) * Real.exp (2 * |x|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsum : Real.exp (R * |x|) * Real.exp (9 * |x| / 2) =
        Real.exp ((R + 9 / 2) * |x|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hdecay : Real.exp (-2 * scaleZ a - Real.exp (2 * (|x| - a))) =
        Real.exp (-2 * scaleZ a) *
          Real.exp (-Real.exp (-2 * a) * Real.exp (2 * |x|)) := by
      rw [← Real.exp_add, hi]
      congr 1
      ring
    unfold thetaAvgContourEnvelope ThetaTrial.ThetaSeries.doubleExpEnvelope
    rw [hdecay]
    calc
      _ = (thetaAvgContourConstant * (scaleZ a) ^ (13 / 4 : ℝ) * Real.exp (-2 * scaleZ a)) *
          ((Real.exp (R * |x|) * Real.exp (9 * |x| / 2)) *
            Real.exp (-Real.exp (-2 * a) * Real.exp (2 * |x|))) := by ring
      _ = _ := by rw [hsum]
  simp_rw [he]
  exact hg.const_mul _

end ThetaTrial.Paper
