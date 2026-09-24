import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace ProofGap.Exercise2384_1
noncomputable section

open Filter MeasureTheory
open scoped Interval

def fresnelIntegrand (x : ℝ) : ℝ := Real.sin (x ^ 2)

private def tailCoeff (x : ℝ) : ℝ := -(1 / 2 : ℝ) * x⁻¹

private def tailCoeffDeriv (x : ℝ) : ℝ := (1 / 2 : ℝ) * (x ^ 2)⁻¹

private def phaseCos (x : ℝ) : ℝ := Real.cos (x ^ 2)

private def phaseCosDeriv (x : ℝ) : ℝ := -2 * x * Real.sin (x ^ 2)

private def tailRemainder (x : ℝ) : ℝ := tailCoeffDeriv x * phaseCos x

private theorem tailCoeff_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt tailCoeff (tailCoeffDeriv x) x := by
  have h := (hasDerivAt_inv hx).const_mul (-(1 / 2 : ℝ))
  unfold tailCoeff tailCoeffDeriv
  convert h using 1 <;> ring

private theorem phaseCos_hasDerivAt (x : ℝ) :
    HasDerivAt phaseCos (phaseCosDeriv x) x := by
  have hs : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 2
  have h := (Real.hasDerivAt_cos (x ^ 2)).comp x hs
  unfold phaseCos phaseCosDeriv
  convert h using 1 <;> ring

private theorem tailCoeffDeriv_integrableOn :
    IntegrableOn tailCoeffDeriv (Set.Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (-2)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hscaled := hpow.const_mul (1 / 2 : ℝ)
  apply IntegrableOn.congr_fun hscaled
  · intro x hx
    have hxpos : 0 < x := zero_lt_one.trans hx
    have hx0 : x ≠ 0 := hxpos.ne'
    unfold tailCoeffDeriv
    change (1 / 2 : ℝ) * Real.rpow x (-2) = (1 / 2 : ℝ) * (x ^ 2)⁻¹
    have hrneg : Real.rpow x (-2) = (Real.rpow x 2)⁻¹ := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_neg hxpos.le (2 : ℝ)
    have hrnat : Real.rpow x 2 = x ^ 2 := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_natCast x 2
    rw [hrneg, hrnat]
  · exact measurableSet_Ioi

private theorem tailRemainder_integrableOn :
    IntegrableOn tailRemainder (Set.Ioi (1 : ℝ)) := by
  apply Integrable.mono' tailCoeffDeriv_integrableOn
  · apply Measurable.aestronglyMeasurable
    unfold tailRemainder tailCoeffDeriv phaseCos
    measurability
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hc : |Real.cos (x ^ 2)| ≤ 1 := Real.abs_cos_le_one _
    have hw : 0 ≤ tailCoeffDeriv x := by
      unfold tailCoeffDeriv
      positivity
    rw [Real.norm_eq_abs]
    unfold tailRemainder phaseCos
    rw [abs_mul, abs_of_nonneg hw]
    exact (mul_le_mul_of_nonneg_left hc hw).trans_eq (mul_one _)

private theorem fresnel_tail_identity (A : ℝ) (hA : 1 ≤ A) :
    (∫ x in (1 : ℝ)..A, fresnelIntegrand x) =
      tailCoeff A * phaseCos A - tailCoeff 1 * phaseCos 1 -
        ∫ x in (1 : ℝ)..A, tailRemainder x := by
  have hu : ∀ x ∈ Set.uIcc (1 : ℝ) A,
      HasDerivAt tailCoeff (tailCoeffDeriv x) x := by
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    exact tailCoeff_hasDerivAt x (by linarith [hx.1])
  have hv : ∀ x ∈ Set.uIcc (1 : ℝ) A,
      HasDerivAt phaseCos (phaseCosDeriv x) x := by
    intro x _
    exact phaseCos_hasDerivAt x
  have hu' : IntervalIntegrable tailCoeffDeriv volume (1 : ℝ) A := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    unfold tailCoeffDeriv
    exact continuousAt_const.mul ((continuousAt_id.pow 2).inv₀ (by
      have hx0 : x ≠ 0 := by linarith [hx.1]
      simpa [id] using pow_ne_zero 2 hx0))
  have hv' : IntervalIntegrable phaseCosDeriv volume (1 : ℝ) A := by
    apply Continuous.intervalIntegrable
    unfold phaseCosDeriv
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  calc
    (∫ x in (1 : ℝ)..A, fresnelIntegrand x) =
        ∫ x in (1 : ℝ)..A, tailCoeff x * phaseCosDeriv x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      unfold fresnelIntegrand tailCoeff phaseCosDeriv
      field_simp [hx0]
    _ = tailCoeff A * phaseCos A - tailCoeff 1 * phaseCos 1 -
        ∫ x in (1 : ℝ)..A, tailCoeffDeriv x * phaseCos x := hibp
    _ = tailCoeff A * phaseCos A - tailCoeff 1 * phaseCos 1 -
        ∫ x in (1 : ℝ)..A, tailRemainder x := by rfl

private theorem tail_boundary_tendsto_zero :
    Tendsto (fun A => tailCoeff A * phaseCos A) atTop (nhds 0) := by
  have hc : Tendsto tailCoeff atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => -(1 / 2 : ℝ)) atTop
      (nhds (-(1 / 2 : ℝ)))).mul tendsto_inv_atTop_zero
    simpa only [tailCoeff, mul_zero] using h
  have hO : (fun A => tailCoeff A * phaseCos A) =O[atTop] tailCoeff := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, Filter.Eventually.of_forall ?_⟩
    intro A
    rw [norm_mul, one_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by
      simpa [phaseCos, Real.norm_eq_abs] using Real.abs_cos_le_one (A ^ 2))
  exact hO.trans_tendsto hc

private def positivePhaseSeq (n : ℕ) : ℝ :=
  Real.sqrt (Real.pi / 2 + (n : ℝ) * (2 * Real.pi))

private def negativePhaseSeq (n : ℕ) : ℝ :=
  Real.sqrt (3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi))

private theorem positivePhaseSeq_tendsto : Tendsto positivePhaseSeq atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have htwoPi : 0 < (2 * Real.pi : ℝ) := mul_pos (by norm_num) Real.pi_pos
  have hmul : Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi)) atTop atTop :=
    hn.atTop_mul_const htwoPi
  have hadd : Tendsto (fun n : ℕ => Real.pi / 2 + (n : ℝ) * (2 * Real.pi))
      atTop atTop := atTop.tendsto_atTop_add_const_left (Real.pi / 2) hmul
  exact Real.tendsto_sqrt_atTop.comp (by simpa [positivePhaseSeq] using hadd)

private theorem negativePhaseSeq_tendsto : Tendsto negativePhaseSeq atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have htwoPi : 0 < (2 * Real.pi : ℝ) := mul_pos (by norm_num) Real.pi_pos
  have hmul : Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi)) atTop atTop :=
    hn.atTop_mul_const htwoPi
  have hadd : Tendsto (fun n : ℕ => 3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi))
      atTop atTop := atTop.tendsto_atTop_add_const_left (3 * Real.pi / 2) hmul
  exact Real.tendsto_sqrt_atTop.comp (by simpa [negativePhaseSeq] using hadd)

private theorem fresnel_positivePhaseSeq (n : ℕ) :
    fresnelIntegrand (positivePhaseSeq n) = 1 := by
  have hnonneg : 0 ≤ Real.pi / 2 + (n : ℝ) * (2 * Real.pi) := by positivity
  unfold fresnelIntegrand positivePhaseSeq
  rw [Real.sq_sqrt hnonneg, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

private theorem fresnel_negativePhaseSeq (n : ℕ) :
    fresnelIntegrand (negativePhaseSeq n) = -1 := by
  have hnonneg : 0 ≤ 3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi) := by positivity
  unfold fresnelIntegrand negativePhaseSeq
  rw [Real.sq_sqrt hnonneg, Real.sin_add_nat_mul_two_pi]
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
    Real.sin_add_pi, Real.sin_pi_div_two]

theorem gap1 :
    ∃ L : ℝ,
      Tendsto (fun A => ∫ x in (0 : ℝ)..A, fresnelIntegrand x)
        atTop (nhds L) := by
  let C : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), fresnelIntegrand x
  let R : ℝ := ∫ x in Set.Ioi (1 : ℝ), tailRemainder x
  refine ⟨C - tailCoeff 1 * phaseCos 1 - R, ?_⟩
  have hrem : Tendsto (fun A => ∫ x in (1 : ℝ)..A, tailRemainder x)
      atTop (nhds R) := by
    simpa only [R] using intervalIntegral_tendsto_integral_Ioi
      1 tailRemainder_integrableOn tendsto_id
  have hlim : Tendsto
      (fun A => C + tailCoeff A * phaseCos A - tailCoeff 1 * phaseCos 1 -
        ∫ x in (1 : ℝ)..A, tailRemainder x)
      atTop (nhds (C - tailCoeff 1 * phaseCos 1 - R)) := by
    have hC : Tendsto (fun _ : ℝ => C) atTop (nhds C) := tendsto_const_nhds
    have hK : Tendsto (fun _ : ℝ => tailCoeff 1 * phaseCos 1) atTop
        (nhds (tailCoeff 1 * phaseCos 1)) := tendsto_const_nhds
    have h := (hC.add tail_boundary_tendsto_zero).sub hK
    simpa using h.sub hrem
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
  have h01 : IntervalIntegrable fresnelIntegrand volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    unfold fresnelIntegrand
    fun_prop
  have h1A : IntervalIntegrable fresnelIntegrand volume (1 : ℝ) A := by
    apply Continuous.intervalIntegrable
    unfold fresnelIntegrand
    fun_prop
  have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h1A
  rw [← hadd, fresnel_tail_identity A hA]
  unfold C
  ring

theorem gap2 :
    ¬ ∃ L : ℝ, Tendsto fresnelIntegrand atTop (nhds L) := by
  rintro ⟨L, hL⟩
  have hp := hL.comp positivePhaseSeq_tendsto
  have hn := hL.comp negativePhaseSeq_tendsto
  have hp' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds L) := by
    apply hp.congr'
    exact Filter.Eventually.of_forall fresnel_positivePhaseSeq
  have hn' : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds L) := by
    apply hn.congr'
    exact Filter.Eventually.of_forall fresnel_negativePhaseSeq
  have hL1 : L = 1 := tendsto_nhds_unique hp' tendsto_const_nhds
  have hLn : L = -1 := tendsto_nhds_unique hn' tendsto_const_nhds
  linarith

theorem gap3 :
    ¬ Tendsto fresnelIntegrand atTop (nhds 0) := by
  intro h
  exact gap2 ⟨0, h⟩

theorem gap4 :
    ¬ ∀ (f : ℝ → ℝ) (a : ℝ),
      (∃ L : ℝ, Tendsto (fun A => ∫ x in a..A, f x) atTop (nhds L)) →
      Tendsto f atTop (nhds 0) := by
  intro h
  exact gap3 (h fresnelIntegrand 0 gap1)

end
end ProofGap.Exercise2384_1
