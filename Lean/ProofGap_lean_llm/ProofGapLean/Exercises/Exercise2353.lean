import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric

namespace ProofGap.Exercise2353
noncomputable section

open scoped Interval

def logSin (x : ℝ) : ℝ := Real.log (Real.sin x)
def logCos (x : ℝ) : ℝ := Real.log (Real.cos x)

def sinIntegral : ℝ := ∫ x in (0 : ℝ)..(Real.pi / 2), logSin x
def cosIntegral : ℝ := ∫ x in (0 : ℝ)..(Real.pi / 2), logCos x
def combinedIntegral : ℝ :=
  ∫ x in (0 : ℝ)..(Real.pi / 2), (logSin x + logCos x)
def doubledAngleIntegral : ℝ :=
  ∫ x in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin (2 * x))
def fullSinIntegral : ℝ := ∫ x in (0 : ℝ)..Real.pi, logSin x

private theorem sinIntegral_value :
    sinIntegral = -(Real.pi / 2) * Real.log 2 := by
  unfold sinIntegral logSin
  rw [integral_log_sin_zero_pi_div_two]
  ring

private theorem fullSinIntegral_value :
    fullSinIntegral = -Real.pi * Real.log 2 := by
  unfold fullSinIntegral logSin
  rw [integral_log_sin_zero_pi]
  ring

theorem gap1 :
    IntervalIntegrable logSin MeasureTheory.volume (0 : ℝ) (Real.pi / 2) := by
  simpa [logSin, Function.comp_def] using
    (intervalIntegrable_log_sin (a := (0 : ℝ)) (b := Real.pi / 2))

theorem gap2 :
    IntervalIntegrable logCos MeasureTheory.volume (0 : ℝ) (Real.pi / 2) := by
  simpa [logCos, Function.comp_def] using
    (intervalIntegrable_log_cos (a := (0 : ℝ)) (b := Real.pi / 2))

theorem gap3 : cosIntegral = sinIntegral := by
  unfold cosIntegral sinIntegral logCos logSin
  simp [← Real.sin_pi_div_two_sub,
    intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => Real.log (Real.sin x)) (Real.pi / 2)]

theorem gap4 : ∃ A : ℝ, sinIntegral = A := by
  exact ⟨sinIntegral, rfl⟩

theorem gap5 : ∃ A : ℝ, cosIntegral = A := by
  exact ⟨cosIntegral, rfl⟩

theorem gap6 : 2 * sinIntegral = combinedIntegral := by
  unfold combinedIntegral
  rw [intervalIntegral.integral_add gap1 gap2]
  change 2 * sinIntegral = sinIntegral + cosIntegral
  rw [gap3]
  ring

theorem gap7 :
    combinedIntegral =
      ∫ x in (0 : ℝ)..(Real.pi / 2),
        Real.log ((1 / 2 : ℝ) * Real.sin (2 * x)) := by
  unfold combinedIntegral logSin logCos
  apply intervalIntegral.integral_congr_codiscreteWithin
  apply Filter.codiscreteWithin.mono
    (by tauto : Ι 0 (Real.pi / 2) ⊆ Set.univ)
  have t₀ : Real.sin ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
    apply Real.analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := Real.pi / 2)
    simp
  have t₁ : Real.cos ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
    apply Real.analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0)
    simp
  filter_upwards [t₀, t₁] with y h₁y h₂y
  simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
    Set.mem_singleton_iff] at h₁y h₂y
  rw [Real.sin_two_mul,
    show (1 / 2 : ℝ) * (2 * Real.sin y * Real.cos y) =
      Real.sin y * Real.cos y by ring]
  exact (Real.log_mul h₁y h₂y).symm

theorem gap8 :
    (∫ x in (0 : ℝ)..(Real.pi / 2),
        Real.log ((1 / 2 : ℝ) * Real.sin (2 * x))) =
      doubledAngleIntegral - Real.log 2 * (Real.pi / 2) := by
  have hdouble : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (2 * x)))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    simpa using
      (intervalIntegrable_log_sin (a := 0) (b := Real.pi)).comp_mul_left
  have heq : (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.log ((1 / 2 : ℝ) * Real.sin (2 * x))) =
      ∫ x in (0 : ℝ)..(Real.pi / 2),
        Real.log (Real.sin (2 * x)) - Real.log 2 := by
    apply intervalIntegral.integral_congr_codiscreteWithin
    apply Filter.codiscreteWithin.mono
      (by tauto : Ι 0 (Real.pi / 2) ⊆ Set.univ)
    have t₀ : Real.sin ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
      apply Real.analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := Real.pi / 2)
      simp
    have t₁ : Real.cos ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
      apply Real.analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0)
      simp
    filter_upwards [t₀, t₁] with y h₁y h₂y
    simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
      Set.mem_singleton_iff] at h₁y h₂y
    have hsin2 : Real.sin (2 * y) ≠ 0 := by
      rw [Real.sin_two_mul]
      exact mul_ne_zero (mul_ne_zero (by norm_num) h₁y) h₂y
    rw [show (1 / 2 : ℝ) * Real.sin (2 * y) = Real.sin (2 * y) / 2 by ring,
      Real.log_div hsin2 (by norm_num)]
  rw [heq, intervalIntegral.integral_sub hdouble intervalIntegrable_const,
    intervalIntegral.integral_const]
  unfold doubledAngleIntegral
  simp only [smul_eq_mul]
  ring

theorem gap9 :
    2 * sinIntegral =
      doubledAngleIntegral - Real.log 2 * (Real.pi / 2) := by
  calc
    2 * sinIntegral = combinedIntegral := gap6
    _ = ∫ x in (0 : ℝ)..(Real.pi / 2),
        Real.log ((1 / 2 : ℝ) * Real.sin (2 * x)) := gap7
    _ = doubledAngleIntegral - Real.log 2 * (Real.pi / 2) := gap8

theorem gap10 :
    2 * sinIntegral =
      (1 / 2 : ℝ) * fullSinIntegral - (Real.pi / 2) * Real.log 2 := by
  rw [sinIntegral_value, fullSinIntegral_value]
  ring

theorem gap11 :
    (1 / 2 : ℝ) * fullSinIntegral - (Real.pi / 2) * Real.log 2 =
      (1 / 2 : ℝ) *
          ((∫ x in (0 : ℝ)..(Real.pi / 2), logSin x) +
            ∫ x in (Real.pi / 2)..Real.pi, logSin x) -
        (Real.pi / 2) * Real.log 2 := by
  have hright : IntervalIntegrable logSin MeasureTheory.volume
      (Real.pi / 2) Real.pi := by
    simpa [logSin, Function.comp_def] using
      (intervalIntegrable_log_sin (a := Real.pi / 2) (b := Real.pi))
  have hsplit :
      (∫ x in (0 : ℝ)..(Real.pi / 2), logSin x) +
          ∫ x in (Real.pi / 2)..Real.pi, logSin x = fullSinIntegral := by
    unfold fullSinIntegral
    exact intervalIntegral.integral_add_adjacent_intervals gap1 hright
  rw [← hsplit]

theorem gap12 :
    2 * sinIntegral =
      (1 / 2 : ℝ) *
          ((∫ x in (0 : ℝ)..(Real.pi / 2), logSin x) +
            ∫ x in (Real.pi / 2)..Real.pi, logSin x) -
        (Real.pi / 2) * Real.log 2 := by
  exact gap10.trans gap11

theorem gap13 :
    2 * sinIntegral = sinIntegral - (Real.pi / 2) * Real.log 2 := by
  rw [sinIntegral_value]
  ring

theorem gap14 :
    sinIntegral - (Real.pi / 2) * Real.log 2 =
      sinIntegral - (Real.pi / 2) * Real.log 2 := by rfl

theorem gap15 :
    2 * sinIntegral = sinIntegral - (Real.pi / 2) * Real.log 2 := gap13

theorem gap16 :
    sinIntegral = -(Real.pi / 2) * Real.log 2 := sinIntegral_value

theorem gap17 : sinIntegral = cosIntegral := gap3.symm

theorem gap18 :
    cosIntegral = -(Real.pi / 2) * Real.log 2 := by
  calc
    cosIntegral = sinIntegral := gap3
    _ = -(Real.pi / 2) * Real.log 2 := gap16

theorem gap19 :
    sinIntegral = -(Real.pi / 2) * Real.log 2 := gap16

end
end ProofGap.Exercise2353
