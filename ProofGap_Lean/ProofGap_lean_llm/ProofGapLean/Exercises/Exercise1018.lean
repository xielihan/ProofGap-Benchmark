import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1018

noncomputable section

open scoped Topology

def signFunction (x : ℝ) : ℝ := Real.sign x
def differenceQuotient (h : ℝ) : ℝ :=
  (signFunction h - signFunction 0) / h
def puncturedZero : Filter ℝ := 𝓝[({0} : Set ℝ)ᶜ] 0

theorem gap1 (f : ℝ → ℝ) (x₀ : ℝ)
    (h : ¬ ContinuousAt f x₀) :
    ¬ DifferentiableAt ℝ f x₀ := by
  intro hdiff
  exact h hdiff.continuousAt

theorem gap2 : ¬ ContinuousAt signFunction 0 := by
  intro hc
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδpos, hcontrol⟩ := hc ((1 : ℝ) / 2) (by norm_num)
  have hxpos : 0 < δ / 2 := by linarith
  have hdist : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]
    linarith
  have hbad :
      dist (signFunction (δ / 2)) (signFunction 0) < (1 : ℝ) / 2 :=
    hcontrol hdist
  simp only [signFunction, Real.sign_zero, Real.dist_eq, sub_zero] at hbad
  rw [Real.sign_of_pos hxpos] at hbad
  norm_num at hbad

theorem gap3 (h : ℝ) (hh : h ≠ 0) :
    differenceQuotient h = (|h| / h) / h := by
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · unfold differenceQuotient signFunction
    rw [Real.sign_of_neg hneg, Real.sign_zero, sub_zero, abs_of_neg hneg]
    field_simp [hh]
  · exact (hh hzero).elim
  · unfold differenceQuotient signFunction
    rw [Real.sign_of_pos hpos, Real.sign_zero, sub_zero, abs_of_pos hpos]
    field_simp [hh]

theorem gap4 (h : ℝ) (hh : h ≠ 0) :
    (|h| / h) / h = 1 / |h| := by
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · rw [abs_of_neg hneg]
    field_simp [hh]
  · exact (hh hzero).elim
  · rw [abs_of_pos hpos]
    field_simp [hh]

theorem gap5 (h : ℝ) (hh : h ≠ 0) :
    differenceQuotient h = 1 / |h| := by
  rw [gap3 h hh, gap4 h hh]

theorem gap6 : Tendsto differenceQuotient puncturedZero atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have hdpos : 0 < |b| + 1 := by
    nlinarith [abs_nonneg b]
  have heps : 0 < 1 / (|b| + 1) := one_div_pos.mpr hdpos
  have hnear0 : ∀ᶠ h in 𝓝 (0 : ℝ), |h| < 1 / (|b| + 1) := by
    change {h : ℝ | |h| < 1 / (|b| + 1)} ∈ 𝓝 0
    have hball_eq :
        {h : ℝ | |h| < 1 / (|b| + 1)} =
          Metric.ball 0 (1 / (|b| + 1)) := by
      ext h
      simp [Metric.mem_ball, Real.dist_eq]
    rw [hball_eq]
    exact Metric.ball_mem_nhds (0 : ℝ) heps
  have hnear : ∀ᶠ h in puncturedZero, |h| < 1 / (|b| + 1) := by
    apply Filter.Eventually.filter_mono ?_ hnear0
    change 𝓝[({0} : Set ℝ)ᶜ] 0 ≤ 𝓝 0
    exact inf_le_left
  have hne : ∀ᶠ h in puncturedZero, h ≠ 0 := by
    change ∀ᶠ h in 𝓝[({0} : Set ℝ)ᶜ] 0, h ≠ 0
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh
  filter_upwards [hnear, hne] with h hsmall hh
  rw [gap5 h hh]
  have habspos : 0 < |h| := abs_pos.mpr hh
  have hprod : |h| * (|b| + 1) < 1 :=
    (lt_div_iff₀ hdpos).mp hsmall
  have hmul : |b| * |h| < 1 := by
    nlinarith [abs_nonneg b]
  have hinv : |b| < 1 / |h| :=
    (lt_div_iff₀ habspos).2 hmul
  exact (le_abs_self b).trans hinv.le

end

end ProofGap.Exercise1018
