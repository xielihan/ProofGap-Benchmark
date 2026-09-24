import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped Interval

namespace ProofGap.Exercise2237_2

noncomputable section

def f (t x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0 : ℝ) t then x
  else if x ∈ Set.Icc t 1 then t * ((1 - x) / (1 - t))
  else 0

theorem gap1 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, f t x) =
      (∫ x in (0 : ℝ)..t, x) +
        ∫ x in t..1, t * ((1 - x) / (1 - t)) := by
  have hleft : ∀ x ∈ Set.uIcc (0 : ℝ) t, f t x = x := by
    intro x hx
    rw [Set.uIcc_of_le ht.1.le] at hx
    simp [f, hx]
  have hne : 1 - t ≠ 0 := by
    linarith [ht.2]
  have hright :
      ∀ x ∈ Set.uIcc t (1 : ℝ),
        f t x = t * ((1 - x) / (1 - t)) := by
    intro x hx
    rw [Set.uIcc_of_le ht.2.le] at hx
    by_cases hxt : x = t
    · subst x
      simp [f, ht.1.le, hne]
    · have hnot : x ∉ Set.Icc (0 : ℝ) t := by
        intro hx0
        exact hxt (le_antisymm hx0.2 hx.1)
      simp [f, hnot, hx]
  have hcont : Continuous (fun x : ℝ => t * ((1 - x) / (1 - t))) :=
    continuous_const.mul ((continuous_const.sub continuous_id).div_const (1 - t))
  have hf_left :
      IntervalIntegrable (f t) MeasureTheory.volume (0 : ℝ) t :=
    ((continuous_id.intervalIntegrable
      (μ := MeasureTheory.volume) (0 : ℝ) t).congr
        (fun x hx =>
          (hleft x (Set.uIoc_subset_uIcc hx)).symm))
  have hf_right :
      IntervalIntegrable (f t) MeasureTheory.volume t (1 : ℝ) :=
    ((hcont.intervalIntegrable
      (μ := MeasureTheory.volume) t (1 : ℝ)).congr
        (fun x hx =>
          (hright x (Set.uIoc_subset_uIcc hx)).symm))
  have hint_left :
      (∫ x in (0 : ℝ)..t, f t x) = ∫ x in (0 : ℝ)..t, x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hleft x hx
  have hint_right :
      (∫ x in t..1, f t x) =
        ∫ x in t..1, t * ((1 - x) / (1 - t)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hright x hx
  calc
    (∫ x in (0 : ℝ)..1, f t x) =
        (∫ x in (0 : ℝ)..t, f t x) + ∫ x in t..1, f t x := by
          exact
            (intervalIntegral.integral_add_adjacent_intervals
              hf_left hf_right).symm
    _ = (∫ x in (0 : ℝ)..t, x) +
          ∫ x in t..1, t * ((1 - x) / (1 - t)) := by
          rw [hint_left, hint_right]

theorem gap2 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..t, x) +
        (∫ x in t..1, t * ((1 - x) / (1 - t))) =
      t / 2 := by
  have hne : 1 - t ≠ 0 := by
    linarith [ht.2]
  have hid (a b : ℝ) (hab : a < b) :
      (∫ x in a..b, x) = b ^ 2 / 2 - a ^ 2 / 2 := by
    have hderiv (x : ℝ) :
        HasDerivAt (fun y : ℝ => y * y) ((2 : ℝ) * x) x := by
      simpa [id, two_mul] using
        ((hasDerivAt_id x).mul (hasDerivAt_id x))
    have hderiv_eq :
        deriv (fun y : ℝ => y * y) = fun x : ℝ => (2 : ℝ) * x := by
      funext x
      exact (hderiv x).deriv
    have hdiff : Differentiable ℝ (fun y : ℝ => y * y) :=
      fun x => (hderiv x).differentiableAt
    have hdiff_uIcc :
        ∀ x ∈ Set.uIcc a b,
          DifferentiableAt ℝ (fun y : ℝ => y * y) x := by
      intro x _
      exact hdiff x
    have hcont : Continuous (fun x : ℝ => (2 : ℝ) * x) :=
      continuous_const.mul continuous_id
    have hcont_deriv :
        Continuous (deriv (fun y : ℝ => y * y)) := by
      rw [hderiv_eq]
      exact hcont
    have hint :
        IntervalIntegrable (fun x : ℝ => (2 : ℝ) * x)
          MeasureTheory.volume a b :=
      hcont.intervalIntegrable (μ := MeasureTheory.volume) a b
    have hanti_cont : Continuous (fun y : ℝ => y * y) :=
      hdiff.continuous
    have hdiff_on :
        DifferentiableOn ℝ (fun y : ℝ => y * y) (Set.uIcc a b) :=
      hdiff.differentiableOn
    have hcont_on :
        ContinuousOn (fun x : ℝ => (2 : ℝ) * x) (Set.uIcc a b) :=
      hcont.continuousOn
    have hanti_cont_on :
        ContinuousOn (fun y : ℝ => y * y) (Set.uIcc a b) :=
      hanti_cont.continuousOn
    have hderiv_on :
        ∀ x ∈ Set.uIcc a b,
          HasDerivAt (fun y : ℝ => y * y) ((2 : ℝ) * x) x := by
      intro x _
      exact hderiv x
    have hab_le : a ≤ b := hab.le
    have hdouble :
        (∫ x in a..b, (2 : ℝ) * x) = b * b - a * a := by
      apply intervalIntegral.integral_deriv_eq_sub'
        (fun y : ℝ => y * y)
      all_goals assumption
    have hscale :
        (∫ x in a..b, (2 : ℝ) * x) =
          (2 : ℝ) * (∫ x in a..b, x) := by
      rw [intervalIntegral.integral_const_mul]
    have htwice :
        (2 : ℝ) * (∫ x in a..b, x) = b * b - a * a := by
      calc
        (2 : ℝ) * (∫ x in a..b, x) =
            ∫ x in a..b, (2 : ℝ) * x := hscale.symm
        _ = b * b - a * a := hdouble
    calc
      (∫ x in a..b, x) =
          ((2 : ℝ) * (∫ x in a..b, x)) / 2 := by ring
      _ = (b * b - a * a) / 2 := by rw [htwice]
      _ = b ^ 2 / 2 - a ^ 2 / 2 := by ring
  have hfirst : (∫ x in (0 : ℝ)..t, x) = t ^ 2 / 2 := by
    rw [hid (0 : ℝ) t ht.1]
    norm_num
  have hxint : (∫ x in t..1, x) = (1 - t ^ 2) / 2 := by
    rw [hid t (1 : ℝ) ht.2]
    ring
  have h_one :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
        MeasureTheory.volume t (1 : ℝ) :=
    continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) t (1 : ℝ)
  have h_id :
      IntervalIntegrable (fun x : ℝ => x)
        MeasureTheory.volume t (1 : ℝ) :=
    continuous_id.intervalIntegrable
      (μ := MeasureTheory.volume) t (1 : ℝ)
  have hlin :
      (∫ x in t..1, (1 : ℝ) - x) =
        (1 - t) - (1 - t ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub h_one h_id,
      intervalIntegral.integral_const, hxint]
    simp
  have hrewrite :
      (fun x : ℝ => t * ((1 - x) / (1 - t))) =
        fun x : ℝ => (t / (1 - t)) * (1 - x) := by
    funext x
    ring
  have hsecond :
      (∫ x in t..1, t * ((1 - x) / (1 - t))) =
        t * (1 - t) / 2 := by
    rw [hrewrite, intervalIntegral.integral_const_mul, hlin]
    field_simp [hne] <;> ring
  rw [hfirst, hsecond]
  ring

theorem gap3 (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, f t x) = t / 2 := by
  rw [gap1 t ht, gap2 t ht]

end

end ProofGap.Exercise2237_2
