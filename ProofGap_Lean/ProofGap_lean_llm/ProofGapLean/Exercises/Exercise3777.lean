import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3777

noncomputable section

open MeasureTheory
open scoped Interval

def gaussian (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2))

def F (a : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), Real.exp (-((x - a) ^ 2))

private theorem private_continuous_gaussian : Continuous gaussian := by
  unfold gaussian
  exact Real.continuous_exp.comp ((continuous_id.pow 2).neg)

private theorem private_integrable_gaussian : Integrable gaussian := by
  simpa [gaussian, one_mul] using
    (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1))

private theorem private_gaussian_tail_split_of_le (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Set.Ioi a, gaussian x) =
      (∫ x in a..b, gaussian x) + ∫ x in Set.Ioi b, gaussian x := by
  rw [intervalIntegral.integral_of_le hab]
  have hset : Set.Ioi a = Set.Ioc a b ∪ Set.Ioi b := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      by_cases hxb : x ≤ b
      · exact Or.inl ⟨hx, hxb⟩
      · exact Or.inr (lt_of_not_ge hxb)
    · rintro (hx | hx)
      · exact hx.1
      · exact lt_of_le_of_lt hab hx
  have hdis : Disjoint (Set.Ioc a b) (Set.Ioi b) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  calc
    (∫ x in Set.Ioi a, gaussian x) =
        ∫ x in Set.Ioc a b ∪ Set.Ioi b, gaussian x := by
          rw [hset]
    _ = ∫ x : ℝ, (Set.Ioc a b ∪ Set.Ioi b).indicator gaussian x := by
          symm
          exact MeasureTheory.integral_indicator
            (measurableSet_Ioc.union measurableSet_Ioi)
    _ = ∫ x : ℝ, ((Set.Ioc a b).indicator gaussian x +
          (Set.Ioi b).indicator gaussian x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ Set.Ioc a b
          · have hxb : x ∉ Set.Ioi b := by
              intro hxb
              exact (Set.disjoint_left.mp hdis) hx hxb
            simp [hx, hxb]
          · by_cases hxb : x ∈ Set.Ioi b
            · simp [hx, hxb]
            · simp [hx, hxb]
    _ = (∫ x : ℝ, (Set.Ioc a b).indicator gaussian x) +
          ∫ x : ℝ, (Set.Ioi b).indicator gaussian x := by
          exact MeasureTheory.integral_add
            (private_integrable_gaussian.indicator measurableSet_Ioc)
            (private_integrable_gaussian.indicator measurableSet_Ioi)
    _ = (∫ x in Set.Ioc a b, gaussian x) +
          ∫ x in Set.Ioi b, gaussian x := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioc,
            MeasureTheory.integral_indicator measurableSet_Ioi]

private theorem private_gaussian_tail_split (a b : ℝ) :
    (∫ x in Set.Ioi a, gaussian x) =
      (∫ x in a..b, gaussian x) + ∫ x in Set.Ioi b, gaussian x := by
  rcases le_total a b with hab | hba
  · exact private_gaussian_tail_split_of_le a b hab
  · have h := private_gaussian_tail_split_of_le b a hba
    rw [h, intervalIntegral.integral_symm]
    ring

private theorem private_gaussian_interval_reflect (a : ℝ) :
    (∫ x in (-a)..0, gaussian x) = ∫ x in (0 : ℝ)..a, gaussian x := by
  simpa [gaussian] using
    (intervalIntegral.integral_comp_neg (f := gaussian) (a := (0 : ℝ)) (b := a)).symm

private theorem private_gaussian_Ioi_zero :
    (∫ x in Set.Ioi (0 : ℝ), gaussian x) = Real.sqrt Real.pi / 2 := by
  simpa [gaussian] using (integral_gaussian_Ioi (1 : ℝ))

theorem gap1 (a : ℝ) :
    F a = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-((x - a) ^ 2)) := by
  rfl

theorem gap2 (a : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-((x - a) ^ 2))) =
      ∫ x in Set.Ioi (-a), gaussian x := by
  calc
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-((x - a) ^ 2))) =
        ∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator
          (fun x => Real.exp (-((x - a) ^ 2))) x := by
            symm
            exact MeasureTheory.integral_indicator measurableSet_Ioi
    _ = ∫ y : ℝ, (Set.Ioi (0 : ℝ)).indicator
          (fun x => Real.exp (-((x - a) ^ 2))) (y + a) := by
            symm
            apply MeasureTheory.integral_add_right_eq_self
    _ = ∫ y : ℝ, (Set.Ioi (-a)).indicator gaussian y := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with y
          by_cases hy : y ∈ Set.Ioi (-a)
          · have hy' : y + a ∈ Set.Ioi (0 : ℝ) := by
              change 0 < y + a
              change -a < y at hy
              linarith
            simp [hy, hy', gaussian]
          · have hy' : y + a ∉ Set.Ioi (0 : ℝ) := by
              intro h
              apply hy
              change -a < y
              change 0 < y + a at h
              linarith
            simp [hy, hy']
    _ = ∫ x in Set.Ioi (-a), gaussian x := by
          exact MeasureTheory.integral_indicator measurableSet_Ioi

theorem gap3 (a : ℝ) :
    F a = ∫ x in Set.Ioi (-a), gaussian x := by
  calc
    F a = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-((x - a) ^ 2)) := gap1 a
    _ = ∫ x in Set.Ioi (-a), gaussian x := gap2 a

theorem gap4 (a : ℝ) :
    F a =
      (∫ x in (-a)..0, gaussian x) +
        ∫ x in Set.Ioi (0 : ℝ), gaussian x := by
  calc
    F a = ∫ x in Set.Ioi (-a), gaussian x := gap3 a
    _ = (∫ x in (-a)..0, gaussian x) +
        ∫ x in Set.Ioi (0 : ℝ), gaussian x :=
      private_gaussian_tail_split (-a) 0

theorem gap5 (a : ℝ) :
    (∫ x in (-a)..0, gaussian x) +
        (∫ x in Set.Ioi (0 : ℝ), gaussian x) =
      (∫ x in (0 : ℝ)..a, gaussian x) +
        Real.sqrt Real.pi / 2 := by
  rw [private_gaussian_interval_reflect, private_gaussian_Ioi_zero]

theorem gap6 (a : ℝ) :
    F a =
      (∫ x in (0 : ℝ)..a, gaussian x) +
        Real.sqrt Real.pi / 2 := by
  calc
    F a = (∫ x in (-a)..0, gaussian x) +
        ∫ x in Set.Ioi (0 : ℝ), gaussian x := gap4 a
    _ = (∫ x in (0 : ℝ)..a, gaussian x) +
        Real.sqrt Real.pi / 2 := gap5 a

theorem gap7 :
    Continuous (fun a : ℝ => ∫ x in (0 : ℝ)..a, gaussian x) := by
  rw [continuous_iff_continuousAt]
  intro a
  exact
    (intervalIntegral.integral_hasDerivAt_right
      (private_continuous_gaussian.intervalIntegrable 0 a)
      private_continuous_gaussian.stronglyMeasurable.stronglyMeasurableAtFilter
      private_continuous_gaussian.continuousAt).continuousAt

theorem gap8 :
    Continuous F := by
  have hcont : Continuous
      (fun a : ℝ => (∫ x in (0 : ℝ)..a, gaussian x) +
        Real.sqrt Real.pi / 2) :=
    gap7.add continuous_const
  exact hcont.congr (fun a => (gap6 a).symm)

theorem gap9 :
    Continuous F := by
  exact gap8

end

end ProofGap.Exercise3777
