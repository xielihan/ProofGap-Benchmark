import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

open scoped Interval

namespace ProofGap.Exercise2256

noncomputable section

def fixedBounds (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ y in a..b, f (x + y)

def movingBounds (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ y in a + x..b + x, f y

def shift (x y : ℝ) : ℝ := x + y
def shiftJacobian : ℝ := 1

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) (a b x : ℝ) :
    deriv (fixedBounds f a b) x =
      deriv (movingBounds f a b) x := by
  have hfun : fixedBounds f a b = movingBounds f a b := by
    funext z
    change (∫ y in a..b, f (z + y)) = ∫ y in a + z..b + z, f y
    calc
      (∫ y in a..b, f (z + y)) = ∫ y in a..b, f (y + z) := by
        apply intervalIntegral.integral_congr
        intro y
        simp [add_comm]
      _ = ∫ y in a + z..b + z, f y := by
        rw [intervalIntegral.integral_comp_add_right]
  rw [hfun]

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) (a b x : ℝ) :
    deriv (movingBounds f a b) x =
      f (b + x) - f (a + x) := by
  let F : ℝ → ℝ := fun t => ∫ y in (0 : ℝ)..t, f y
  have hF (t : ℝ) : HasDerivAt F (f t) t := by
    dsimp [F]
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hf.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) t
    · exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
    · exact hf.continuousAt
  have hfun : movingBounds f a b =
      (fun z => F (b + z) - F (a + z)) := by
    funext z
    dsimp [movingBounds, F]
    have hadd :
        (∫ y in (0 : ℝ)..a + z, f y) +
            (∫ y in a + z..b + z, f y) =
          ∫ y in (0 : ℝ)..b + z, f y := by
      apply intervalIntegral.integral_add_adjacent_intervals
      · exact hf.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) (a + z)
      · exact hf.intervalIntegrable (μ := MeasureTheory.volume) (a + z) (b + z)
    linarith
  have hbshift : HasDerivAt (fun z : ℝ => b + z) 1 x := by
    simpa using
      (hasDerivAt_const (x := x) (c := b)).add (hasDerivAt_id x)
  have hashift : HasDerivAt (fun z : ℝ => a + z) 1 x := by
    simpa using
      (hasDerivAt_const (x := x) (c := a)).add (hasDerivAt_id x)
  have hbF : HasDerivAt (fun z => F (b + z)) (f (b + x)) x := by
    simpa using (hF (b + x)).comp x hbshift
  have haF : HasDerivAt (fun z => F (a + z)) (f (a + x)) x := by
    simpa using (hF (a + x)).comp x hashift
  rw [hfun]
  exact (hbF.sub haF).deriv

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) (a b x : ℝ) :
    deriv (fixedBounds f a b) x =
      f (b + x) - f (a + x) := by
  calc
    deriv (fixedBounds f a b) x = deriv (movingBounds f a b) x :=
      gap1 f hf a b x
    _ = f (b + x) - f (a + x) := gap2 f hf a b x

end

end ProofGap.Exercise2256
