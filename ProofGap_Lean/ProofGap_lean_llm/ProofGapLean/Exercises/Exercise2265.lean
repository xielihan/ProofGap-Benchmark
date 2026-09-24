import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2265

noncomputable section

def I (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, f x

theorem gap1 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ a, I f a (a + T) = I f a 0 + I f 0 T + I f T (a + T) := by
  intro a
  unfold I
  have hsplit₁ :
      (∫ x in a..0, f x) + ∫ x in 0..T, f x = ∫ x in a..T, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hsplit₂ :
      (∫ x in a..T, f x) + ∫ x in T..a + T, f x =
        ∫ x in a..a + T, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  calc
    (∫ x in a..a + T, f x) =
        (∫ x in a..T, f x) + ∫ x in T..a + T, f x := hsplit₂.symm
    _ = ((∫ x in a..0, f x) + ∫ x in 0..T, f x) +
          ∫ x in T..a + T, f x :=
      congrArg (fun z : ℝ => z + ∫ x in T..a + T, f x) hsplit₁.symm

theorem gap2 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f) :
    ∀ a, I f T (a + T) = ∫ t in 0..a, f (t + T) := by
  intro a
  unfold I
  rw [intervalIntegral.integral_comp_add_right]
  simp

theorem gap3 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ a, (∫ t in 0..a, f (t + T)) = I f 0 a := by
  intro a
  unfold I
  apply intervalIntegral.integral_congr
  intro t ht
  exact hper t

theorem gap4 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ a, I f T (a + T) = I f 0 a := by
  intro a
  rw [gap2 f T hf a]
  exact gap3 f T hf hper a

theorem gap5 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ a, I f a (a + T) = I f a 0 + I f 0 T + I f 0 a := by
  intro a
  rw [gap1 f T hf hper a]
  rw [gap4 f T hf hper a]

theorem gap6 (f : ℝ → ℝ) (T a : ℝ) (hf : Continuous f) :
    I f a 0 + I f 0 T + I f 0 a = I f 0 T := by
  unfold I
  rw [intervalIntegral.integral_symm]
  ring

theorem gap7 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ a, I f a (a + T) = I f 0 T := by
  intro a
  rw [gap5 f T hf hper a]
  exact gap6 f T a hf

theorem gap8 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ a, I f a (a + T) = I f 0 T := by
  exact gap7 f T hf hper

end

end ProofGap.Exercise2265
