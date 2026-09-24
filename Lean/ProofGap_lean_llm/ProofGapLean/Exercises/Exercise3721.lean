import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3721

noncomputable section

open scoped Interval

def doubleAverage (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / h ^ 2) *
    ∫ ξ in (0 : ℝ)..h, ∫ η in (0 : ℝ)..h, f (x + ξ + η)

def shiftedAverage (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / h ^ 2) *
    ∫ ξ in (0 : ℝ)..h, ∫ u in x + ξ..x + ξ + h, f u

def firstDerivativeIntegral (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / h ^ 2) *
    ∫ ξ in (0 : ℝ)..h, (f (x + ξ + h) - f (x + ξ))

def firstDerivativeShifted (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / h ^ 2) *
    ((∫ u in x + h..x + 2 * h, f u) - ∫ u in x..x + h, f u)

def secondDifference (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f (x + 2 * h) - 2 * f (x + h) + f x) / h ^ 2

private def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, f u

private lemma primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x := by
  have hmeas :
      StronglyMeasurableAtFilter f (nhds x) MeasureTheory.volume :=
    hf.stronglyMeasurable.stronglyMeasurableAtFilter
  simpa [primitive] using
    (intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable (0 : ℝ) x) hmeas hf.continuousAt)

private lemma primitive_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (primitive f) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (primitive_hasDerivAt hf x).continuousAt

private lemma integral_eq_primitive_sub {f : ℝ → ℝ} (hf : Continuous f)
    (a b : ℝ) :
    (∫ u in a..b, f u) = primitive f b - primitive f a := by
  unfold primitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (0 : ℝ) a) (hf.intervalIntegrable a b)]
  ring_nf

private lemma integral_translate {f : ℝ → ℝ} (hf : Continuous f)
    (c a b : ℝ) :
    (∫ t in a..b, f (c + t)) = primitive f (c + b) - primitive f (c + a) := by
  calc
    (∫ t in a..b, f (c + t)) = ∫ t in a + c..b + c, f t := by
      simpa only [add_comm] using
        (intervalIntegral.integral_comp_add_right
          (f := f) (a := a) (b := b) (d := c))
    _ = primitive f (c + b) - primitive f (c + a) := by
      rw [integral_eq_primitive_sub hf]
      simp only [add_comm]

private lemma firstDerivativeIntegral_formula (h : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (x : ℝ) :
    firstDerivativeIntegral h f x =
      (1 / h ^ 2) *
        (primitive f (x + 2 * h) - 2 * primitive f (x + h) + primitive f x) := by
  unfold firstDerivativeIntegral
  apply congrArg (fun z : ℝ => (1 / h ^ 2) * z)
  have h₁ : Continuous (fun ξ : ℝ => f ((x + h) + ξ)) :=
    hf.comp (continuous_const.add continuous_id)
  have h₂ : Continuous (fun ξ : ℝ => f (x + ξ)) :=
    hf.comp (continuous_const.add continuous_id)
  calc
    (∫ ξ in (0 : ℝ)..h, (f (x + ξ + h) - f (x + ξ))) =
        ∫ ξ in (0 : ℝ)..h, (f ((x + h) + ξ) - f (x + ξ)) := by
          apply intervalIntegral.integral_congr
          intro ξ hξ
          change f (x + ξ + h) - f (x + ξ) =
            f ((x + h) + ξ) - f (x + ξ)
          congr 1
          ring_nf
    _ = (∫ ξ in (0 : ℝ)..h, f ((x + h) + ξ)) -
          ∫ ξ in (0 : ℝ)..h, f (x + ξ) :=
      intervalIntegral.integral_sub
        (h₁.intervalIntegrable (0 : ℝ) h)
        (h₂.intervalIntegrable (0 : ℝ) h)
    _ = primitive f (x + 2 * h) - 2 * primitive f (x + h) + primitive f x := by
      rw [integral_translate hf (x + h) (0 : ℝ) h,
        integral_translate hf x (0 : ℝ) h]
      ring_nf

private lemma doubleAverage_formula (h : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (x : ℝ) :
    doubleAverage h f x =
      (1 / h ^ 2) *
        (primitive (primitive f) (x + 2 * h) -
          2 * primitive (primitive f) (x + h) + primitive (primitive f) x) := by
  have hP : Continuous (primitive f) := primitive_continuous hf
  calc
    doubleAverage h f x = firstDerivativeIntegral h (primitive f) x := by
      unfold doubleAverage firstDerivativeIntegral
      apply congrArg (fun z : ℝ => (1 / h ^ 2) * z)
      apply intervalIntegral.integral_congr
      intro ξ hξ
      simpa [add_assoc] using
        (integral_translate hf (x + ξ) (0 : ℝ) h)
    _ = (1 / h ^ 2) *
        (primitive (primitive f) (x + 2 * h) -
          2 * primitive (primitive f) (x + h) + primitive (primitive f) x) :=
      firstDerivativeIntegral_formula h (primitive f) hP x

private lemma firstDerivativeShifted_formula (h : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (x : ℝ) :
    firstDerivativeShifted h f x =
      (1 / h ^ 2) *
        (primitive f (x + 2 * h) - 2 * primitive f (x + h) + primitive f x) := by
  unfold firstDerivativeShifted
  rw [integral_eq_primitive_sub hf (x + h) (x + 2 * h),
    integral_eq_primitive_sub hf x (x + h)]
  ring_nf

theorem gap1 (h : ℝ) (f : ℝ → ℝ) (hh : 0 < h)
    (hf : Continuous f) :
    ∀ x : ℝ, doubleAverage h f x = shiftedAverage h f x := by
  intro x
  unfold doubleAverage shiftedAverage
  apply congrArg (fun z : ℝ => (1 / h ^ 2) * z)
  apply intervalIntegral.integral_congr
  intro ξ hξ
  calc
    (∫ η in (0 : ℝ)..h, f (x + ξ + η)) =
        primitive f (x + ξ + h) - primitive f (x + ξ) := by
          simpa [add_assoc] using
            (integral_translate hf (x + ξ) (0 : ℝ) h)
    _ = ∫ u in x + ξ..x + ξ + h, f u := by
          symm
          exact integral_eq_primitive_sub hf (x + ξ) (x + ξ + h)

theorem gap2 (h : ℝ) (f : ℝ → ℝ) (hh : 0 < h)
    (hf : Continuous f) :
    ∀ x : ℝ,
      deriv (doubleAverage h f) x = firstDerivativeIntegral h f x := by
  intro x
  have hP : Continuous (primitive f) := primitive_continuous hf
  have heq :
      doubleAverage h f =
        fun y => (1 / h ^ 2) *
          (primitive (primitive f) (y + 2 * h) -
            2 * primitive (primitive f) (y + h) +
            primitive (primitive f) y) := by
    funext y
    exact doubleAverage_formula h f hf y
  have hA :
      HasDerivAt
        (fun y : ℝ => primitive (primitive f) (y + 2 * h))
        (primitive f (x + 2 * h)) x := by
    have hi : HasDerivAt (fun y : ℝ => y + 2 * h) 1 x :=
      (hasDerivAt_id x).add_const (2 * h)
    simpa only [Function.comp_def, mul_one] using
      (HasDerivAt.comp x (primitive_hasDerivAt hP (x + 2 * h)) hi)
  have hB :
      HasDerivAt
        (fun y : ℝ => primitive (primitive f) (y + h))
        (primitive f (x + h)) x := by
    have hi : HasDerivAt (fun y : ℝ => y + h) 1 x :=
      (hasDerivAt_id x).add_const h
    simpa only [Function.comp_def, mul_one] using
      (HasDerivAt.comp x (primitive_hasDerivAt hP (x + h)) hi)
  have hC :
      HasDerivAt (primitive (primitive f)) (primitive f x) x :=
    primitive_hasDerivAt hP x
  have hd :=
    ((hA.sub (hB.const_mul 2)).add hC).const_mul (1 / h ^ 2)
  rw [heq, firstDerivativeIntegral_formula h f hf x]
  convert hd.deriv using 1 <;> ring_nf

theorem gap3 (h : ℝ) (f : ℝ → ℝ) (hh : 0 < h)
    (hf : Continuous f) :
    ∀ x : ℝ,
      deriv (doubleAverage h f) x = firstDerivativeShifted h f x := by
  intro x
  calc
    deriv (doubleAverage h f) x = firstDerivativeIntegral h f x :=
      gap2 h f hh hf x
    _ = (1 / h ^ 2) *
        (primitive f (x + 2 * h) - 2 * primitive f (x + h) + primitive f x) :=
      firstDerivativeIntegral_formula h f hf x
    _ = firstDerivativeShifted h f x := by
      symm
      exact firstDerivativeShifted_formula h f hf x

theorem gap4 (h : ℝ) (f : ℝ → ℝ) (hh : 0 < h)
    (hf : Continuous f) :
    ∀ x : ℝ,
      deriv (deriv (doubleAverage h f)) x =
        (1 / h ^ 2) *
          (f (x + 2 * h) - f (x + h) - f (x + h) + f x) := by
  intro x
  have hderiv :
      deriv (doubleAverage h f) = firstDerivativeIntegral h f := by
    funext y
    exact gap2 h f hh hf y
  have hform :
      firstDerivativeIntegral h f =
        fun y => (1 / h ^ 2) *
          (primitive f (y + 2 * h) -
            2 * primitive f (y + h) + primitive f y) := by
    funext y
    exact firstDerivativeIntegral_formula h f hf y
  have hA :
      HasDerivAt (fun y : ℝ => primitive f (y + 2 * h))
        (f (x + 2 * h)) x := by
    have hi : HasDerivAt (fun y : ℝ => y + 2 * h) 1 x :=
      (hasDerivAt_id x).add_const (2 * h)
    simpa only [Function.comp_def, mul_one] using
      (HasDerivAt.comp x (primitive_hasDerivAt hf (x + 2 * h)) hi)
  have hB :
      HasDerivAt (fun y : ℝ => primitive f (y + h))
        (f (x + h)) x := by
    have hi : HasDerivAt (fun y : ℝ => y + h) 1 x :=
      (hasDerivAt_id x).add_const h
    simpa only [Function.comp_def, mul_one] using
      (HasDerivAt.comp x (primitive_hasDerivAt hf (x + h)) hi)
  have hC : HasDerivAt (primitive f) (f x) x :=
    primitive_hasDerivAt hf x
  have hd :=
    ((hA.sub (hB.const_mul 2)).add hC).const_mul (1 / h ^ 2)
  rw [hderiv, hform]
  convert hd.deriv using 1 <;> ring_nf

theorem gap5 (h : ℝ) (f : ℝ → ℝ) (hh : 0 < h)
    (hf : Continuous f) :
    ∀ x : ℝ,
      deriv (deriv (doubleAverage h f)) x = secondDifference h f x := by
  intro x
  rw [gap4 h f hh hf x]
  unfold secondDifference
  ring_nf

end

end ProofGap.Exercise3721
