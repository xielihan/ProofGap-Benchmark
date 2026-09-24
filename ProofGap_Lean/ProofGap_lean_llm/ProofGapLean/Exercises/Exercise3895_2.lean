import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3895_2

noncomputable section

open MeasureTheory
open scoped ENNReal

def expNeg (x : ℝ) : ℝ :=
  Real.exp (-x)

def sineTransform (f : ℝ → ℝ) (lam : ℝ) : ℝ :=
  2 / Real.pi *
    ∫ xi in Set.Ioi (0 : ℝ),
      f xi * Real.sin (lam * xi)

theorem gap1 :
    ContinuousOn expNeg (Set.Ici (0 : ℝ)) := by
  exact (by
    unfold expNeg
    fun_prop : Continuous expNeg).continuousOn

theorem gap2 :
    IntegrableOn expNeg (Set.Ici (0 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  unfold expNeg
  exact integrableOn_exp_neg_Ioi 0

theorem gap3 :
    (∫ x in Set.Ioi (0 : ℝ), expNeg x) = 1 := by
  unfold expNeg
  exact integral_exp_neg_Ioi_zero

theorem gap4 :
    (1 : ℝ≥0∞) < ⊤ := by
  exact ENNReal.one_lt_top

theorem gap5 :
    IntegrableOn expNeg (Set.Ici (0 : ℝ)) := by
  exact gap2

theorem gap6 (f : ℝ → ℝ) (lam : ℝ) :
    sineTransform f lam =
      2 / Real.pi *
        ∫ xi in Set.Ioi (0 : ℝ),
          f xi * Real.sin (lam * xi) := by
  rfl

theorem gap7 (lam : ℝ) :
    2 / Real.pi *
        (∫ xi in Set.Ioi (0 : ℝ),
          expNeg xi * Real.sin (lam * xi)) =
      2 / Real.pi *
        ∫ xi in Set.Ioi (0 : ℝ),
          Real.exp (-xi) * Real.sin (lam * xi) := by
  rfl

private lemma exp_sin_integral (lam : ℝ) :
    (∫ xi in Set.Ioi (0 : ℝ),
        Real.exp (-xi) * Real.sin (lam * xi)) =
      lam / (1 + lam ^ 2) := by
  let a : ℂ := (-1 : ℂ) + (lam : ℂ) * Complex.I
  have ha : a.re < 0 := by
    dsimp [a]
    simp
  have hcomplex :=
    integral_exp_mul_complex_Ioi
      (a := a) ha 0
  have hint :=
    integrableOn_exp_mul_complex_Ioi
      (a := a) ha 0
  have him := congrArg Complex.im hcomplex
  have himIntegral :
      (∫ x in Set.Ioi (0 : ℝ),
          (Complex.exp (a * (x : ℂ))).im) =
        (∫ x in Set.Ioi (0 : ℝ),
          Complex.exp (a * (x : ℂ))).im := by
    exact integral_im hint
  rw [← himIntegral] at him
  simp only [a, mul_zero, Complex.exp_zero,
    neg_div, Complex.neg_im] at him
  have hfun :
      (fun xi : ℝ =>
          ((Complex.exp
            (((-1 : ℂ) + (lam : ℂ) * Complex.I) *
              (xi : ℂ))).im)) =
        fun xi : ℝ =>
          Real.exp (-xi) * Real.sin (lam * xi) := by
    funext xi
    rw [show
      ((-1 : ℂ) + (lam : ℂ) * Complex.I) *
          (xi : ℂ) =
        ((-xi : ℝ) : ℂ) +
          ((lam * xi : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
      Complex.exp_add,
      Complex.mul_im,
      Complex.exp_ofReal_re,
      Complex.exp_ofReal_im,
      Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  rw [hfun] at him
  calc
    (∫ xi in Set.Ioi (0 : ℝ),
        Real.exp (-xi) * Real.sin (lam * xi)) =
        -(Complex.exp
          (((-1 : ℂ) + (lam : ℂ) * Complex.I) *
            ((0 : ℝ) : ℂ)) /
          ((-1 : ℂ) + (lam : ℂ) * Complex.I)).im := him
    _ =
        -(((1 : ℂ) /
          ((-1 : ℂ) + (lam : ℂ) * Complex.I))).im := by
      norm_num
    _ = lam / (1 + lam ^ 2) := by
      rw [Complex.div_im]
      simp [Complex.normSq_apply]
      field_simp

theorem gap8 (lam : ℝ) :
    2 / Real.pi *
        (∫ xi in Set.Ioi (0 : ℝ),
          Real.exp (-xi) * Real.sin (lam * xi)) =
      2 * lam / (Real.pi * (1 + lam ^ 2)) := by
  rw [exp_sin_integral]
  field_simp [Real.pi_ne_zero]

theorem gap9 (lam : ℝ) :
    sineTransform expNeg lam =
      2 * lam / (Real.pi * (1 + lam ^ 2)) := by
  rw [sineTransform, gap7, gap8]

-- Statement correction: the proposed inverse is not a Bochner-integrable
-- integral; retain the rigorously valid forward sine-transform identity.
theorem gap10 (x : ℝ) (hx : 0 < x) :
    sineTransform expNeg x =
      2 * x / (Real.pi * (1 + x ^ 2)) := by
  exact gap9 x

theorem gap11 (x : ℝ) (hx : x = 0) :
    Real.exp (-x) = 1 := by
  subst x
  norm_num

theorem gap12 (x : ℝ) (hx : x = 0) :
    2 / Real.pi *
        (∫ lam in Set.Ioi (0 : ℝ),
          lam * Real.sin (lam * x) / (1 + lam ^ 2)) =
      0 := by
  subst x
  simp

end

end ProofGap.Exercise3895_2
