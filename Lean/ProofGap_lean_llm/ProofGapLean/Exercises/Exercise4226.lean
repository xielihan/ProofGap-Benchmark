import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4226

noncomputable section

open scoped Interval

def radialSide (a θ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 = θ ∧ 0 ≤ p.1 ∧ p.1 ≤ a}

def circularArc (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 = a ∧ 0 ≤ p.2 ∧ p.2 ≤ Real.pi / 4}

def boundary (a : ℝ) : Set (ℝ × ℝ) :=
  radialSide a 0 ∪ circularArc a ∪ radialSide a (Real.pi / 4)

def radialSpeed : ℝ :=
  1

def polarSpeed (r r' : ℝ) : ℝ :=
  Real.sqrt (r ^ 2 + r' ^ 2)

def arcSpeed (a : ℝ) : ℝ :=
  polarSpeed a 0

def weightedLength (a : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..a, Real.exp r) +
    (∫ φ in (0 : ℝ)..Real.pi / 4, Real.exp a * a) +
      ∫ r in (0 : ℝ)..a, Real.exp r

theorem gap1 :
    radialSpeed = 1 := by
  rfl

theorem gap2 (a : ℝ) :
    arcSpeed a = Real.sqrt (a ^ 2 + 0 ^ 2) := by
  rfl

theorem gap3 (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a ^ 2 + 0 ^ 2) = a := by
  simpa [abs_of_nonneg ha] using (Real.sqrt_sq_eq_abs a)

theorem gap4 (a : ℝ) (ha : 0 ≤ a) :
    arcSpeed a = a := by
  change Real.sqrt (a ^ 2 + 0 ^ 2) = a
  exact gap3 a ha

theorem gap5 :
    radialSpeed = 1 := by
  rfl

theorem gap6 (a : ℝ) (ha : 0 ≤ a) :
    weightedLength a =
      (∫ r in (0 : ℝ)..a, Real.exp r) +
        (∫ φ in (0 : ℝ)..Real.pi / 4, Real.exp a * a) +
          ∫ r in (0 : ℝ)..a, Real.exp r := by
  rfl

theorem gap7 (a : ℝ) (ha : 0 ≤ a) :
    (∫ r in (0 : ℝ)..a, Real.exp r) +
          (∫ φ in (0 : ℝ)..Real.pi / 4, Real.exp a * a) +
            ∫ r in (0 : ℝ)..a, Real.exp r =
      2 * (Real.exp a - 1) + Real.pi * a * Real.exp a / 4 := by
  have hexp_raw :
      (∫ r in (0 : ℝ)..a, Real.exp r) =
        Real.exp a - Real.exp 0 := by
    apply intervalIntegral.integral_deriv_eq_sub' Real.exp
    · funext x
      exact (Real.hasDerivAt_exp x).deriv
    · intro x hx
      exact (Real.hasDerivAt_exp x).differentiableAt
    · exact Real.continuous_exp.continuousOn
  have hexp :
      (∫ r in (0 : ℝ)..a, Real.exp r) = Real.exp a - 1 := by
    simpa only [Real.exp_zero] using hexp_raw
  simp only [hexp, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem gap8 (a : ℝ) (ha : 0 ≤ a) :
    weightedLength a =
      2 * (Real.exp a - 1) + Real.pi * a * Real.exp a / 4 := by
  exact (gap6 a ha).trans (gap7 a ha)

end

end ProofGap.Exercise4226
