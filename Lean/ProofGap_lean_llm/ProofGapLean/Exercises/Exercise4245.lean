import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4245

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def xyArcMap (a φ : ℝ) : Vec3 :=
  (a * Real.cos φ, a * Real.sin φ, 0)

def xzArcMap (a ψ : ℝ) : Vec3 :=
  (a * Real.cos ψ, 0, a * Real.sin ψ)

def yzArcMap (a ψ : ℝ) : Vec3 :=
  (0, a * Real.cos ψ, a * Real.sin ψ)

def xyArc (a : ℝ) : Set Vec3 :=
  xyArcMap a '' Set.Icc 0 (Real.pi / 2)

def xzArc (a : ℝ) : Set Vec3 :=
  xzArcMap a '' Set.Icc 0 (Real.pi / 2)

def yzArc (a : ℝ) : Set Vec3 :=
  yzArcMap a '' Set.Icc 0 (Real.pi / 2)

def octantBoundary (a : ℝ) : Set Vec3 :=
  xyArc a ∪ xzArc a ∪ yzArc a

def totalLength (a : ℝ) : ℝ :=
  3 * (Real.pi * a / 2)

def xMoment (a : ℝ) : ℝ :=
  (∫ φ in (0 : ℝ)..Real.pi / 2, a * Real.cos φ * a) +
    ∫ ψ in (0 : ℝ)..Real.pi / 2, a * Real.cos ψ * a

def xCentroid (a : ℝ) : ℝ :=
  xMoment a / totalLength a

def yCentroid (a : ℝ) : ℝ :=
  xCentroid a

def zCentroid (a : ℝ) : ℝ :=
  xCentroid a

theorem gap1 (a : ℝ) :
    xyArc a =
      {p | ∃ φ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        p = (a * Real.cos φ, a * Real.sin φ, 0)} := by
  ext p
  simp [xyArc, xyArcMap, eq_comm]

theorem gap2 (a : ℝ) :
    xzArc a =
      {p | ∃ ψ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        p = (a * Real.cos ψ, 0, a * Real.sin ψ)} := by
  ext p
  simp [xzArc, xzArcMap, eq_comm]

theorem gap3 (a : ℝ) :
    yzArc a =
      {p | ∃ ψ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        p = (0, a * Real.cos ψ, a * Real.sin ψ)} := by
  ext p
  simp [yzArc, yzArcMap, eq_comm]

theorem gap4 (a : ℝ) (ha : 0 < a) :
    totalLength a = 3 * (Real.pi * a / 2) := by
  rfl

theorem gap5 (a : ℝ) :
    3 * (Real.pi * a / 2) = 3 * Real.pi * a / 2 := by
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    totalLength a = 3 * Real.pi * a / 2 := by
  simpa [totalLength] using gap5 a

theorem gap7 (a : ℝ) (ha : 0 < a) :
    xCentroid a =
      ((∫ φ in (0 : ℝ)..Real.pi / 2, a * Real.cos φ * a) +
        ∫ ψ in (0 : ℝ)..Real.pi / 2, a * Real.cos ψ * a) /
          (3 * Real.pi * a / 2) := by
  simp only [xCentroid, xMoment, gap6 a ha]

theorem gap8 (a : ℝ) :
    ((∫ φ in (0 : ℝ)..Real.pi / 2, a * Real.cos φ * a) +
          ∫ ψ in (0 : ℝ)..Real.pi / 2, a * Real.cos ψ * a) /
        (3 * Real.pi * a / 2) =
      2 * a ^ 2 / (3 * Real.pi * a / 2) := by
  have hcos :
      (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x) = 1 := by
    calc
      (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x) =
          Real.sin (Real.pi / 2) - Real.sin 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.sin)
        all_goals
          first
          | exact Real.continuous_cos.intervalIntegrable _ _
          | exact Real.continuous_cos.continuousOn
          | exact Real.continuous_sin.continuousOn
          | exact Real.continuous_cos
          | exact Real.continuous_sin
          | intro x hx
            exact Real.hasDerivAt_sin x
          | intro x hx
            exact (Real.hasDerivAt_sin x).hasDerivWithinAt
          | intro x
            exact Real.hasDerivAt_sin x
      _ = 1 := by norm_num
  have hint :
      (∫ x in (0 : ℝ)..Real.pi / 2, a * Real.cos x * a) = a ^ 2 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, hcos]
    ring
  simp only [hint]
  ring

theorem gap9 (a : ℝ) (ha : 0 < a) :
    2 * a ^ 2 / (3 * Real.pi * a / 2) =
      4 * a / (3 * Real.pi) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [ha0, hpi] <;> ring

theorem gap10 (a : ℝ) (ha : 0 < a) :
    xCentroid a = 4 * a / (3 * Real.pi) := by
  calc
    xCentroid a =
        ((∫ φ in (0 : ℝ)..Real.pi / 2, a * Real.cos φ * a) +
          ∫ ψ in (0 : ℝ)..Real.pi / 2, a * Real.cos ψ * a) /
            (3 * Real.pi * a / 2) := gap7 a ha
    _ = 2 * a ^ 2 / (3 * Real.pi * a / 2) := gap8 a
    _ = 4 * a / (3 * Real.pi) := gap9 a ha

theorem gap11 (a : ℝ) :
    xCentroid a = yCentroid a := by
  rfl

theorem gap12 (a : ℝ) :
    yCentroid a = zCentroid a := by
  rfl

theorem gap13 (a : ℝ) (ha : 0 < a) :
    zCentroid a = 4 * a / (3 * Real.pi) := by
  simpa [zCentroid] using gap10 a ha

theorem gap14 (a : ℝ) (ha : 0 < a) :
    xCentroid a = 4 * a / (3 * Real.pi) := by
  exact gap10 a ha

end

end ProofGap.Exercise4245
