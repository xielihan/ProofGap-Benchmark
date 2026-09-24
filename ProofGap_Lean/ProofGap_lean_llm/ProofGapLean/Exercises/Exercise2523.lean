import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2523

noncomputable section

def inertiaDensity (R δ z : ℝ) : ℝ :=
  1 / 2 * Real.pi * δ * (R ^ 2 - z ^ 2) ^ 2
def axialInertia (R δ : ℝ) : ℝ :=
  ∫ z in -R..R, inertiaDensity R δ z

private def inertiaPrimitive (R δ z : ℝ) : ℝ :=
  (1 / 2 * Real.pi * δ) *
    (R ^ 4 * z - (2 / 3) * R ^ 2 * z ^ 3 + (1 / 5) * z ^ 5)

private theorem inertiaPrimitive_hasDerivAt (R δ z : ℝ) :
    HasDerivAt (inertiaPrimitive R δ) (inertiaDensity R δ z) z := by
  have h1 := (hasDerivAt_id z).const_mul (R ^ 4)
  have h3 := ((hasDerivAt_id z).fun_pow 3).const_mul
    ((2 / 3 : ℝ) * R ^ 2)
  have h5 := ((hasDerivAt_id z).fun_pow 5).const_mul (1 / 5 : ℝ)
  have hpoly : HasDerivAt
      (fun y : ℝ => R ^ 4 * y - (2 / 3) * R ^ 2 * y ^ 3 +
        (1 / 5) * y ^ 5)
      ((R ^ 2 - z ^ 2) ^ 2) z := by
    convert (h1.sub h3).add h5 using 1 <;> simp [id] <;> ring
  unfold inertiaPrimitive inertiaDensity
  exact hpoly.const_mul (1 / 2 * Real.pi * δ)

theorem gap1 (R δ z : ℝ) :
    inertiaDensity R δ z =
      1 / 2 * Real.pi * (R ^ 2 - z ^ 2) * δ *
        (R ^ 2 - z ^ 2) := by
  unfold inertiaDensity
  ring

theorem gap2 (R δ z : ℝ) :
    1 / 2 * Real.pi * (R ^ 2 - z ^ 2) * δ *
        (R ^ 2 - z ^ 2) =
      1 / 2 * Real.pi * δ * (R ^ 2 - z ^ 2) ^ 2 := by
  ring

theorem gap3 (R δ z : ℝ) :
    inertiaDensity R δ z =
      1 / 2 * Real.pi * δ * (R ^ 2 - z ^ 2) ^ 2 := by
  rfl

theorem gap4 (R δ Jz : ℝ) (hJz : Jz = axialInertia R δ) :
    Jz = ∫ z in -R..R,
      1 / 2 * Real.pi * δ * (R ^ 2 - z ^ 2) ^ 2 := by
  simpa [axialInertia, inertiaDensity] using hJz

theorem gap5 (R δ : ℝ) :
    (∫ z in -R..R,
      1 / 2 * Real.pi * δ * (R ^ 2 - z ^ 2) ^ 2) =
        8 / 15 * Real.pi * δ * R ^ 5 := by
  have hint : IntervalIntegrable (inertiaDensity R δ) MeasureTheory.volume (-R) R :=
    (by unfold inertiaDensity; fun_prop : Continuous (inertiaDensity R δ)).intervalIntegrable _ _
  calc
    (∫ z in -R..R,
      1 / 2 * Real.pi * δ * (R ^ 2 - z ^ 2) ^ 2) =
        inertiaPrimitive R δ R - inertiaPrimitive R δ (-R) := by
          simpa [inertiaDensity] using
            (intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun z _ => inertiaPrimitive_hasDerivAt R δ z) hint)
    _ = 8 / 15 * Real.pi * δ * R ^ 5 := by
      unfold inertiaPrimitive
      ring

theorem gap6 (R δ Jz : ℝ) (hJz : Jz = axialInertia R δ) :
    Jz = 8 / 15 * Real.pi * δ * R ^ 5 := by
  rw [hJz]
  simpa [axialInertia, inertiaDensity] using gap5 R δ

theorem gap7 (J ω E : ℝ) (hE : E = 1 / 2 * J * ω ^ 2) :
    E = 1 / 2 * J * ω ^ 2 := by
  exact hE

theorem gap8 (R δ J Jz ω : ℝ)
    (hJ : J = Jz)
    (hJz : Jz = 8 / 15 * Real.pi * δ * R ^ 5) :
    1 / 2 * J * ω ^ 2 =
      4 / 15 * Real.pi * δ * ω ^ 2 * R ^ 5 := by
  rw [hJ, hJz]
  ring

theorem gap9 (R δ J Jz ω E : ℝ)
    (hJ : J = Jz)
    (hJz : Jz = 8 / 15 * Real.pi * δ * R ^ 5)
    (hE : E = 1 / 2 * J * ω ^ 2) :
    E = 4 / 15 * Real.pi * δ * ω ^ 2 * R ^ 5 := by
  rw [hE]
  exact gap8 R δ J Jz ω hJ hJz

end

end ProofGap.Exercise2523
