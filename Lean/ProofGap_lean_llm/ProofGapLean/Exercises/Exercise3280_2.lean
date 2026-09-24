import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3280_2

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def radialOperator (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * partialX f x y + y * partialY f x y

def u (x y : ℝ) : ℝ :=
  Real.log (Real.sqrt (x ^ 2 + y ^ 2))

private theorem partialX_logRadius (x y : ℝ)
    (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialX u x y = x / (x ^ 2 + y ^ 2) := by
  unfold partialX
  have hs0 : 0 ≤ x ^ 2 + y ^ 2 := by
    positivity
  have hspos : 0 < x ^ 2 + y ^ 2 :=
    lt_of_le_of_ne hs0 (Ne.symm hr)
  have hsqrt : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hspos)
  have hpoly :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (((hasDerivAt_id x).pow 2).add_const (y ^ 2))
  have hcomp :=
    (Real.hasDerivAt_log hsqrt).comp x
      ((Real.hasDerivAt_sqrt hr).comp x hpoly)
  change HasDerivAt (fun t : ℝ => u t y) _ x at hcomp
  have hcoef :
      (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ *
          (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * x)) =
        x / (x ^ 2 + y ^ 2) := by
    calc
      (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ *
            (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * x)) =
          x / (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 := by
            field_simp [hsqrt] <;> ring
      _ = x / (x ^ 2 + y ^ 2) := by
        rw [Real.sq_sqrt hs0]
  rw [hcoef] at hcomp
  exact hcomp.deriv

theorem gap1 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialX u x y = x / (x ^ 2 + y ^ 2) := by
  exact partialX_logRadius x y hr

theorem gap2 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    partialY u x y = y / (x ^ 2 + y ^ 2) := by
  have hr' : y ^ 2 + x ^ 2 ≠ 0 := by
    simpa [add_comm] using hr
  simpa [partialX, partialY, u, add_comm] using
    (partialX_logRadius y x hr')

theorem gap3 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator u x y =
      x ^ 2 / (x ^ 2 + y ^ 2) +
        y ^ 2 / (x ^ 2 + y ^ 2) := by
  simp only [radialOperator, gap1 x y hr, gap2 x y hr]
  ring

theorem gap4 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    x ^ 2 / (x ^ 2 + y ^ 2) +
        y ^ 2 / (x ^ 2 + y ^ 2) = 1 := by
  field_simp [hr]

theorem gap5 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator u x y = 1 := by
  calc
    radialOperator u x y =
        x ^ 2 / (x ^ 2 + y ^ 2) +
          y ^ 2 / (x ^ 2 + y ^ 2) := gap3 x y hr
    _ = 1 := gap4 x y hr

theorem gap6 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator (fun a b => radialOperator u a b) x y =
      radialOperator (fun _ _ => (1 : ℝ)) x y := by
  change
    x * partialX (fun a b => radialOperator u a b) x y +
        y * partialY (fun a b => radialOperator u a b) x y =
      x * partialX (fun _ _ => (1 : ℝ)) x y +
        y * partialY (fun _ _ => (1 : ℝ)) x y
  have hxterm :
      x * partialX (fun a b => radialOperator u a b) x y =
        x * partialX (fun _ _ => (1 : ℝ)) x y := by
    by_cases hx : x = 0
    · simp [hx]
    · have heq :
          (fun t : ℝ => radialOperator u t y) =ᶠ[nhds x]
            (fun _ : ℝ => (1 : ℝ)) :=
        (eventually_ne_nhds hx).mono (by
          intro t ht
          have ht2 : 0 < t ^ 2 := by
            rw [pow_two]
            exact mul_self_pos.mpr ht
          have hsumpos : 0 < t ^ 2 + y ^ 2 := by
            nlinarith [sq_nonneg y]
          exact gap5 t y (ne_of_gt hsumpos))
      apply congrArg (fun z : ℝ => x * z)
      simpa [partialX] using heq.deriv_eq
  have hyterm :
      y * partialY (fun a b => radialOperator u a b) x y =
        y * partialY (fun _ _ => (1 : ℝ)) x y := by
    by_cases hy : y = 0
    · simp [hy]
    · have heq :
          (fun t : ℝ => radialOperator u x t) =ᶠ[nhds y]
            (fun _ : ℝ => (1 : ℝ)) :=
        (eventually_ne_nhds hy).mono (by
          intro t ht
          have ht2 : 0 < t ^ 2 := by
            rw [pow_two]
            exact mul_self_pos.mpr ht
          have hsumpos : 0 < x ^ 2 + t ^ 2 := by
            nlinarith [sq_nonneg x]
          exact gap5 x t (ne_of_gt hsumpos))
      apply congrArg (fun z : ℝ => y * z)
      simpa [partialY] using heq.deriv_eq
  exact congrArg₂ (fun a b : ℝ => a + b) hxterm hyterm

theorem gap7 (x y : ℝ) :
    radialOperator (fun _ _ => (1 : ℝ)) x y = 0 := by
  simp [radialOperator, partialX, partialY]

theorem gap8 (x y : ℝ) (hr : x ^ 2 + y ^ 2 ≠ 0) :
    radialOperator (fun a b => radialOperator u a b) x y = 0 := by
  calc
    radialOperator (fun a b => radialOperator u a b) x y =
        radialOperator (fun _ _ => (1 : ℝ)) x y := gap6 x y hr
    _ = 0 := gap7 x y

end

end ProofGap.Exercise3280_2
