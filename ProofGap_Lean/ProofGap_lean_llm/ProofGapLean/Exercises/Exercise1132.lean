import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1132

noncomputable section

def y (x : ℝ) : ℝ := Real.log x / x

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def secondDifferential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  secondDeriv f x * dx ^ 2

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = (1 - Real.log x) / x ^ 2 := by
  have h :=
    (Real.hasDerivAt_log hx.ne').div (hasDerivAt_id x) hx.ne'
  change HasDerivAt (fun t : ℝ => Real.log t / t)
    ((x⁻¹ * x - Real.log x * 1) / x ^ 2) x at h
  unfold y
  rw [h.deriv]
  field_simp [hx.ne'] <;> ring

theorem gap2 (x : ℝ) (hx : 0 < x) :
    secondDeriv y x = (2 * Real.log x - 3) / x ^ 3 := by
  unfold secondDeriv
  have heq :
      (fun t => deriv y t) =ᶠ[nhds x]
        (((fun _ : ℝ => (1 : ℝ)) - Real.log) / id ^ 2) :=
    (eventually_gt_nhds hx).mono (fun t ht => by
      change deriv y t = (1 - Real.log t) / t ^ 2
      exact gap1 t ht)
  have hnum :=
    (hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_log hx.ne')
  have hden := (hasDerivAt_id x).pow 2
  have hquot := hnum.div hden (pow_ne_zero 2 hx.ne')
  have hsecond := hquot.congr_of_eventuallyEq heq
  rw [hsecond.deriv]
  dsimp [id]
  field_simp [hx.ne'] <;> ring

theorem gap3 (x dx : ℝ) (hx : 0 < x) :
    secondDifferential y x dx =
      ((2 * Real.log x - 3) / x ^ 3) * dx ^ 2 := by
  unfold secondDifferential
  rw [gap2 x hx]

end

end ProofGap.Exercise1132
