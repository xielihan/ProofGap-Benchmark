import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3217

noncomputable section

def u (x y : ℝ) : ℝ :=
  x * Real.sin (x + y)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def secondXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def secondYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

theorem gap1 :
    ∀ x y : ℝ,
      partialX u x y =
        Real.sin (x + y) + x * Real.cos (x + y) := by
  intro x y
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (t + y))
        (Real.cos (x + y)) x := by
    simpa using
      (Real.hasDerivAt_sin (x + y)).comp x
        ((hasDerivAt_id x).add (hasDerivAt_const x y))
  have h := (hasDerivAt_id x).mul hsin
  simpa [partialX, u] using h.deriv

theorem gap2 :
    ∀ x y : ℝ,
      partialY u x y = x * Real.cos (x + y) := by
  intro x y
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (x + t))
        (Real.cos (x + y)) y := by
    simpa using
      (Real.hasDerivAt_sin (x + y)).comp y
        ((hasDerivAt_const y x).add (hasDerivAt_id y))
  have h :
      HasDerivAt (fun t : ℝ => x * Real.sin (x + t))
        (x * Real.cos (x + y)) y := by
    convert (hasDerivAt_const y x).mul hsin using 1 <;> simp
  change deriv (fun t : ℝ => x * Real.sin (x + t)) y =
    x * Real.cos (x + y)
  exact h.deriv

theorem gap3 :
    ∀ x y : ℝ,
      secondXX u x y =
        Real.cos (x + y) + Real.cos (x + y) -
          x * Real.sin (x + y) := by
  intro x y
  unfold secondXX
  have hfun :
      (fun t : ℝ => partialX u t y) =
        (fun t : ℝ =>
          Real.sin (t + y) + t * Real.cos (t + y)) := by
    funext t
    exact gap1 t y
  rw [hfun]
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (t + y))
        (Real.cos (x + y)) x := by
    simpa using
      (Real.hasDerivAt_sin (x + y)).comp x
        ((hasDerivAt_id x).add (hasDerivAt_const x y))
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (t + y))
        (-Real.sin (x + y)) x := by
    simpa using
      (Real.hasDerivAt_cos (x + y)).comp x
        ((hasDerivAt_id x).add (hasDerivAt_const x y))
  have h :
      HasDerivAt
        (fun t : ℝ =>
          Real.sin (t + y) + t * Real.cos (t + y))
        (Real.cos (x + y) + Real.cos (x + y) -
          x * Real.sin (x + y)) x := by
    convert hsin.add ((hasDerivAt_id x).mul hcos) using 1 <;>
      simp [id] <;> ring
  exact h.deriv

theorem gap4 :
    ∀ x y : ℝ,
      Real.cos (x + y) + Real.cos (x + y) -
          x * Real.sin (x + y) =
        2 * Real.cos (x + y) - x * Real.sin (x + y) := by
  intro x y
  ring

theorem gap5 :
    ∀ x y : ℝ,
      secondXX u x y =
        2 * Real.cos (x + y) - x * Real.sin (x + y) := by
  intro x y
  calc
    secondXX u x y =
        Real.cos (x + y) + Real.cos (x + y) -
          x * Real.sin (x + y) := gap3 x y
    _ = 2 * Real.cos (x + y) - x * Real.sin (x + y) :=
      gap4 x y

theorem gap6 :
    ∀ x y : ℝ,
      secondYY u x y = -x * Real.sin (x + y) := by
  intro x y
  unfold secondYY
  have hfun :
      (fun t : ℝ => partialY u x t) =
        (fun t : ℝ => x * Real.cos (x + t)) := by
    funext t
    exact gap2 x t
  rw [hfun]
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (x + t))
        (-Real.sin (x + y)) y := by
    simpa using
      (Real.hasDerivAt_cos (x + y)).comp y
        ((hasDerivAt_const y x).add (hasDerivAt_id y))
  have h :
      HasDerivAt (fun t : ℝ => x * Real.cos (x + t))
        (-x * Real.sin (x + y)) y := by
    convert (hasDerivAt_const y x).mul hcos using 1 <;> ring
  exact h.deriv

theorem gap7 :
    ∀ x y : ℝ,
      mixedXY u x y =
        Real.cos (x + y) - x * Real.sin (x + y) := by
  intro x y
  unfold mixedXY
  have hfun :
      (fun t : ℝ => partialX u x t) =
        (fun t : ℝ =>
          Real.sin (x + t) + x * Real.cos (x + t)) := by
    funext t
    exact gap1 x t
  rw [hfun]
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (x + t))
        (Real.cos (x + y)) y := by
    simpa using
      (Real.hasDerivAt_sin (x + y)).comp y
        ((hasDerivAt_const y x).add (hasDerivAt_id y))
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (x + t))
        (-Real.sin (x + y)) y := by
    simpa using
      (Real.hasDerivAt_cos (x + y)).comp y
        ((hasDerivAt_const y x).add (hasDerivAt_id y))
  have h :
      HasDerivAt
        (fun t : ℝ =>
          Real.sin (x + t) + x * Real.cos (x + t))
        (Real.cos (x + y) - x * Real.sin (x + y)) y := by
    convert hsin.add ((hasDerivAt_const y x).mul hcos) using 1 <;> ring
  exact h.deriv

end

end ProofGap.Exercise3217
