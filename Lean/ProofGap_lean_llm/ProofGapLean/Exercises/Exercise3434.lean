import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3434

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def dydx (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 y t / d1 x t

def d2ydx2 (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  (d2 y t * d1 x t - d1 y t * d2 x t) / (d1 x t) ^ 3

theorem gap1 (x y : ℝ → ℝ) (t : ℝ)
    (hRegular : d1 x t ≠ 0) :
    dydx x y t = d1 y t / d1 x t := by
  rfl

theorem gap2 (x y : ℝ → ℝ) (t : ℝ)
    (hRegular : d1 x t ≠ 0) :
    d2ydx2 x y t =
      (d2 y t * d1 x t - d1 y t * d2 x t) / (d1 x t) ^ 3 := by
  rfl

theorem gap3 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.exp t) :
    ∀ t, d1 x t = Real.exp t := by
  intro t
  rw [show x = Real.exp from funext hParam]
  simpa [d1] using (Real.hasDerivAt_exp t).deriv

theorem gap4 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.exp t) :
    ∀ t, Real.exp t = x t := by
  intro t
  exact (hParam t).symm

theorem gap5 (x : ℝ → ℝ)
    (hDerivative : ∀ t, d1 x t = Real.exp t)
    (hParam : ∀ t, Real.exp t = x t) :
    ∀ t, d1 x t = x t := by
  intro t
  rw [hDerivative t, hParam t]

theorem gap6 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.exp t) :
    ∀ t, d2 x t = Real.exp t := by
  have hx : x = Real.exp := funext hParam
  have hd : deriv Real.exp = Real.exp :=
    funext fun s => (Real.hasDerivAt_exp s).deriv
  intro t
  rw [hx]
  simpa [d2, hd] using (Real.hasDerivAt_exp t).deriv

theorem gap7 (x : ℝ → ℝ)
    (hParam : ∀ t, x t = Real.exp t) :
    ∀ t, Real.exp t = x t := by
  intro t
  exact (hParam t).symm

theorem gap8 (x : ℝ → ℝ)
    (hSecond : ∀ t, d2 x t = Real.exp t)
    (hParam : ∀ t, Real.exp t = x t) :
    ∀ t, d2 x t = x t := by
  intro t
  rw [hSecond t, hParam t]

theorem gap9 (x y : ℝ → ℝ)
    (hFirstX : ∀ t, d1 x t = x t) :
    ∀ t, dydx x y t = d1 y t / x t := by
  intro t
  simp only [dydx, hFirstX t]

theorem gap10 (x y : ℝ → ℝ)
    (hFirstX : ∀ t, d1 x t = x t)
    (hSecondX : ∀ t, d2 x t = x t) :
    ∀ t,
      d2ydx2 x y t =
        (x t * d2 y t - x t * d1 y t) / (x t) ^ 3 := by
  intro t
  simp only [d2ydx2, hFirstX t, hSecondX t]
  ring

theorem gap11 (x y : ℝ → ℝ)
    (hNonzero : ∀ t, x t ≠ 0) :
    ∀ t,
      (x t * d2 y t - x t * d1 y t) / (x t) ^ 3 =
        (d2 y t - d1 y t) / (x t) ^ 2 := by
  intro t
  field_simp [hNonzero t] <;> ring

theorem gap12 (x y : ℝ → ℝ)
    (hExpanded :
      ∀ t,
        d2ydx2 x y t =
          (x t * d2 y t - x t * d1 y t) / (x t) ^ 3)
    (hCancel :
      ∀ t,
        (x t * d2 y t - x t * d1 y t) / (x t) ^ 3 =
          (d2 y t - d1 y t) / (x t) ^ 2) :
    ∀ t,
      d2ydx2 x y t = (d2 y t - d1 y t) / (x t) ^ 2 := by
  intro t
  rw [hExpanded t, hCancel t]

theorem gap13 (x y : ℝ → ℝ)
    (hODE :
      ∀ t, (x t) ^ 2 * d2ydx2 x y t + x t * dydx x y t + y t = 0)
    (hFirst : ∀ t, dydx x y t = d1 y t / x t)
    (hSecond :
      ∀ t, d2ydx2 x y t = (d2 y t - d1 y t) / (x t) ^ 2)
    (hNonzero : ∀ t, x t ≠ 0) :
    ∀ t, d2 y t + y t = 0 := by
  intro t
  have h := hODE t
  rw [hFirst t, hSecond t] at h
  have hsimpl :
      (x t) ^ 2 * ((d2 y t - d1 y t) / (x t) ^ 2) +
          x t * (d1 y t / x t) + y t =
        d2 y t + y t := by
    field_simp [hNonzero t] <;> ring
  rw [hsimpl] at h
  exact h

end

end ProofGap.Exercise3434
