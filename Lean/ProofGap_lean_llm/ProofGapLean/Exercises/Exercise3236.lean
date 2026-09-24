import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise3236

noncomputable section

def u (x y : ℝ) : ℝ :=
  x / y

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def firstForm (x y dx dy : ℝ) : ℝ :=
  (y * dx - x * dy) / y ^ 2

def secondRaw (x y dx dy : ℝ) : ℝ :=
  (y ^ 2 * (dx * dy - dx * dy) -
      2 * y * dy * (y * dx - x * dy)) /
    y ^ 4

def secondSimplified (x y dx dy : ℝ) : ℝ :=
  (-2 / y ^ 3) * (y * dx - x * dy) * dy

private theorem partialX_u_formula (x y : ℝ) :
    partialX u x y = 1 / y := by
  unfold partialX
  simpa [u] using ((hasDerivAt_id x).div_const y).deriv

private theorem partialY_u_formula (x y : ℝ) (hy : y ≠ 0) :
    partialY u x y = -x / y ^ 2 := by
  unfold partialY
  simpa [u] using
    (((hasDerivAt_const (x := y) x).div (hasDerivAt_id y) hy).deriv)

private theorem partialXX_u_formula (x y : ℝ) :
    partialXX u x y = 0 := by
  unfold partialXX
  have hfun : (fun t : ℝ => partialX u t y) = (fun _ : ℝ => 1 / y) := by
    funext t
    exact partialX_u_formula t y
  rw [hfun]
  simp

private theorem partialXY_u_formula (x y : ℝ) (hy : y ≠ 0) :
    partialXY u x y = -1 / y ^ 2 := by
  unfold partialXY
  have hfun : (fun t : ℝ => partialX u x t) = (fun t : ℝ => 1 / t) := by
    funext t
    exact partialX_u_formula x t
  rw [hfun]
  simpa [div_eq_mul_inv] using
    (((hasDerivAt_const (x := y) (1 : ℝ)).div (hasDerivAt_id y) hy).deriv)

private theorem partialYY_u_formula (x y : ℝ) (hy : y ≠ 0) :
    partialYY u x y = 2 * x / y ^ 3 := by
  have hfun :
      (fun t : ℝ => partialY u x t) =ᶠ[nhds y]
        (fun t : ℝ => -x / t ^ 2) := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    exact partialY_u_formula x t ht
  have hderiv :
      HasDerivAt (fun t : ℝ => -x / t ^ 2) (2 * x / y ^ 3) y := by
    convert
      ((hasDerivAt_const (x := y) (-x)).div
        ((hasDerivAt_id y).pow 2) (pow_ne_zero 2 hy)) using 1 <;>
      field_simp [hy] <;> simp <;> ring
  unfold partialYY
  exact (hderiv.congr_of_eventuallyEq hfun).deriv

theorem gap1 :
    ∀ x y dx dy : ℝ, y ≠ 0 →
      differential u x y dx dy = firstForm x y dx dy := by
  intro x y dx dy hy
  unfold differential firstForm
  rw [partialX_u_formula x y, partialY_u_formula x y hy]
  field_simp [hy]
  ring

theorem gap2 :
    ∀ x y dx dy : ℝ, y ≠ 0 →
      secondDifferential u x y dx dy = secondRaw x y dx dy := by
  intro x y dx dy hy
  unfold secondDifferential secondRaw
  rw [partialXX_u_formula x y, partialXY_u_formula x y hy,
    partialYY_u_formula x y hy]
  field_simp [hy]
  ring

theorem gap3 :
    ∀ x y dx dy : ℝ, y ≠ 0 →
      secondRaw x y dx dy = secondSimplified x y dx dy := by
  intro x y dx dy hy
  unfold secondRaw secondSimplified
  field_simp [hy]
  ring

theorem gap4 :
    ∀ x y dx dy : ℝ, y ≠ 0 →
      secondDifferential u x y dx dy =
        secondSimplified x y dx dy := by
  intro x y dx dy hy
  calc
    secondDifferential u x y dx dy = secondRaw x y dx dy :=
      gap2 x y dx dy hy
    _ = secondSimplified x y dx dy := gap3 x y dx dy hy

end

end ProofGap.Exercise3236
