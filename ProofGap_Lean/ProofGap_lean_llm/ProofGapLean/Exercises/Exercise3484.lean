import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3484

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX (partialX f) x y

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY (partialX f) x y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY (partialY f) x y

def secondDifferential (D : ℝ → ℝ) (q : ℝ) : ℝ :=
  D (D q)

def radialFirst (x y r dx dy : ℝ) : ℝ :=
  x / r * dx + y / r * dy

def angularFirst (x y r dx dy : ℝ) : ℝ :=
  x / r ^ 2 * dy - y / r ^ 2 * dx

def radialSecondExpanded (x y r dx dy dr : ℝ) : ℝ :=
  1 / r * (dx ^ 2 + dy ^ 2) - (x * dx + y * dy) / r ^ 2 * dr

def radialSecondPolar (x y r dx dy : ℝ) : ℝ :=
  1 / r ^ 3 * (y * dx - x * dy) ^ 2

def angularSecondIntermediate (x y r dx dy dr : ℝ) : ℝ :=
  -(2 * (x * dy - y * dx) / r ^ 3) * dr

def angularSecondPolar (x y r dx dy : ℝ) : ℝ :=
  -(2 / r ^ 4) * (x * dy - y * dx) * (x * dx + y * dy)

def cartesianSecondForm (U : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX U x y * dx ^ 2 +
    2 * partialXY U x y * dx * dy +
    partialYY U x y * dy ^ 2

def polarSecondForm (u : ℝ → ℝ → ℝ) (r φ dr dφ d2r d2φ : ℝ) : ℝ :=
  partialXX u r φ * dr ^ 2 +
    2 * partialXY u r φ * dr * dφ +
    partialYY u r φ * dφ ^ 2 +
    partialX u r φ * d2r +
    partialY u r φ * d2φ

theorem gap1 (D : ℝ → ℝ) (r : ℝ) :
    secondDifferential D r = D (D r) := by
  rfl

theorem gap2 (D : ℝ → ℝ) (x y r dx dy : ℝ)
    (hDr : D r = radialFirst x y r dx dy) :
    D (D r) = D (radialFirst x y r dx dy) := by
  rw [hDr]

theorem gap3 (D : ℝ → ℝ) (x y r dx dy : ℝ)
    (hSecond : secondDifferential D r = D (D r))
    (hSubstitute : D (D r) = D (radialFirst x y r dx dy)) :
    secondDifferential D r = D (radialFirst x y r dx dy) := by
  exact hSecond.trans hSubstitute

theorem gap4 (D : ℝ → ℝ) (x y r dx dy : ℝ)
    (hr : r ≠ 0)
    (hDr : D r = radialFirst x y r dx dy)
    (hDifferentiate :
      D (radialFirst x y r dx dy) =
        radialSecondExpanded x y r dx dy (D r)) :
    secondDifferential D r =
      radialSecondExpanded x y r dx dy (D r) := by
  unfold secondDifferential
  exact (congrArg D hDr).trans hDifferentiate

theorem gap5 (x y r dx dy dr : ℝ)
    (hr : r ≠ 0)
    (hRadius : x ^ 2 + y ^ 2 = r ^ 2)
    (hDr : dr = radialFirst x y r dx dy) :
    radialSecondExpanded x y r dx dy dr =
      radialSecondPolar x y r dx dy := by
  subst dr
  unfold radialSecondExpanded radialSecondPolar radialFirst
  have hnum :
      r ^ 2 * (dx ^ 2 + dy ^ 2) - (x * dx + y * dy) ^ 2 =
        (y * dx - x * dy) ^ 2 := by
    rw [← hRadius]
    ring
  field_simp [hr] <;> nlinarith [hnum]

theorem gap6 (D : ℝ → ℝ) (x y r dx dy : ℝ)
    (hExpanded :
      secondDifferential D r =
        radialSecondExpanded x y r dx dy (D r))
    (hSimplified :
      radialSecondExpanded x y r dx dy (D r) =
        radialSecondPolar x y r dx dy) :
    secondDifferential D r = radialSecondPolar x y r dx dy := by
  exact hExpanded.trans hSimplified

theorem gap7 (D : ℝ → ℝ) (φ : ℝ) :
    secondDifferential D φ = D (D φ) := by
  rfl

theorem gap8 (D : ℝ → ℝ) (x y r φ dx dy : ℝ)
    (hDφ : D φ = angularFirst x y r dx dy) :
    D (D φ) = D (angularFirst x y r dx dy) := by
  rw [hDφ]

theorem gap9 (D : ℝ → ℝ) (x y r dx dy : ℝ)
    (hr : r ≠ 0)
    (hDifferentiate :
      D (angularFirst x y r dx dy) =
        angularSecondIntermediate x y r dx dy (D r)) :
    D (angularFirst x y r dx dy) =
      angularSecondIntermediate x y r dx dy (D r) := by
  exact hDifferentiate

theorem gap10 (x y r dx dy dr : ℝ)
    (hr : r ≠ 0)
    (hDr : dr = radialFirst x y r dx dy) :
    angularSecondIntermediate x y r dx dy dr =
      angularSecondPolar x y r dx dy := by
  subst dr
  unfold angularSecondIntermediate angularSecondPolar radialFirst
  field_simp [hr] <;> ring

theorem gap11 (D : ℝ → ℝ) (x y r φ dx dy : ℝ)
    (hDefinition : secondDifferential D φ = D (D φ))
    (hSubstitute : D (D φ) = D (angularFirst x y r dx dy))
    (hDifferentiate :
      D (angularFirst x y r dx dy) =
        angularSecondPolar x y r dx dy) :
    secondDifferential D φ = angularSecondPolar x y r dx dy := by
  exact hDefinition.trans (hSubstitute.trans hDifferentiate)

theorem gap12 (u : ℝ → ℝ → ℝ) (r φ dr dφ d2r d2φ d2u : ℝ)
    (hSecondOrderChainRule :
      d2u = polarSecondForm u r φ dr dφ d2r d2φ) :
    d2u = partialXX u r φ * dr ^ 2 +
        2 * partialXY u r φ * dr * dφ +
        partialYY u r φ * dφ ^ 2 +
        partialX u r φ * d2r +
        partialY u r φ * d2φ := by
  simpa [polarSecondForm] using hSecondOrderChainRule

theorem gap13 (U : ℝ → ℝ → ℝ) (x y dx dy d2U : ℝ)
    (hCartesianSecond :
      d2U = cartesianSecondForm U x y dx dy) :
    d2U = partialXX U x y * dx ^ 2 +
      2 * partialXY U x y * dx * dy +
      partialYY U x y * dy ^ 2 := by
  simpa [cartesianSecondForm] using hCartesianSecond

theorem gap14 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hCoefficient :
      partialXX U (x r φ) (y r φ) =
        x r φ ^ 2 / r ^ 2 * partialXX u r φ -
          (2 * x r φ * y r φ) / r ^ 3 * partialXY u r φ +
          y r φ ^ 2 / r ^ 4 * partialYY u r φ +
          y r φ ^ 2 / r ^ 3 * partialX u r φ +
          (2 * x r φ * y r φ) / r ^ 4 * partialY u r φ) :
    partialXX U (x r φ) (y r φ) =
      x r φ ^ 2 / r ^ 2 * partialXX u r φ -
        (2 * x r φ * y r φ) / r ^ 3 * partialXY u r φ +
        y r φ ^ 2 / r ^ 4 * partialYY u r φ +
        y r φ ^ 2 / r ^ 3 * partialX u r φ +
        (2 * x r φ * y r φ) / r ^ 4 * partialY u r φ := by
  exact hCoefficient

theorem gap15 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hCoefficient :
      partialYY U (x r φ) (y r φ) =
        y r φ ^ 2 / r ^ 2 * partialXX u r φ +
          (2 * x r φ * y r φ) / r ^ 3 * partialXY u r φ +
          x r φ ^ 2 / r ^ 4 * partialYY u r φ +
          x r φ ^ 2 / r ^ 3 * partialX u r φ -
          (2 * x r φ * y r φ) / r ^ 4 * partialY u r φ) :
    partialYY U (x r φ) (y r φ) =
      y r φ ^ 2 / r ^ 2 * partialXX u r φ +
        (2 * x r φ * y r φ) / r ^ 3 * partialXY u r φ +
        x r φ ^ 2 / r ^ 4 * partialYY u r φ +
        x r φ ^ 2 / r ^ 3 * partialX u r φ -
        (2 * x r φ * y r φ) / r ^ 4 * partialY u r φ := by
  exact hCoefficient

theorem gap16 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hRadius : x r φ ^ 2 + y r φ ^ 2 = r ^ 2)
    (hUxx :
      partialXX U (x r φ) (y r φ) =
        x r φ ^ 2 / r ^ 2 * partialXX u r φ -
          (2 * x r φ * y r φ) / r ^ 3 * partialXY u r φ +
          y r φ ^ 2 / r ^ 4 * partialYY u r φ +
          y r φ ^ 2 / r ^ 3 * partialX u r φ +
          (2 * x r φ * y r φ) / r ^ 4 * partialY u r φ)
    (hUyy :
      partialYY U (x r φ) (y r φ) =
        y r φ ^ 2 / r ^ 2 * partialXX u r φ +
          (2 * x r φ * y r φ) / r ^ 3 * partialXY u r φ +
          x r φ ^ 2 / r ^ 4 * partialYY u r φ +
          x r φ ^ 2 / r ^ 3 * partialX u r φ -
          (2 * x r φ * y r φ) / r ^ 4 * partialY u r φ) :
    partialXX U (x r φ) (y r φ) + partialYY U (x r φ) (y r φ) =
      partialXX u r φ + 1 / r ^ 2 * partialYY u r φ +
        1 / r * partialX u r φ := by
  rw [hUxx, hUyy]
  have h2 :
      x r φ ^ 2 / r ^ 2 + y r φ ^ 2 / r ^ 2 = 1 := by
    field_simp [hr] <;> nlinarith [hRadius]
  have h3 :
      y r φ ^ 2 / r ^ 3 + x r φ ^ 2 / r ^ 3 = 1 / r := by
    field_simp [hr] <;> nlinarith [hRadius]
  have h4 :
      y r φ ^ 2 / r ^ 4 + x r φ ^ 2 / r ^ 4 = 1 / r ^ 2 := by
    field_simp [hr] <;> nlinarith [hRadius]
  calc
    _ =
        (x r φ ^ 2 / r ^ 2 + y r φ ^ 2 / r ^ 2) * partialXX u r φ +
          (y r φ ^ 2 / r ^ 4 + x r φ ^ 2 / r ^ 4) * partialYY u r φ +
          (y r φ ^ 2 / r ^ 3 + x r φ ^ 2 / r ^ 3) * partialX u r φ := by
            ring
    _ = _ := by
      rw [h2, h4, h3]
      ring

end

end ProofGap.Exercise3484
