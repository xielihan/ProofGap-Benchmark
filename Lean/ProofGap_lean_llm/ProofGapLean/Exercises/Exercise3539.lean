import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3539

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def surfaceHeight (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f x s) y

def graphNormal (f : ℝ → ℝ → ℝ) (x y : ℝ) : Point3 :=
  (partialX f x y, (partialY f x y, -1))

def basePoint : Point3 := (1, (2, 5))

def baseNormal : Point3 := graphNormal surfaceHeight 1 2

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def displacement (Q P : Point3) : Point3 :=
  (Q.1 - P.1, (Q.2.1 - P.2.1, Q.2.2 - P.2.2))

def planeFromPointNormal (P N : Point3) : Set Point3 :=
  {Q | dot N (displacement Q P) = 0}

def tangentPlane : Set Point3 :=
  planeFromPointNormal basePoint baseNormal

def simplifiedPlane : Set Point3 :=
  {Q | 2 * Q.1 + 4 * Q.2.1 - Q.2.2 = 5}

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def normalLine : Set Point3 :=
  {Q | ∃ s : ℝ, Q = linePoint basePoint baseNormal s}

theorem gap1 (x y : ℝ) :
    graphNormal surfaceHeight x y =
      (partialX surfaceHeight x y, (partialY surfaceHeight x y, -1)) := by
  rfl

theorem gap2 :
    ∀ x y, graphNormal surfaceHeight x y = (2 * x, (2 * y, -1)) := by
  intro x y
  have hx :
      deriv (fun s : ℝ => surfaceHeight s y) x = 2 * x := by
    simpa [surfaceHeight, pow_two, two_mul] using
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).add
        (hasDerivAt_const x (y ^ 2))).deriv
  have hy :
      deriv (fun s : ℝ => surfaceHeight x s) y = 2 * y := by
    simpa [surfaceHeight, pow_two, two_mul] using
      ((hasDerivAt_const y (x ^ 2)).add
        ((hasDerivAt_id y).mul (hasDerivAt_id y))).deriv
  simp [graphNormal, partialX, partialY, hx, hy]

theorem gap3 :
    graphNormal surfaceHeight 1 2 = (2, (4, -1)) := by
  have h := gap2 (1 : ℝ) (2 : ℝ)
  norm_num at h
  exact h

theorem gap4 :
    baseNormal = (2, (4, -1)) := by
  simpa [baseNormal] using gap3

theorem gap5 :
    tangentPlane =
      {Q | 2 * (Q.1 - 1) + 4 * (Q.2.1 - 2) - (Q.2.2 - 5) = 0} := by
  apply Set.ext
  intro Q
  change
    dot baseNormal (displacement Q basePoint) = 0 ↔
      2 * (Q.1 - 1) + 4 * (Q.2.1 - 2) - (Q.2.2 - 5) = 0
  rw [gap4]
  simp [dot, displacement, basePoint]
  constructor <;> intro h <;> linarith

theorem gap6 :
    {Q : Point3 |
        2 * (Q.1 - 1) + 4 * (Q.2.1 - 2) - (Q.2.2 - 5) = 0} =
      simplifiedPlane := by
  apply Set.ext
  intro Q
  change
    (2 * (Q.1 - 1) + 4 * (Q.2.1 - 2) - (Q.2.2 - 5) = 0) ↔
      (2 * Q.1 + 4 * Q.2.1 - Q.2.2 = 5)
  constructor <;> intro h <;> linarith

theorem gap7 :
    tangentPlane = simplifiedPlane := by
  exact gap5.trans gap6

theorem gap8 :
    normalLine =
      {Q |
        (Q.1 - 1) * 4 = (Q.2.1 - 2) * 2 ∧
        (Q.2.1 - 2) * (-1) = (Q.2.2 - 5) * 4 ∧
        (Q.1 - 1) * (-1) = (Q.2.2 - 5) * 2} := by
  apply Set.ext
  intro Q
  change
    (∃ s : ℝ, Q = linePoint basePoint baseNormal s) ↔
      ((Q.1 - 1) * 4 = (Q.2.1 - 2) * 2 ∧
       (Q.2.1 - 2) * (-1) = (Q.2.2 - 5) * 4 ∧
       (Q.1 - 1) * (-1) = (Q.2.2 - 5) * 2)
  constructor
  · rintro ⟨s, rfl⟩
    rw [gap4]
    dsimp [linePoint, basePoint]
    constructor
    · ring
    · constructor <;> ring
  · rintro ⟨hxy, hyz, hxz⟩
    refine ⟨(Q.1 - 1) / 2, ?_⟩
    rw [gap4]
    apply Prod.ext
    · dsimp [linePoint, basePoint]
      linarith
    · apply Prod.ext
      · dsimp [linePoint, basePoint]
        linarith
      · dsimp [linePoint, basePoint]
        linarith

end

end ProofGap.Exercise3539
