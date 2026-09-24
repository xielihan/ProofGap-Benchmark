import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3543

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def implicitF (P : Point3) : ℝ :=
  P.2.1 + Real.log P.1 - Real.log P.2.2 - P.2.2

def partialX3 (f : Point3 → ℝ) (P : Point3) : ℝ :=
  deriv (fun x => f (x, (P.2.1, P.2.2))) P.1

def partialY3 (f : Point3 → ℝ) (P : Point3) : ℝ :=
  deriv (fun y => f (P.1, (y, P.2.2))) P.2.1

def partialZ3 (f : Point3 → ℝ) (P : Point3) : ℝ :=
  deriv (fun z => f (P.1, (P.2.1, z))) P.2.2

def gradient3 (f : Point3 → ℝ) (P : Point3) : Point3 :=
  (partialX3 f P, (partialY3 f P, partialZ3 f P))

def basePoint : Point3 := (1, (1, 1))

def baseNormal : Point3 := gradient3 implicitF basePoint

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def displacement (Q P : Point3) : Point3 :=
  (Q.1 - P.1, (Q.2.1 - P.2.1, Q.2.2 - P.2.2))

def planeFromPointNormal (P N : Point3) : Set Point3 :=
  {Q | dot N (displacement Q P) = 0}

def tangentPlane : Set Point3 :=
  planeFromPointNormal basePoint baseNormal

def rawPlane : Set Point3 :=
  {Q | Q.1 - 1 + (Q.2.1 - 1) - 2 * (Q.2.2 - 1) = 0}

def simplifiedPlane : Set Point3 :=
  {Q | Q.1 + Q.2.1 - 2 * Q.2.2 = 0}

def normalDirection : Point3 := (1, (1, -2))

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def normalLine : Set Point3 :=
  {Q | ∃ s : ℝ, Q = linePoint basePoint normalDirection s}

theorem gap1 (x y z : ℝ) (hx : 0 < x) (hz : 0 < z) :
    gradient3 implicitF (x, (y, z)) =
      (1 / x, (1, -1 / z - 1)) := by
  apply Prod.ext
  · change
      deriv (fun t : ℝ => y + Real.log t - Real.log z - z) x = 1 / x
    simpa [one_div] using
      ((((hasDerivAt_const x y).add
          (Real.hasDerivAt_log hx.ne')).sub_const (Real.log z)).sub_const z).deriv
  · apply Prod.ext
    · change
        deriv (fun t : ℝ => t + Real.log x - Real.log z - z) y = 1
      simpa using
        ((((hasDerivAt_id y).add
            (hasDerivAt_const y (Real.log x))).sub_const (Real.log z)).sub_const z).deriv
    · change
        deriv (fun t : ℝ => y + Real.log x - Real.log t - t) z =
          -1 / z - 1
      simpa [one_div, div_eq_mul_inv] using
        (((hasDerivAt_const z (y + Real.log x)).sub
            (Real.hasDerivAt_log hz.ne')).sub (hasDerivAt_id z)).deriv

theorem gap2 :
    gradient3 implicitF basePoint = (1, (1, -2)) := by
  change gradient3 implicitF (1, (1, 1)) = (1, (1, -2))
  have h := gap1 (1 : ℝ) 1 1 zero_lt_one zero_lt_one
  norm_num at h
  exact h

theorem gap3 :
    baseNormal = (1, (1, -2)) := by
  simpa [baseNormal] using gap2

theorem gap4 :
    tangentPlane = rawPlane := by
  ext Q
  change
    dot baseNormal (displacement Q basePoint) = 0 ↔
      Q.1 - 1 + (Q.2.1 - 1) - 2 * (Q.2.2 - 1) = 0
  rw [gap3]
  simp only [dot, displacement, basePoint, Prod.fst, Prod.snd, one_mul]
  ring_nf

theorem gap5 :
    rawPlane = simplifiedPlane := by
  ext Q
  change
    Q.1 - 1 + (Q.2.1 - 1) - 2 * (Q.2.2 - 1) = 0 ↔
      Q.1 + Q.2.1 - 2 * Q.2.2 = 0
  ring_nf

theorem gap6 :
    tangentPlane = simplifiedPlane := by
  calc
    tangentPlane = rawPlane := gap4
    _ = simplifiedPlane := gap5

theorem gap7 :
    normalLine =
      {Q |
        (Q.1 - 1) = (Q.2.1 - 1) ∧
        (Q.2.1 - 1) * (-2) = (Q.2.2 - 1)} := by
  ext Q
  rcases Q with ⟨x, y, z⟩
  change
    (∃ s : ℝ,
      (x, (y, z)) =
        (1 + s * 1, (1 + s * 1, 1 + s * (-2)))) ↔
      x - 1 = y - 1 ∧ (y - 1) * (-2) = z - 1
  constructor
  · rintro ⟨s, hs⟩
    have hx : x = 1 + s := by
      simpa using congrArg (fun P : Point3 => P.1) hs
    have hy : y = 1 + s := by
      simpa using congrArg (fun P : Point3 => P.2.1) hs
    have hz : z = 1 + s * (-2) := by
      simpa using congrArg (fun P : Point3 => P.2.2) hs
    constructor <;> linarith
  · rintro ⟨hxy, hyz⟩
    refine ⟨y - 1, ?_⟩
    apply Prod.ext
    · dsimp
      linarith
    · apply Prod.ext
      · dsimp
        ring
      · dsimp
        linarith

end

end ProofGap.Exercise3543
