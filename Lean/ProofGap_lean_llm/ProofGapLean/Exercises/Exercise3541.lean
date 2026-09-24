import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3541

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def surfaceHeight (x y : ℝ) : ℝ := Real.arctan (y / x)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f x s) y

def graphNormal (f : ℝ → ℝ → ℝ) (x y : ℝ) : Point3 :=
  (partialX f x y, (partialY f x y, -1))

def basePoint : Point3 := (1, (1, Real.pi / 4))

def baseNormal : Point3 := graphNormal surfaceHeight 1 1

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def displacement (Q P : Point3) : Point3 :=
  (Q.1 - P.1, (Q.2.1 - P.2.1, Q.2.2 - P.2.2))

def planeFromPointNormal (P N : Point3) : Set Point3 :=
  {Q | dot N (displacement Q P) = 0}

def tangentPlane : Set Point3 :=
  planeFromPointNormal basePoint baseNormal

def rawPlane : Set Point3 :=
  {Q |
    Q.2.2 - Real.pi / 4 =
      -(1 : ℝ) / 2 * (Q.1 - 1) + (1 : ℝ) / 2 * (Q.2.1 - 1)}

def simplifiedPlane : Set Point3 :=
  {Q | Q.2.2 = Real.pi / 4 - (1 : ℝ) / 2 * (Q.1 - Q.2.1)}

def normalDirection : Point3 := (1, (-1, 2))

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def normalLine : Set Point3 :=
  {Q | ∃ s : ℝ, Q = linePoint basePoint normalDirection s}

theorem gap1 (x y : ℝ) (hx : x ≠ 0) :
    graphNormal surfaceHeight x y =
      (-y / (x ^ 2 + y ^ 2), (x / (x ^ 2 + y ^ 2), -1)) := by
  have hsum : x ^ 2 + y ^ 2 ≠ 0 :=
    ne_of_gt
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y))
  have hatan : 1 + (y / x) ^ 2 ≠ 0 :=
    ne_of_gt
      (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg (y / x)))
  have hdivX :
      HasDerivAt (fun s : ℝ => y / s) (-y / x ^ 2) x := by
    simpa only [zero_mul, mul_zero, one_mul, mul_one, zero_sub, sub_zero] using
      ((hasDerivAt_const x y).div (hasDerivAt_id x) hx)
  have hdivY :
      HasDerivAt (fun s : ℝ => s / x) (x / x ^ 2) y := by
    simpa only [zero_mul, mul_zero, one_mul, mul_one, zero_sub, sub_zero] using
      ((hasDerivAt_id y).div (hasDerivAt_const y x) hx)
  have hdx :
      HasDerivAt (fun s : ℝ => Real.arctan (y / s))
        (-y / (x ^ 2 + y ^ 2)) x := by
    convert (Real.hasDerivAt_arctan (y / x)).comp x hdivX using 1 <;>
      field_simp [hx, hsum, hatan] <;> ring
  have hdy :
      HasDerivAt (fun s : ℝ => Real.arctan (s / x))
        (x / (x ^ 2 + y ^ 2)) y := by
    convert (Real.hasDerivAt_arctan (y / x)).comp y hdivY using 1 <;>
      field_simp [hx, hsum, hatan] <;> ring
  unfold graphNormal partialX partialY
  apply Prod.ext
  · simpa only [surfaceHeight] using hdx.deriv
  · apply Prod.ext
    · simpa only [surfaceHeight] using hdy.deriv
    · rfl

theorem gap2 :
    graphNormal surfaceHeight 1 1 =
      (-(1 : ℝ) / 2, ((1 : ℝ) / 2, -1)) := by
  rw [gap1 1 1 (by norm_num)]
  norm_num

theorem gap3 :
    baseNormal = (-(1 : ℝ) / 2, ((1 : ℝ) / 2, -1)) := by
  unfold baseNormal
  exact gap2

theorem gap4 :
    tangentPlane = rawPlane := by
  apply Set.ext
  intro Q
  change
    dot baseNormal (displacement Q basePoint) = 0 ↔
      Q.2.2 - Real.pi / 4 =
        -(1 : ℝ) / 2 * (Q.1 - 1) + (1 : ℝ) / 2 * (Q.2.1 - 1)
  rw [gap3]
  simp only [dot, displacement, basePoint, Prod.fst, Prod.snd]
  constructor <;> intro h <;> linarith

theorem gap5 :
    rawPlane = simplifiedPlane := by
  apply Set.ext
  intro Q
  change
    (Q.2.2 - Real.pi / 4 =
        -(1 : ℝ) / 2 * (Q.1 - 1) + (1 : ℝ) / 2 * (Q.2.1 - 1)) ↔
      Q.2.2 = Real.pi / 4 - (1 : ℝ) / 2 * (Q.1 - Q.2.1)
  constructor <;> intro h <;> linarith

theorem gap6 :
    tangentPlane = simplifiedPlane := by
  rw [gap4, gap5]

theorem gap7 :
    normalLine =
      {Q |
        (Q.1 - 1) * (-1) = (Q.2.1 - 1) ∧
        (Q.2.1 - 1) * 2 = (Q.2.2 - Real.pi / 4) * (-1)} := by
  apply Set.ext
  intro Q
  change
    (∃ s : ℝ, Q = linePoint basePoint normalDirection s) ↔
      (Q.1 - 1) * (-1) = Q.2.1 - 1 ∧
        (Q.2.1 - 1) * 2 = (Q.2.2 - Real.pi / 4) * (-1)
  constructor
  · intro h
    obtain ⟨s, rfl⟩ := h
    constructor <;>
      simp only [linePoint, basePoint, normalDirection, Prod.fst, Prod.snd] <;>
      ring
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨Q.1 - 1, ?_⟩
    apply Prod.ext
    · change Q.1 = 1 + (Q.1 - 1) * 1
      ring
    · apply Prod.ext
      · change Q.2.1 = 1 + (Q.1 - 1) * (-1)
        linarith
      · change Q.2.2 = Real.pi / 4 + (Q.1 - 1) * 2
        linarith

end

end ProofGap.Exercise3541
