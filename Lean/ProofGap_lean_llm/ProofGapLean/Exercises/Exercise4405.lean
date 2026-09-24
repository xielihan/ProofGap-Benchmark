import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace ProofGap.Exercise4405

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def squaredRadius (p : Vec3) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

def u (p : Vec3) : ℝ :=
  p.1 / squaredRadius p

def gradient (p : Vec3) : Vec3 :=
  ((p.2.1 ^ 2 + p.2.2 ^ 2 - p.1 ^ 2) / squaredRadius p ^ 2,
    -(2 * p.1 * p.2.1) / squaredRadius p ^ 2,
    -(2 * p.1 * p.2.2) / squaredRadius p ^ 2)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def cosineBetween (a b : Vec3) : ℝ :=
  dot a b / (norm3 a * norm3 b)

def A : Vec3 := (1, 2, 2)

def B : Vec3 := (-3, 1, 0)

def gradientAngle : ℝ :=
  Real.arccos (cosineBetween (gradient A) (gradient B))

private theorem hasDerivAt_coordinateSquare (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa [id, mul_comm] using (hasDerivAt_id x).pow 2

theorem gap1 (p : Vec3) (h : squaredRadius p ≠ 0) :
    HasDerivAt
      (fun x => u (x, p.2.1, p.2.2))
      ((p.2.1 ^ 2 + p.2.2 ^ 2 - p.1 ^ 2) /
        squaredRadius p ^ 2) p.1 := by
  have hden :
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≠ 0 := by
    simpa [squaredRadius] using h
  have hd :
      HasDerivAt
        (fun x : ℝ => x ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)
        (2 * p.1) p.1 := by
    convert
      (((hasDerivAt_coordinateSquare p.1).add
          (hasDerivAt_const (x := p.1) (c := p.2.1 ^ 2))).add
        (hasDerivAt_const (x := p.1) (c := p.2.2 ^ 2))) using 1 <;>
      ring_nf
  have hnum : HasDerivAt (fun x : ℝ => x) 1 p.1 := by
    simpa [id] using (hasDerivAt_id p.1)
  have hquot :
      HasDerivAt
        (fun x : ℝ => x / (x ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))
        ((p.2.1 ^ 2 + p.2.2 ^ 2 - p.1 ^ 2) /
          (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 2) p.1 := by
    convert hnum.div hd hden using 1 <;> ring_nf
  simpa [u, squaredRadius] using hquot

theorem gap2 (p : Vec3) (h : squaredRadius p ≠ 0) :
    HasDerivAt
      (fun y => u (p.1, y, p.2.2))
      (-(2 * p.1 * p.2.1) / squaredRadius p ^ 2) p.2.1 := by
  have hden :
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≠ 0 := by
    simpa [squaredRadius] using h
  have hd :
      HasDerivAt
        (fun y : ℝ => p.1 ^ 2 + y ^ 2 + p.2.2 ^ 2)
        (2 * p.2.1) p.2.1 := by
    convert
      (((hasDerivAt_const (x := p.2.1) (c := p.1 ^ 2)).add
          (hasDerivAt_coordinateSquare p.2.1)).add
        (hasDerivAt_const (x := p.2.1) (c := p.2.2 ^ 2))) using 1 <;>
      ring_nf
  have hquot :
      HasDerivAt
        (fun y : ℝ => p.1 / (p.1 ^ 2 + y ^ 2 + p.2.2 ^ 2))
        (-(2 * p.1 * p.2.1) /
          (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 2) p.2.1 := by
    convert
      (hasDerivAt_const (x := p.2.1) (c := p.1)).div hd hden using 1 <;>
      ring_nf
  simpa [u, squaredRadius] using hquot

theorem gap3 (p : Vec3) (h : squaredRadius p ≠ 0) :
    HasDerivAt
      (fun z => u (p.1, p.2.1, z))
      (-(2 * p.1 * p.2.2) / squaredRadius p ^ 2) p.2.2 := by
  have hden :
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≠ 0 := by
    simpa [squaredRadius] using h
  have hd :
      HasDerivAt
        (fun z : ℝ => p.1 ^ 2 + p.2.1 ^ 2 + z ^ 2)
        (2 * p.2.2) p.2.2 := by
    convert
      (((hasDerivAt_const (x := p.2.2) (c := p.1 ^ 2)).add
          (hasDerivAt_const (x := p.2.2) (c := p.2.1 ^ 2))).add
        (hasDerivAt_coordinateSquare p.2.2)) using 1 <;>
      ring_nf
  have hquot :
      HasDerivAt
        (fun z : ℝ => p.1 / (p.1 ^ 2 + p.2.1 ^ 2 + z ^ 2))
        (-(2 * p.1 * p.2.2) /
          (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 2) p.2.2 := by
    convert
      (hasDerivAt_const (x := p.2.2) (c := p.1)).div hd hden using 1 <;>
      ring_nf
  simpa [u, squaredRadius] using hquot

theorem gap4 :
    gradient A = (7 / 81, -4 / 81, -4 / 81) := by
  norm_num [gradient, A, squaredRadius]

theorem gap5 :
    gradient B = (-2 / 25, 3 / 50, 0) := by
  norm_num [gradient, B, squaredRadius]

theorem gap6 :
    cosineBetween (gradient A) (gradient B) =
      dot (gradient A) (gradient B) /
        (norm3 (gradient A) * norm3 (gradient B)) := by
  rfl

theorem gap7 :
    dot (gradient A) (gradient B) /
        (norm3 (gradient A) * norm3 (gradient B)) =
      (-4 / 405) / ((1 / 9) * (1 / 10)) := by
  rw [gap4, gap5]
  have hA :
      norm3 ((7 / 81, -4 / 81, -4 / 81) : Vec3) = 1 / 9 := by
    change
      Real.sqrt
          ((7 / 81 : ℝ) ^ 2 + (-4 / 81 : ℝ) ^ 2 +
            (-4 / 81 : ℝ) ^ 2) =
        1 / 9
    have hsq :
        (7 / 81 : ℝ) ^ 2 + (-4 / 81 : ℝ) ^ 2 +
            (-4 / 81 : ℝ) ^ 2 =
          (1 / 9 : ℝ) ^ 2 := by
      norm_num
    rw [hsq]
    have hs :
        (Real.sqrt ((1 / 9 : ℝ) ^ 2)) ^ 2 = (1 / 9 : ℝ) ^ 2 :=
      Real.sq_sqrt (sq_nonneg (1 / 9 : ℝ))
    have hn : 0 ≤ Real.sqrt ((1 / 9 : ℝ) ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith [hs, hn]
  have hB :
      norm3 ((-2 / 25, 3 / 50, 0) : Vec3) = 1 / 10 := by
    change
      Real.sqrt
          ((-2 / 25 : ℝ) ^ 2 + (3 / 50 : ℝ) ^ 2 + (0 : ℝ) ^ 2) =
        1 / 10
    have hsq :
        (-2 / 25 : ℝ) ^ 2 + (3 / 50 : ℝ) ^ 2 + (0 : ℝ) ^ 2 =
          (1 / 10 : ℝ) ^ 2 := by
      norm_num
    rw [hsq]
    have hs :
        (Real.sqrt ((1 / 10 : ℝ) ^ 2)) ^ 2 = (1 / 10 : ℝ) ^ 2 :=
      Real.sq_sqrt (sq_nonneg (1 / 10 : ℝ))
    have hn : 0 ≤ Real.sqrt ((1 / 10 : ℝ) ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith [hs, hn]
  rw [hA, hB]
  norm_num [dot]

theorem gap8 :
    (-4 / 405 : ℝ) / ((1 / 9) * (1 / 10)) = -8 / 9 := by
  norm_num

theorem gap9 :
    cosineBetween (gradient A) (gradient B) = -8 / 9 := by
  exact gap6.trans (gap7.trans gap8)

theorem gap10 :
    gradientAngle = Real.arccos (-8 / 9) := by
  simpa [gradientAngle] using congrArg Real.arccos gap9

end

end ProofGap.Exercise4405
