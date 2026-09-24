import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4401_3

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def u (p : Vec3) : ℝ :=
  p.1 ^ 2 + 2 * p.2.1 ^ 2 + 3 * p.2.2 ^ 2 +
    p.1 * p.2.1 + 3 * p.1 - 2 * p.2.1 - 6 * p.2.2

def gradient (p : Vec3) : Vec3 :=
  (2 * p.1 + p.2.1 + 3, 4 * p.2.1 + p.1 - 2, 6 * p.2.2 - 6)

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def directionCosines (p : Vec3) : Vec3 :=
  ((gradient p).1 / norm3 (gradient p),
    (gradient p).2.1 / norm3 (gradient p),
    (gradient p).2.2 / norm3 (gradient p))

def B : Vec3 := (2, 0, 1)

theorem gap1 (y z : ℝ) (x : ℝ) :
    HasDerivAt (fun t => u (t, y, z)) (2 * x + y + 3) x := by
  have hs : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).pow 2
  have hxy : HasDerivAt (fun t : ℝ => t * y) y x := by
    simpa using (hasDerivAt_id x).mul_const y
  have h3x : HasDerivAt (fun t : ℝ => 3 * t) 3 x := by
    simpa using (hasDerivAt_id x).const_mul 3
  have h1 := hs.add_const (2 * y ^ 2)
  have h2 := h1.add_const (3 * z ^ 2)
  have h3 := h2.add hxy
  have h4 := h3.add h3x
  have h5 := h4.sub_const (2 * y)
  have h6 := h5.sub_const (6 * z)
  convert h6 using 1 <;> simp [u] <;> ring

theorem gap2 (x z : ℝ) (y : ℝ) :
    HasDerivAt (fun t => u (x, t, z)) (4 * y + x - 2) y := by
  convert
    (((((((hasDerivAt_const y (x ^ 2)).add
      (((hasDerivAt_id y).pow 2).const_mul 2)).add
      (hasDerivAt_const y (3 * z ^ 2))).add
      ((hasDerivAt_id y).const_mul x)).add
      (hasDerivAt_const y (3 * x))).sub
      ((hasDerivAt_id y).const_mul 2)).sub
      (hasDerivAt_const y (6 * z))) using 1 <;>
    simp [u] <;> ring

theorem gap3 (x y : ℝ) (z : ℝ) :
    HasDerivAt (fun t => u (x, y, t)) (6 * z - 6) z := by
  convert
    (((((((hasDerivAt_const z (x ^ 2)).add
      (hasDerivAt_const z (2 * y ^ 2))).add
      (((hasDerivAt_id z).pow 2).const_mul 3)).add
      (hasDerivAt_const z (x * y))).add
      (hasDerivAt_const z (3 * x))).sub
      (hasDerivAt_const z (2 * y))).sub
      ((hasDerivAt_id z).const_mul 6)) using 1 <;>
    simp [u] <;> ring

theorem gap4 :
    gradient B = (7, 0, 0) := by
  norm_num [gradient, B]

theorem gap5 :
    norm3 (gradient B) = 7 := by
  calc
    norm3 (gradient B) = Real.sqrt ((7 : ℝ) ^ 2) := by
      rw [gap4]
      norm_num [norm3]
    _ = |(7 : ℝ)| := Real.sqrt_sq_eq_abs 7
    _ = 7 := by norm_num

theorem gap6 :
    directionCosines B = (1, 0, 0) := by
  rw [directionCosines, gap5, gap4]
  norm_num

end

end ProofGap.Exercise4401_3
