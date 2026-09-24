import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise4401_2

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

def A : Vec3 := (1, 1, 1)

theorem gap1 (y z : ℝ) (x : ℝ) :
    HasDerivAt (fun t => u (t, y, z)) (2 * x + y + 3) x := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id x).mul (hasDerivAt_id x))
  have h2 := hsq.add_const (2 * y ^ 2)
  have h3 := h2.add_const (3 * z ^ 2)
  have h4 := h3.add ((hasDerivAt_id x).mul_const y)
  have h5 := h4.add ((hasDerivAt_id x).const_mul 3)
  have h6 := h5.sub_const (2 * y)
  have h7 := h6.sub_const (6 * z)
  simpa [u] using h7

theorem gap2 (x z : ℝ) (y : ℝ) :
    HasDerivAt (fun t => u (x, t, z)) (4 * y + x - 2) y := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id y).mul (hasDerivAt_id y))
  have hscaled : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * y) y := by
    convert hsq.const_mul 2 using 1 <;> ring
  have h0 : HasDerivAt (fun _ : ℝ => x ^ 2) 0 y :=
    hasDerivAt_const (x := y) (c := x ^ 2)
  have h1 := h0.add hscaled
  have h2 := h1.add_const (3 * z ^ 2)
  have h3 := h2.add ((hasDerivAt_id y).const_mul x)
  have h4 := h3.add_const (3 * x)
  have h5 := h4.sub ((hasDerivAt_id y).const_mul 2)
  have h6 := h5.sub_const (6 * z)
  simpa [u] using h6

theorem gap3 (x y : ℝ) (z : ℝ) :
    HasDerivAt (fun t => u (x, y, t)) (6 * z - 6) z := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id z).mul (hasDerivAt_id z))
  have hscaled : HasDerivAt (fun t : ℝ => 3 * t ^ 2) (6 * z) z := by
    convert hsq.const_mul 3 using 1 <;> ring
  have h0 : HasDerivAt (fun _ : ℝ => x ^ 2) 0 z :=
    hasDerivAt_const (x := z) (c := x ^ 2)
  have h1 := h0.add_const (2 * y ^ 2)
  have h2 := h1.add hscaled
  have h3 := h2.add_const (x * y)
  have h4 := h3.add_const (3 * x)
  have h5 := h4.sub_const (2 * y)
  have h6 := h5.sub ((hasDerivAt_id z).const_mul 6)
  simpa [u] using h6

theorem gap4 :
    gradient A = (6, 3, 0) := by
  norm_num [gradient, A]

theorem gap5 :
    norm3 (gradient A) = 3 * Real.sqrt 5 := by
  rw [gap4]
  norm_num [norm3]
  calc
    Real.sqrt 45 = Real.sqrt (9 * 5) := by norm_num
    _ = Real.sqrt 9 * Real.sqrt 5 := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
    _ = |(3 : ℝ)| * Real.sqrt 5 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    _ = 3 * Real.sqrt 5 := by norm_num

theorem gap6 :
    directionCosines A =
      (2 / Real.sqrt 5, 1 / Real.sqrt 5, 0) := by
  rw [directionCosines, gap5, gap4]
  have hs : Real.sqrt 5 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  apply Prod.ext
  · dsimp
    field_simp [hs] <;> norm_num
  · apply Prod.ext
    · dsimp
      field_simp [hs] <;> norm_num
    · simp

end

end ProofGap.Exercise4401_2
