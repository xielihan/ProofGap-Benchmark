import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4401_1

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

def O : Vec3 := (0, 0, 0)

theorem gap1 (y z : ℝ) (x : ℝ) :
    HasDerivAt (fun t => u (t, y, z)) (2 * x + y + 3) x := by
  have h0 := (hasDerivAt_id x).mul (hasDerivAt_id x)
  have h1 := h0.add (hasDerivAt_const x (2 * y ^ 2))
  have h2 := h1.add (hasDerivAt_const x (3 * z ^ 2))
  have h3 := h2.add ((hasDerivAt_id x).mul (hasDerivAt_const x y))
  have h4 := h3.add ((hasDerivAt_const x 3).mul (hasDerivAt_id x))
  have h5 := h4.sub (hasDerivAt_const x (2 * y))
  have h6 := h5.sub (hasDerivAt_const x (6 * z))
  convert h6 using 1
  · funext t
    simp [u, pow_two] <;> ring
  · simp <;> ring

theorem gap2 (x z : ℝ) (y : ℝ) :
    HasDerivAt (fun t => u (x, t, z)) (4 * y + x - 2) y := by
  have h0 := hasDerivAt_const y (x ^ 2)
  have hy2 := (hasDerivAt_id y).mul (hasDerivAt_id y)
  have h1 := h0.add ((hasDerivAt_const y 2).mul hy2)
  have h2 := h1.add (hasDerivAt_const y (3 * z ^ 2))
  have h3 := h2.add ((hasDerivAt_const y x).mul (hasDerivAt_id y))
  have h4 := h3.add (hasDerivAt_const y (3 * x))
  have h5 := h4.sub ((hasDerivAt_const y 2).mul (hasDerivAt_id y))
  have h6 := h5.sub (hasDerivAt_const y (6 * z))
  convert h6 using 1
  · funext t
    simp [u, pow_two] <;> ring
  · simp <;> ring

theorem gap3 (x y : ℝ) (z : ℝ) :
    HasDerivAt (fun t => u (x, y, t)) (6 * z - 6) z := by
  have h0 := hasDerivAt_const z (x ^ 2)
  have h1 := h0.add (hasDerivAt_const z (2 * y ^ 2))
  have hz2 := (hasDerivAt_id z).mul (hasDerivAt_id z)
  have h2 := h1.add ((hasDerivAt_const z 3).mul hz2)
  have h3 := h2.add (hasDerivAt_const z (x * y))
  have h4 := h3.add (hasDerivAt_const z (3 * x))
  have h5 := h4.sub (hasDerivAt_const z (2 * y))
  have h6 := h5.sub ((hasDerivAt_const z 6).mul (hasDerivAt_id z))
  convert h6 using 1
  · funext t
    simp [u, pow_two] <;> ring
  · simp <;> ring

theorem gap4 :
    gradient O = (3, -2, -6) := by
  norm_num [gradient, O]

theorem gap5 :
    norm3 (gradient O) = 7 := by
  rw [gap4]
  norm_num [norm3]
  convert Real.sqrt_sq (show (0 : ℝ) ≤ 7 by norm_num) using 1 <;> norm_num

theorem gap6 :
    directionCosines O = (3 / 7, -2 / 7, -6 / 7) := by
  unfold directionCosines
  rw [gap5, gap4]

end

end ProofGap.Exercise4401_1
