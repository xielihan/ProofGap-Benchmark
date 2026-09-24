import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise4402_1

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def u (p : Vec3) : ℝ :=
  p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3 -
    3 * p.1 * p.2.1 * p.2.2

def partialX (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

def partialY (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

def partialZ (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

def gradient (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def verticalUnit : Vec3 := (0, 0, 1)

def zeroVerticalDerivativeLocus : Set Vec3 :=
  {p | p.2.2 ^ 2 = p.1 * p.2.1}

theorem gap1 (x y z : ℝ) :
    gradient (x, y, z) =
      (3 * x ^ 2 - 3 * y * z,
        3 * y ^ 2 - 3 * x * z,
        3 * z ^ 2 - 3 * x * y) := by
  have hidx : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hidy : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
  have hidz : HasDerivAt (fun t : ℝ => t) 1 z := hasDerivAt_id z
  have hcubex : HasDerivAt (fun t : ℝ => t * t * t) (3 * x ^ 2) x := by
    convert (hidx.mul hidx).mul hidx using 1 <;>
      (try funext t) <;> simp <;> ring
  have hcubey : HasDerivAt (fun t : ℝ => t * t * t) (3 * y ^ 2) y := by
    convert (hidy.mul hidy).mul hidy using 1 <;>
      (try funext t) <;> simp <;> ring
  have hcubez : HasDerivAt (fun t : ℝ => t * t * t) (3 * z ^ 2) z := by
    convert (hidz.mul hidz).mul hidz using 1 <;>
      (try funext t) <;> simp <;> ring
  have hx :
      HasDerivAt
        (fun t : ℝ => t ^ 3 + y ^ 3 + z ^ 3 - 3 * t * y * z)
        (3 * x ^ 2 - 3 * y * z) x := by
    convert
      (((hcubex.add_const (y ^ 3)).add_const (z ^ 3)).sub
        (((hidx.const_mul 3).mul_const y).mul_const z))
      using 1 <;> (try funext t) <;> simp <;> ring
  have hy :
      HasDerivAt
        (fun t : ℝ => x ^ 3 + t ^ 3 + z ^ 3 - 3 * x * t * z)
        (3 * y ^ 2 - 3 * x * z) y := by
    convert
      ((((hasDerivAt_const y (x ^ 3)).add hcubey).add_const (z ^ 3)).sub
        ((hidy.const_mul (3 * x)).mul_const z))
      using 1 <;> (try funext t) <;> simp <;> ring
  have hz :
      HasDerivAt
        (fun t : ℝ => x ^ 3 + y ^ 3 + t ^ 3 - 3 * x * y * t)
        (3 * z ^ 2 - 3 * x * y) z := by
    convert
      ((((hasDerivAt_const z (x ^ 3)).add_const (y ^ 3)).add hcubez).sub
        (hidz.const_mul (3 * x * y)))
      using 1 <;> (try funext t) <;> simp <;> ring
  have hpx : partialX u (x, y, z) = 3 * x ^ 2 - 3 * y * z := by
    simpa [partialX, u] using hx.deriv
  have hpy : partialY u (x, y, z) = 3 * y ^ 2 - 3 * x * z := by
    simpa [partialY, u] using hy.deriv
  have hpz : partialZ u (x, y, z) = 3 * z ^ 2 - 3 * x * y := by
    simpa [partialZ, u] using hz.deriv
  change
    (partialX u (x, y, z), partialY u (x, y, z), partialZ u (x, y, z)) =
      (3 * x ^ 2 - 3 * y * z, 3 * y ^ 2 - 3 * x * z,
        3 * z ^ 2 - 3 * x * y)
  rw [hpx, hpy, hpz]

theorem gap2 (x y z : ℝ)
    (h : 3 * z ^ 2 - 3 * x * y = 0) :
    dot (gradient (x, y, z)) verticalUnit = 0 := by
  rw [gap1]
  simpa [dot, verticalUnit] using h

theorem gap3 (x y z : ℝ) (h : z ^ 2 = x * y) :
    3 * z ^ 2 - 3 * x * y = 0 := by
  rw [h]
  ring

theorem gap4 (x y z : ℝ) (h : z ^ 2 = x * y) :
    dot (gradient (x, y, z)) verticalUnit = 0 := by
  exact gap2 x y z (gap3 x y z h)

theorem gap5 (x y z : ℝ) :
    (x, y, z) ∈ zeroVerticalDerivativeLocus ↔
      dot (gradient (x, y, z)) verticalUnit = 0 := by
  change
    z ^ 2 = x * y ↔ dot (gradient (x, y, z)) verticalUnit = 0
  constructor
  · exact gap4 x y z
  · intro h
    have h' : 3 * z ^ 2 - 3 * x * y = 0 := by
      simpa [dot, verticalUnit, gap1] using h
    nlinarith

end

end ProofGap.Exercise4402_1
