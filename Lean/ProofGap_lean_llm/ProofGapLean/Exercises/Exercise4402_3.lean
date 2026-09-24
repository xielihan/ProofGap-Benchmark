import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4402_3

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

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def diagonalCriticalLocus : Set Vec3 :=
  {p | p.1 = p.2.1 ∧ p.2.1 = p.2.2}

private theorem norm3_eq_zero_iff_components (a b c : ℝ) :
    norm3 (a, b, c) = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  change Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) = 0 ↔
    a = 0 ∧ b = 0 ∧ c = 0
  constructor
  · intro h
    have hnonneg : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hsqrt := Real.sq_sqrt hnonneg
    have hsum : a ^ 2 + b ^ 2 + c ^ 2 = 0 := by
      nlinarith
    refine ⟨?_, ?_, ?_⟩ <;>
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem gap1 (x y z : ℝ) :
    gradient (x, y, z) =
      (3 * x ^ 2 - 3 * y * z,
        3 * y ^ 2 - 3 * x * z,
        3 * z ^ 2 - 3 * x * y) := by
  have hxCubeRaw :
      HasDerivAt (fun t : ℝ => (t * t) * t)
        (((1 : ℝ) * x + x * 1) * x + (x * x) * 1) x :=
    ((hasDerivAt_id x).mul (hasDerivAt_id x)).mul (hasDerivAt_id x)
  have hxCube :
      HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    convert hxCubeRaw using 1 <;> ring
  have hxProd :
      HasDerivAt (fun t : ℝ => 3 * t * y * z) (3 * y * z) x := by
    simpa using
      ((((hasDerivAt_const x (3 : ℝ)).mul (hasDerivAt_id x)).mul
        (hasDerivAt_const x y)).mul (hasDerivAt_const x z))
  have hx :
      HasDerivAt (fun t : ℝ => u (t, y, z))
        (3 * x ^ 2 - 3 * y * z) x := by
    simpa [u] using
      (((hxCube.add (hasDerivAt_const x (y ^ 3))).add
        (hasDerivAt_const x (z ^ 3))).sub hxProd)
  have hyCubeRaw :
      HasDerivAt (fun t : ℝ => (t * t) * t)
        (((1 : ℝ) * y + y * 1) * y + (y * y) * 1) y :=
    ((hasDerivAt_id y).mul (hasDerivAt_id y)).mul (hasDerivAt_id y)
  have hyCube :
      HasDerivAt (fun t : ℝ => t ^ 3) (3 * y ^ 2) y := by
    convert hyCubeRaw using 1 <;> ring
  have hyProd :
      HasDerivAt (fun t : ℝ => 3 * x * t * z) (3 * x * z) y := by
    simpa using
      ((((hasDerivAt_const y (3 : ℝ)).mul (hasDerivAt_const y x)).mul
        (hasDerivAt_id y)).mul (hasDerivAt_const y z))
  have hy :
      HasDerivAt (fun t : ℝ => u (x, t, z))
        (3 * y ^ 2 - 3 * x * z) y := by
    simpa [u] using
      ((((hasDerivAt_const y (x ^ 3)).add hyCube).add
        (hasDerivAt_const y (z ^ 3))).sub hyProd)
  have hzCubeRaw :
      HasDerivAt (fun t : ℝ => (t * t) * t)
        (((1 : ℝ) * z + z * 1) * z + (z * z) * 1) z :=
    ((hasDerivAt_id z).mul (hasDerivAt_id z)).mul (hasDerivAt_id z)
  have hzCube :
      HasDerivAt (fun t : ℝ => t ^ 3) (3 * z ^ 2) z := by
    convert hzCubeRaw using 1 <;> ring
  have hzProd :
      HasDerivAt (fun t : ℝ => 3 * x * y * t) (3 * x * y) z := by
    simpa using
      ((((hasDerivAt_const z (3 : ℝ)).mul (hasDerivAt_const z x)).mul
        (hasDerivAt_const z y)).mul (hasDerivAt_id z))
  have hz :
      HasDerivAt (fun t : ℝ => u (x, y, t))
        (3 * z ^ 2 - 3 * x * y) z := by
    simpa [u] using
      ((((hasDerivAt_const z (x ^ 3)).add
        (hasDerivAt_const z (y ^ 3))).add hzCube).sub hzProd)
  change
    (deriv (fun t : ℝ => u (t, y, z)) x,
      deriv (fun t : ℝ => u (x, t, z)) y,
      deriv (fun t : ℝ => u (x, y, t)) z) = _
  rw [hx.deriv, hy.deriv, hz.deriv]

theorem gap2 (x y z : ℝ) :
    norm3 (gradient (x, y, z)) = 0 ↔
      3 * x ^ 2 - 3 * y * z = 0 ∧
        3 * y ^ 2 - 3 * x * z = 0 ∧
          3 * z ^ 2 - 3 * x * y = 0 := by
  rw [gap1]
  exact norm3_eq_zero_iff_components _ _ _

theorem gap3 (x y z : ℝ)
    (h : norm3 (gradient (x, y, z)) = 0) :
    3 * x ^ 2 - 3 * y * z = 0 := by
  exact ((gap2 x y z).mp h).1

theorem gap4 (x y z : ℝ)
    (h : norm3 (gradient (x, y, z)) = 0) :
    3 * y ^ 2 - 3 * x * z = 0 := by
  exact ((gap2 x y z).mp h).2.1

theorem gap5 (x y z : ℝ)
    (h : norm3 (gradient (x, y, z)) = 0) :
    3 * z ^ 2 - 3 * x * y = 0 := by
  exact ((gap2 x y z).mp h).2.2

theorem gap6 (x y z : ℝ)
    (h : norm3 (gradient (x, y, z)) = 0) :
    x = y := by
  rcases (gap2 x y z).mp h with ⟨hx, hy, hz⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z),
    sq_nonneg (z - x)]

theorem gap7 (x y z : ℝ)
    (h : norm3 (gradient (x, y, z)) = 0) :
    y = z := by
  rcases (gap2 x y z).mp h with ⟨hx, hy, hz⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z),
    sq_nonneg (z - x)]

theorem gap8 (x y z : ℝ)
    (h : norm3 (gradient (x, y, z)) = 0) :
    x = z := by
  exact (gap6 x y z h).trans (gap7 x y z h)

theorem gap9 (x y z : ℝ) :
    (x, y, z) ∈ diagonalCriticalLocus ↔
      norm3 (gradient (x, y, z)) = 0 := by
  constructor
  · intro hp
    change x = y ∧ y = z at hp
    rcases hp with ⟨hxy, hyz⟩
    subst y
    subst z
    apply (gap2 x x x).2
    constructor
    · ring
    constructor <;> ring
  · intro h
    change x = y ∧ y = z
    exact ⟨gap6 x y z h, gap7 x y z h⟩

end

end ProofGap.Exercise4402_3
