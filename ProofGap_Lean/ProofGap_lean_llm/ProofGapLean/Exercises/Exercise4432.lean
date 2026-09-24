import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise4432

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (F q).1) p +
    partialY (fun q => (F q).2.1) p +
      partialZ (fun q => (F q).2.2) p

def inverseSquareField (k : ℝ) (p : Vec3) : Vec3 :=
  (k * p.1 / radius p ^ 3,
    k * p.2.1 / radius p ^ 3,
    k * p.2.2 / radius p ^ 3)

def inverseSquarePartialSum (k : ℝ) (p : Vec3) : ℝ :=
  partialX (fun q => (inverseSquareField k q).1) p +
    partialY (fun q => (inverseSquareField k q).2.1) p +
      partialZ (fun q => (inverseSquareField k q).2.2) p

def inverseSquareDivergence (k : ℝ) (p : Vec3) : ℝ :=
  divergence (inverseSquareField k) p

private theorem sumSquaresPos (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
  rcases p with ⟨x, y, z⟩
  dsimp at hp ⊢
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hz : 0 ≤ z ^ 2 := sq_nonneg z
  by_contra h
  have hx0 : x = 0 := by nlinarith
  have hy0 : y = 0 := by nlinarith
  have hz0 : z = 0 := by nlinarith
  subst x
  subst y
  subst z
  exact hp rfl

private theorem inverseSquareComponentDeriv
    (k x a b : ℝ) (h : 0 < a + x ^ 2 + b) :
    deriv (fun t => k * t / (Real.sqrt (a + t ^ 2 + b)) ^ 3) x =
      k * (1 / (Real.sqrt (a + x ^ 2 + b)) ^ 3 -
        3 * x ^ 2 / (Real.sqrt (a + x ^ 2 + b)) ^ 5) := by
  have harg : a + x ^ 2 + b ≠ 0 := ne_of_gt h
  have hsqrt : Real.sqrt (a + x ^ 2 + b) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 h)
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hinner : HasDerivAt (fun t => a + t ^ 2 + b) (2 * x) x := by
    simpa only [zero_add] using
      ((hasDerivAt_const x a).add hsq).add_const b
  have hsqrtDeriv :
      HasDerivAt (fun t : ℝ => Real.sqrt (a + t ^ 2 + b))
        (1 / (2 * Real.sqrt (a + x ^ 2 + b)) * (2 * x)) x :=
    (Real.hasDerivAt_sqrt harg).comp x hinner
  have hnum : HasDerivAt (fun t => k * t) k x := by
    simpa only [zero_mul, one_mul, zero_add, mul_one, id_eq] using
      (hasDerivAt_const x k).mul (hasDerivAt_id x)
  have hquot :
      HasDerivAt
        (fun t : ℝ => k * t / (Real.sqrt (a + t ^ 2 + b)) ^ 3) _ x :=
    hnum.div (hsqrtDeriv.pow 3) (pow_ne_zero 3 hsqrt)
  calc
    deriv (fun t => k * t / (Real.sqrt (a + t ^ 2 + b)) ^ 3) x = _ :=
      hquot.deriv
    _ = k * (1 / (Real.sqrt (a + x ^ 2 + b)) ^ 3 -
        3 * x ^ 2 / (Real.sqrt (a + x ^ 2 + b)) ^ 5) := by
      field_simp [hsqrt]
      <;> ring

theorem gap1 (k : ℝ) (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    inverseSquareDivergence k p = inverseSquarePartialSum k p := by
  rfl

theorem gap2 (k : ℝ) (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    inverseSquareDivergence k p =
      k *
        ((1 / radius p ^ 3 - 3 * p.1 ^ 2 / radius p ^ 5) +
          (1 / radius p ^ 3 - 3 * p.2.1 ^ 2 / radius p ^ 5) +
          (1 / radius p ^ 3 - 3 * p.2.2 ^ 2 / radius p ^ 5)) := by
  rcases p with ⟨x, y, z⟩
  have hs : 0 < x ^ 2 + y ^ 2 + z ^ 2 :=
    sumSquaresPos (x, y, z) hp
  have hdx :
      deriv (fun t => k * t / (Real.sqrt (t ^ 2 + y ^ 2 + z ^ 2)) ^ 3) x =
        k * (1 / (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 3 -
          3 * x ^ 2 / (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 5) := by
    simpa only [zero_add, add_assoc] using
      inverseSquareComponentDeriv k x 0 (y ^ 2 + z ^ 2)
        (by simpa only [zero_add, add_assoc] using hs)
  have hdy :
      deriv (fun t => k * t / (Real.sqrt (x ^ 2 + t ^ 2 + z ^ 2)) ^ 3) y =
        k * (1 / (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 3 -
          3 * y ^ 2 / (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 5) := by
    exact inverseSquareComponentDeriv k y (x ^ 2) (z ^ 2) hs
  have hdz :
      deriv (fun t => k * t / (Real.sqrt (x ^ 2 + y ^ 2 + t ^ 2)) ^ 3) z =
        k * (1 / (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 3 -
          3 * z ^ 2 / (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 5) := by
    simpa only [add_zero] using
      inverseSquareComponentDeriv k z (x ^ 2 + y ^ 2) 0
        (by simpa only [add_zero] using hs)
  simp only [inverseSquareDivergence, divergence, partialX, partialY,
    partialZ, inverseSquareField, radius]
  rw [hdx, hdy, hdz]
  ring

theorem gap3 (k : ℝ) (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    inverseSquareDivergence k p =
      k *
        (3 / radius p ^ 3 -
          3 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) /
            radius p ^ 5) := by
  rw [gap2 k p hp]
  ring

theorem gap4 (k : ℝ) (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    k *
        (3 / radius p ^ 3 -
          3 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) /
            radius p ^ 5) =
      k * (3 / radius p ^ 3 - 3 / radius p ^ 3) := by
  have hs : 0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 :=
    sumSquaresPos p hp
  have hrpos : 0 < radius p := by
    simpa [radius] using Real.sqrt_pos.2 hs
  have hrne : radius p ≠ 0 := ne_of_gt hrpos
  have hrsq :
      radius p ^ 2 = p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
    simpa [radius] using Real.sq_sqrt (le_of_lt hs)
  have hsum :
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = radius p ^ 2 :=
    hrsq.symm
  rw [hsum]
  field_simp [hrne]
  <;> ring

theorem gap5 (k : ℝ) (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    k * (3 / radius p ^ 3 - 3 / radius p ^ 3) = 0 := by
  ring

theorem gap6 (k : ℝ) (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    inverseSquareDivergence k p = 0 := by
  calc
    inverseSquareDivergence k p =
        k *
          (3 / radius p ^ 3 -
            3 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) /
              radius p ^ 5) := gap3 k p hp
    _ = k * (3 / radius p ^ 3 - 3 / radius p ^ 3) := gap4 k p hp
    _ = 0 := gap5 k p hp

end

end ProofGap.Exercise4432
