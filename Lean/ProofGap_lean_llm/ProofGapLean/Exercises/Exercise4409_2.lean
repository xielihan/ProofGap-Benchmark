import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise4409_2

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def radiusSquared (p : Vec3) : ℝ :=
  radius p ^ 2

def radialVector (p : Vec3) : Vec3 :=
  p

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def scaleVec (c : ℝ) (v : Vec3) : Vec3 :=
  (c * v.1, c * v.2.1, c * v.2.2)

private theorem sum_sq_pos (x y z : ℝ)
    (h : (x, y, z) ≠ ((0, 0, 0) : Vec3)) :
    0 < x ^ 2 + y ^ 2 + z ^ 2 := by
  by_contra hn
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  apply h
  simp [hx, hy, hz]

private theorem hasDerivAt_sqrt_sq_add (x a b : ℝ)
    (h : 0 < x ^ 2 + a ^ 2 + b ^ 2) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + a ^ 2 + b ^ 2))
      (x / Real.sqrt (x ^ 2 + a ^ 2 + b ^ 2)) x := by
  have hinner :
      HasDerivAt (fun t : ℝ => t ^ 2 + a ^ 2 + b ^ 2) (2 * x) x := by
    simpa [add_assoc] using
      (((hasDerivAt_id x).pow 2).add_const (a ^ 2 + b ^ 2))
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + a ^ 2 + b ^ 2))
        ((1 / (2 * Real.sqrt (x ^ 2 + a ^ 2 + b ^ 2))) * (2 * x)) x :=
    (Real.hasDerivAt_sqrt (ne_of_gt h)).comp x hinner
  convert hsqrt using 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 h)]
  <;> ring

private theorem radius_hasDerivs (p : Vec3) (h : p ≠ (0, 0, 0)) :
    HasDerivAt (fun x => radius (x, p.2.1, p.2.2))
        (p.1 / radius p) p.1 ∧
      HasDerivAt (fun y => radius (p.1, y, p.2.2))
        (p.2.1 / radius p) p.2.1 ∧
      HasDerivAt (fun z => radius (p.1, p.2.1, z))
        (p.2.2 / radius p) p.2.2 := by
  rcases p with ⟨x, y, z⟩
  have hp : 0 < x ^ 2 + y ^ 2 + z ^ 2 := sum_sq_pos x y z h
  constructor
  · simpa [radius] using hasDerivAt_sqrt_sq_add x y z hp
  constructor
  · have hp' : 0 < y ^ 2 + x ^ 2 + z ^ 2 := by nlinarith
    simpa [radius, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_sqrt_sq_add y x z hp'
  · have hp' : 0 < z ^ 2 + x ^ 2 + y ^ 2 := by nlinarith
    simpa [radius, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_sqrt_sq_add z x y hp'

theorem gap1 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    gradient radiusSquared p =
      scaleVec (2 * radius p) (gradient radius p) := by
  rcases radius_hasDerivs p h with ⟨hx, hy, hz⟩
  apply Prod.ext
  · change
      deriv (fun t => radius (t, p.2.1, p.2.2) ^ 2) p.1 =
        (2 * radius p) * deriv (fun t => radius (t, p.2.1, p.2.2)) p.1
    simpa [hx.deriv] using (hx.pow 2).deriv
  · apply Prod.ext
    · change
        deriv (fun t => radius (p.1, t, p.2.2) ^ 2) p.2.1 =
          (2 * radius p) * deriv (fun t => radius (p.1, t, p.2.2)) p.2.1
      simpa [hy.deriv] using (hy.pow 2).deriv
    · change
        deriv (fun t => radius (p.1, p.2.1, t) ^ 2) p.2.2 =
          (2 * radius p) * deriv (fun t => radius (p.1, p.2.1, t)) p.2.2
      simpa [hz.deriv] using (hz.pow 2).deriv

theorem gap2 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    scaleVec (2 * radius p) (gradient radius p) =
      scaleVec (2 * radius p)
        (scaleVec (1 / radius p) (radialVector p)) := by
  rcases radius_hasDerivs p h with ⟨hx, hy, hz⟩
  apply Prod.ext
  · change
      (2 * radius p) * deriv (fun t => radius (t, p.2.1, p.2.2)) p.1 =
        (2 * radius p) * ((1 / radius p) * p.1)
    rw [hx.deriv]
    ring
  · apply Prod.ext
    · change
        (2 * radius p) * deriv (fun t => radius (p.1, t, p.2.2)) p.2.1 =
          (2 * radius p) * ((1 / radius p) * p.2.1)
      rw [hy.deriv]
      ring
    · change
        (2 * radius p) * deriv (fun t => radius (p.1, p.2.1, t)) p.2.2 =
          (2 * radius p) * ((1 / radius p) * p.2.2)
      rw [hz.deriv]
      ring

theorem gap3 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    scaleVec (2 * radius p)
        (scaleVec (1 / radius p) (radialVector p)) =
      scaleVec 2 (radialVector p) := by
  rcases p with ⟨x, y, z⟩
  have hr : radius (x, y, z) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sum_sq_pos x y z h))
  apply Prod.ext
  · change
      (2 * radius (x, y, z)) * ((1 / radius (x, y, z)) * x) = 2 * x
    field_simp [hr]
  · apply Prod.ext
    · change
        (2 * radius (x, y, z)) * ((1 / radius (x, y, z)) * y) = 2 * y
      field_simp [hr]
    · change
        (2 * radius (x, y, z)) * ((1 / radius (x, y, z)) * z) = 2 * z
      field_simp [hr]

end

end ProofGap.Exercise4409_2
