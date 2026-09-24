import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4409_3

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def inverseRadius (p : Vec3) : ℝ :=
  1 / radius p

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

private theorem radius_sq_pos (p : Vec3) (h : p ≠ (0, 0, 0)) :
    0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
  rcases p with ⟨x, y, z⟩
  dsimp at h ⊢
  by_contra hn
  have hle : x ^ 2 + y ^ 2 + z ^ 2 ≤ 0 := le_of_not_gt hn
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  apply h
  simp [hx, hy, hz]

private theorem hasDerivAt_sqrt_add_sq_add (a x b : ℝ)
    (h : 0 < a + x ^ 2 + b) :
    HasDerivAt (fun t : ℝ => Real.sqrt (a + t ^ 2 + b))
      (x / Real.sqrt (a + x ^ 2 + b)) x := by
  have hp : HasDerivAt (fun t : ℝ => a + t ^ 2 + b) (2 * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_add a).add_const b using 1 <;>
      norm_num <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt h)).comp x hp
  convert hs using 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 h)]

private theorem deriv_one_div {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hfx : f x ≠ 0) :
    deriv (fun y => 1 / f y) x =
      (-1 / f x ^ 2) * deriv f x := by
  have hi :
      deriv (fun y => 1 / f y) x = -deriv f x / f x ^ 2 := by
    simpa [one_div] using (hf.hasDerivAt.inv hfx).deriv
  calc
    deriv (fun y => 1 / f y) x = -deriv f x / f x ^ 2 := hi
    _ = (-1 / f x ^ 2) * deriv f x := by ring

theorem gap1 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    gradient inverseRadius p =
      scaleVec (-1 / radius p ^ 2) (gradient radius p) := by
  have hq := radius_sq_pos p h
  have hrpos : 0 < radius p := by
    simpa [radius] using (Real.sqrt_pos.2 hq)
  have hrne : radius p ≠ 0 := ne_of_gt hrpos
  have hfx :
      HasDerivAt (fun x : ℝ => radius (x, p.2.1, p.2.2))
        (p.1 / radius p) p.1 := by
    simpa [radius, add_assoc] using
      (hasDerivAt_sqrt_add_sq_add 0 p.1
        (p.2.1 ^ 2 + p.2.2 ^ 2) (by simpa [add_assoc] using hq))
  have hfy :
      HasDerivAt (fun y : ℝ => radius (p.1, y, p.2.2))
        (p.2.1 / radius p) p.2.1 := by
    simpa [radius, add_assoc] using
      (hasDerivAt_sqrt_add_sq_add (p.1 ^ 2) p.2.1
        (p.2.2 ^ 2) (by simpa [add_assoc] using hq))
  have hfz :
      HasDerivAt (fun z : ℝ => radius (p.1, p.2.1, z))
        (p.2.2 / radius p) p.2.2 := by
    simpa only [radius, add_zero] using
      (hasDerivAt_sqrt_add_sq_add (p.1 ^ 2 + p.2.1 ^ 2) p.2.2
        0 (by simpa only [add_zero] using hq))
  have hx :
      partialX inverseRadius p =
        (-1 / radius p ^ 2) * partialX radius p := by
    simpa [partialX, inverseRadius] using
      (deriv_one_div hfx.differentiableAt hrne)
  have hy :
      partialY inverseRadius p =
        (-1 / radius p ^ 2) * partialY radius p := by
    simpa [partialY, inverseRadius] using
      (deriv_one_div hfy.differentiableAt hrne)
  have hz :
      partialZ inverseRadius p =
        (-1 / radius p ^ 2) * partialZ radius p := by
    simpa [partialZ, inverseRadius] using
      (deriv_one_div hfz.differentiableAt hrne)
  simpa only [gradient, scaleVec, hx, hy, hz]

theorem gap2 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    scaleVec (-1 / radius p ^ 2) (gradient radius p) =
      scaleVec (-1 / radius p ^ 3) (radialVector p) := by
  have hq := radius_sq_pos p h
  have hrpos : 0 < radius p := by
    simpa [radius] using (Real.sqrt_pos.2 hq)
  have hrne : radius p ≠ 0 := ne_of_gt hrpos
  have hfx :
      HasDerivAt (fun x : ℝ => radius (x, p.2.1, p.2.2))
        (p.1 / radius p) p.1 := by
    simpa [radius, add_assoc] using
      (hasDerivAt_sqrt_add_sq_add 0 p.1
        (p.2.1 ^ 2 + p.2.2 ^ 2) (by simpa [add_assoc] using hq))
  have hfy :
      HasDerivAt (fun y : ℝ => radius (p.1, y, p.2.2))
        (p.2.1 / radius p) p.2.1 := by
    simpa [radius, add_assoc] using
      (hasDerivAt_sqrt_add_sq_add (p.1 ^ 2) p.2.1
        (p.2.2 ^ 2) (by simpa [add_assoc] using hq))
  have hfz :
      HasDerivAt (fun z : ℝ => radius (p.1, p.2.1, z))
        (p.2.2 / radius p) p.2.2 := by
    simpa only [radius, add_zero] using
      (hasDerivAt_sqrt_add_sq_add (p.1 ^ 2 + p.2.1 ^ 2) p.2.2
        0 (by simpa only [add_zero] using hq))
  have hx : partialX radius p = p.1 / radius p := by
    simpa [partialX] using hfx.deriv
  have hy : partialY radius p = p.2.1 / radius p := by
    simpa [partialY] using hfy.deriv
  have hz : partialZ radius p = p.2.2 / radius p := by
    simpa [partialZ] using hfz.deriv
  have hmul (x : ℝ) :
      (-1 / radius p ^ 2) * (x / radius p) =
        (-1 / radius p ^ 3) * x := by
    field_simp [hrne]
  simpa only [gradient, scaleVec, radialVector, hx, hy, hz, hmul]

end

end ProofGap.Exercise4409_3
