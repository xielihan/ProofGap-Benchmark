import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4409_1

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

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

private lemma radius_sq_pos (p : Vec3) (h : p ≠ (0, 0, 0)) :
    0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
  rcases p with ⟨x, y, z⟩
  simp only
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

theorem gap1 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    HasDerivAt (fun x => radius (x, p.2.1, p.2.2))
      (p.1 / radius p) p.1 := by
  have hs := radius_sq_pos p h
  have hpoly :
      HasDerivAt
        (fun x : ℝ => x ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)
        (2 * p.1) p.1 := by
    simpa using
      (((hasDerivAt_id p.1).pow 2).add_const (p.2.1 ^ 2)).add_const
        (p.2.2 ^ 2)
  have hr : Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hs)
  have hcoef :
      (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))⁻¹ * (2 : ℝ)⁻¹ *
          (2 * p.1) =
        p.1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
    field_simp [hr]
    <;> ring
  have hcomp :=
    (Real.hasDerivAt_sqrt (ne_of_gt hs)).comp p.1 hpoly
  simpa [radius, Function.comp_def, hcoef] using hcomp

theorem gap2 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    HasDerivAt (fun y => radius (p.1, y, p.2.2))
      (p.2.1 / radius p) p.2.1 := by
  have hs := radius_sq_pos p h
  have hpoly :
      HasDerivAt
        (fun y : ℝ => p.1 ^ 2 + y ^ 2 + p.2.2 ^ 2)
        (2 * p.2.1) p.2.1 := by
    simpa using
      ((hasDerivAt_const p.2.1 (p.1 ^ 2)).add
        ((hasDerivAt_id p.2.1).pow 2)).add_const (p.2.2 ^ 2)
  have hr : Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hs)
  have hcoef :
      (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))⁻¹ * (2 : ℝ)⁻¹ *
          (2 * p.2.1) =
        p.2.1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
    field_simp [hr]
    <;> ring
  have hcomp :=
    (Real.hasDerivAt_sqrt (ne_of_gt hs)).comp p.2.1 hpoly
  simpa [radius, Function.comp_def, hcoef] using hcomp

theorem gap3 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    HasDerivAt (fun z => radius (p.1, p.2.1, z))
      (p.2.2 / radius p) p.2.2 := by
  have hs := radius_sq_pos p h
  have hsq :
      HasDerivAt (fun z : ℝ => z ^ 2) (2 * p.2.2) p.2.2 := by
    simpa using (hasDerivAt_id p.2.2).pow 2
  have hpoly :
      HasDerivAt
        (fun z : ℝ => p.1 ^ 2 + p.2.1 ^ 2 + z ^ 2)
        (2 * p.2.2) p.2.2 :=
    hsq.const_add (p.1 ^ 2 + p.2.1 ^ 2)
  have hr : Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hs)
  have hcoef :
      (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))⁻¹ * (2 : ℝ)⁻¹ *
          (2 * p.2.2) =
        p.2.2 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
    field_simp [hr]
    <;> ring
  have hcomp :=
    (Real.hasDerivAt_sqrt (ne_of_gt hs)).comp p.2.2 hpoly
  simpa [radius, Function.comp_def, hcoef] using hcomp

theorem gap4 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    gradient radius p = scaleVec (1 / radius p) (radialVector p) := by
  unfold gradient scaleVec radialVector partialX partialY partialZ
  rw [(gap1 p h).deriv, (gap2 p h).deriv, (gap3 p h).deriv]
  simp [div_eq_mul_inv, mul_comm]

end

end ProofGap.Exercise4409_1
