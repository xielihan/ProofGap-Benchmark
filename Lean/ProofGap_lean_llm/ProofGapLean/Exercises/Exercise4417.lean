import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4417

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def inverseRadius (p : Vec3) : ℝ :=
  1 / radius p

def gradient (p : Vec3) : Vec3 :=
  (-p.1 / radius p ^ 3,
    -p.2.1 / radius p ^ 3,
    -p.2.2 / radius p ^ 3)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def radialUnit (p : Vec3) : Vec3 :=
  (p.1 / radius p, p.2.1 / radius p, p.2.2 / radius p)

def directionalDerivative (p l : Vec3) : ℝ :=
  dot (gradient p) l

def radialCosine (l p : Vec3) : ℝ :=
  dot l (radialUnit p)

def IsTangentDirection (l p : Vec3) : Prop :=
  dot l p = 0

private theorem sqSumPos (p : Vec3) (h : p ≠ (0, 0, 0)) :
    0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
  rcases p with ⟨x, y, z⟩
  simp only [Prod.fst, Prod.snd] at h ⊢
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

private theorem radiusPos (p : Vec3) (h : p ≠ (0, 0, 0)) :
    0 < radius p := by
  unfold radius
  exact Real.sqrt_pos.2 (sqSumPos p h)

private theorem hasDerivAt_inverseSqrtSumSq
    (x y z : ℝ) (hpos : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    HasDerivAt
      (fun t : ℝ => 1 / Real.sqrt (t ^ 2 + y ^ 2 + z ^ 2))
      (-x / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 3) x := by
  have hq :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2 + z ^ 2) (2 * x) x := by
    convert ((((hasDerivAt_id x).pow 2).add_const (y ^ 2)).add_const (z ^ 2)) using 1 <;>
      simp [id] <;> ring
  have hs :
      HasDerivAt
        (fun t : ℝ => Real.sqrt (t ^ 2 + y ^ 2 + z ^ 2))
        (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) * (2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hpos.ne').comp x hq
  have hsqrt_ne : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hi := hs.inv hsqrt_ne
  have hderiv :
      -(1 / (2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) * (2 * x)) /
          Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 =
        -x / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
    field_simp [hsqrt_ne]
    <;> ring
  rw [hderiv] at hi
  simpa only [Function.comp_apply, one_div] using hi

theorem gap1 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    HasDerivAt (fun x => inverseRadius (x, p.2.1, p.2.2))
      (-p.1 / radius p ^ 3) p.1 := by
  simpa [inverseRadius, radius] using
    hasDerivAt_inverseSqrtSumSq p.1 p.2.1 p.2.2 (sqSumPos p h)

theorem gap2 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    HasDerivAt (fun y => inverseRadius (p.1, y, p.2.2))
      (-p.2.1 / radius p ^ 3) p.2.1 := by
  simpa [inverseRadius, radius, add_comm, add_left_comm, add_assoc] using
    hasDerivAt_inverseSqrtSumSq p.2.1 p.1 p.2.2 (by
      simpa [add_comm, add_left_comm, add_assoc] using sqSumPos p h)

theorem gap3 (p : Vec3) (h : p ≠ (0, 0, 0)) :
    HasDerivAt (fun z => inverseRadius (p.1, p.2.1, z))
      (-p.2.2 / radius p ^ 3) p.2.2 := by
  simpa [inverseRadius, radius, add_comm, add_left_comm, add_assoc] using
    hasDerivAt_inverseSqrtSumSq p.2.2 p.1 p.2.1 (by
      simpa [add_comm, add_left_comm, add_assoc] using sqSumPos p h)

theorem gap4 (p l : Vec3) (h : p ≠ (0, 0, 0)) :
    directionalDerivative p l =
      -p.1 / radius p ^ 3 * l.1 -
        p.2.1 / radius p ^ 3 * l.2.1 -
          p.2.2 / radius p ^ 3 * l.2.2 := by
  unfold directionalDerivative gradient dot
  ring

theorem gap5 (p l : Vec3) (h : p ≠ (0, 0, 0)) :
    directionalDerivative p l =
      (-1 / radius p ^ 2) * dot (radialUnit p) l := by
  have hr : radius p ≠ 0 := (radiusPos p h).ne'
  unfold directionalDerivative gradient dot radialUnit
  field_simp [hr]
  <;> ring

theorem gap6 (p l : Vec3) (h : p ≠ (0, 0, 0)) :
    (-1 / radius p ^ 2) * dot (radialUnit p) l =
      -radialCosine l p / radius p ^ 2 := by
  have hr : radius p ≠ 0 := (radiusPos p h).ne'
  unfold radialCosine radialUnit dot
  field_simp [hr]
  <;> ring

theorem gap7 (p l : Vec3) (h : p ≠ (0, 0, 0)) :
    directionalDerivative p l =
      -radialCosine l p / radius p ^ 2 := by
  calc
    directionalDerivative p l =
        (-1 / radius p ^ 2) * dot (radialUnit p) l := gap5 p l h
    _ = -radialCosine l p / radius p ^ 2 := gap6 p l h

theorem gap8 (p l : Vec3) (hp : p ≠ (0, 0, 0))
    (h : radialCosine l p = 0) :
    directionalDerivative p l = 0 := by
  simpa [h] using gap7 p l hp

theorem gap9 (p l : Vec3) (hp : p ≠ (0, 0, 0))
    (hOrthogonal : dot l p = 0) :
    radialCosine l p = 0 := by
  have hr : radius p ≠ 0 := (radiusPos p hp).ne'
  have hscale : radialCosine l p = dot l p / radius p := by
    unfold radialCosine radialUnit dot
    field_simp [hr]
    <;> ring
  rw [hscale, hOrthogonal]
  simp

theorem gap10 (p l : Vec3) (hp : p ≠ (0, 0, 0))
    (hOrthogonal : dot l p = 0) :
    directionalDerivative p l = 0 := by
  apply gap8 p l hp
  exact gap9 p l hp hOrthogonal

theorem gap11 (p l : Vec3) (hTangent : IsTangentDirection l p) :
    dot l p = 0 := by
  simpa [IsTangentDirection] using hTangent

end

end ProofGap.Exercise4417
