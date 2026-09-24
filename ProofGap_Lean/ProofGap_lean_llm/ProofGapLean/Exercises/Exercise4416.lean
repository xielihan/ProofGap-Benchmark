import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4416

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def ellipsoidForm (axes p : Vec3) : ℝ :=
  p.1 ^ 2 / axes.1 ^ 2 +
    p.2.1 ^ 2 / axes.2.1 ^ 2 +
      p.2.2 ^ 2 / axes.2.2 ^ 2

def gradient (axes p : Vec3) : Vec3 :=
  (2 * p.1 / axes.1 ^ 2,
    2 * p.2.1 / axes.2.1 ^ 2,
    2 * p.2.2 / axes.2.2 ^ 2)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def radialUnit (p : Vec3) : Vec3 :=
  (p.1 / radius p, p.2.1 / radius p, p.2.2 / radius p)

def radialDerivative (axes p : Vec3) : ℝ :=
  dot (gradient axes p) (radialUnit p)

def AxesNonzero (axes : Vec3) : Prop :=
  axes.1 ≠ 0 ∧ axes.2.1 ≠ 0 ∧ axes.2.2 ≠ 0

def IsSpherical (axes : Vec3) : Prop :=
  axes.1 = axes.2.1 ∧ axes.2.1 = axes.2.2

theorem gap1 (axes p : Vec3) (hp : p ≠ (0, 0, 0)) :
    radialDerivative axes p =
      dot (gradient axes p) (radialUnit p) := by
  rfl

theorem gap2 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    (radialUnit p).1 = p.1 / radius p := by
  rfl

theorem gap3 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    (radialUnit p).2.1 = p.2.1 / radius p := by
  rfl

theorem gap4 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    (radialUnit p).2.2 = p.2.2 / radius p := by
  rfl

theorem gap5 (p : Vec3) :
    radius p = Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
  rfl

theorem gap6 (axes p : Vec3) (hp : p ≠ (0, 0, 0))
    (hAxes : AxesNonzero axes) :
    radialDerivative axes p =
      (2 * p.1 / axes.1 ^ 2) * (p.1 / radius p) +
        (2 * p.2.1 / axes.2.1 ^ 2) * (p.2.1 / radius p) +
          (2 * p.2.2 / axes.2.2 ^ 2) * (p.2.2 / radius p) := by
  rfl

theorem gap7 (axes p : Vec3) (hp : p ≠ (0, 0, 0))
    (hAxes : AxesNonzero axes) :
    (2 * p.1 / axes.1 ^ 2) * (p.1 / radius p) +
        (2 * p.2.1 / axes.2.1 ^ 2) * (p.2.1 / radius p) +
          (2 * p.2.2 / axes.2.2 ^ 2) * (p.2.2 / radius p) =
      2 * ellipsoidForm axes p / radius p := by
  unfold ellipsoidForm
  ring

theorem gap8 (axes p : Vec3) (hp : p ≠ (0, 0, 0))
    (hAxes : AxesNonzero axes) :
    radialDerivative axes p =
      2 * ellipsoidForm axes p / radius p := by
  calc
    radialDerivative axes p =
        (2 * p.1 / axes.1 ^ 2) * (p.1 / radius p) +
          (2 * p.2.1 / axes.2.1 ^ 2) * (p.2.1 / radius p) +
            (2 * p.2.2 / axes.2.2 ^ 2) * (p.2.2 / radius p) :=
      gap6 axes p hp hAxes
    _ = 2 * ellipsoidForm axes p / radius p := gap7 axes p hp hAxes

theorem gap9 (axes p : Vec3) (hAxes : AxesNonzero axes) :
    norm3 (gradient axes p) =
      2 * Real.sqrt
        (p.1 ^ 2 / axes.1 ^ 4 +
          p.2.1 ^ 2 / axes.2.1 ^ 4 +
          p.2.2 ^ 2 / axes.2.2 ^ 4) := by
  have ha : axes.1 ≠ 0 := hAxes.1
  have hb : axes.2.1 ≠ 0 := hAxes.2.1
  have hc : axes.2.2 ≠ 0 := hAxes.2.2
  unfold norm3 gradient
  let q : ℝ :=
    p.1 ^ 2 / axes.1 ^ 4 +
      p.2.1 ^ 2 / axes.2.1 ^ 4 +
        p.2.2 ^ 2 / axes.2.2 ^ 4
  change
    Real.sqrt
        ((2 * p.1 / axes.1 ^ 2) ^ 2 +
          (2 * p.2.1 / axes.2.1 ^ 2) ^ 2 +
            (2 * p.2.2 / axes.2.2 ^ 2) ^ 2) =
      2 * Real.sqrt q
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hs :
      (2 * p.1 / axes.1 ^ 2) ^ 2 +
          (2 * p.2.1 / axes.2.1 ^ 2) ^ 2 +
            (2 * p.2.2 / axes.2.2 ^ 2) ^ 2 =
        (2 * Real.sqrt q) ^ 2 := by
    calc
      (2 * p.1 / axes.1 ^ 2) ^ 2 +
            (2 * p.2.1 / axes.2.1 ^ 2) ^ 2 +
              (2 * p.2.2 / axes.2.2 ^ 2) ^ 2 = 4 * q := by
        dsimp [q]
        field_simp [ha, hb, hc] <;> ring
      _ = 4 * (Real.sqrt q) ^ 2 := by
        rw [Real.sq_sqrt hq]
      _ = (2 * Real.sqrt q) ^ 2 := by ring
  have hnonneg : 0 ≤ 2 * Real.sqrt q := by positivity
  calc
    Real.sqrt
        ((2 * p.1 / axes.1 ^ 2) ^ 2 +
          (2 * p.2.1 / axes.2.1 ^ 2) ^ 2 +
            (2 * p.2.2 / axes.2.2 ^ 2) ^ 2) =
      Real.sqrt ((2 * Real.sqrt q) ^ 2) := congrArg Real.sqrt hs
    _ = |2 * Real.sqrt q| := Real.sqrt_sq_eq_abs _
    _ = 2 * Real.sqrt q := abs_of_nonneg hnonneg

theorem gap10 (axes p : Vec3) (hp : p ≠ (0, 0, 0))
    (hAxes : AxesNonzero axes)
    (hRelation :
      ellipsoidForm axes p / radius p =
        Real.sqrt
          (p.1 ^ 2 / axes.1 ^ 4 +
            p.2.1 ^ 2 / axes.2.1 ^ 4 +
            p.2.2 ^ 2 / axes.2.2 ^ 4)) :
    norm3 (gradient axes p) = radialDerivative axes p := by
  calc
    norm3 (gradient axes p) =
        2 * Real.sqrt
          (p.1 ^ 2 / axes.1 ^ 4 +
            p.2.1 ^ 2 / axes.2.1 ^ 4 +
              p.2.2 ^ 2 / axes.2.2 ^ 4) := gap9 axes p hAxes
    _ = 2 * (ellipsoidForm axes p / radius p) := by rw [hRelation]
    _ = 2 * ellipsoidForm axes p / radius p := by ring
    _ = radialDerivative axes p := (gap8 axes p hp hAxes).symm

theorem gap11 (axes p : Vec3) (hp : p ≠ (0, 0, 0))
    (hAxes : AxesNonzero axes) (hSphere : IsSpherical axes) :
    ellipsoidForm axes p / radius p =
      Real.sqrt
        (p.1 ^ 2 / axes.1 ^ 4 +
          p.2.1 ^ 2 / axes.2.1 ^ 4 +
          p.2.2 ^ 2 / axes.2.2 ^ 4) := by
  have ha : axes.1 ≠ 0 := hAxes.1
  have hab : axes.1 = axes.2.1 := hSphere.1
  have hbc : axes.2.1 = axes.2.2 := hSphere.2
  rcases p with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  unfold ellipsoidForm radius
  simp only [Prod.fst, Prod.snd] at hp ⊢
  rw [← hbc, ← hab]
  have hS : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    by_contra h
    have hle : x ^ 2 + y ^ 2 + z ^ 2 ≤ 0 := le_of_not_gt h
    have hx : x = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy : y = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz : z = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    apply hp
    simp [hx, hy, hz]
  have hsqrt_sq :
      (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 =
        x ^ 2 + y ^ 2 + z ^ 2 :=
    Real.sq_sqrt (le_of_lt hS)
  have hsqrt_ne :
      Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hS)
  have hsum2 :
      x ^ 2 / axes.1 ^ 2 + y ^ 2 / axes.1 ^ 2 + z ^ 2 / axes.1 ^ 2 =
        (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 2 := by
    ring
  have hleft :
      (x ^ 2 / axes.1 ^ 2 + y ^ 2 / axes.1 ^ 2 + z ^ 2 / axes.1 ^ 2) /
          Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) =
        Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 2 := by
    calc
      (x ^ 2 / axes.1 ^ 2 + y ^ 2 / axes.1 ^ 2 + z ^ 2 / axes.1 ^ 2) /
            Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) =
          ((x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 2) /
            Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) :=
        congrArg
          (fun t : ℝ => t / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) hsum2
      _ =
          ((Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 / axes.1 ^ 2) /
            Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) :=
        congrArg
          (fun t : ℝ =>
            (t / axes.1 ^ 2) / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2))
          hsqrt_sq.symm
      _ = Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 2 := by
        field_simp [ha, hsqrt_ne] <;> ring
  have hsum4 :
      x ^ 2 / axes.1 ^ 4 + y ^ 2 / axes.1 ^ 4 + z ^ 2 / axes.1 ^ 4 =
        (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 4 := by
    ring
  have hinside :
      x ^ 2 / axes.1 ^ 4 + y ^ 2 / axes.1 ^ 4 + z ^ 2 / axes.1 ^ 4 =
        (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 2) ^ 2 := by
    calc
      x ^ 2 / axes.1 ^ 4 + y ^ 2 / axes.1 ^ 4 + z ^ 2 / axes.1 ^ 4 =
          (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 4 := hsum4
      _ = (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 / axes.1 ^ 4 :=
        congrArg (fun t : ℝ => t / axes.1 ^ 4) hsqrt_sq.symm
      _ = (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 2) ^ 2 := by
        ring
  have hquot :
      0 ≤ Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) / axes.1 ^ 2 :=
    div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  rw [hleft, hinside, Real.sqrt_sq_eq_abs, abs_of_nonneg hquot]

theorem gap12 (axes p : Vec3) (hp : p ≠ (0, 0, 0))
    (hAxes : AxesNonzero axes) (hSphere : IsSpherical axes) :
    norm3 (gradient axes p) = radialDerivative axes p := by
  exact gap10 axes p hp hAxes (gap11 axes p hp hAxes hSphere)

theorem gap13 (axes : Vec3) (hSphere : IsSpherical axes) :
    axes.1 = axes.2.1 := by
  exact hSphere.1

theorem gap14 (axes : Vec3) (hSphere : IsSpherical axes) :
    axes.2.1 = axes.2.2 := by
  exact hSphere.2

theorem gap15 (axes : Vec3) (hSphere : IsSpherical axes) :
    axes.1 = axes.2.2 := by
  exact hSphere.1.trans hSphere.2

end

end ProofGap.Exercise4416
