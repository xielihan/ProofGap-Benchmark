import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3559

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def firstLevelFunction (b : ℝ) (p : Point3) : ℝ :=
  p.x * p.y - b * p.z

def secondLevelFunction (p : Point3) : ℝ :=
  p.x ^ 2 + p.y ^ 2

def normal1 (b : ℝ) (p : Point3) : Point3 :=
  ⟨deriv (fun t => firstLevelFunction b ⟨t, p.y, p.z⟩) p.x,
    deriv (fun t => firstLevelFunction b ⟨p.x, t, p.z⟩) p.y,
    deriv (fun t => firstLevelFunction b ⟨p.x, p.y, t⟩) p.z⟩

def normal2 (p : Point3) : Point3 :=
  ⟨deriv (fun t => secondLevelFunction ⟨t, p.y, p.z⟩) p.x,
    deriv (fun t => secondLevelFunction ⟨p.x, t, p.z⟩) p.y,
    deriv (fun t => secondLevelFunction ⟨p.x, p.y, t⟩) p.z⟩

def dot (u v : Point3) : ℝ :=
  u.x * v.x + u.y * v.y + u.z * v.z

def norm (u : Point3) : ℝ :=
  Real.sqrt (u.x ^ 2 + u.y ^ 2 + u.z ^ 2)

def angleCosine (b : ℝ) (p : Point3) : ℝ :=
  dot (normal1 b p) (normal2 p) /
    (norm (normal1 b p) * norm (normal2 p))

def onIntersection (a b : ℝ) (p : Point3) : Prop :=
  p.x ^ 2 + p.y ^ 2 = a ^ 2 ∧ b * p.z = p.x * p.y

theorem gap1 (b : ℝ) :
    ∀ p : Point3, normal1 b p = ⟨p.y, p.x, -b⟩ := by
  intro p
  cases p with
  | mk x y z =>
    have hxy :=
      (((hasDerivAt_id x).mul_const y).sub_const (b * z))
    have hyx :=
      (((hasDerivAt_id y).const_mul x).sub_const (b * z))
    have hzb :=
      ((hasDerivAt_const z (x * y)).sub
        ((hasDerivAt_id z).const_mul b))
    have hx : deriv (fun t : ℝ => t * y - b * z) x = y := by
      simpa using hxy.deriv
    have hy : deriv (fun t : ℝ => x * t - b * z) y = x := by
      simpa using hyx.deriv
    have hz : deriv (fun t : ℝ => x * y - b * t) z = -b := by
      simpa using hzb.deriv
    change Point3.mk (deriv (fun t : ℝ => t * y - b * z) x)
      (deriv (fun t : ℝ => x * t - b * z) y)
      (deriv (fun t : ℝ => x * y - b * t) z) = Point3.mk y x (-b)
    rw [hx, hy, hz]

theorem gap2 :
    ∀ p : Point3, normal2 p = ⟨2 * p.x, 2 * p.y, 0⟩ := by
  intro p
  cases p with
  | mk x y z =>
    have hxSq :=
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).add_const (y ^ 2))
    have hySq :=
      ((hasDerivAt_const y (x ^ 2)).add
        ((hasDerivAt_id y).mul (hasDerivAt_id y)))
    have hzConst :=
      (hasDerivAt_const z (x ^ 2 + y ^ 2))
    have hx : deriv (fun t : ℝ => t ^ 2 + y ^ 2) x = 2 * x := by
      simpa [pow_two, two_mul] using hxSq.deriv
    have hy : deriv (fun t : ℝ => x ^ 2 + t ^ 2) y = 2 * y := by
      simpa [pow_two, two_mul] using hySq.deriv
    have hz : deriv (fun _t : ℝ => x ^ 2 + y ^ 2) z = 0 := by
      simpa using hzConst.deriv
    change Point3.mk (deriv (fun t : ℝ => t ^ 2 + y ^ 2) x)
      (deriv (fun t : ℝ => x ^ 2 + t ^ 2) y)
      (deriv (fun _t : ℝ => x ^ 2 + y ^ 2) z) = Point3.mk (2 * x) (2 * y) 0
    rw [hx, hy, hz]

theorem gap3 (b : ℝ) :
    ∀ p : Point3,
      angleCosine b p =
        dot (normal1 b p) (normal2 p) /
          (norm (normal1 b p) * norm (normal2 p)) := by
  intro p
  rfl

theorem gap4 (b : ℝ) :
    ∀ p : Point3,
      dot (normal1 b p) (normal2 p) /
          (norm (normal1 b p) * norm (normal2 p)) =
        (2 * p.x * p.y + 2 * p.x * p.y + 0) /
          (Real.sqrt (p.x ^ 2 + p.y ^ 2 + b ^ 2) *
            Real.sqrt (4 * p.x ^ 2 + 4 * p.y ^ 2)) := by
  intro p
  rw [gap1 b p, gap2 p]
  simp only [dot, norm]
  have hnum :
      p.y * (2 * p.x) + p.x * (2 * p.y) + (-b) * 0 =
        2 * p.x * p.y + 2 * p.x * p.y + 0 := by
    ring
  have hn1 :
      p.y ^ 2 + p.x ^ 2 + (-b) ^ 2 =
        p.x ^ 2 + p.y ^ 2 + b ^ 2 := by
    ring
  have hn2 :
      (2 * p.x) ^ 2 + (2 * p.y) ^ 2 + (0 : ℝ) ^ 2 =
        4 * p.x ^ 2 + 4 * p.y ^ 2 := by
    ring
  rw [hnum, hn1, hn2]

theorem gap5 (a b : ℝ) (ha : 0 < a) :
    ∀ p : Point3, onIntersection a b p →
      (2 * p.x * p.y + 2 * p.x * p.y + 0) /
          (Real.sqrt (p.x ^ 2 + p.y ^ 2 + b ^ 2) *
            Real.sqrt (4 * p.x ^ 2 + 4 * p.y ^ 2)) =
        (4 * b * p.z) /
          (Real.sqrt (a ^ 2 + b ^ 2) * (2 * a)) := by
  intro p hp
  have hnum :
      2 * p.x * p.y + 2 * p.x * p.y + 0 = 4 * b * p.z := by
    calc
      2 * p.x * p.y + 2 * p.x * p.y + 0 = 4 * (p.x * p.y) := by ring
      _ = 4 * (b * p.z) := by rw [← hp.2]
      _ = 4 * b * p.z := by ring
  have hfirst :
      p.x ^ 2 + p.y ^ 2 + b ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hp.1]
  have harg :
      4 * p.x ^ 2 + 4 * p.y ^ 2 = (2 * a) ^ 2 := by
    calc
      4 * p.x ^ 2 + 4 * p.y ^ 2 = 4 * (p.x ^ 2 + p.y ^ 2) := by ring
      _ = 4 * a ^ 2 := by rw [hp.1]
      _ = (2 * a) ^ 2 := by ring
  have hsqrt :
      Real.sqrt (4 * p.x ^ 2 + 4 * p.y ^ 2) = 2 * a := by
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (by norm_num) ha)]
  rw [hnum, hfirst, hsqrt]

theorem gap6 (a b : ℝ) :
    ∀ p : Point3,
      (4 * b * p.z) /
          (Real.sqrt (a ^ 2 + b ^ 2) * (2 * a)) =
        (2 * b * p.z) /
          (a * Real.sqrt (a ^ 2 + b ^ 2)) := by
  intro p
  by_cases ha : a = 0
  · simp [ha]
  · have hsum : 0 < a ^ 2 + b ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg b)
    have hsqrt : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hsum)
    field_simp [ha, hsqrt] <;> ring

theorem gap7 (a b : ℝ) (ha : 0 < a) :
    ∀ p : Point3, onIntersection a b p →
      angleCosine b p =
        (2 * b * p.z) /
          (a * Real.sqrt (a ^ 2 + b ^ 2)) := by
  intro p hp
  rw [gap3 b p, gap4 b p, gap5 a b ha p hp, gap6 a b p]

end

end ProofGap.Exercise3559
