import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4412

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def cross (a b : Vec3) : Vec3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
    a.2.2 * b.1 - a.1 * b.2.2,
    a.1 * b.2.1 - a.2.1 * b.1)

def crossSquared (c p : Vec3) : ℝ :=
  let w := cross c p
  w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def scaleVec (s : ℝ) (v : Vec3) : Vec3 :=
  (s * v.1, s * v.2.1, s * v.2.2)

def subVec (a b : Vec3) : Vec3 :=
  (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

theorem gap1 (c p : Vec3) :
    gradient (crossSquared c) p =
      (2 * c.2.2 * (c.2.2 * p.1 - c.1 * p.2.2) -
          2 * c.2.1 * (c.1 * p.2.1 - c.2.1 * p.1),
        -2 * c.2.2 * (c.2.1 * p.2.2 - c.2.2 * p.2.1) +
          2 * c.1 * (c.1 * p.2.1 - c.2.1 * p.1),
        2 * c.2.1 * (c.2.1 * p.2.2 - c.2.2 * p.2.1) -
          2 * c.1 * (c.2.2 * p.1 - c.1 * p.2.2)) := by
  apply Prod.ext
  · change
      deriv
          (fun x : ℝ =>
            (c.2.1 * p.2.2 - c.2.2 * p.2.1) ^ 2 +
                (c.2.2 * x - c.1 * p.2.2) ^ 2 +
              (c.1 * p.2.1 - c.2.1 * x) ^ 2)
          p.1 =
        2 * c.2.2 * (c.2.2 * p.1 - c.1 * p.2.2) -
          2 * c.2.1 * (c.1 * p.2.1 - c.2.1 * p.1)
    have ha :=
      hasDerivAt_const p.1 (c.2.1 * p.2.2 - c.2.2 * p.2.1)
    have hb0 : HasDerivAt (fun x : ℝ => c.2.2 * x) c.2.2 p.1 := by
      convert (hasDerivAt_const p.1 c.2.2).mul (hasDerivAt_id p.1) using 1 <;>
        ring
    have hb := hb0.sub_const (c.1 * p.2.2)
    have hc0 : HasDerivAt (fun x : ℝ => c.2.1 * x) c.2.1 p.1 := by
      convert (hasDerivAt_const p.1 c.2.1).mul (hasDerivAt_id p.1) using 1 <;>
        ring
    have hc :=
      (hasDerivAt_const p.1 (c.1 * p.2.1)).sub hc0
    have h :
        HasDerivAt
          (fun x : ℝ =>
            (c.2.1 * p.2.2 - c.2.2 * p.2.1) ^ 2 +
                (c.2.2 * x - c.1 * p.2.2) ^ 2 +
              (c.1 * p.2.1 - c.2.1 * x) ^ 2)
          (2 * c.2.2 * (c.2.2 * p.1 - c.1 * p.2.2) -
            2 * c.2.1 * (c.1 * p.2.1 - c.2.1 * p.1))
          p.1 := by
      convert (((ha.mul ha).add (hb.mul hb)).add (hc.mul hc)) using 1
      · funext x
        dsimp
        ring
      · dsimp
        ring
    exact h.deriv
  · apply Prod.ext
    · change
        deriv
            (fun y : ℝ =>
              (c.2.1 * p.2.2 - c.2.2 * y) ^ 2 +
                  (c.2.2 * p.1 - c.1 * p.2.2) ^ 2 +
                (c.1 * y - c.2.1 * p.1) ^ 2)
            p.2.1 =
          -2 * c.2.2 * (c.2.1 * p.2.2 - c.2.2 * p.2.1) +
            2 * c.1 * (c.1 * p.2.1 - c.2.1 * p.1)
      have ha0 : HasDerivAt (fun y : ℝ => c.2.2 * y) c.2.2 p.2.1 := by
        convert (hasDerivAt_const p.2.1 c.2.2).mul (hasDerivAt_id p.2.1) using 1 <;>
          ring
      have ha :=
        (hasDerivAt_const p.2.1 (c.2.1 * p.2.2)).sub ha0
      have hb :=
        hasDerivAt_const p.2.1 (c.2.2 * p.1 - c.1 * p.2.2)
      have hc0 : HasDerivAt (fun y : ℝ => c.1 * y) c.1 p.2.1 := by
        convert (hasDerivAt_const p.2.1 c.1).mul (hasDerivAt_id p.2.1) using 1 <;>
          ring
      have hc := hc0.sub_const (c.2.1 * p.1)
      have h :
          HasDerivAt
            (fun y : ℝ =>
              (c.2.1 * p.2.2 - c.2.2 * y) ^ 2 +
                  (c.2.2 * p.1 - c.1 * p.2.2) ^ 2 +
                (c.1 * y - c.2.1 * p.1) ^ 2)
            (-2 * c.2.2 * (c.2.1 * p.2.2 - c.2.2 * p.2.1) +
              2 * c.1 * (c.1 * p.2.1 - c.2.1 * p.1))
            p.2.1 := by
        convert (((ha.mul ha).add (hb.mul hb)).add (hc.mul hc)) using 1
        · funext y
          dsimp
          ring
        · dsimp
          ring
      exact h.deriv
    · change
        deriv
            (fun z : ℝ =>
              (c.2.1 * z - c.2.2 * p.2.1) ^ 2 +
                  (c.2.2 * p.1 - c.1 * z) ^ 2 +
                (c.1 * p.2.1 - c.2.1 * p.1) ^ 2)
            p.2.2 =
          2 * c.2.1 * (c.2.1 * p.2.2 - c.2.2 * p.2.1) -
            2 * c.1 * (c.2.2 * p.1 - c.1 * p.2.2)
      have ha0 : HasDerivAt (fun z : ℝ => c.2.1 * z) c.2.1 p.2.2 := by
        convert (hasDerivAt_const p.2.2 c.2.1).mul (hasDerivAt_id p.2.2) using 1 <;>
          ring
      have ha := ha0.sub_const (c.2.2 * p.2.1)
      have hb0 : HasDerivAt (fun z : ℝ => c.1 * z) c.1 p.2.2 := by
        convert (hasDerivAt_const p.2.2 c.1).mul (hasDerivAt_id p.2.2) using 1 <;>
          ring
      have hb :=
        (hasDerivAt_const p.2.2 (c.2.2 * p.1)).sub hb0
      have hc :=
        hasDerivAt_const p.2.2 (c.1 * p.2.1 - c.2.1 * p.1)
      have h :
          HasDerivAt
            (fun z : ℝ =>
              (c.2.1 * z - c.2.2 * p.2.1) ^ 2 +
                  (c.2.2 * p.1 - c.1 * z) ^ 2 +
                (c.1 * p.2.1 - c.2.1 * p.1) ^ 2)
            (2 * c.2.1 * (c.2.1 * p.2.2 - c.2.2 * p.2.1) -
              2 * c.1 * (c.2.2 * p.1 - c.1 * p.2.2))
            p.2.2 := by
        convert (((ha.mul ha).add (hb.mul hb)).add (hc.mul hc)) using 1
        · funext z
          dsimp
          ring
        · dsimp
          ring
      exact h.deriv

theorem gap2 (c p : Vec3) :
    gradient (crossSquared c) p =
      subVec (scaleVec (2 * dot c c) p)
        (scaleVec (2 * dot c p) c) := by
  rw [gap1 c p]
  apply Prod.ext
  · simp only [subVec, scaleVec, dot]
    ring
  · apply Prod.ext
    · simp only [subVec, scaleVec, dot]
      ring
    · simp only [subVec, scaleVec, dot]
      ring

end

end ProofGap.Exercise4412
