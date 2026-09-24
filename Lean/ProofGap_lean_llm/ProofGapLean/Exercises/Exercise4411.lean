import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4411

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def position (p : Vec3) : Vec3 :=
  p

def linearPotential (c : Vec3) (p : Vec3) : ℝ :=
  dot c (position p)

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

theorem gap1 (c p : Vec3) :
    dot c (position p) =
      c.1 * p.1 + c.2.1 * p.2.1 + c.2.2 * p.2.2 := by
  rfl

theorem gap2 (c p : Vec3) :
    HasDerivAt (fun x => linearPotential c (x, p.2.1, p.2.2))
      c.1 p.1 := by
  simpa [linearPotential, dot, position] using
    ((((hasDerivAt_const (x := p.1) (c := c.1)).mul
      (hasDerivAt_id p.1)).add_const
        (c.2.1 * p.2.1)).add_const (c.2.2 * p.2.2))

theorem gap3 (c p : Vec3) :
    HasDerivAt (fun y => linearPotential c (p.1, y, p.2.2))
      c.2.1 p.2.1 := by
  simpa [linearPotential, dot, position] using
    (((hasDerivAt_const (x := p.2.1) (c := c.1 * p.1)).add
      ((hasDerivAt_const (x := p.2.1) (c := c.2.1)).mul
        (hasDerivAt_id p.2.1))).add_const (c.2.2 * p.2.2))

theorem gap4 (c p : Vec3) :
    HasDerivAt (fun z => linearPotential c (p.1, p.2.1, z))
      c.2.2 p.2.2 := by
  simpa [linearPotential, dot, position] using
    ((hasDerivAt_const (x := p.2.2) (c := c.2.2)).mul
      (hasDerivAt_id p.2.2))

theorem gap5 (c p : Vec3) :
    gradient (linearPotential c) p = c := by
  unfold gradient partialX partialY partialZ
  rw [(gap2 c p).deriv, (gap3 c p).deriv, (gap4 c p).deriv]

end

end ProofGap.Exercise4411
