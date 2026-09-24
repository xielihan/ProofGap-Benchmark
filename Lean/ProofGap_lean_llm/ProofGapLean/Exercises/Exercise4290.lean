import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4290

noncomputable section

abbrev Point3 := ℝ × ℝ × ℝ

def field (p : Point3) : Point3 :=
  (p.1 ^ 2 - 2 * p.2.1 * p.2.2,
    p.2.1 ^ 2 - 2 * p.1 * p.2.2,
    p.2.2 ^ 2 - 2 * p.1 * p.2.1)

def potential (p : Point3) : ℝ :=
  (p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3) / 3 -
    2 * p.1 * p.2.1 * p.2.2

def coordinateDifferential (V v : Point3) : ℝ :=
  V.1 * v.1 + V.2.1 * v.2.1 + V.2.2 * v.2.2

def differential (F : Point3 → ℝ) (p v : Point3) : ℝ :=
  deriv (fun x => F (x, p.2.1, p.2.2)) p.1 * v.1 +
    deriv (fun y => F (p.1, y, p.2.2)) p.2.1 * v.2.1 +
      deriv (fun z => F (p.1, p.2.1, z)) p.2.2 * v.2.2

def decomposedDifferential (p v : Point3) : ℝ :=
  p.1 ^ 2 * v.1 + p.2.1 ^ 2 * v.2.1 + p.2.2 ^ 2 * v.2.2 -
    2 * (p.2.1 * p.2.2 * v.1 + p.1 * p.2.2 * v.2.1 +
      p.1 * p.2.1 * v.2.2)

def HasCoordinateGradientAt
    (F : Point3 → ℝ) (V : Point3) (p : Point3) : Prop :=
  HasDerivAt (fun x => F (x, p.2.1, p.2.2)) V.1 p.1 ∧
    HasDerivAt (fun y => F (p.1, y, p.2.2)) V.2.1 p.2.1 ∧
      HasDerivAt (fun z => F (p.1, p.2.1, z)) V.2.2 p.2.2

def IsSolution (u : Point3 → ℝ) : Prop :=
  ∀ p, HasCoordinateGradientAt u (field p) p

private theorem potential_hasCoordinateGradientAt (p : Point3) :
    HasCoordinateGradientAt potential (field p) p := by
  unfold HasCoordinateGradientAt
  constructor
  · change HasDerivAt
      (fun x : ℝ =>
        (x ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3) / 3 -
          2 * x * p.2.1 * p.2.2)
      (p.1 ^ 2 - 2 * p.2.1 * p.2.2) p.1
    have hcube : HasDerivAt (fun x : ℝ => x ^ 3) (3 * p.1 ^ 2) p.1 := by
      convert
        ((hasDerivAt_id p.1).mul (hasDerivAt_id p.1)).mul
          (hasDerivAt_id p.1) using 1
      · funext x
        change x ^ 3 = x * x * x
        ring
      · simp [id_eq] <;> ring_nf
    have hpoly : HasDerivAt
        (fun x : ℝ => (x ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3) / 3)
        (p.1 ^ 2) p.1 := by
      convert
        ((hcube.add_const (p.2.1 ^ 3)).add_const
          (p.2.2 ^ 3)).div_const 3 using 1 <;> ring
    have hlinear : HasDerivAt
        (fun x : ℝ => 2 * x * p.2.1 * p.2.2)
        (2 * p.2.1 * p.2.2) p.1 := by
      convert
        ((((hasDerivAt_id p.1).const_mul 2).mul_const p.2.1).mul_const
          p.2.2) using 1 <;> ring
    exact hpoly.sub hlinear
  · constructor
    · change HasDerivAt
        (fun y : ℝ =>
          (p.1 ^ 3 + y ^ 3 + p.2.2 ^ 3) / 3 -
            2 * p.1 * y * p.2.2)
        (p.2.1 ^ 2 - 2 * p.1 * p.2.2) p.2.1
      have hcube : HasDerivAt (fun y : ℝ => y ^ 3)
          (3 * p.2.1 ^ 2) p.2.1 := by
        convert
          ((hasDerivAt_id p.2.1).mul (hasDerivAt_id p.2.1)).mul
            (hasDerivAt_id p.2.1) using 1
        · funext y
          change y ^ 3 = y * y * y
          ring
        · simp [id_eq] <;> ring_nf
      have hpoly : HasDerivAt
          (fun y : ℝ => (p.1 ^ 3 + y ^ 3 + p.2.2 ^ 3) / 3)
          (p.2.1 ^ 2) p.2.1 := by
        convert
          ((hcube.const_add (p.1 ^ 3)).add_const
            (p.2.2 ^ 3)).div_const 3 using 1 <;> ring
      have hlinear : HasDerivAt
          (fun y : ℝ => 2 * p.1 * y * p.2.2)
          (2 * p.1 * p.2.2) p.2.1 := by
        convert
          (((hasDerivAt_id p.2.1).const_mul (2 * p.1)).mul_const
            p.2.2) using 1 <;> ring
      exact hpoly.sub hlinear
    · change HasDerivAt
        (fun z : ℝ =>
          (p.1 ^ 3 + p.2.1 ^ 3 + z ^ 3) / 3 -
            2 * p.1 * p.2.1 * z)
        (p.2.2 ^ 2 - 2 * p.1 * p.2.1) p.2.2
      have hcube : HasDerivAt (fun z : ℝ => z ^ 3)
          (3 * p.2.2 ^ 2) p.2.2 := by
        convert
          ((hasDerivAt_id p.2.2).mul (hasDerivAt_id p.2.2)).mul
            (hasDerivAt_id p.2.2) using 1
        · funext z
          change z ^ 3 = z * z * z
          ring
        · simp [id_eq] <;> ring_nf
      have hpoly : HasDerivAt
          (fun z : ℝ => (p.1 ^ 3 + p.2.1 ^ 3 + z ^ 3) / 3)
          (p.2.2 ^ 2) p.2.2 := by
        convert
          (hcube.const_add
            (p.1 ^ 3 + p.2.1 ^ 3)).div_const 3 using 1 <;> ring
      have hlinear : HasDerivAt
          (fun z : ℝ => 2 * p.1 * p.2.1 * z)
          (2 * p.1 * p.2.1) p.2.2 := by
        convert
          ((hasDerivAt_id p.2.2).const_mul
            (2 * p.1 * p.2.1)) using 1 <;> ring
      exact hpoly.sub hlinear

theorem gap1 (u : Point3 → ℝ) (p v : Point3) :
    differential u p v = coordinateDifferential (field p) v ↔
      differential u p v = decomposedDifferential p v := by
  have hcoord :
      coordinateDifferential (field p) v = decomposedDifferential p v := by
    unfold coordinateDifferential field decomposedDifferential
    ring
  rw [hcoord]

theorem gap2 (p v : Point3) :
    decomposedDifferential p v = differential potential p v := by
  rcases potential_hasCoordinateGradientAt p with ⟨hx, hy, hz⟩
  unfold decomposedDifferential differential
  rw [hx.deriv, hy.deriv, hz.deriv]
  simp only [field]
  ring

theorem gap3 (u : Point3 → ℝ) (p v : Point3) :
    differential u p v = coordinateDifferential (field p) v ↔
      differential u p v = differential potential p v := by
  simpa only [gap2 p v] using gap1 u p v

theorem gap4 (u : Point3 → ℝ) :
    IsSolution u ↔ ∃ C : ℝ, ∀ p, u p = potential p + C := by
  constructor
  · intro hu
    refine ⟨u (0, 0, 0) - potential (0, 0, 0), ?_⟩
    intro p
    have hconst_x (b c x y : ℝ) :
        u (x, b, c) - potential (x, b, c) =
          u (y, b, c) - potential (y, b, c) := by
      let f : ℝ → ℝ := fun t => u (t, b, c) - potential (t, b, c)
      have hf (t : ℝ) : HasDerivAt f 0 t := by
        dsimp [f]
        simpa using
          ((hu (t, b, c)).1.sub
            (potential_hasCoordinateGradientAt (t, b, c)).1)
      exact is_const_of_deriv_eq_zero
        (fun t => (hf t).differentiableAt)
        (fun t => (hf t).deriv) x y
    have hconst_y (a c x y : ℝ) :
        u (a, x, c) - potential (a, x, c) =
          u (a, y, c) - potential (a, y, c) := by
      let f : ℝ → ℝ := fun t => u (a, t, c) - potential (a, t, c)
      have hf (t : ℝ) : HasDerivAt f 0 t := by
        dsimp [f]
        simpa using
          ((hu (a, t, c)).2.1.sub
            (potential_hasCoordinateGradientAt (a, t, c)).2.1)
      exact is_const_of_deriv_eq_zero
        (fun t => (hf t).differentiableAt)
        (fun t => (hf t).deriv) x y
    have hconst_z (a b x y : ℝ) :
        u (a, b, x) - potential (a, b, x) =
          u (a, b, y) - potential (a, b, y) := by
      let f : ℝ → ℝ := fun t => u (a, b, t) - potential (a, b, t)
      have hf (t : ℝ) : HasDerivAt f 0 t := by
        dsimp [f]
        simpa using
          ((hu (a, b, t)).2.2.sub
            (potential_hasCoordinateGradientAt (a, b, t)).2.2)
      exact is_const_of_deriv_eq_zero
        (fun t => (hf t).differentiableAt)
        (fun t => (hf t).deriv) x y
    have hconst :
        u p - potential p = u (0, 0, 0) - potential (0, 0, 0) := by
      calc
        u p - potential p =
            u (0, p.2.1, p.2.2) - potential (0, p.2.1, p.2.2) := by
              simpa using hconst_x p.2.1 p.2.2 p.1 0
        _ = u (0, 0, p.2.2) - potential (0, 0, p.2.2) :=
          hconst_y 0 p.2.2 p.2.1 0
        _ = u (0, 0, 0) - potential (0, 0, 0) :=
          hconst_z 0 0 p.2.2 0
    calc
      u p = potential p + (u p - potential p) := by ring
      _ = potential p + (u (0, 0, 0) - potential (0, 0, 0)) := by
        rw [hconst]
  · rintro ⟨C, hC⟩
    have hu_eq : u = fun p => potential p + C := funext hC
    rw [hu_eq]
    intro p
    rcases potential_hasCoordinateGradientAt p with ⟨hx, hy, hz⟩
    exact ⟨by simpa using hx.add_const C,
      by simpa using hy.add_const C,
      by simpa using hz.add_const C⟩

theorem gap5 (C : ℝ) :
    IsSolution (fun p => potential p + C) := by
  intro p
  rcases potential_hasCoordinateGradientAt p with ⟨hx, hy, hz⟩
  exact ⟨by simpa using hx.add_const C,
    by simpa using hy.add_const C,
    by simpa using hz.add_const C⟩

end

end ProofGap.Exercise4290
