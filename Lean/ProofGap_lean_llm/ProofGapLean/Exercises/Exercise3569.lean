import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3569

noncomputable section

structure Point2 where
  x : ℝ
  y : ℝ

def familyFunction (x y p : ℝ) : ℝ :=
  y ^ 2 - 2 * p * x - p ^ 2

def parameterDerivative (x y p : ℝ) : ℝ :=
  deriv (fun t => familyFunction x y t) p

def envelopeCondition (q : Point2) (p : ℝ) : Prop :=
  familyFunction q.x q.y p = 0 ∧
    parameterDerivative q.x q.y p = 0

def envelope : Set Point2 :=
  {q | ∃ p : ℝ, envelopeCondition q p}

def originSet : Set Point2 :=
  {q | q = ⟨0, 0⟩}

private theorem parameterDerivative_formula (x y p : ℝ) :
    parameterDerivative x y p = -2 * x - 2 * p := by
  have hconst : HasDerivAt (fun _ : ℝ => y ^ 2) 0 p :=
    hasDerivAt_const p (y ^ 2)
  have hlinear : HasDerivAt (fun t : ℝ => 2 * t * x) (2 * x) p := by
    convert ((hasDerivAt_const p 2).mul (hasDerivAt_id p)).mul_const x using 1 <;> ring
  have hsquare : HasDerivAt (fun t : ℝ => t ^ 2) (2 * p) p := by
    convert ((hasDerivAt_id p).mul (hasDerivAt_id p)) using 1
    · funext t
      simp [pow_two]
    · change 2 * p = 1 * p + p * 1
      ring
  have htotal : HasDerivAt
      (fun t : ℝ => y ^ 2 - 2 * t * x - t ^ 2)
      (-2 * x - 2 * p) p := by
    convert (hconst.sub hlinear).sub hsquare using 1 <;> ring
  simpa [parameterDerivative, familyFunction] using htotal.deriv

theorem gap1 :
    ∀ q : Point2, ∀ p : ℝ, envelopeCondition q p →
      familyFunction q.x q.y p = 0 := by
  intro q p h
  exact h.1

theorem gap2 :
    ∀ q : Point2, ∀ p : ℝ, envelopeCondition q p →
      parameterDerivative q.x q.y p = 0 := by
  intro q p h
  exact h.2

theorem gap3 :
    ∀ x y p : ℝ, familyFunction x y p = 0 →
      y ^ 2 - 2 * p * x - p ^ 2 = 0 := by
  intro x y p h
  simpa [familyFunction] using h

theorem gap4 :
    ∀ x y p : ℝ, parameterDerivative x y p = 0 →
      -2 * x - 2 * p = 0 := by
  intro x y p h
  rw [parameterDerivative_formula] at h
  exact h

theorem gap5 :
    ∀ x y p : ℝ, y ^ 2 - 2 * p * x - p ^ 2 = 0 →
      2 * p * x - y ^ 2 + p ^ 2 = 0 := by
  intro x y p h
  linarith

theorem gap6 :
    ∀ x p : ℝ, -2 * x - 2 * p = 0 →
      x + p = 0 := by
  intro x p h
  linarith

theorem gap7 :
    ∀ x y p : ℝ,
      y ^ 2 - 2 * p * x - p ^ 2 = 0 →
      x + p = 0 →
      x ^ 2 + y ^ 2 = 0 := by
  intro x y p hfamily hparameter
  have hp : p = -x := by
    linarith
  rw [hp] at hfamily
  nlinarith

theorem gap8 :
    envelope = originSet := by
  apply Set.ext
  intro q
  constructor
  · intro hq
    change ∃ p : ℝ, envelopeCondition q p at hq
    rcases hq with ⟨p, hp⟩
    have hfamily : familyFunction q.x q.y p = 0 := gap1 q p hp
    have hderiv : parameterDerivative q.x q.y p = 0 := gap2 q p hp
    have hpoly : q.y ^ 2 - 2 * p * q.x - p ^ 2 = 0 :=
      gap3 q.x q.y p hfamily
    have hlinear : -2 * q.x - 2 * p = 0 :=
      gap4 q.x q.y p hderiv
    have hsum : q.x + p = 0 := gap6 q.x p hlinear
    have hnorm : q.x ^ 2 + q.y ^ 2 = 0 :=
      gap7 q.x q.y p hpoly hsum
    have hx : q.x = 0 := by
      nlinarith [sq_nonneg q.x, sq_nonneg q.y]
    have hy : q.y = 0 := by
      nlinarith [sq_nonneg q.x, sq_nonneg q.y]
    change q = ⟨0, 0⟩
    cases q with
    | mk qx qy => simp_all
  · intro hq
    change q = ⟨0, 0⟩ at hq
    subst q
    change ∃ p : ℝ, envelopeCondition ⟨0, 0⟩ p
    refine ⟨0, ?_⟩
    constructor
    · simp [familyFunction]
    · simpa using (parameterDerivative_formula 0 0 0)

end

end ProofGap.Exercise3569
