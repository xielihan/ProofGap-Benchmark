import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3621

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + (p.2 - 1) ^ 2

def partialX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => g (x, p.2)) p.1

def partialY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => g (p.1, y)) p.2

def basePoint : ℝ × ℝ :=
  (0, 1)

def IsUniqueGlobalMinimizer
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  (∀ q, g p ≤ g q) ∧ (∀ q, g q = g p → q = p)

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ ({basePoint} : Set (ℝ × ℝ)) →
      partialX z p = 2 * p.1 ∧ 2 * p.1 = 0 ∧
      partialY z p = 2 * (p.2 - 1) ∧ 2 * (p.2 - 1) = 0 := by
  intro p hp
  have hp' : p = basePoint := by
    simpa using hp
  subst p
  have hxderiv :
      HasDerivAt (fun x : ℝ => z (x, basePoint.2)) 0 0 := by
    simpa [z, basePoint, pow_two] using
      ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ)))
  have hyderiv :
      HasDerivAt (fun y : ℝ => z (basePoint.1, y)) 0 1 := by
    have h := (hasDerivAt_id (1 : ℝ)).sub_const 1
    simpa [z, basePoint, pow_two] using h.mul h
  have hx : partialX z basePoint = 0 := by
    simpa [partialX, basePoint] using hxderiv.deriv
  have hy : partialY z basePoint = 0 := by
    simpa [partialY, basePoint] using hyderiv.deriv
  constructor
  · simpa [basePoint] using hx
  constructor
  · simp [basePoint]
  constructor
  · simpa [basePoint] using hy
  · simp [basePoint]

theorem gap2 :
    basePoint = (0, 1) := by
  rfl

theorem gap3 :
    z basePoint = 0 := by
  simp [z, basePoint]

theorem gap4 :
    ∀ p : ℝ × ℝ, p ≠ basePoint → 0 < z p := by
  rintro ⟨x, y⟩ hp
  change 0 < x ^ 2 + (y - 1) ^ 2
  by_cases hx : x = 0
  · have hy : y - 1 ≠ 0 := by
      intro hyzero
      apply hp
      apply Prod.ext
      · simpa [basePoint] using hx
      · simpa [basePoint] using (sub_eq_zero.mp hyzero)
    exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hy)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg (y - 1))

theorem gap5 :
    IsUniqueGlobalMinimizer z basePoint := by
  constructor
  · intro q
    rw [gap3]
    simpa [z] using
      add_nonneg (sq_nonneg q.1) (sq_nonneg (q.2 - 1))
  · intro q hq
    classical
    by_contra hne
    have hpos : 0 < z q := gap4 q hne
    have hz : z q = 0 := hq.trans gap3
    rw [hz] at hpos
    exact (lt_irrefl 0 hpos)

theorem gap6 :
    z basePoint = 0 := by
  exact gap3

end

end ProofGap.Exercise3621
