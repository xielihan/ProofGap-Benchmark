import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise768

noncomputable section

def quadraticMap (x : ℝ) : ℝ := 2 * x - x ^ 2
def inverseFiber (y : ℝ) : Set ℝ := {x | quadraticMap x = y}
def lowerBranch (y : ℝ) : ℝ := 1 - Real.sqrt (1 - y)
def upperBranch (y : ℝ) : ℝ := 1 + Real.sqrt (1 - y)

/-- Source: `proof_gap/exercise_768/1.txt`; replace the false universal
equation by an implication from `y=2x-x²`. -/
theorem gap1 (x y : ℝ) (h : y = quadraticMap x) :
    x ^ 2 - 2 * x + y = 0 := by
  unfold quadraticMap at h
  nlinarith

/-- Source: `proof_gap/exercise_768/2.txt`; interpret `±` as a disjunction and
add `y≤1`. -/
theorem gap2 (x y : ℝ) (hy : y ≤ 1)
    (h : x ^ 2 - 2 * x + y = 0) :
    x = (2 - Real.sqrt (4 - 4 * y)) / 2 ∨
      x = (2 + Real.sqrt (4 - 4 * y)) / 2 := by
  have hdisc : 0 ≤ 4 - 4 * y := by
    linarith
  have hsqrt : (Real.sqrt (4 - 4 * y)) ^ 2 = 4 - 4 * y :=
    Real.sq_sqrt hdisc
  have hprod :
      (2 * x - 2 - Real.sqrt (4 - 4 * y)) *
          (2 * x - 2 + Real.sqrt (4 - 4 * y)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · right
    linarith
  · left
    linarith

/-- Source: `proof_gap/exercise_768/3.txt`; split the two meanings of `±`. -/
theorem gap3 (y : ℝ) (hy : y ≤ 1) :
    (2 - Real.sqrt (4 - 4 * y)) / 2 = lowerBranch y ∧
      (2 + Real.sqrt (4 - 4 * y)) / 2 = upperBranch y := by
  have hone : 0 ≤ 1 - y := by
    linarith
  have hdisc : 0 ≤ 4 - 4 * y := by
    linarith
  have hsone : (Real.sqrt (1 - y)) ^ 2 = 1 - y :=
    Real.sq_sqrt hone
  have hsdisc : (Real.sqrt (4 - 4 * y)) ^ 2 = 4 - 4 * y :=
    Real.sq_sqrt hdisc
  have hprod :
      (Real.sqrt (4 - 4 * y) - 2 * Real.sqrt (1 - y)) *
          (Real.sqrt (4 - 4 * y) + 2 * Real.sqrt (1 - y)) = 0 := by
    nlinarith
  have hsqrt : Real.sqrt (4 - 4 * y) = 2 * Real.sqrt (1 - y) := by
    rcases mul_eq_zero.mp hprod with hminus | hplus
    · linarith
    · have hdnonneg : 0 ≤ Real.sqrt (4 - 4 * y) := Real.sqrt_nonneg _
      have honenonneg : 0 ≤ Real.sqrt (1 - y) := Real.sqrt_nonneg _
      linarith
  constructor
  · unfold lowerBranch
    linarith
  · unfold upperBranch
    linarith

/-- Source: `proof_gap/exercise_768/4.txt`; add the defining quadratic
equation. -/
theorem gap4 (x y : ℝ) (hy : y ≤ 1)
    (h : quadraticMap x = y) :
    x = lowerBranch y ∨ x = upperBranch y := by
  have hroots := gap2 x y hy (gap1 x y h.symm)
  have hbranches := gap3 y hy
  rcases hroots with hx | hx
  · left
    calc
      x = (2 - Real.sqrt (4 - 4 * y)) / 2 := hx
      _ = lowerBranch y := hbranches.1
  · right
    calc
      x = (2 + Real.sqrt (4 - 4 * y)) / 2 := hx
      _ = upperBranch y := hbranches.2

/-- Source: `proof_gap/exercise_768/5.txt`; represent the inverse of a
non-injective function as a fiber-valued map. -/
theorem gap5 (y : ℝ) (hy : y ≤ 1) :
    inverseFiber y = {lowerBranch y, upperBranch y} := by
  apply Set.ext
  intro x
  simp only [inverseFiber, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro hx
    exact gap4 x y hy hx
  · intro hx
    have hone : 0 ≤ 1 - y := by
      linarith
    have hsqrt : (Real.sqrt (1 - y)) ^ 2 = 1 - y :=
      Real.sq_sqrt hone
    rcases hx with hx | hx
    · rw [hx]
      unfold quadraticMap lowerBranch
      nlinarith
    · rw [hx]
      unfold quadraticMap upperBranch
      nlinarith

end

end ProofGap.Exercise768
