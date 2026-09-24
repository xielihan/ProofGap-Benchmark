import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.Ring

/-!
# Exercise 3

Semantic formalization of `proof_gap/exercise_3/{1,...,9}.txt`.

All finite sums are indexed by natural numbers and evaluated in `ℚ`.  This
matches the ordinary meaning of the source fractions while keeping the discrete
summation bounds explicit.
-/

namespace ProofGap.Exercise3

def sumCubes (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ 3

def sumNaturals (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, (i : ℚ)

def CubesFormula (n : ℕ) : Prop :=
  sumCubes n = (sumNaturals n) ^ 2

def BaseCase : Prop :=
  ∀ n : ℕ, n = 1 → CubesFormula n

def SuccessorSumStep : Prop :=
  ∀ k n : ℕ, CubesFormula k → n = k + 1 →
    sumCubes (k + 1) = (sumNaturals k) ^ 2 + ((k : ℚ) + 1) ^ 3

def ReplaceNaturalSum : Prop :=
  ∀ k n : ℕ, CubesFormula k → n = k + 1 →
    (sumNaturals k) ^ 2 + ((k : ℚ) + 1) ^ 3 =
      ((k : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 2) / 4 + ((k : ℚ) + 1) ^ 3

def FactorSuccessor : Prop :=
  ∀ k n : ℕ, CubesFormula k → n = k + 1 →
    ((k : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 2) / 4 + ((k : ℚ) + 1) ^ 3 =
      (((k : ℚ) + 1) ^ 2 * ((k : ℚ) + 2) ^ 2) / 4

def RewriteAsTriangularSquare : Prop :=
  ∀ k n : ℕ, CubesFormula k → n = k + 1 →
    (((k : ℚ) + 1) ^ 2 * ((k : ℚ) + 2) ^ 2) / 4 =
      ((((k : ℚ) + 1) * ((k : ℚ) + 2)) / 2) ^ 2

def IdentifySuccessorNaturalSum : Prop :=
  ∀ k n : ℕ, CubesFormula k → n = k + 1 →
    ((((k : ℚ) + 1) * ((k : ℚ) + 2)) / 2) ^ 2 =
      (sumNaturals (k + 1)) ^ 2

def InductionStep : Prop :=
  ∀ k n : ℕ, CubesFormula k → n = k + 1 → CubesFormula (k + 1)

private theorem sumCubes_succ (k : ℕ) :
    sumCubes (k + 1) = sumCubes k + ((k : ℚ) + 1) ^ 3 := by
  have hnot : k + 1 ∉ Finset.Icc 1 k := by
    simp
  have hset :
      Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [sumCubes, sumCubes, hset, Finset.sum_insert hnot]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem sumNaturals_eq (k : ℕ) :
    sumNaturals k = (k : ℚ) * ((k : ℚ) + 1) / 2 := by
  induction k with
  | zero => norm_num [sumNaturals]
  | succ k ih =>
      have hnot : k + 1 ∉ Finset.Icc 1 k := by
        simp
      have hset :
          Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [sumNaturals, hset, Finset.sum_insert hnot, ← sumNaturals, ih]
      push_cast
      ring

/-- Source: `proof_gap/exercise_3/1.txt`. -/
theorem gap1 : BaseCase := by
  intro n hn
  subst n
  norm_num [CubesFormula, sumCubes, sumNaturals]

/-- Source: `proof_gap/exercise_3/2.txt`. -/
theorem gap2
    (h1 : BaseCase) :
    SuccessorSumStep := by
  intro k n hCn hn
  change sumCubes k = (sumNaturals k) ^ 2 at hCn
  rw [sumCubes_succ, hCn]

/-- Source: `proof_gap/exercise_3/3.txt`. -/
theorem gap3
    (h1 : BaseCase)
    (h2 : SuccessorSumStep) :
    ReplaceNaturalSum := by
  intro k n hCn hn
  rw [sumNaturals_eq k]
  ring

/-- Source: `proof_gap/exercise_3/4.txt`. -/
theorem gap4
    (h1 : BaseCase)
    (h2 : SuccessorSumStep)
    (h3 : ReplaceNaturalSum) :
    FactorSuccessor := by
  intro k n hCn hn
  ring

/-- Source: `proof_gap/exercise_3/5.txt`. -/
theorem gap5
    (h1 : BaseCase)
    (h2 : SuccessorSumStep)
    (h3 : ReplaceNaturalSum)
    (h4 : FactorSuccessor) :
    RewriteAsTriangularSquare := by
  intro k n hCn hn
  ring

/-- Source: `proof_gap/exercise_3/6.txt`. -/
theorem gap6
    (h1 : BaseCase)
    (h2 : SuccessorSumStep)
    (h3 : ReplaceNaturalSum)
    (h4 : FactorSuccessor)
    (h5 : RewriteAsTriangularSquare) :
    IdentifySuccessorNaturalSum := by
  intro k n hCn hn
  rw [sumNaturals_eq (k + 1)]
  push_cast
  ring

/-- Source: `proof_gap/exercise_3/7.txt`. -/
theorem gap7
    (h1 : BaseCase)
    (h2 : SuccessorSumStep)
    (h3 : ReplaceNaturalSum)
    (h4 : FactorSuccessor)
    (h5 : RewriteAsTriangularSquare)
    (h6 : IdentifySuccessorNaturalSum) :
    InductionStep := by
  intro k n hCn hn
  change sumCubes (k + 1) = (sumNaturals (k + 1)) ^ 2
  calc
    sumCubes (k + 1) = (sumNaturals k) ^ 2 + ((k : ℚ) + 1) ^ 3 := h2 k n hCn hn
    _ = ((k : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 2) / 4 + ((k : ℚ) + 1) ^ 3 :=
      h3 k n hCn hn
    _ = (((k : ℚ) + 1) ^ 2 * ((k : ℚ) + 2) ^ 2) / 4 := h4 k n hCn hn
    _ = ((((k : ℚ) + 1) * ((k : ℚ) + 2)) / 2) ^ 2 := h5 k n hCn hn
    _ = (sumNaturals (k + 1)) ^ 2 := h6 k n hCn hn

/-- Source: `proof_gap/exercise_3/8.txt`. -/
theorem gap8
    (h1 : BaseCase)
    (h2 : SuccessorSumStep)
    (h3 : ReplaceNaturalSum)
    (h4 : FactorSuccessor)
    (h5 : RewriteAsTriangularSquare)
    (h6 : IdentifySuccessorNaturalSum)
    (h7 : InductionStep) :
    ∀ n : ℕ, CubesFormula n := by
  intro n
  induction n with
  | zero => norm_num [CubesFormula, sumCubes, sumNaturals]
  | succ k ih => exact h7 k (k + 1) ih rfl

/--
Source: `proof_gap/exercise_3/9.txt`.

The goal repeats the immediately preceding result and is retained as a distinct
benchmark item.
-/
theorem gap9
    (h1 : BaseCase)
    (h2 : SuccessorSumStep)
    (h3 : ReplaceNaturalSum)
    (h4 : FactorSuccessor)
    (h5 : RewriteAsTriangularSquare)
    (h6 : IdentifySuccessorNaturalSum)
    (h7 : InductionStep)
    (h8 : ∀ n : ℕ, CubesFormula n) :
    ∀ n : ℕ, CubesFormula n := by
  exact h8

end ProofGap.Exercise3
