import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology

/-!
# Exercise 41

Semantic formalization of `proof_gap/exercise_41/{1,...,11}.txt`.
The textbook indexes the sequence from one.  Lean sequences are functions on
`ℕ`; the same formula is used at zero as a harmless extension.
-/

namespace ProofGap.Exercise41

noncomputable section

def x (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)

def N (ε : ℝ) : ℕ :=
  Nat.floor (1 / ε)

def ErrorFormula : Prop :=
  ∀ n : ℕ, |x n - 1| = 1 / ((n : ℝ) + 1)

def ErrorTransfer : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    1 / ((n : ℝ) + 1) < ε → |x n - 1| < ε

def IndexEstimate : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > 1 / ε - 1 →
    1 / ((n : ℝ) + 1) < ε

def ErrorFromIndex : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > 1 / ε - 1 → |x n - 1| < ε

def ErrorFromCutoff : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    N ε < n → |x n - 1| < ε

def Converges : Prop :=
  Tendsto x atTop (𝓝 1)

/-- Source: `proof_gap/exercise_41/1.txt`. -/
theorem gap1 : ErrorFormula := by
  intro n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hx : x n - 1 = -(1 / ((n : ℝ) + 1)) := by
    unfold x
    field_simp
    ring
  rw [hx, abs_neg, abs_of_pos (one_div_pos.mpr hden)]

/-- Source: `proof_gap/exercise_41/2.txt`. -/
theorem gap2
    (h1 : ErrorFormula) :
    ErrorTransfer := by
  intro n ε hε hn
  rw [h1 n]
  exact hn

/-- Source: `proof_gap/exercise_41/3.txt`. -/
theorem gap3
    (h2 : ErrorTransfer) :
    IndexEstimate := by
  intro n ε hε hn
  have hrecip : 1 / ε < (n : ℝ) + 1 := by linarith
  have hprod : 1 < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hrecip
  apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
  simpa [mul_comm] using hprod

/-- Source: `proof_gap/exercise_41/4.txt`. -/
theorem gap4
    (h2 : ErrorTransfer)
    (h3 : IndexEstimate) :
    ErrorFromIndex := by
  intro n ε hε hn
  exact h2 n ε hε (h3 n ε hε hn)

/-- Source: `proof_gap/exercise_41/5.txt`. -/
theorem gap5
    (h4 : ErrorFromIndex) :
    ErrorFromCutoff := by
  intro n ε hε hn
  apply h4 n ε hε
  unfold N at hn
  have hsuc : Nat.floor (1 / ε) + 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor (1 / ε) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hsuc
  have hfloor :
      1 / ε < ((Nat.floor (1 / ε) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one (1 / ε)
  linarith

/-- Source: `proof_gap/exercise_41/6.txt`. -/
theorem gap6
    (h5 : ErrorFromCutoff) :
    N (0.1 : ℝ) = 10 := by
  norm_num [N]

/-- Source: `proof_gap/exercise_41/7.txt`. -/
theorem gap7
    (h5 : ErrorFromCutoff)
    (h6 : N (0.1 : ℝ) = 10) :
    N (0.01 : ℝ) = 100 := by
  norm_num [N]

/-- Source: `proof_gap/exercise_41/8.txt`. -/
theorem gap8
    (h5 : ErrorFromCutoff)
    (h7 : N (0.01 : ℝ) = 100) :
    N (0.001 : ℝ) = 1000 := by
  norm_num [N]

/-- Source: `proof_gap/exercise_41/9.txt`. -/
theorem gap9
    (h5 : ErrorFromCutoff)
    (h8 : N (0.001 : ℝ) = 1000) :
    N (0.0001 : ℝ) = 10000 := by
  norm_num [N]

/-- Source: `proof_gap/exercise_41/10.txt`. -/
theorem gap10
    (h5 : ErrorFromCutoff) :
    Converges := by
  simpa [Converges, x] using
    (tendsto_natCast_div_add_atTop (1 : ℝ))

/-- Source: `proof_gap/exercise_41/11.txt`. -/
theorem gap11
    (h10 : Converges) :
    Converges := by
  exact h10

end

end ProofGap.Exercise41
