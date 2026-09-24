import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology

/-!
# Exercise 41

Semantic formalization of Exercise 41, gaps 1,...,11.
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

/-- Exercise 41, gap 1. -/
theorem gap1 : ErrorFormula := by
  intro n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hx : x n - 1 = -(1 / ((n : ℝ) + 1)) := by
    unfold x
    field_simp
    ring
  rw [hx, abs_neg, abs_of_pos (one_div_pos.mpr hden)]

/-- Exercise 41, gap 2. -/
theorem gap2
    (h1 : ErrorFormula) :
    ErrorTransfer := by
  intro n ε hε hn
  rw [h1 n]
  exact hn

/-- Exercise 41, gap 3. -/
theorem gap3
    (h2 : ErrorTransfer) :
    IndexEstimate := by
  intro n ε hε hn
  have hrecip : 1 / ε < (n : ℝ) + 1 := by linarith
  have hprod : 1 < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hrecip
  apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
  simpa [mul_comm] using hprod

/-- Exercise 41, gap 4. -/
theorem gap4
    (h2 : ErrorTransfer)
    (h3 : IndexEstimate) :
    ErrorFromIndex := by
  intro n ε hε hn
  exact h2 n ε hε (h3 n ε hε hn)

/-- Exercise 41, gap 5. -/
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

/-- Exercise 41, gap 6. -/
theorem gap6
    (h5 : ErrorFromCutoff) :
    N (0.1 : ℝ) = 10 := by
  norm_num [N]

/-- Exercise 41, gap 7. -/
theorem gap7
    (h5 : ErrorFromCutoff)
    (h6 : N (0.1 : ℝ) = 10) :
    N (0.01 : ℝ) = 100 := by
  norm_num [N]

/-- Exercise 41, gap 8. -/
theorem gap8
    (h5 : ErrorFromCutoff)
    (h7 : N (0.01 : ℝ) = 100) :
    N (0.001 : ℝ) = 1000 := by
  norm_num [N]

/-- Exercise 41, gap 9. -/
theorem gap9
    (h5 : ErrorFromCutoff)
    (h8 : N (0.001 : ℝ) = 1000) :
    N (0.0001 : ℝ) = 10000 := by
  norm_num [N]

/-- Exercise 41, gap 10. -/
theorem gap10
    (h5 : ErrorFromCutoff) :
    Converges := by
  simpa [Converges, x] using
    (tendsto_natCast_div_add_atTop (1 : ℝ))

/-- Exercise 41, gap 11. -/
theorem gap11
    (h10 : Converges) :
    Converges := by
  exact h10

end

end ProofGap.Exercise41
