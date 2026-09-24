import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

local infixl:70 " /. " => fun x y => ((x : ℝ) / (y : ℝ))

noncomputable def DefInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x in a..b, f x
noncomputable def DefIntInf (a : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x in Set.Ioi a, f x
noncomputable def seriesFrom (m : ℕ) (u : ℕ → ℝ) : ℝ := ∑' n : ℕ, if n < m then 0 else u n
def ConvergentSeries (_x : ℝ) : Prop := True
def Approx (eps x y : ℝ) : Prop := |x - y| ≤ eps

-- exercise: exercise_2623

theorem proof_gap_exercise_2623_1 (f : ℝ → ℝ) :
    ConvergentSeries (DefIntInf 1 f) := by
  sorry

theorem proof_gap_exercise_2623_2 (f : ℝ → ℝ) :
    ∀ n : ℕ, ∀ k : ℕ, 0 < n ∧ 0 < k →
      f (n + k + 1) ≤ DefInt (n + k) (n + k + 1) f := by
  sorry

theorem proof_gap_exercise_2623_3 (f : ℝ → ℝ) :
    ∀ n : ℕ, ∀ k : ℕ, 0 < n ∧ 0 < k →
      DefInt (n + k) (n + k + 1) f ≤ f (n + k) := by
  sorry

theorem proof_gap_exercise_2623_4 (f : ℝ → ℝ) :
    ∀ n : ℕ, ∀ k : ℕ, 0 < n ∧ 0 < k → f (n + k + 1) ≤ f (n + k) := by
  sorry

theorem proof_gap_exercise_2623_5 (f : ℝ → ℝ) :
    ∀ n : ℕ, 0 < n → seriesFrom 1 (fun k => f (n + k + 1)) ≤ DefIntInf (n + 1) f := by
  sorry

theorem proof_gap_exercise_2623_6 (f : ℝ → ℝ) :
    ∀ n : ℕ, 0 < n → DefIntInf (n + 1) f ≤ seriesFrom 1 (fun k => f (n + k)) := by
  sorry

theorem proof_gap_exercise_2623_7 (f : ℝ → ℝ) :
    ∀ n : ℕ, 0 < n → seriesFrom 1 (fun k => f (n + k + 1)) ≤ seriesFrom 1 (fun k => f (n + k)) := by
  sorry

theorem proof_gap_exercise_2623_8 (f : ℝ → ℝ) (R : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → R n - f (n + 1) ≤ DefIntInf (n + 1) f := by
  sorry

theorem proof_gap_exercise_2623_9 (f : ℝ → ℝ) (R : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → DefIntInf (n + 1) f ≤ R n := by
  sorry

theorem proof_gap_exercise_2623_10 (f : ℝ → ℝ) (R : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → R n - f (n + 1) ≤ R n := by
  sorry

theorem proof_gap_exercise_2623_11 (f : ℝ → ℝ) (R : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → DefIntInf (n + 1) f ≤ R n := by
  sorry

theorem proof_gap_exercise_2623_12 (f : ℝ → ℝ) (R : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → R n ≤ f (n + 1) + DefIntInf (n + 1) f := by
  sorry

theorem proof_gap_exercise_2623_13 (R : ℕ → ℝ) :
    R 8 ≤ (1 /. (9 ^ 3 : ℝ)) + DefIntInf 9 (fun x => 1 /. x ^ 3) := by
  sorry

theorem proof_gap_exercise_2623_14 :
    (1 /. (9 ^ 3 : ℝ)) + DefIntInf 9 (fun x => 1 /. x ^ 3) < 0.008 := by
  sorry

theorem proof_gap_exercise_2623_15 (R : ℕ → ℝ) :
    R 8 < 0.008 := by
  sorry

theorem proof_gap_exercise_2623_16 (T : ℝ) :
    Approx 0.01 (∑ k ∈ Finset.Icc (1 : ℕ) 8, 1 /. ((k : ℝ) ^ 3)) T := by
  sorry

theorem proof_gap_exercise_2623_17 :
    Approx 0.01 (∑ k ∈ Finset.Icc (1 : ℕ) 8, 1 /. ((k : ℝ) ^ 3)) 1.20 := by
  sorry

theorem proof_gap_exercise_2623_18 (f : ℝ → ℝ) (R : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n →
      DefIntInf (n + 1) f ≤ R n ∧ R n ≤ f (n + 1) + DefIntInf (n + 1) f := by
  sorry

theorem proof_gap_exercise_2623_19 (f : ℝ → ℝ) (R : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n →
      DefIntInf (n + 1) f ≤ R n ∧ R n ≤ f (n + 1) + DefIntInf (n + 1) f := by
  sorry
