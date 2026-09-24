import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Filter
open scoped Topology BigOperators

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def PosInt (n : ℕ) : Prop := 0 < n
def Ioo01 (x : ℝ) : Prop := 0 < x ∧ x < 1
def Icc01 (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1
def Icc0Half (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ (1 /. 2)
def seqLim (u : ℕ -> ℝ) (a : ℝ) : Prop := Tendsto u atTop (𝓝 a)
def seqTendsToTop (u : ℝ -> ℝ) : Prop := Tendsto u (𝓝[<] (1 : ℝ)) atTop
def UniformConvergentSeq (F : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |F n x - g x| < ε

-- exercise: exercise_2744

noncomputable abbrev tailSin (n : ℕ) (x : ℝ) : ℝ := ∑' k : ℕ, if n + 1 ≤ k then Real.sin (k * x) /. (k * (k + 1)) else 0
noncomputable abbrev finiteTail (n N : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc (n+1) N, Real.sin (k * x) /. (k * (k + 1))
noncomputable abbrev finiteAbsTail (n N : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc (n+1) N, |Real.sin (k * x)| /. (k * (k + 1))
noncomputable abbrev finiteTel (n N : ℕ) : ℝ := ∑ k ∈ Finset.Icc (n+1) N, (1 /. k - 1 /. (k+1))

-- GAPs 1-17 for the sine series tail estimate.
theorem proof_gap_exercise_2744_1 (S : ℝ -> ℝ) (Sn : ℕ -> ℕ -> ℝ -> ℝ) (Delta : ℕ -> ℝ -> ℝ) (N0 : ℝ -> ℕ) (ε : ℝ)
  (hε : ε > 0) : ∀ x, Summable (fun k : ℕ => Real.sin (k * x) /. (k * (k + 1))) := by sorry

theorem proof_gap_exercise_2744_2 (S : ℝ -> ℝ) (Sn : ℕ -> ℕ -> ℝ -> ℝ) (Delta : ℕ -> ℝ -> ℝ) (N0 : ℝ -> ℕ) (ε : ℝ)
  (h1 : ∀ x, Summable (fun k : ℕ => Real.sin (k * x) /. (k * (k + 1)))) : ∀ n x, Delta n x = |tailSin n x| := by sorry

theorem proof_gap_exercise_2744_3 (Delta : ℕ -> ℝ -> ℝ) : ∀ n x, Delta n x = |tailSin n x| -> seqLim (fun N => finiteTail n N x) (tailSin n x) := by sorry

theorem proof_gap_exercise_2744_4 (Delta : ℕ -> ℝ -> ℝ) : ∀ n x, Delta n x ≤ ∑' k : ℕ, if n + 1 ≤ k then |Real.sin (k * x)| /. (k * (k + 1)) else 0 := by sorry

theorem proof_gap_exercise_2744_5 : ∀ n x, (∑' k : ℕ, if n + 1 ≤ k then |Real.sin (k * x)| /. (k * (k + 1)) else 0) ≤ (∑' k : ℕ, if n + 1 ≤ k then 1 /. (k * (k + 1)) else 0) := by sorry

theorem proof_gap_exercise_2744_6 : ∀ n, (∑' k : ℕ, if n + 1 ≤ k then 1 /. (k * (k + 1)) else 0) = (∑' k : ℕ, if n + 1 ≤ k then (1 /. k - 1 /. (k+1)) else 0) := by sorry

theorem proof_gap_exercise_2744_7 : ∀ n, seqLim (fun N => finiteTel n N) (1 /. (n+1)) := by sorry

theorem proof_gap_exercise_2744_8 : ∀ n, seqLim (fun N => 1 /. (n+1) - 1 /. (N+1)) (1 /. (n+1)) := by sorry

theorem proof_gap_exercise_2744_9 : ∀ n, (∑' k : ℕ, if n + 1 ≤ k then (1 /. k - 1 /. (k+1)) else 0) = 1 /. (n+1) := by sorry

theorem proof_gap_exercise_2744_10 (Delta : ℕ -> ℝ -> ℝ) (ε : ℝ) : ∀ (n : ℕ) (x : ℝ), (1 /. (n+1)) < ε -> Delta n x < ε := by sorry

theorem proof_gap_exercise_2744_11 (ε : ℝ) (hε : ε > 0) : ∀ n, (n : ℝ) > (1 /. ε) - 1 -> (1 /. (n+1)) < ε := by sorry

theorem proof_gap_exercise_2744_12 (Delta : ℕ -> ℝ -> ℝ) (ε : ℝ) (h10 : ∀ (n : ℕ) (x : ℝ), (1 /. (n+1)) < ε -> Delta n x < ε)
  (h11 : ∀ n, (n : ℝ) > (1 /. ε) - 1 -> (1 /. (n+1)) < ε) : ∀ (n : ℕ) (x : ℝ), (n : ℝ) > (1 /. ε) - 1 -> Delta n x < ε := by sorry

theorem proof_gap_exercise_2744_13 (N0 : ℝ -> ℕ) (ε : ℝ) : (N0 ε : ℝ) = Int.floor (1 /. ε) := by sorry

theorem proof_gap_exercise_2744_14 (N0 : ℝ -> ℕ) : N0 0.1 = 10 := by sorry

theorem proof_gap_exercise_2744_15 (N0 : ℝ -> ℕ) : N0 0.01 = 100 := by sorry

theorem proof_gap_exercise_2744_16 (N0 : ℝ -> ℕ) : N0 0.001 = 1000 := by sorry

theorem proof_gap_exercise_2744_17 (Delta : ℕ -> ℝ -> ℝ) (N0 : ℝ -> ℕ) (ε : ℝ)
  (hN : (N0 ε : ℝ) = Int.floor (1 /. ε)) : ∀ n x, PosInt n -> n ≥ N0 ε -> Delta n x < ε := by sorry
