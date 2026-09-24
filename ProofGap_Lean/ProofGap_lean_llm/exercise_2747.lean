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

-- exercise: exercise_2747

noncomputable abbrev deriv1 (g : ℝ -> ℝ) (x : ℝ) : ℝ := deriv g x
noncomputable abbrev maxPointOn (g : ℝ -> ℝ) (s : Set ℝ) : Set ℝ := {x | x ∈ s ∧ ∀ y ∈ s, g y ≤ g x}

theorem proof_gap_exercise_2747_1 (f : ℕ -> ℝ -> ℝ) (h g : ℝ -> ℝ)
  (hf : ∀ n x, PosInt n -> Icc01 x -> f n x = x ^ n - x ^ (n+1)) (hh : ∀ x, Icc01 x -> h x = 0) :
  ∀ x, x = 0 ∨ x = 1 -> ∀ n, PosInt n -> f n x = 0 := by sorry

theorem proof_gap_exercise_2747_2 (f : ℕ -> ℝ -> ℝ) : ∀ x, Ioo01 x -> seqLim (fun n => f n x) 0 := by sorry

theorem proof_gap_exercise_2747_3 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ∀ x, Icc01 x -> seqLim (fun n => f n x) (h x) := by sorry

theorem proof_gap_exercise_2747_4 (f : ℕ -> ℝ -> ℝ) (h g : ℝ -> ℝ) : ∀ n x, |f n x - h x| = x ^ n - x ^ (n+1) := by sorry

theorem proof_gap_exercise_2747_5 (g : ℝ -> ℝ) : ∀ n x, x ^ n - x ^ (n+1) = g x := by sorry

theorem proof_gap_exercise_2747_6 (f : ℕ -> ℝ -> ℝ) (h g : ℝ -> ℝ) : ∀ n x, |f n x - h x| = g x := by sorry

theorem proof_gap_exercise_2747_7 (g : ℝ -> ℝ) : ∀ n x, deriv1 g x = x ^ (n-1) * ((n : ℝ) - (n+1) * x) := by sorry

theorem proof_gap_exercise_2747_8 (g : ℝ -> ℝ) : ∀ n x, deriv1 g x = 0 ↔ x = (n /. (n+1)) := by sorry

theorem proof_gap_exercise_2747_9 (g : ℝ -> ℝ) : ∀ n, maxPointOn g {x | Icc01 x} = {x | x = n /. (n+1)} := by sorry

theorem proof_gap_exercise_2747_10 (g : ℝ -> ℝ) : ∀ n x, Icc01 x -> g x ≤ (n /. (n+1)) ^ n * (1 - n /. (n+1)) ∧ (n /. (n+1)) ^ n * (1 - n /. (n+1)) = (n /. (n+1)) ^ n * (1 /. (n+1)) ∧ (n /. (n+1)) ^ n * (1 /. (n+1)) < 1 /. (n+1) := by sorry

theorem proof_gap_exercise_2747_11 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ∀ (n : ℕ) (x ε : ℝ), ε > 0 -> (1 /. (n+1)) < ε -> |f n x - h x| < ε := by sorry

theorem proof_gap_exercise_2747_12 : ∀ n ε, ε > 0 -> (n : ℝ) > (1 /. ε) -> (1 /. (n+1)) < ε := by sorry

theorem proof_gap_exercise_2747_13 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ∀ (n : ℕ) (x ε : ℝ), ε > 0 -> (n : ℝ) > (1 /. ε) -> |f n x - h x| < ε := by sorry

theorem proof_gap_exercise_2747_14 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ)
  (hN : ∃ N : ℝ -> ℕ, ∀ ε, ε > 0 -> (N ε : ℝ) = Int.floor (1 /. ε)) :
  ∀ (N : ℝ -> ℕ) (n : ℕ) (ε : ℝ), ε > 0 -> n > N ε -> ∀ x, Icc01 x -> |f n x - h x| < ε := by sorry

theorem proof_gap_exercise_2747_15 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : UniformConvergentSeq f {x | Icc01 x} h := by sorry

theorem proof_gap_exercise_2747_16 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : UniformConvergentSeq f {x | Icc01 x} h := by sorry
