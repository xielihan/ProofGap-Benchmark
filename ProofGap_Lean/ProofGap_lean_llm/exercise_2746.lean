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

-- exercise: exercise_2746

noncomputable abbrev g2Limit (x : ℝ) : ℝ := if x = 1 then 1 else 0

theorem proof_gap_exercise_2746_1 (f : ℕ -> ℝ -> ℝ) (g1 g2 : ℝ -> ℝ)
  (hf : ∀ n x, PosInt n -> f n x = x ^ n) (hg1 : ∀ x, Icc0Half x -> g1 x = 0)
  (hg2 : ∀ x, Icc01 x -> g2 x = g2Limit x) : ∀ x, Icc0Half x -> seqLim (fun n => f n x) 0 := by sorry

theorem proof_gap_exercise_2746_2 (f : ℕ -> ℝ -> ℝ) (g1 g2 : ℝ -> ℝ) : ∀ n x ε, ε > 0 -> |f n x - g1 x| = |x| ^ n := by sorry

theorem proof_gap_exercise_2746_3 : ∀ x n ε, ε > 0 -> |x| ^ n ≤ (1 /. 2) ^ n := by sorry

theorem proof_gap_exercise_2746_4 (f : ℕ -> ℝ -> ℝ) (g1 g2 : ℝ -> ℝ)
  (h2 : ∀ n x ε, ε > 0 -> |f n x - g1 x| = |x| ^ n) (h3 : ∀ x n ε, ε > 0 -> |x| ^ n ≤ (1 /. 2) ^ n) :
  ∀ n x ε, ε > 0 -> |f n x - g1 x| ≤ (1 /. 2) ^ n := by sorry

theorem proof_gap_exercise_2746_5 (f : ℕ -> ℝ -> ℝ) (g1 : ℝ -> ℝ) : ∀ (n : ℕ) (x ε : ℝ), ε > 0 -> (1 /. (2 ^ n)) < ε -> |f n x - g1 x| < ε := by sorry

theorem proof_gap_exercise_2746_6 : ∀ n ε, ε > 0 -> (n : ℝ) > (Real.log (1 /. ε) /. Real.log 2) -> (1 /. (2 ^ n)) < ε := by sorry

theorem proof_gap_exercise_2746_7 (f : ℕ -> ℝ -> ℝ) (g1 : ℝ -> ℝ) : ∀ (n : ℕ) (x ε : ℝ), ε > 0 -> (n : ℝ) > (Real.log (1 /. ε) /. Real.log 2) -> |f n x - g1 x| < ε := by sorry

theorem proof_gap_exercise_2746_8 (f : ℕ -> ℝ -> ℝ) (g1 : ℝ -> ℝ)
  (hN : ∃ N : ℝ -> ℕ, ∀ ε, ε > 0 -> (N ε : ℝ) = Int.floor (Real.log (1 /. ε) /. Real.log 2)) :
  ∀ (N : ℝ -> ℕ) (n : ℕ) (ε : ℝ), ε > 0 -> n ≥ N ε -> ∀ x, Icc0Half x -> |f n x - g1 x| < ε := by sorry

theorem proof_gap_exercise_2746_9 (f : ℕ -> ℝ -> ℝ) (g1 : ℝ -> ℝ) : UniformConvergentSeq f {x | Icc0Half x} g1 := by sorry

theorem proof_gap_exercise_2746_10 (f : ℕ -> ℝ -> ℝ) (g2 : ℝ -> ℝ) : ∀ x, Icc01 x -> seqLim (fun n => f n x) (g2 x) := by sorry

theorem proof_gap_exercise_2746_11 : ∀ ε0, 0 < ε0 -> ε0 < (1 /. 2) -> ∀ n, PosInt n -> ∃ x : ℝ, Icc01 x := by sorry

theorem proof_gap_exercise_2746_12 (f : ℕ -> ℝ -> ℝ) (g2 : ℝ -> ℝ) : ∀ ε0, 0 < ε0 -> ε0 < (1 /. 2) -> ∀ n, PosInt n -> ∃ x : ℝ, |f n x - g2 x| = 1 /. 2 := by sorry

theorem proof_gap_exercise_2746_13 : ∀ ε0, 0 < ε0 -> ε0 < (1 /. 2) -> ∀ n, PosInt n -> (1 /. 2) > ε0 := by sorry

theorem proof_gap_exercise_2746_14 (f : ℕ -> ℝ -> ℝ) (g2 : ℝ -> ℝ) : ∀ ε0, 0 < ε0 -> ε0 < (1 /. 2) -> ∀ n, PosInt n -> ∃ x : ℝ, |f n x - g2 x| > ε0 := by sorry

theorem proof_gap_exercise_2746_15 (f : ℕ -> ℝ -> ℝ) (g2 : ℝ -> ℝ) : ¬ UniformConvergentSeq f {x | Icc01 x} g2 := by sorry

theorem proof_gap_exercise_2746_16 (f : ℕ -> ℝ -> ℝ) (g1 : ℝ -> ℝ) : UniformConvergentSeq f {x | Icc0Half x} g1 := by sorry

theorem proof_gap_exercise_2746_17 (f : ℕ -> ℝ -> ℝ) (g2 : ℝ -> ℝ) : ¬ UniformConvergentSeq f {x | Icc01 x} g2 := by sorry

theorem proof_gap_exercise_2746_18 (f : ℕ -> ℝ -> ℝ) (g1 g2 : ℝ -> ℝ) : UniformConvergentSeq f {x | Icc0Half x} g1 ∧ ¬ UniformConvergentSeq f {x | Icc01 x} g2 := by sorry
