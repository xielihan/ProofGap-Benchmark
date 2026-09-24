import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Filter
open scoped Topology BigOperators

def PosInt (n : ℕ) : Prop := 0 < n
def Ioo01 (x : ℝ) : Prop := 0 < x ∧ x < 1
def Icc01 (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1
def Icc0Half (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ ((1 : ℝ) / 2)
def seqLim (u : ℕ -> ℝ) (a : ℝ) : Prop := Tendsto u atTop (𝓝 a)
def seqTendsToTop (u : ℝ -> ℝ) : Prop := Tendsto u (𝓝[<] (1 : ℝ)) atTop
def UniformConvergentSeq (F : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |F n x - g x| < ε

-- exercise: exercise_2748

theorem proof_gap_exercise_2748_1 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ)
  (hf : ∀ n x, PosInt n -> Icc01 x -> f n x = x ^ n - x ^ (2*n)) (hh : ∀ x, Icc01 x -> h x = 0) :
  ∀ x, Icc01 x -> seqLim (fun n => f n x) 0 := by sorry

theorem proof_gap_exercise_2748_2 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ∀ x, Icc01 x -> seqLim (fun n => f n x) (h x) := by sorry

theorem proof_gap_exercise_2748_3 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ∀ n x, PosInt n -> Icc01 x -> |f n x - h x| = x ^ n - x ^ (2*n) := by sorry

theorem proof_gap_exercise_2748_4 :
  ∀ ε0, 0 < ε0 -> ε0 < ((1 : ℝ) / 4) -> ∀ n, PosInt n ->
    ∃ x : ℝ, x = (1 : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ∧ Icc01 x := by sorry

theorem proof_gap_exercise_2748_5 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) :
  ∀ ε0, 0 < ε0 -> ε0 < ((1 : ℝ) / 4) -> ∀ n, PosInt n ->
    ∃ x : ℝ, x = (1 : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ∧
      |f n x - h x| = ((1 : ℝ) / 4) := by sorry

theorem proof_gap_exercise_2748_6 :
  ∀ ε0, 0 < ε0 -> ε0 < ((1 : ℝ) / 4) -> ∀ n, PosInt n -> ((1 : ℝ) / 4) > ε0 := by sorry

theorem proof_gap_exercise_2748_7 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) :
  ∀ ε0, 0 < ε0 -> ε0 < ((1 : ℝ) / 4) -> ∀ n, PosInt n ->
    ∃ x : ℝ, x = (1 : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ∧
      |f n x - h x| > ε0 := by sorry

theorem proof_gap_exercise_2748_8 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ¬ UniformConvergentSeq f {x | Icc01 x} h := by sorry

theorem proof_gap_exercise_2748_9 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ∀ x, Icc01 x -> seqLim (fun n => f n x) (h x) := by sorry

theorem proof_gap_exercise_2748_10 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : ¬ UniformConvergentSeq f {x | Icc01 x} h := by sorry

theorem proof_gap_exercise_2748_11 (f : ℕ -> ℝ -> ℝ) (h : ℝ -> ℝ) : (∀ x, Icc01 x -> seqLim (fun n => f n x) (h x)) ∧ ¬ UniformConvergentSeq f {x | Icc01 x} h := by sorry
