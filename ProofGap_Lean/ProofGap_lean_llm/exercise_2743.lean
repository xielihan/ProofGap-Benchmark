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

-- exercise: exercise_2743

noncomputable abbrev lg (x : ℝ) : ℝ := Real.logb 10 x

-- GAP 1: source only defines f and g on n>0 and 0<x<1, but the gap asks all n,x.
theorem proof_gap_exercise_2743_1
  (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (hf : ∀ n x, PosInt n -> Ioo01 x -> f n x = x ^ n)
  (hg : ∀ x, Ioo01 x -> g x = 0)
  (hε : ε = 0.001) :
  ∀ n x, |f n x - g x| = |x ^ n - 0| := by
  sorry

theorem proof_gap_exercise_2743_2 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (hf : ∀ n x, PosInt n -> Ioo01 x -> f n x = x ^ n) (hg : ∀ x, Ioo01 x -> g x = 0) (hε : ε = 0.001)
  (h1 : ∀ n x, |f n x - g x| = |x ^ n - 0|) :
  ∀ x n, Ioo01 x -> (|x ^ n - 0| < ε ↔ x ^ n < ε) := by
  sorry

theorem proof_gap_exercise_2743_3 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (hf : ∀ n x, PosInt n -> Ioo01 x -> f n x = x ^ n) (hg : ∀ x, Ioo01 x -> g x = 0) (hε : ε = 0.001)
  (h1 : ∀ n x, |f n x - g x| = |x ^ n - 0|)
  (h2 : ∀ x n, Ioo01 x -> (|x ^ n - 0| < ε ↔ x ^ n < ε)) :
  ∀ x n, Ioo01 x -> (x ^ n < ε ↔ (n : ℝ) > lg ε /. lg x) := by
  sorry

theorem proof_gap_exercise_2743_4 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (hf : ∀ n x, PosInt n -> Ioo01 x -> f n x = x ^ n) (hg : ∀ x, Ioo01 x -> g x = 0) (hε : ε = 0.001)
  (h1 : ∀ n x, |f n x - g x| = |x ^ n - 0|)
  (h2 : ∀ x n, Ioo01 x -> (|x ^ n - 0| < ε ↔ x ^ n < ε))
  (h3 : ∀ x n, Ioo01 x -> (x ^ n < ε ↔ (n : ℝ) > lg ε /. lg x)) :
  ∀ x, Ioo01 x -> (N ε x : ℝ) = Int.floor (lg ε /. lg x) := by
  sorry

theorem proof_gap_exercise_2743_5 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (h4 : ∀ x, Ioo01 x -> (N ε x : ℝ) = Int.floor (lg ε /. lg x)) : N 0.001 (1 /. 10) = 3 := by
  sorry

theorem proof_gap_exercise_2743_6 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (h4 : ∀ x, Ioo01 x -> (N ε x : ℝ) = Int.floor (lg ε /. lg x))
  (h5 : N 0.001 (1 /. 10) = 3) : N 0.001 (1 /. Real.sqrt 10) = 6 := by
  sorry

theorem proof_gap_exercise_2743_7 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (h4 : ∀ x, Ioo01 x -> (N ε x : ℝ) = Int.floor (lg ε /. lg x))
  (h5 : N 0.001 (1 /. 10) = 3) (h6 : N 0.001 (1 /. Real.sqrt 10) = 6) :
  ∀ m, PosInt m -> N 0.001 (1 /. (10 : ℝ) ^ (1 /. (m : ℝ))) = 3 * m := by
  sorry

theorem proof_gap_exercise_2743_8 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (hε : ε = 0.001) : seqTendsToTop (fun x => lg ε /. lg x) := by
  sorry

theorem proof_gap_exercise_2743_9 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (hf : ∀ n x, PosInt n -> Ioo01 x -> f n x = x ^ n) (hg : ∀ x, Ioo01 x -> g x = 0)
  (hε : ε = 0.001) (h8 : seqTendsToTop (fun x => lg ε /. lg x)) :
  ¬ (∃ M : ℕ, PosInt M ∧ ∀ n x, PosInt n -> Ioo01 x -> n > M -> |f n x - g x| < ε) := by
  sorry

theorem proof_gap_exercise_2743_10 (f : ℕ -> ℝ -> ℝ) (g : ℝ -> ℝ) (N : ℝ -> ℝ -> ℕ) (ε : ℝ)
  (h4 : ∀ x, Ioo01 x -> (N ε x : ℝ) = Int.floor (lg ε /. lg x))
  (h9 : ¬ (∃ M : ℕ, PosInt M ∧ ∀ n x, PosInt n -> Ioo01 x -> n > M -> |f n x - g x| < ε)) :
  ∀ x, (N ε x : ℝ) = Int.floor (lg ε /. lg x) ∧ ¬ UniformConvergentSeq f {x | Ioo01 x} g ->
    PosInt (N ε x) ∧ ∀ n y, PosInt n -> Ioo01 y -> n ≥ N ε x -> |f n y - g y| < ε := by
  sorry
