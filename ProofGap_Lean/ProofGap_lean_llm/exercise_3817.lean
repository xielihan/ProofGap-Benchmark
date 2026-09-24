import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

noncomputable abbrev DefInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := 0
noncomputable abbrev VPInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := 0
noncomputable abbrev FunDeri (f : ℝ → ℝ) (m k : ℕ) : ℝ → ℝ := fun _ => 0
def UniformConvergent (F : ℝ → ℝ) (S : Set ℝ) (g : ℝ → ℝ) : Prop := True
def ContinuousFuncOn (f : ℝ → ℝ) (S : Set ℝ) : Prop := ContinuousOn f S
def ConvergentSeries (x : ℝ) : Prop := True
noncomputable abbrev posInf : ℝ := 0
noncomputable abbrev negInf : ℝ := 0
noncomputable abbrev sgn (x : ℝ) : ℝ := SignType.sign x
noncomputable abbrev boundary (f : ℝ → ℝ) (a b : ℝ) : ℝ := f b - f a
local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_3817
-- Exercise 3817, gap 1
axiom exercise_3817_gap_1_statement : Prop
theorem proof_gap_exercise_3817_1 : exercise_3817_gap_1_statement := by sorry
-- Exercise 3817, gap 2
axiom exercise_3817_gap_2_statement : Prop
theorem proof_gap_exercise_3817_2 : exercise_3817_gap_2_statement := by sorry
-- Exercise 3817, gap 3
axiom exercise_3817_gap_3_statement : Prop
theorem proof_gap_exercise_3817_3 : exercise_3817_gap_3_statement := by sorry
-- Exercise 3817, gap 4
axiom exercise_3817_gap_4_statement : Prop
theorem proof_gap_exercise_3817_4 : exercise_3817_gap_4_statement := by sorry
-- Exercise 3817, gap 5
axiom exercise_3817_gap_5_statement : Prop
theorem proof_gap_exercise_3817_5 : exercise_3817_gap_5_statement := by sorry
-- Exercise 3817, gap 6
axiom exercise_3817_gap_6_statement : Prop
theorem proof_gap_exercise_3817_6 : exercise_3817_gap_6_statement := by sorry
-- Exercise 3817, gap 7
axiom exercise_3817_gap_7_statement : Prop
theorem proof_gap_exercise_3817_7 : exercise_3817_gap_7_statement := by sorry
-- Exercise 3817, gap 8
axiom exercise_3817_gap_8_statement : Prop
theorem proof_gap_exercise_3817_8 : exercise_3817_gap_8_statement := by sorry
-- Exercise 3817, gap 9
axiom exercise_3817_gap_9_statement : Prop
theorem proof_gap_exercise_3817_9 : exercise_3817_gap_9_statement := by sorry
-- Exercise 3817, gap 10
axiom exercise_3817_gap_10_statement : Prop
theorem proof_gap_exercise_3817_10 : exercise_3817_gap_10_statement := by sorry
-- Exercise 3817, gap 11
axiom exercise_3817_gap_11_statement : Prop
theorem proof_gap_exercise_3817_11 : exercise_3817_gap_11_statement := by sorry
-- Exercise 3817, gap 12
axiom exercise_3817_gap_12_statement : Prop
theorem proof_gap_exercise_3817_12 : exercise_3817_gap_12_statement := by sorry
-- Exercise 3817, gap 13
axiom exercise_3817_gap_13_statement : Prop
theorem proof_gap_exercise_3817_13 : exercise_3817_gap_13_statement := by sorry
-- Exercise 3817, gap 14
axiom exercise_3817_gap_14_statement : Prop
theorem proof_gap_exercise_3817_14 : exercise_3817_gap_14_statement := by sorry
-- Exercise 3817, gap 15
axiom exercise_3817_gap_15_statement : Prop
theorem proof_gap_exercise_3817_15 : exercise_3817_gap_15_statement := by sorry
-- Exercise 3817, gap 16
axiom exercise_3817_gap_16_statement : Prop
theorem proof_gap_exercise_3817_16 : exercise_3817_gap_16_statement := by sorry
-- Exercise 3817, gap 17
axiom exercise_3817_gap_17_statement : Prop
theorem proof_gap_exercise_3817_17 : exercise_3817_gap_17_statement := by sorry
-- Exercise 3817, gap 18
axiom exercise_3817_gap_18_statement : Prop
theorem proof_gap_exercise_3817_18 : exercise_3817_gap_18_statement := by sorry
-- Exercise 3817, gap 19
axiom exercise_3817_gap_19_statement : Prop
theorem proof_gap_exercise_3817_19 : exercise_3817_gap_19_statement := by sorry
-- Exercise 3817, gap 20
axiom exercise_3817_gap_20_statement : Prop
theorem proof_gap_exercise_3817_20 : exercise_3817_gap_20_statement := by sorry
