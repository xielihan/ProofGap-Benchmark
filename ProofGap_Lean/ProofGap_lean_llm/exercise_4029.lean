import Mathlib

set_option linter.style.longLine false

open MeasureTheory
open scoped Real

noncomputable section

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def volumeIntegral2 (Ω : Set (ℝ × ℝ)) (f : ℝ × ℝ -> ℝ) : ℝ := ∫ p in Ω, f p ∂volume

def volumeIntegral3 (Ω : Set (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ -> ℝ) : ℝ := ∫ p in Ω, f p ∂volume

def defInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in a..b, f x

def E4029Omega : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ p.1 ^ 2 ∧ p.1 ^ 2 ≤ 2 * p.2 ∧
       p.1 ≤ p.2 ^ 2 ∧ p.2 ^ 2 ≤ 2 * p.1}

def E4029Solid (Ω : Set (ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  {p | (p.1, p.2.1) ∈ Ω ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ p.1 * p.2.1}

def E4029SquareIntegral : ℝ :=
  (1 /. 3) * defInt (1 /. 2) 1 (fun v => defInt (1 /. 2) 1 (fun u => Real.rpow u (-3) * Real.rpow v (-3)))

def E4029SeparatedIntegral : ℝ :=
  (1 /. 3) * (defInt (1 /. 2) 1 (fun u => Real.rpow u (-3))) ^ 2

-- exercise: exercise_4029

theorem proof_gap_exercise_4029_1 (V : ℝ) (Ω : Set (ℝ × ℝ))
  (hΩ : Ω = E4029Omega) (hsolid : V = volumeIntegral3 (E4029Solid Ω) (fun _ => 1)) :
  V = volumeIntegral2 Ω (fun p => p.1 * p.2) := by
  sorry

theorem proof_gap_exercise_4029_2 (u : ℝ) (hrange : u ∈ Set.Icc (1 /. 2) 1) :
  1 /. 2 ≤ u := by
  sorry

theorem proof_gap_exercise_4029_3 (u : ℝ) (hrange : u ∈ Set.Icc (1 /. 2) 1) :
  u ≤ 1 := by
  sorry

theorem proof_gap_exercise_4029_4 (v : ℝ) (hrange : v ∈ Set.Icc (1 /. 2) 1) :
  1 /. 2 ≤ v := by
  sorry

theorem proof_gap_exercise_4029_5 (v : ℝ) (hrange : v ∈ Set.Icc (1 /. 2) 1) :
  v ≤ 1 := by
  sorry

theorem proof_gap_exercise_4029_6 (u v : ℝ) :
  ∃ I : ℝ, |I| = (1 /. 3) * Real.rpow u (-2) * Real.rpow v (-2) := by
  sorry

theorem proof_gap_exercise_4029_7 (V : ℝ) :
  V = E4029SquareIntegral := by
  sorry

theorem proof_gap_exercise_4029_8 (V : ℝ) :
  V = E4029SeparatedIntegral := by
  sorry

theorem proof_gap_exercise_4029_9 (V : ℝ) :
  V = (1 /. 3) * (9 /. 4) := by
  sorry

theorem proof_gap_exercise_4029_10 (V : ℝ) :
  V = 3 /. 4 := by
  sorry

end
