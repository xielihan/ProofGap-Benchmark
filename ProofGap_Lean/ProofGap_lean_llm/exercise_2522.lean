import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def approx (eps a b : ℝ) : Prop := |a - b| ≤ eps

-- exercise: exercise_2522

/-- Exercise 2522, gap 1
RNFL goal: forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ T ⇒ FunDeri(s, 1, 1)(t) = v(t) ∧ v(t) = v_{0} + a * t
-/
theorem proof_gap_exercise_2522_1
  (s v : ℝ -> ℝ)
  (sTotal v0 accel T : ℝ)
  (hT : 0 ≤ T)
  : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v t ∧ v t = v0 + accel * t := by
  sorry

/-- Exercise 2522, gap 2
RNFL goal: forall (t), t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ T ⇒ diff(s) = (v_{0} + a * t) * diff(fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ T] . t)
-/
theorem proof_gap_exercise_2522_2
  (s v : ℝ -> ℝ)
  (sTotal v0 accel T : ℝ)
  (hT : 0 ≤ T)
  (h1 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v t ∧ v t = v0 + accel * t)
  : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v0 + accel * t := by
  sorry

/-- Exercise 2522, gap 3
RNFL goal: s = DefInt(0, T, (fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ T] . v_{0} + a * t) * diff(fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ T] . t))
-/
theorem proof_gap_exercise_2522_3
  (s v : ℝ -> ℝ)
  (sTotal v0 accel T : ℝ)
  (hT : 0 ≤ T)
  (h1 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v t ∧ v t = v0 + accel * t)
  (h2 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v0 + accel * t)
  : sTotal = ∫ t in (0 : ℝ)..T, v0 + accel * t := by
  sorry

/-- Exercise 2522, gap 4
RNFL goal: DefInt(0, T, (fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ T] . v_{0} + a * t) * diff(fun t [t ∈ RealSet ∧ 0 ≤ t ∧ t ≤ T] . t)) = v_{0} * T + frac(1, 2) * a * T^{2}
-/
theorem proof_gap_exercise_2522_4
  (s v : ℝ -> ℝ)
  (sTotal v0 accel T : ℝ)
  (hT : 0 ≤ T)
  (h1 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v t ∧ v t = v0 + accel * t)
  (h2 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v0 + accel * t)
  (h3 : sTotal = ∫ t in (0 : ℝ)..T, v0 + accel * t)
  : (∫ t in (0 : ℝ)..T, v0 + accel * t) = v0 * T + ((1 : ℝ) /. 2) * accel * T ^ 2 := by
  sorry

/-- Exercise 2522, gap 5
RNFL goal: s = v_{0} * T + frac(1, 2) * a * T^{2}
-/
theorem proof_gap_exercise_2522_5
  (s v : ℝ -> ℝ)
  (sTotal v0 accel T : ℝ)
  (hT : 0 ≤ T)
  (h1 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v t ∧ v t = v0 + accel * t)
  (h2 : ∀ t : ℝ, 0 ≤ t ∧ t ≤ T → deriv s t = v0 + accel * t)
  (h3 : sTotal = ∫ t in (0 : ℝ)..T, v0 + accel * t)
  (h4 : (∫ t in (0 : ℝ)..T, v0 + accel * t) = v0 * T + ((1 : ℝ) /. 2) * accel * T ^ 2)
  : sTotal = v0 * T + ((1 : ℝ) /. 2) * accel * T ^ 2 := by
  sorry

