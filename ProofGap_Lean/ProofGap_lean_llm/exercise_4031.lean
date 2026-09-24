import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))
noncomputable abbrev rp (x y : ℝ) : ℝ := Real.rpow x y
noncomputable abbrev DefInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in a..b, f x
noncomputable abbrev EvalAt (f : ℝ -> ℝ) (a b : ℝ) : ℝ := f b - f a
noncomputable abbrev AreaInt (D : Set (ℝ × ℝ)) (f : ℝ × ℝ -> ℝ) : ℝ := ∫ p in D, f p
noncomputable abbrev VolumeInt (E : Set (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ -> ℝ) : ℝ := ∫ p in E, f p
noncomputable abbrev FunDeri (z : ℝ × ℝ -> ℝ) (i n : ℕ) : ℝ × ℝ -> ℝ := fun p => if i = 1 then iteratedDeriv n (fun x => z (x, p.2)) p.1 else iteratedDeriv n (fun y => z (p.1, y)) p.2

-- exercise: exercise_4031

noncomputable abbrev D4031 : Set (ℝ × ℝ) := {p | 0 <= p.1 ∧ 0 <= p.2 ∧ p.1 + p.2 <= 1}
noncomputable abbrev E4031 (Ω : Set (ℝ × ℝ)) (z : ℝ × ℝ -> ℝ) : Set (ℝ × ℝ × ℝ) := {p | (p.1, p.2.1) ∈ Ω ∧ 0 <= p.2.2 ∧ p.2.2 <= z (p.1, p.2.1)}
noncomputable abbrev F4031 (x y : ℝ) : ℝ := rp x (3 /. 2) + rp y (3 /. 2)

theorem proof_gap_exercise_4031_1 (V : ℝ) (Ω : Set (ℝ × ℝ)) (z : ℝ × ℝ -> ℝ) (hΩ : Ω = D4031) (hz : ∀ x y, 0 <= x -> 0 <= y -> z (x,y) = F4031 x y) (hV : V = VolumeInt (E4031 Ω z) (fun _ => 1)) : V = AreaInt Ω (fun p => F4031 p.1 p.2) := by sorry
theorem proof_gap_exercise_4031_2 (V : ℝ) (Ω : Set (ℝ × ℝ)) (z : ℝ × ℝ -> ℝ) (hΩ : Ω = D4031) (hz : ∀ x y, 0 <= x -> 0 <= y -> z (x,y) = F4031 x y) (hV : V = VolumeInt (E4031 Ω z) (fun _ => 1)) (h1 : V = AreaInt Ω (fun p => F4031 p.1 p.2)) : V = DefInt 0 1 (fun x => DefInt 0 (1 - x) (fun y => F4031 x y)) := by sorry
theorem proof_gap_exercise_4031_3 (V : ℝ) (Ω : Set (ℝ × ℝ)) (z : ℝ × ℝ -> ℝ) (hΩ : Ω = D4031) (hz : ∀ x y, 0 <= x -> 0 <= y -> z (x,y) = F4031 x y) (hV : V = VolumeInt (E4031 Ω z) (fun _ => 1)) (h1 : V = AreaInt Ω (fun p => F4031 p.1 p.2)) (h2 : V = DefInt 0 1 (fun x => DefInt 0 (1 - x) (fun y => F4031 x y))) : V = DefInt 0 1 (fun x => rp x (3 /. 2) * (1 - x) + (2 /. 5) * rp (1 - x) (5 /. 2)) := by sorry
theorem proof_gap_exercise_4031_4 (V : ℝ) (Ω : Set (ℝ × ℝ)) (z : ℝ × ℝ -> ℝ) (hΩ : Ω = D4031) (hz : ∀ x y, 0 <= x -> 0 <= y -> z (x,y) = F4031 x y) (hV : V = VolumeInt (E4031 Ω z) (fun _ => 1)) (h1 : V = AreaInt Ω (fun p => F4031 p.1 p.2)) (h2 : V = DefInt 0 1 (fun x => DefInt 0 (1 - x) (fun y => F4031 x y))) (h3 : V = DefInt 0 1 (fun x => rp x (3 /. 2) * (1 - x) + (2 /. 5) * rp (1 - x) (5 /. 2))) : V = EvalAt (fun x => (2 /. 5) * rp x (5 /. 2)) 0 1 - EvalAt (fun x => (2 /. 7) * rp x (7 /. 2)) 0 1 - EvalAt (fun x => (4 /. 35) * rp (1 - x) (7 /. 2)) 0 1 := by sorry
theorem proof_gap_exercise_4031_5 (V : ℝ) (Ω : Set (ℝ × ℝ)) (z : ℝ × ℝ -> ℝ) (hΩ : Ω = D4031) (hz : ∀ x y, 0 <= x -> 0 <= y -> z (x,y) = F4031 x y) (hV : V = VolumeInt (E4031 Ω z) (fun _ => 1)) (h1 : V = AreaInt Ω (fun p => F4031 p.1 p.2)) (h2 : V = DefInt 0 1 (fun x => DefInt 0 (1 - x) (fun y => F4031 x y))) (h3 : V = DefInt 0 1 (fun x => rp x (3 /. 2) * (1 - x) + (2 /. 5) * rp (1 - x) (5 /. 2))) (h4 : V = EvalAt (fun x => (2 /. 5) * rp x (5 /. 2)) 0 1 - EvalAt (fun x => (2 /. 7) * rp x (7 /. 2)) 0 1 - EvalAt (fun x => (4 /. 35) * rp (1 - x) (7 /. 2)) 0 1) : V = (2 /. 5) - (2 /. 7) + (4 /. 35) := by sorry
theorem proof_gap_exercise_4031_6 (V : ℝ) (Ω : Set (ℝ × ℝ)) (z : ℝ × ℝ -> ℝ) (hΩ : Ω = D4031) (hz : ∀ x y, 0 <= x -> 0 <= y -> z (x,y) = F4031 x y) (hV : V = VolumeInt (E4031 Ω z) (fun _ => 1)) (h1 : V = AreaInt Ω (fun p => F4031 p.1 p.2)) (h2 : V = DefInt 0 1 (fun x => DefInt 0 (1 - x) (fun y => F4031 x y))) (h3 : V = DefInt 0 1 (fun x => rp x (3 /. 2) * (1 - x) + (2 /. 5) * rp (1 - x) (5 /. 2))) (h4 : V = EvalAt (fun x => (2 /. 5) * rp x (5 /. 2)) 0 1 - EvalAt (fun x => (2 /. 7) * rp x (7 /. 2)) 0 1 - EvalAt (fun x => (4 /. 35) * rp (1 - x) (7 /. 2)) 0 1) (h5 : V = (2 /. 5) - (2 /. 7) + (4 /. 35)) : V = (8 /. 35) := by sorry
