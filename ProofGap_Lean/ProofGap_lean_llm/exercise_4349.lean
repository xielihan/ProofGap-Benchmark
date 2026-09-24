import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))
noncomputable def sqrtn (n : ℕ) (x : ℝ) : ℝ := Real.rpow x ((n:ℝ)⁻¹)
noncomputable def DefInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in a..b, f t
noncomputable def ScalarSurfaceInt {α : Type*} (S : Set α) (f : ℝ) : ℝ := 0
noncomputable def diff {α : Type*} (x : α) : ℝ := 1
noncomputable def FunDeri {α : Type*} (f : α) (i j : ℕ) : α := f
noncomputable def evalOn (f : ℝ → ℝ) (a b : ℝ) : ℝ := f b - f a

-- exercise: exercise_4349
abbrev ConeSurface := Set (ℝ × ℝ)
abbrev coneCond (a r phi : ℝ) : Prop := r ∈ (Set.univ:Set ℝ) ∧ 0 ≤ r ∧ r ≤ a ∧ phi ∈ (Set.univ:Set ℝ) ∧ 0 ≤ phi ∧ phi ≤ 2*Real.pi
noncomputable abbrev coneDouble (a α : ℝ) := DefInt 0 (2*Real.pi) (fun phi => DefInt 0 a (fun r => r^2 * Real.cos α^2 * r * Real.sin α))

theorem proof_gap_exercise_4349_1 (S : ConeSurface) (x y z E F G : ℝ×ℝ→ℝ) (a α : ℝ) (ha : a>0) (halpha : 0<α ∧ α<Real.pi/.2) : ∀ r phi, coneCond a r phi → E (r,phi) = Real.cos phi^2 * Real.sin α^2 + Real.sin phi^2 * Real.sin α^2 + Real.cos α^2 := by sorry
theorem proof_gap_exercise_4349_2 (a α : ℝ) : ∀ phi, phi ∈ (Set.univ:Set ℝ) ∧ 0 ≤ phi ∧ phi ≤ 2*Real.pi → Real.cos phi^2 * Real.sin α^2 + Real.sin phi^2 * Real.sin α^2 + Real.cos α^2 = 1 := by sorry
theorem proof_gap_exercise_4349_3 (E : ℝ×ℝ→ℝ) (a α : ℝ) : ∀ r phi, coneCond a r phi → E (r,phi) = 1 := by sorry
theorem proof_gap_exercise_4349_4 (G : ℝ×ℝ→ℝ) (a α : ℝ) : ∀ r phi, coneCond a r phi → G (r,phi) = r^2 * Real.cos phi^2 * Real.sin α^2 + r^2 * Real.sin phi^2 * Real.sin α^2 := by sorry
theorem proof_gap_exercise_4349_5 (a α : ℝ) : ∀ r phi, coneCond a r phi → r^2 * Real.cos phi^2 * Real.sin α^2 + r^2 * Real.sin phi^2 * Real.sin α^2 = r^2 * Real.sin α^2 := by sorry
theorem proof_gap_exercise_4349_6 (G : ℝ×ℝ→ℝ) (a α : ℝ) : ∀ r phi, coneCond a r phi → G (r,phi) = r^2 * Real.sin α^2 := by sorry
theorem proof_gap_exercise_4349_7 (F : ℝ×ℝ→ℝ) (a α : ℝ) : ∀ r phi, coneCond a r phi → F (r,phi) = Real.cos phi * Real.sin α * (-r * Real.sin phi) * Real.sin α + Real.sin phi * Real.sin α * r * Real.cos phi * Real.sin α := by sorry
theorem proof_gap_exercise_4349_8 (a α : ℝ) : ∀ phi r, phi ∈ (Set.univ:Set ℝ) ∧ 0 ≤ phi ∧ phi ≤ 2*Real.pi ∧ r ∈ (Set.univ:Set ℝ) ∧ 0 ≤ r ∧ r ≤ a → Real.cos phi * Real.sin α * (-r * Real.sin phi) * Real.sin α + Real.sin phi * Real.sin α * r * Real.cos phi * Real.sin α = 0 := by sorry
theorem proof_gap_exercise_4349_9 (F : ℝ×ℝ→ℝ) (a α : ℝ) : ∀ r phi, coneCond a r phi → F (r,phi) = 0 := by sorry
theorem proof_gap_exercise_4349_10 (E F G : ℝ×ℝ→ℝ) (a α : ℝ) : ∀ r phi, coneCond a r phi → sqrtn 2 (E (r,phi)*G (r,phi) - F (r,phi)^2) = r * Real.sin α := by sorry
theorem proof_gap_exercise_4349_11 (S : ConeSurface) (z : ℝ×ℝ→ℝ) (a α : ℝ) : ScalarSurfaceInt S ((z (0,0))^2 * diff S) = coneDouble a α := by sorry
theorem proof_gap_exercise_4349_12 (a α : ℝ) : coneDouble a α = ((Real.pi * a^4)/.2) * Real.sin α * Real.cos α^2 := by sorry
theorem proof_gap_exercise_4349_13 (S : ConeSurface) (z : ℝ×ℝ→ℝ) (a α : ℝ) (h11 : ScalarSurfaceInt S ((z (0,0))^2 * diff S) = coneDouble a α) (h12 : coneDouble a α = ((Real.pi * a^4)/.2) * Real.sin α * Real.cos α^2) : ScalarSurfaceInt S ((z (0,0))^2 * diff S) = ((Real.pi * a^4)/.2) * Real.sin α * Real.cos α^2 := by sorry
theorem proof_gap_exercise_4349_14 (S : ConeSurface) (z : ℝ×ℝ→ℝ) (a α : ℝ) (h13 : ScalarSurfaceInt S ((z (0,0))^2 * diff S) = ((Real.pi * a^4)/.2) * Real.sin α * Real.cos α^2) : ScalarSurfaceInt S ((z (0,0))^2 * diff S) = ((Real.pi * a^4)/.2) * Real.sin α * Real.cos α^2 := by sorry
