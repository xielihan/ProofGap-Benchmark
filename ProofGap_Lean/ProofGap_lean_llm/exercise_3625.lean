import Mathlib

set_option linter.style.longLine false
open scoped BigOperators Topology

abbrev R2 := ℝ × ℝ
noncomputable def coordDeriv (f : R2 -> ℝ) (coord : ℕ) : R2 -> ℝ :=
  fun p =>
    if coord = 1 then deriv (fun t : ℝ => f (t, p.2)) p.1
    else if coord = 2 then deriv (fun t : ℝ => f (p.1, t)) p.2
    else f p
noncomputable def FunDeri (f : R2 -> ℝ) (coord order : ℕ) : R2 -> ℝ :=
  Nat.iterate (coordDeriv · coord) order f
def FuncOfClassKOn (f : R2 -> ℝ) (s : Set R2) (k : ℕ) : Prop := ContDiffOn ℝ k f s
def Dom (f : R2 -> ℝ) : Set R2 := {p | DifferentiableAt ℝ f p}
def MaximumPoint (f : R2 -> ℝ) : Set R2 := {p | ∀ q, f q ≤ f p}
def MinimumPoint (f : R2 -> ℝ) : Set R2 := {p | ∀ q, f p ≤ f q}
def approxPow (h : ℝ) (n : ℕ) (a b : ℝ) : Prop := Tendsto (fun k : ℕ => a + b / (k + 1 : ℝ) ^ n) atTop (nhds h)
def diffX (x y : ℝ) : ℝ := x - 1
def diffY (x y : ℝ) : ℝ := y - 1

-- exercise: exercise_3625

-- Source: proofgap/exercise_3625/1.txt
theorem proof_gap_exercise_3625_1
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y) := by
  sorry

-- Source: proofgap/exercise_3625/2.txt
theorem proof_gap_exercise_3625_2
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y) := by
  sorry

-- Source: proofgap/exercise_3625/3.txt
theorem proof_gap_exercise_3625_3
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3) := by
  sorry

-- Source: proofgap/exercise_3625/4.txt
theorem proof_gap_exercise_3625_4
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  : A=-162 := by
  sorry

-- Source: proofgap/exercise_3625/5.txt
theorem proof_gap_exercise_3625_5
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  : B=-108 := by
  sorry

-- Source: proofgap/exercise_3625/6.txt
theorem proof_gap_exercise_3625_6
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  : C=-144 := by
  sorry

-- Source: proofgap/exercise_3625/7.txt
theorem proof_gap_exercise_3625_7
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  (h7 : C=-144)
  : A*C-B^2>0 := by
  sorry

-- Source: proofgap/exercise_3625/8.txt
theorem proof_gap_exercise_3625_8
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  (h7 : C=-144)
  (h8 : A*C-B^2>0)
  : z (2,3)=108 := by
  sorry

-- Source: proofgap/exercise_3625/9.txt
theorem proof_gap_exercise_3625_9
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  (h7 : C=-144)
  (h8 : A*C-B^2>0)
  (h9 : z (2,3)=108)
  : MaximumPoint z = ({(2,3)} ∪ {p | p.1=0 ∧ (p.2<0 ∨ p.2>6)}) := by
  sorry

-- Source: proofgap/exercise_3625/10.txt
theorem proof_gap_exercise_3625_10
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  (h7 : C=-144)
  (h8 : A*C-B^2>0)
  (h9 : z (2,3)=108)
  (h10 : MaximumPoint z = ({(2,3)} ∪ {p | p.1=0 ∧ (p.2<0 ∨ p.2>6)}))
  : MinimumPoint z = {p | p.1=0 ∧ 0<p.2 ∧ p.2<6} := by
  sorry

-- Source: proofgap/exercise_3625/11.txt
theorem proof_gap_exercise_3625_11
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  (h7 : C=-144)
  (h8 : A*C-B^2>0)
  (h9 : z (2,3)=108)
  (h10 : MaximumPoint z = ({(2,3)} ∪ {p | p.1=0 ∧ (p.2<0 ∨ p.2>6)}))
  (h11 : MinimumPoint z = {p | p.1=0 ∧ 0<p.2 ∧ p.2<6})
  : ∀ x : ℝ, x≠0 ∧ x≠6 -> ¬((x,0)∈MaximumPoint z ∨ (x,0)∈MinimumPoint z) := by
  sorry

-- Source: proofgap/exercise_3625/12.txt
theorem proof_gap_exercise_3625_12
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  (h7 : C=-144)
  (h8 : A*C-B^2>0)
  (h9 : z (2,3)=108)
  (h10 : MaximumPoint z = ({(2,3)} ∪ {p | p.1=0 ∧ (p.2<0 ∨ p.2>6)}))
  (h11 : MinimumPoint z = {p | p.1=0 ∧ 0<p.2 ∧ p.2<6})
  (h12 : ∀ x : ℝ, x≠0 ∧ x≠6 -> ¬((x,0)∈MaximumPoint z ∨ (x,0)∈MinimumPoint z))
  : ¬((0,0)∈MaximumPoint z ∨ (0,0)∈MinimumPoint z) := by
  sorry

-- Source: proofgap/exercise_3625/13.txt
theorem proof_gap_exercise_3625_13
  (z : R2 -> ℝ)
  (A B C : ℝ)
  (h1 : ∀ x y : ℝ, z (x,y) = x^2*y^3*(6-x-y))
  (h2 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=x*y^3*(12-3*x-2*y))
  (h3 : ∀ x y : ℝ, FunDeri z 2 1 (x,y)=x^2*y^2*(18-3*x-4*y))
  (h4 : ∀ x y : ℝ, FunDeri z 1 1 (x,y)=0 ∧ FunDeri z 2 1 (x,y)=0 ↔ x=0 ∨ y=0 ∨ (x,y)=(2,3))
  (h5 : A=-162)
  (h6 : B=-108)
  (h7 : C=-144)
  (h8 : A*C-B^2>0)
  (h9 : z (2,3)=108)
  (h10 : MaximumPoint z = ({(2,3)} ∪ {p | p.1=0 ∧ (p.2<0 ∨ p.2>6)}))
  (h11 : MinimumPoint z = {p | p.1=0 ∧ 0<p.2 ∧ p.2<6})
  (h12 : ∀ x : ℝ, x≠0 ∧ x≠6 -> ¬((x,0)∈MaximumPoint z ∨ (x,0)∈MinimumPoint z))
  (h13 : ¬((0,0)∈MaximumPoint z ∨ (0,0)∈MinimumPoint z))
  : ¬((6,0)∈MaximumPoint z ∨ (6,0)∈MinimumPoint z) := by
  sorry
