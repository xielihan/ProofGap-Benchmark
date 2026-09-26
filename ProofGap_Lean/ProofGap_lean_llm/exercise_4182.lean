import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

abbrev RealSet : Set ℝ := {x : ℝ | x = x}
abbrev Plane := ℝ × ℝ
def CartesianProd (A B : Set ℝ) : Set Plane := Set.prod A B
def diff {α : Type*} [Norm α] (x : α) : ℝ := ‖x‖
noncomputable def VolumeInt (S : Set Plane) (ω : ℝ) : ℝ := (MeasureTheory.volume S).toReal * ω
noncomputable def DefInt (a b : EReal) (ω : ℝ) : ℝ := (b.toReal - a.toReal) * ω
def ContinuousFuncOn (f : ℝ → ℝ → ℝ) (S : Set Plane) : Prop := ContinuousOn (fun z : Plane => f z.1 z.2) S
def BoundedFuncOn (f : ℝ → ℝ → ℝ) (S : Set Plane) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, |f z.1 z.2| ≤ C
def Defined (f : ℝ → ℝ → ℝ) (S : Set Plane) : Prop := ∀ z ∈ S, f z.1 z.2 = f z.1 z.2
def finite (_x : ℝ) : Prop := (_x : EReal) < (⊤ : EReal)
def divergentToTop (_x : ℝ) : Prop := (_x : EReal) = ⊤
noncomputable def powr (x p : ℝ) : ℝ := Real.rpow x p
noncomputable def abspow (x p : ℝ) : ℝ := Real.rpow |x| p
noncomputable def sqrtn (_n : ℕ) (x : ℝ) : ℝ := Real.sqrt x
noncomputable def limZeroPos (f : ℝ → ℝ) : EReal := EReal.limsup (fun x => (f x : EReal)) (𝓝[>] 0)
noncomputable def casesRadial (p : ℝ) : EReal := if p < 1 then ((1/(2*(1-p)) : ℝ) : EReal) else ⊤
noncomputable def jac (x y : ℝ → ℝ → ℝ) : ℝ := deriv (fun s => x s 0) 0 * deriv (fun s => y 0 s) 0 - deriv (fun s => x 0 s) 0 * deriv (fun s => y s 0) 0

-- exercise: exercise_4182

/-- Source: proofgap/exercise_4182/1.txt. -/
theorem proof_gap_exercise_4182_1
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ≠ (0,0) → x^2+x*y+y^2 = (1/.2)*(x^2+y^2)+(1/.2)*(x+y)^2 ∧ (1/.2)*(x^2+y^2)+(1/.2)*(x+y)^2 > 0 := by
  sorry

/-- Source: proofgap/exercise_4182/2.txt. -/
theorem proof_gap_exercise_4182_2
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D ∧ (x,y) ≠ (0,0) → m / powr (x^2+x*y+y^2) p ≤ |φ x y| / powr (x^2+x*y+y^2) p ∧ |φ x y| / powr (x^2+x*y+y^2) p ≤ M / powr (x^2+x*y+y^2) p := by
  sorry

/-- Source: proofgap/exercise_4182/3.txt. -/
theorem proof_gap_exercise_4182_3
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  (∃ I : ℝ, I ∈ RealSet ∧ (I = VolumeInt D (φ x y / powr (x^2+x*y+y^2) p * diff x * diff y) ↔ ∃ J : ℝ, J ∈ RealSet ∧ J = VolumeInt D (1 / powr (x^2+x*y+y^2) p * diff x * diff y))) := by
  sorry

/-- Source: proofgap/exercise_4182/4.txt. -/
theorem proof_gap_exercise_4182_4
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  ∀ r θ : ℝ, r ∈ RealSet ∧ 0 ≤ r ∧ r ≤ 1 ∧ θ ∈ RealSet ∧ 0 ≤ θ ∧ θ ≤ 2*Real.pi → X r θ ^2 + X r θ * Y r θ + Y r θ ^2 = r^2 * (1 + (1/.2)*Real.sin (2*θ)) := by
  sorry

/-- Source: proofgap/exercise_4182/5.txt. -/
theorem proof_gap_exercise_4182_5
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  VolumeInt D (1 / powr (x^2+x*y+y^2) p * diff x * diff y) = DefInt 0 (2*Real.pi) (1 / powr (1+(1/.2)*Real.sin (2*θ)) p * diff θ) * DefInt 0 1 (1 / powr r (2*p-1) * diff r) := by
  sorry

/-- Source: proofgap/exercise_4182/6.txt. -/
theorem proof_gap_exercise_4182_6
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  ∀ θ : ℝ, θ ∈ RealSet ∧ θ ∈ Set.Icc 0 (2*Real.pi) → 1 + (1/.2)*Real.sin (2*θ) ≥ (1/.2) ∧ (1/.2:ℝ) > 0 := by
  sorry

/-- Source: proofgap/exercise_4182/7.txt. -/
theorem proof_gap_exercise_4182_7
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  ∃ A : ℝ, A ∈ RealSet ∧ A = DefInt 0 (2*Real.pi) (1 / powr (1+(1/.2)*Real.sin (2*θ)) p * diff θ) := by
  sorry

/-- Source: proofgap/exercise_4182/8.txt. -/
theorem proof_gap_exercise_4182_8
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  (DefInt 0 1 (1 / powr r (2*p-1) * diff r) : EReal) = casesRadial p := by
  sorry

/-- Source: proofgap/exercise_4182/9.txt. -/
theorem proof_gap_exercise_4182_9
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  p < 1 → ∃ J : ℝ, J ∈ RealSet ∧ J = VolumeInt D (1 / powr (x^2+x*y+y^2) p * diff x * diff y) := by
  sorry

/-- Source: proofgap/exercise_4182/10.txt. -/
theorem proof_gap_exercise_4182_10
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  p < 1 → ∃ I : ℝ, I ∈ RealSet ∧ I = VolumeInt D (φ x y / powr (x^2+x*y+y^2) p * diff x * diff y) := by
  sorry

/-- Source: proofgap/exercise_4182/11.txt. -/
theorem proof_gap_exercise_4182_11
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  p ≥ 1 → ¬(∃ J : ℝ, J ∈ RealSet ∧ J = VolumeInt D (1 / powr (x^2+x*y+y^2) p * diff x * diff y)) := by
  sorry

/-- Source: proofgap/exercise_4182/12.txt. -/
theorem proof_gap_exercise_4182_12
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  p ≥ 1 → ¬(∃ I : ℝ, I ∈ RealSet ∧ I = VolumeInt D (φ x y / powr (x^2+x*y+y^2) p * diff x * diff y)) := by
  sorry

/-- Source: proofgap/exercise_4182/13.txt. -/
theorem proof_gap_exercise_4182_13
  (p m M x y r θ : ℝ) (φ X Y : ℝ → ℝ → ℝ) (D : Set Plane)
  (hD : D = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1^2 + z.2^2 ≤ 1})
  (hcont : ContinuousFuncOn φ D) (hm : 0 < m)
  (hbound : ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ (x,y) ∈ D → m ≤ |φ x y| ∧ |φ x y| ≤ M) :
  p ∈ {p : ℝ | p ∈ RealSet ∧ p < 1} ↔ ∃ I : ℝ, I ∈ RealSet ∧ I = VolumeInt D (φ x y / powr (x^2+x*y+y^2) p * diff x * diff y) := by
  sorry
