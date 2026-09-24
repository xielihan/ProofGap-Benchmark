import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

abbrev RealSet : Set ℝ := Set.univ
abbrev Plane := ℝ × ℝ
def CartesianProd (A B : Set ℝ) : Set Plane := Set.prod A B
def diff {α : Type*} (_x : α) : ℝ := 1
def VolumeInt (_S : Set Plane) (_ω : ℝ) : ℝ := 0
def DefInt (_a _b : EReal) (_ω : ℝ) : ℝ := 0
def ContinuousFuncOn (_f : ℝ → ℝ → ℝ) (_S : Set Plane) : Prop := True
def BoundedFuncOn (_f : ℝ → ℝ → ℝ) (_S : Set Plane) : Prop := True
def Defined (_f : ℝ → ℝ → ℝ) (_S : Set Plane) : Prop := True
def finite (x : ℝ) : Prop := (x : EReal) < (⊤ : EReal)
def divergentToTop (x : ℝ) : Prop := (x : EReal) = ⊤
noncomputable def powr (x p : ℝ) : ℝ := Real.rpow x p
noncomputable def abspow (x p : ℝ) : ℝ := Real.rpow |x| p
noncomputable def sqrtn (_n : ℕ) (x : ℝ) : ℝ := Real.sqrt x
noncomputable def limZeroPos (_f : ℝ → ℝ) : EReal := 0
noncomputable def casesRadial (p : ℝ) : EReal := if p < 1 then ((1/(2*(1-p)) : ℝ) : EReal) else ⊤
noncomputable def jac (_x _y : ℝ → ℝ → ℝ) : ℝ := 0

-- exercise: exercise_4184

/-- Exercise 4184, gap 1. -/
theorem proof_gap_exercise_4184_1
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  ∃ m M : ℝ, m ∈ RealSet ∧ M ∈ RealSet ∧ ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ 0 ≤ x ∧ x ≤ a ∧ 0 ≤ y ∧ y ≤ a ∧ x ≠ y → m/abspow (x-y) p ≤ |φ x y|/abspow (x-y) p ∧ |φ x y|/abspow (x-y) p ≤ M/abspow (x-y) p := by
  sorry

/-- Exercise 4184, gap 2. -/
theorem proof_gap_exercise_4184_2
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  finite (VolumeInt D (φ x y/abspow (x-y) p*diff x*diff y)) ↔ finite (VolumeInt D (1/abspow (x-y) p*diff x*diff y)) := by
  sorry

/-- Exercise 4184, gap 3. -/
theorem proof_gap_exercise_4184_3
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  VolumeInt D (1/abspow (x-y) p*diff x*diff y)=2*VolumeInt T (1/powr (x-y) p*diff x*diff y) := by
  sorry

/-- Exercise 4184, gap 4. -/
theorem proof_gap_exercise_4184_4
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p < 1 → VolumeInt T (1/powr (x-y) p*diff x*diff y)=DefInt 0 a (DefInt 0 x (1/powr (x-y) p*diff y)*diff x) := by
  sorry

/-- Exercise 4184, gap 5. -/
theorem proof_gap_exercise_4184_5
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p < 1 → DefInt 0 a (DefInt 0 x (1/powr (x-y) p*diff y)*diff x)=DefInt 0 a (powr x (1-p)/(1-p)*diff x) := by
  sorry

/-- Exercise 4184, gap 6. -/
theorem proof_gap_exercise_4184_6
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p < 1 → DefInt 0 a (powr x (1-p)/(1-p)*diff x)=powr a (2-p)/((1-p)*(2-p)) := by
  sorry

/-- Exercise 4184, gap 7. -/
theorem proof_gap_exercise_4184_7
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p < 1 → VolumeInt D (1/abspow (x-y) p*diff x*diff y)=2*powr a (2-p)/((1-p)*(2-p)) := by
  sorry

/-- Exercise 4184, gap 8. -/
theorem proof_gap_exercise_4184_8
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p < 1 → finite (VolumeInt D (1/abspow (x-y) p*diff x*diff y)) := by
  sorry

/-- Exercise 4184, gap 9. -/
theorem proof_gap_exercise_4184_9
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p = 1 → (VolumeInt T (1/powr (x-y) p*diff x*diff y) : EReal) =
    limZeroPos (fun ε => VolumeInt {z : Plane | ε ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1-ε} (1/(x-y)*diff x*diff y)) := by
  sorry

/-- Exercise 4184, gap 10. -/
theorem proof_gap_exercise_4184_10
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  ∀ ε : ℝ, ε ∈ RealSet ∧ 0 < ε ∧ ε ≤ a ∧ p = 1 → VolumeInt {z : Plane | ε ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1-ε} (1/(x-y)*diff x*diff y)=DefInt ε a ((Real.log x-Real.log ε)*diff x) := by
  sorry

/-- Exercise 4184, gap 11. -/
theorem proof_gap_exercise_4184_11
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  ∀ ε : ℝ, ε ∈ RealSet ∧ 0 < ε ∧ ε ≤ a ∧ p = 1 → DefInt ε a ((Real.log x-Real.log ε)*diff x)=a*Real.log a-a+ε-a*Real.log ε := by
  sorry

/-- Exercise 4184, gap 12. -/
theorem proof_gap_exercise_4184_12
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p = 1 → limZeroPos (fun ε => a*Real.log a-a+ε-a*Real.log ε)=⊤ := by
  sorry

/-- Exercise 4184, gap 13. -/
theorem proof_gap_exercise_4184_13
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p = 1 → divergentToTop (VolumeInt D (1/abspow (x-y) p*diff x*diff y)) := by
  sorry

/-- Exercise 4184, gap 14. -/
theorem proof_gap_exercise_4184_14
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  ∀ ε : ℝ, ε ∈ RealSet ∧ 0 < ε ∧ ε ≤ a ∧ p = 2 → VolumeInt {z : Plane | ε ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1-ε} (1/powr (x-y) 2*diff x*diff y)=DefInt ε a ((1/ε-1/x)*diff x) := by
  sorry

/-- Exercise 4184, gap 15. -/
theorem proof_gap_exercise_4184_15
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  ∀ ε : ℝ, ε ∈ RealSet ∧ 0 < ε ∧ ε ≤ a ∧ p = 2 → DefInt ε a ((1/ε-1/x)*diff x)=a/ε-1-Real.log a+Real.log ε := by
  sorry

/-- Exercise 4184, gap 16. -/
theorem proof_gap_exercise_4184_16
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p = 2 → limZeroPos (fun ε => a/ε-1-Real.log a+Real.log ε)=⊤ := by
  sorry

/-- Exercise 4184, gap 17. -/
theorem proof_gap_exercise_4184_17
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p = 2 → divergentToTop (VolumeInt D (1/abspow (x-y) p*diff x*diff y)) := by
  sorry

/-- Exercise 4184, gap 18. -/
theorem proof_gap_exercise_4184_18
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  ∀ ε : ℝ, ε ∈ RealSet ∧ 0 < ε ∧ ε ≤ a ∧ p > 1 ∧ p ≠ 2 → VolumeInt {z : Plane | ε ≤ z.1 ∧ z.1 ≤ a ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1-ε} (1/powr (x-y) p*diff x*diff y)= (1/(p-1))*DefInt ε a ((powr ε (1-p)-powr x (1-p))*diff x) := by
  sorry

/-- Exercise 4184, gap 19. -/
theorem proof_gap_exercise_4184_19
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  ∀ ε : ℝ, ε ∈ RealSet ∧ 0 < ε ∧ ε ≤ a ∧ p > 1 ∧ p ≠ 2 → (1/(p-1))*DefInt ε a ((powr ε (1-p)-powr x (1-p))*diff x)=1/((p-1)*powr ε (p-1))*(a-((p-1)/(p-2))*ε)+1/((p-1)*(p-2)*powr a (p-2)) := by
  sorry

/-- Exercise 4184, gap 20. -/
theorem proof_gap_exercise_4184_20
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p > 1 → p ≠ 2 → limZeroPos (fun ε => 1/((p-1)*powr ε (p-1))*(a-((p-1)/(p-2))*ε)+1/((p-1)*(p-2)*powr a (p-2)))=⊤ := by
  sorry

/-- Exercise 4184, gap 21. -/
theorem proof_gap_exercise_4184_21
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p > 1 → p ≠ 2 → divergentToTop (VolumeInt D (1/abspow (x-y) p*diff x*diff y)) := by
  sorry

/-- Exercise 4184, gap 22. -/
theorem proof_gap_exercise_4184_22
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  finite (VolumeInt D (φ x y/abspow (x-y) p*diff x*diff y)) ↔ p < 1 := by
  sorry

/-- Exercise 4184, gap 23. -/
theorem proof_gap_exercise_4184_23
  (a p x y : ℝ) (φ : ℝ → ℝ → ℝ) (D T : Set Plane)
  (ha : a > 0) (hD : D = CartesianProd (Set.Icc 0 a) (Set.Icc 0 a))
  (hT : T = {z : Plane | z.1 ∈ RealSet ∧ z.2 ∈ RealSet ∧ z.1 ≥ 0 ∧ z.1 ≤ a ∧ z.2 ≥ 0 ∧ z.2 ≤ z.1})
  (hdef : Defined φ D) (hcont : ContinuousFuncOn φ D) (hbdd : BoundedFuncOn φ D) :
  p ∈ {p : ℝ | p ∈ RealSet ∧ p < 1} ↔ finite (VolumeInt D (φ x y/abspow (x-y) p*diff x*diff y)) := by
  sorry
