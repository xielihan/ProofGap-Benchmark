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

-- exercise: exercise_4183

/-- Source: proofgap/exercise_4183/1.txt. -/
theorem proof_gap_exercise_4183_1
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  VolumeInt D (1/(abspow x p + abspow y q)*diff x*diff y) = 4 * VolumeInt Q (1/(powr x p + powr y q)*diff x*diff y) := by
  sorry

/-- Source: proofgap/exercise_4183/2.txt. -/
theorem proof_gap_exercise_4183_2
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  4*VolumeInt Q (1/(powr x p + powr y q)*diff x*diff y)=4*VolumeInt Ω1 (1/(powr x p + powr y q)*diff x*diff y)+4*VolumeInt Ω2 (1/(powr x p + powr y q)*diff x*diff y) := by
  sorry

/-- Source: proofgap/exercise_4183/3.txt. -/
theorem proof_gap_exercise_4183_3
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ x ≥ 0 ∧ y ≥ 0 ∧ powr x p + powr y q ≤ 1 / powr 2 (p+q) → x ≤ 1/2 := by
  sorry

/-- Source: proofgap/exercise_4183/4.txt. -/
theorem proof_gap_exercise_4183_4
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ x ≥ 0 ∧ y ≥ 0 ∧ powr x p + powr y q ≤ 1 / powr 2 (p+q) → y ≤ 1/2 := by
  sorry

/-- Source: proofgap/exercise_4183/5.txt. -/
theorem proof_gap_exercise_4183_5
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  ∀ x y : ℝ, x ∈ RealSet ∧ y ∈ RealSet ∧ x ≥ 0 ∧ y ≥ 0 ∧ powr x p + powr y q ≤ 1 / powr 2 (p+q) → x + y ≤ 1 := by
  sorry

/-- Source: proofgap/exercise_4183/6.txt. -/
theorem proof_gap_exercise_4183_6
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  Ω3 = Ω2 := by
  sorry

/-- Source: proofgap/exercise_4183/7.txt. -/
theorem proof_gap_exercise_4183_7
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  ContinuousFuncOn (fun x y => 1/(powr x p + powr y q)) Ω1 := by
  sorry

/-- Source: proofgap/exercise_4183/8.txt. -/
theorem proof_gap_exercise_4183_8
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  finite (VolumeInt Ω1 (1/(powr x p + powr y q)*diff x*diff y)) := by
  sorry

/-- Source: proofgap/exercise_4183/9.txt. -/
theorem proof_gap_exercise_4183_9
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  finite (VolumeInt D (1/(abspow x p+abspow y q)*diff x*diff y)) ↔ finite (VolumeInt Ω3 (1/(powr x p+powr y q)*diff x*diff y)) := by
  sorry

/-- Source: proofgap/exercise_4183/10.txt. -/
theorem proof_gap_exercise_4183_10
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  ∀ r θ : ℝ, r ∈ RealSet ∧ 0 ≤ r ∧ r ≤ powr (sqrtn 2 2) (-p-q) ∧ θ ∈ RealSet ∧ 0 ≤ θ ∧ θ ≤ Real.pi/2 → X r θ = powr r (2/p) * powr (Real.cos θ) (2/p) := by
  sorry

/-- Source: proofgap/exercise_4183/11.txt. -/
theorem proof_gap_exercise_4183_11
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  ∀ r θ : ℝ, r ∈ RealSet ∧ 0 ≤ r ∧ r ≤ powr (sqrtn 2 2) (-p-q) ∧ θ ∈ RealSet ∧ 0 ≤ θ ∧ θ ≤ Real.pi/2 → Y r θ = powr r (2/q) * powr (Real.sin θ) (2/q) := by
  sorry

/-- Source: proofgap/exercise_4183/12.txt. -/
theorem proof_gap_exercise_4183_12
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  ∀ r θ : ℝ, r ∈ RealSet ∧ 0 ≤ r ∧ r ≤ powr (sqrtn 2 2) (-p-q) ∧ θ ∈ RealSet ∧ 0 ≤ θ ∧ θ ≤ Real.pi/2 → jac X Y = (4/(p*q))*powr r (2/p+2/q-1)*powr (Real.sin θ) (2/q-1)*powr (Real.cos θ) (2/p-1) := by
  sorry

/-- Source: proofgap/exercise_4183/13.txt. -/
theorem proof_gap_exercise_4183_13
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  VolumeInt Ω3 (1/(powr x p+powr y q)*diff x*diff y)= (4/(p*q))*DefInt 0 (Real.pi/2) (powr (Real.sin θ) (2/q-1)*powr (Real.cos θ) (2/p-1)*diff θ)*DefInt 0 (powr (sqrtn 2 2) (-p-q)) (powr r (2/p+2/q-3)*diff r) := by
  sorry

/-- Source: proofgap/exercise_4183/14.txt. -/
theorem proof_gap_exercise_4183_14
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  finite (DefInt 0 (powr (sqrtn 2 2) (-p-q)) (powr r (2/p+2/q-3)*diff r)) ↔ 2/p+2/q-3 > -1 := by
  sorry

/-- Source: proofgap/exercise_4183/15.txt. -/
theorem proof_gap_exercise_4183_15
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  2/p+2/q-3 > -1 ↔ 1/p+1/q > 1 := by
  sorry

/-- Source: proofgap/exercise_4183/16.txt. -/
theorem proof_gap_exercise_4183_16
  (p q x y r θ : ℝ) (D Ω1 Ω2 Ω3 Q : Set Plane) (X Y : ℝ → ℝ → ℝ)
  (hp : p > 0) (hq : q > 0) :
  finite (VolumeInt D (1/(abspow x p+abspow y q)*diff x*diff y)) ↔ 1/p+1/q > 1 := by
  sorry
