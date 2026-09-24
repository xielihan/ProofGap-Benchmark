import Mathlib

set_option linter.style.longLine false

noncomputable section

open scoped Real

axiom TripleIntegral4194 : (ℝ → ℝ → ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → EReal
axiom UnitTripleIntegral4194 : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → EReal
axiom F4194 : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → EReal
axiom TransformedF4194 : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → EReal
axiom DiskBoundIntegral4194 : ℝ → ℝ → EReal
axiom RadialBoundIntegral4194 : ℝ → ℝ → ℝ → EReal
axiom IntervalIntegralF4194 : (ℝ → EReal) → ℝ → EReal
axiom ConvergentIntegral4194 : EReal → Prop
axiom DivergentIntegral4194 : EReal → Prop
axiom BoundedOn4194 : (ℝ → EReal) → Set ℝ → Prop

def InCube4194 (a x y z : ℝ) : Prop :=
  x ∈ Set.Icc 0 a ∧ y ∈ Set.Icc 0 a ∧ z ∈ Set.Icc 0 a

def InsideSingularTrace4194 (a : ℝ) (phi psi : ℝ → ℝ) : Prop :=
  ∃ x : ℝ, x ∈ Set.Icc 0 a ∧ 0 ≤ phi x ∧ phi x ≤ a ∧ 0 ≤ psi x ∧ psi x ≤ a

def StrictInsideSingularTrace4194 (a : ℝ) (phi psi : ℝ → ℝ) : Prop :=
  ∃ x : ℝ, x ∈ Set.Icc 0 a ∧ 0 < phi x ∧ phi x < a ∧ 0 < psi x ∧ psi x < a

def LocalInteriorBand4194 (a eps : ℝ) (I0 : Set ℝ) (phi psi : ℝ → ℝ) : Prop :=
  eps > 0 ∧ I0 ⊆ Set.Icc 0 a ∧ ∀ x : ℝ, x ∈ I0 →
    eps ≤ phi x ∧ phi x ≤ a - eps ∧ eps ≤ psi x ∧ psi x ≤ a - eps

-- exercise: exercise_4194

-- GAP 1: lower comparison m/denom ≤ |f|/denom on the cube.
theorem proof_gap_exercise_4194_1
    (a p m M : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (phi psi : ℝ → ℝ)
    (ha : a > 0) (hm : m > 0)
    (hf : ∀ x y z : ℝ, InCube4194 a x y z → 0 < m ∧ m ≤ |f x y z| ∧ |f x y z| ≤ M)
    (hphi : ContinuousOn phi (Set.Icc 0 a)) (hpsi : ContinuousOn psi (Set.Icc 0 a)) :
    ∀ x y z : ℝ, InCube4194 a x y z →
      (m / (((y - phi x) ^ 2 + (z - psi x) ^ 2) ^ p)) ≤
        (|f x y z| / (((y - phi x) ^ 2 + (z - psi x) ^ 2) ^ p)) := by
  sorry

-- GAP 2: upper comparison |f|/denom ≤ M/denom on the cube.
theorem proof_gap_exercise_4194_2
    (a p m M : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (phi psi : ℝ → ℝ)
    (ha : a > 0) (hm : m > 0)
    (hf : ∀ x y z : ℝ, InCube4194 a x y z → 0 < m ∧ m ≤ |f x y z| ∧ |f x y z| ≤ M)
    (hphi : ContinuousOn phi (Set.Icc 0 a)) (hpsi : ContinuousOn psi (Set.Icc 0 a))
    (hcmp₁ : ∀ x y z : ℝ, InCube4194 a x y z →
      (m / (((y - phi x) ^ 2 + (z - psi x) ^ 2) ^ p)) ≤
        (|f x y z| / (((y - phi x) ^ 2 + (z - psi x) ^ 2) ^ p))) :
    ∀ x y z : ℝ, InCube4194 a x y z →
      (|f x y z| / (((y - phi x) ^ 2 + (z - psi x) ^ 2) ^ p)) ≤
        (M / (((y - phi x) ^ 2 + (z - psi x) ^ 2) ^ p)) := by
  sorry

-- GAP 3: convergence equivalence with the integral whose numerator is 1.
theorem proof_gap_exercise_4194_3
    (a p m M : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (phi psi : ℝ → ℝ) :
    ConvergentIntegral4194 (TripleIntegral4194 f phi psi a p) ↔
      ConvergentIntegral4194 (UnitTripleIntegral4194 phi psi a p) := by
  sorry

-- GAP 4: Tonelli/Fubini reduction to ∫ F(x) dx.
theorem proof_gap_exercise_4194_4
    (a p : ℝ) (phi psi : ℝ → ℝ) :
    UnitTripleIntegral4194 phi psi a p =
      IntervalIntegralF4194 (fun x => F4194 phi psi p x) a := by
  sorry

-- GAP 5: translation in y,z gives the shifted rectangle integral defining F.
theorem proof_gap_exercise_4194_5
    (a p : ℝ) (phi psi : ℝ → ℝ) :
    ∀ x : ℝ, x ∈ Set.Icc 0 a →
      F4194 phi psi p x = TransformedF4194 phi psi p x := by
  sorry

-- GAP 6: for p<1, F is bounded above by the polar disk integral.
theorem proof_gap_exercise_4194_6
    (a p c : ℝ) (phi psi : ℝ → ℝ) :
    p < 1 → c = sSup ((fun x => |phi x| + |psi x|) '' Set.Icc 0 a) →
      ∀ x : ℝ, x ∈ Set.Icc 0 a → F4194 phi psi p x ≤ DiskBoundIntegral4194 p (a + c) := by
  sorry

-- GAP 7: evaluation of the polar bound for p<1.
theorem proof_gap_exercise_4194_7
    (a p c : ℝ) (phi psi : ℝ → ℝ) :
    p < 1 → (∀ x : ℝ, x ∈ Set.Icc 0 a → F4194 phi psi p x ≤ DiskBoundIntegral4194 p (a + c)) →
      ∀ x : ℝ, x ∈ Set.Icc 0 a →
        F4194 phi psi p x ≤
          ((((Real.pi) / (1 - p)) * (Real.sqrt 2 * (a + c)) ^ (2 - 2 * p) : ℝ) : EReal) := by
  sorry

-- GAP 8: boundedness of F on [0,a] for p<1.
theorem proof_gap_exercise_4194_8
    (a p c : ℝ) (phi psi : ℝ → ℝ) :
    p < 1 →
      (∀ x : ℝ, x ∈ Set.Icc 0 a →
        F4194 phi psi p x ≤
          ((((Real.pi) / (1 - p)) * (Real.sqrt 2 * (a + c)) ^ (2 - 2 * p) : ℝ) : EReal)) →
      BoundedOn4194 (fun x => F4194 phi psi p x) (Set.Icc 0 a) := by
  sorry

-- GAP 9: convergence of ∫F for p<1.
theorem proof_gap_exercise_4194_9
    (a p : ℝ) (phi psi : ℝ → ℝ) :
    p < 1 → BoundedOn4194 (fun x => F4194 phi psi p x) (Set.Icc 0 a) →
      ConvergentIntegral4194 (IntervalIntegralF4194 (fun x => F4194 phi psi p x) a) := by
  sorry

-- GAP 10: no singular trace in the cube implies denominator positivity for p≥1.
theorem proof_gap_exercise_4194_10
    (a p : ℝ) (phi psi : ℝ → ℝ) :
    p ≥ 1 → ¬ InsideSingularTrace4194 a phi psi →
      ∀ x y z : ℝ, InCube4194 a x y z →
        0 < (((y - phi x) ^ 2 + (z - psi x) ^ 2) ^ p) := by
  sorry

-- GAP 11: ordinary convergence when p≥1 and no singular trace enters the cube.
theorem proof_gap_exercise_4194_11
    (a p : ℝ) (phi psi : ℝ → ℝ) :
    p ≥ 1 → ¬ InsideSingularTrace4194 a phi psi →
      ConvergentIntegral4194 (IntervalIntegralF4194 (fun x => F4194 phi psi p x) a) := by
  sorry

-- GAP 12: an interior singular point yields a closed subinterval band away from the boundary.
theorem proof_gap_exercise_4194_12
    (a p : ℝ) (phi psi : ℝ → ℝ) :
    p ≥ 1 → StrictInsideSingularTrace4194 a phi psi →
      ∃ eps : ℝ, ∃ I0 : Set ℝ, LocalInteriorBand4194 a eps I0 phi psi := by
  sorry

-- GAP 13: lower bound by the divergent radial integral on the local band.
theorem proof_gap_exercise_4194_13
    (a p eps : ℝ) (I0 : Set ℝ) (phi psi : ℝ → ℝ) :
    p ≥ 1 → StrictInsideSingularTrace4194 a phi psi → LocalInteriorBand4194 a eps I0 phi psi →
      ∀ x : ℝ, x ∈ I0 → F4194 phi psi p x ≥ RadialBoundIntegral4194 p eps x := by
  sorry

-- GAP 14: F is +∞ on the local band for p≥1.
theorem proof_gap_exercise_4194_14
    (a p eps : ℝ) (I0 : Set ℝ) (phi psi : ℝ → ℝ) :
    p ≥ 1 → StrictInsideSingularTrace4194 a phi psi → LocalInteriorBand4194 a eps I0 phi psi →
      ∀ x : ℝ, x ∈ I0 → F4194 phi psi p x = ⊤ := by
  sorry

-- GAP 15: divergence of ∫F when an interior singular trace exists.
theorem proof_gap_exercise_4194_15
    (a p : ℝ) (phi psi : ℝ → ℝ) :
    p ≥ 1 → StrictInsideSingularTrace4194 a phi psi →
      DivergentIntegral4194 (IntervalIntegralF4194 (fun x => F4194 phi psi p x) a) := by
  sorry

-- GAP 16: final convergence criterion for the original integral.
theorem proof_gap_exercise_4194_16
    (a p : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (phi psi : ℝ → ℝ) :
    (p < 1 ∨ p ≥ 1 ∧ ¬ InsideSingularTrace4194 a phi psi) ↔
      ConvergentIntegral4194 (TripleIntegral4194 f phi psi a p) := by
  sorry
