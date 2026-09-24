import Mathlib

set_option linter.style.longLine false

noncomputable section

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def VectorCurveInt (C : Set (ℝ × ℝ)) (ω : ℝ) : ℝ := 0
def ImproperIntZeroAtTop (f : ℝ → ℝ) : ℝ := ∫ t in (0 : ℝ)..(1 : ℝ), f t
def atTopEval (f : ℝ → ℝ) : ℝ := 0
def omegaXY : ℝ := 0

-- exercise: exercise_4310
-- Source: area enclosed by (x+y)^2 = a*x and the Ox axis.

def exercise_4310_C1 (a : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ t : ℝ, t ≥ 0 ∧ p.1 = (a /. ((1 + t) ^ (2 : ℕ))) ∧
    p.2 = (a * t) /. ((1 + t) ^ (2 : ℕ))}

def exercise_4310_C2 (a : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ a ∧ p.2 = 0}

def exercise_4310_integrand (t : ℝ) : ℝ :=
  1 /. ((1 + t) ^ (4 : ℕ))

def exercise_4310_antideriv (a t : ℝ) : ℝ :=
  -((a ^ (2 : ℕ)) /. 6) * (1 /. ((1 + t) ^ (3 : ℕ)))

-- GAP 1: parameter equations x(t)=a/(1+t)^2 and y(t)=a*t/(1+t)^2 for t >= 0.
theorem proof_gap_exercise_4310_1
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)) := by
  sorry

-- GAP 2: C1 ∩ C2 consists of the two intersection points (0,0) and (a,0).
theorem proof_gap_exercise_4310_2
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)))
  : C1 ∩ C2 = ({(0, 0), (a, 0)} : Set (ℝ × ℝ)) := by
  sorry

-- GAP 3: the Ox-axis segment contributes zero to x dy - y dx.
theorem proof_gap_exercise_4310_3
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)))
  (hinter : C1 ∩ C2 = ({(0, 0), (a, 0)} : Set (ℝ × ℝ)))
  : VectorCurveInt C2 omegaXY = 0 := by
  sorry

-- GAP 4: the parabolic arc integral becomes ∫_0^∞ a^2/(1+t)^4 dt.
theorem proof_gap_exercise_4310_4
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)))
  (hinter : C1 ∩ C2 = ({(0, 0), (a, 0)} : Set (ℝ × ℝ)))
  (haxis : VectorCurveInt C2 omegaXY = 0)
  : VectorCurveInt C1 omegaXY =
      ImproperIntZeroAtTop (fun t => (a ^ (2 : ℕ)) /. ((1 + t) ^ (4 : ℕ))) := by
  sorry

-- GAP 5: Green-area formula for the whole boundary C.
theorem proof_gap_exercise_4310_5
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)))
  (hinter : C1 ∩ C2 = ({(0, 0), (a, 0)} : Set (ℝ × ℝ)))
  (haxis : VectorCurveInt C2 omegaXY = 0)
  (harc : VectorCurveInt C1 omegaXY =
      ImproperIntZeroAtTop (fun t => (a ^ (2 : ℕ)) /. ((1 + t) ^ (4 : ℕ))))
  : S = (1 /. 2) * VectorCurveInt C omegaXY := by
  sorry

-- GAP 6: factor out a^2/2 from the improper integral.
theorem proof_gap_exercise_4310_6
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)))
  (hinter : C1 ∩ C2 = ({(0, 0), (a, 0)} : Set (ℝ × ℝ)))
  (haxis : VectorCurveInt C2 omegaXY = 0)
  (harc : VectorCurveInt C1 omegaXY =
      ImproperIntZeroAtTop (fun t => (a ^ (2 : ℕ)) /. ((1 + t) ^ (4 : ℕ))))
  (harea : S = (1 /. 2) * VectorCurveInt C omegaXY)
  : S = ((a ^ (2 : ℕ)) /. 2) * ImproperIntZeroAtTop exercise_4310_integrand := by
  sorry

-- GAP 7: evaluate by the antiderivative -a^2/(6(1+t)^3) from 0 to +∞.
theorem proof_gap_exercise_4310_7
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)))
  (hinter : C1 ∩ C2 = ({(0, 0), (a, 0)} : Set (ℝ × ℝ)))
  (haxis : VectorCurveInt C2 omegaXY = 0)
  (harc : VectorCurveInt C1 omegaXY =
      ImproperIntZeroAtTop (fun t => (a ^ (2 : ℕ)) /. ((1 + t) ^ (4 : ℕ))))
  (harea : S = (1 /. 2) * VectorCurveInt C omegaXY)
  (hint : S = ((a ^ (2 : ℕ)) /. 2) * ImproperIntZeroAtTop exercise_4310_integrand)
  : S = atTopEval (exercise_4310_antideriv a) - exercise_4310_antideriv a 0 := by
  sorry

-- GAP 8: final area a^2/6.
theorem proof_gap_exercise_4310_8
  (a S : ℝ)
  (C C1 C2 : Set (ℝ × ℝ))
  (x y : ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0)
  (hC_sub : C ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC1_sub : C1 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hC2_sub : C2 ⊆ (Set.univ : Set (ℝ × ℝ)))
  (hS : S ∈ (Set.univ : Set ℝ))
  (hC1 : C1 = exercise_4310_C1 a)
  (hC2 : C2 = exercise_4310_C2 a)
  (hC : C = C1 ∪ C2)
  (hparam : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0 →
      x t = (a /. ((1 + t) ^ (2 : ℕ))) ∧
        y t = (a * t) /. ((1 + t) ^ (2 : ℕ)))
  (hinter : C1 ∩ C2 = ({(0, 0), (a, 0)} : Set (ℝ × ℝ)))
  (haxis : VectorCurveInt C2 omegaXY = 0)
  (harc : VectorCurveInt C1 omegaXY =
      ImproperIntZeroAtTop (fun t => (a ^ (2 : ℕ)) /. ((1 + t) ^ (4 : ℕ))))
  (harea : S = (1 /. 2) * VectorCurveInt C omegaXY)
  (hint : S = ((a ^ (2 : ℕ)) /. 2) * ImproperIntZeroAtTop exercise_4310_integrand)
  (hanti : S = atTopEval (exercise_4310_antideriv a) - exercise_4310_antideriv a 0)
  : S = (a ^ (2 : ℕ)) /. 6 := by
  sorry

end
