import Mathlib

noncomputable section

namespace Exercise2158

abbrev RealSet := Set ℝ

def onUnit (x : ℝ) : Prop := -1 < x ∧ x < 1
def FunDeri (f : ℝ → ℝ) (_ n : ℕ) : ℝ → ℝ := Nat.iterate deriv n f
def AntiderivativeSet (F g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {G | ∀ x : ℝ, onUnit x → HasDerivAt G (g x) x ∧ ∀ y : ℝ, onUnit y → G y = F y}

def integrand (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2) * Real.arcsin x
def finalPrimitive (C x : ℝ) : ℝ :=
  (x / 2) * Real.sqrt (1 - x ^ 2) * Real.arcsin x - x ^ 2 / 4 +
    (Real.arcsin x) ^ 2 / 4 + C

-- Source: proofgap/exercise_2158/1.txt
theorem proof_gap_exercise_2158_1
    (C : ℝ) (I : ℝ → Set (ℝ → ℝ))
    (hC : C ∈ (Set.univ : RealSet))
    (hlo : ∀ x : ℝ, x ∈ (Set.univ : RealSet) → (-1 : ℝ) ≤ x)
    (hhi : ∀ x : ℝ, x ∈ (Set.univ : RealSet) → x ≤ (1 : ℝ))
    (hI : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      ∃ F₂ : ℝ → ℝ, I x = AntiderivativeSet F₂ integrand) :
    ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      ∃ F₃ F₅ : ℝ → ℝ,
        (∀ y : ℝ, y ∈ (Set.univ : RealSet) ∧ onUnit y →
          FunDeri F₃ 1 1 y =
            y * (1 - (y * Real.arcsin y) / Real.sqrt (1 - y ^ 2))) ∧
        F₅ x = x * Real.sqrt (1 - x ^ 2) * Real.arcsin x - F₃ x ∧
        I x = AntiderivativeSet F₅ integrand := by
  sorry

-- Source: proofgap/exercise_2158/2.txt
theorem proof_gap_exercise_2158_2
    (C : ℝ) (I : ℝ → Set (ℝ → ℝ))
    (hC : C ∈ (Set.univ : RealSet))
    (hlo : ∀ x : ℝ, x ∈ (Set.univ : RealSet) → (-1 : ℝ) ≤ x)
    (hhi : ∀ x : ℝ, x ∈ (Set.univ : RealSet) → x ≤ (1 : ℝ))
    (hI : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      ∃ F₂ : ℝ → ℝ, I x = AntiderivativeSet F₂ integrand)
    (hparts : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      ∃ F₃ F₅ : ℝ → ℝ,
        (∀ y : ℝ, y ∈ (Set.univ : RealSet) ∧ onUnit y →
          FunDeri F₃ 1 1 y =
            y * (1 - (y * Real.arcsin y) / Real.sqrt (1 - y ^ 2))) ∧
        F₅ x = x * Real.sqrt (1 - x ^ 2) * Real.arcsin x - F₃ x ∧
        I x = AntiderivativeSet F₅ integrand) :
    ∀ x : ℝ, (hx : x ∈ (Set.univ : RealSet) ∧ onUnit x) →
      ∃ F₆ F₈ : ℝ → ℝ,
        (∀ y : ℝ, y ∈ (Set.univ : RealSet) ∧ onUnit y →
          FunDeri F₆ 1 1 y = Real.arcsin y / Real.sqrt (1 - y ^ 2)) ∧
        F₈ x = x * Real.sqrt (1 - x ^ 2) * Real.arcsin x - x ^ 2 / 2 -
          Classical.choose (hI x hx) x + F₆ x ∧
        I x = AntiderivativeSet F₈ integrand := by
  sorry

-- Source: proofgap/exercise_2158/3.txt
theorem proof_gap_exercise_2158_3
    (C : ℝ) (I : ℝ → Set (ℝ → ℝ)) :
    ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      (∃ F₉ : ℝ → ℝ,
        (∀ y : ℝ, y ∈ (Set.univ : RealSet) ∧ onUnit y →
          FunDeri F₉ 1 1 y = Real.arcsin y / Real.sqrt (1 - y ^ 2)) ∧
        F₉ x = (1 / 2 : ℝ) * (Real.arcsin x) ^ 2) := by
  sorry

-- Source: proofgap/exercise_2158/4.txt
theorem proof_gap_exercise_2158_4
    (C : ℝ) (I : ℝ → ℝ)
    (hprev : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      ∃ F₉ : ℝ → ℝ,
        (∀ y : ℝ, y ∈ (Set.univ : RealSet) ∧ onUnit y →
          FunDeri F₉ 1 1 y = Real.arcsin y / Real.sqrt (1 - y ^ 2)) ∧
        F₉ x = (1 / 2 : ℝ) * (Real.arcsin x) ^ 2) :
    ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      I x = x * Real.sqrt (1 - x ^ 2) * Real.arcsin x - x ^ 2 / 2 +
        (1 / 2 : ℝ) * (Real.arcsin x) ^ 2 - I x := by
  sorry

-- Source: proofgap/exercise_2158/5.txt
theorem proof_gap_exercise_2158_5
    (C : ℝ) (I : ℝ → ℝ)
    (hbalance : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      I x = x * Real.sqrt (1 - x ^ 2) * Real.arcsin x - x ^ 2 / 2 +
        (1 / 2 : ℝ) * (Real.arcsin x) ^ 2 - I x) :
    ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
      I x = finalPrimitive C x := by
  sorry

-- Source: proofgap/exercise_2158/6.txt
theorem proof_gap_exercise_2158_6
    (C : ℝ) :
    {F : ℝ → ℝ | ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
        FunDeri F 1 1 x = integrand x} =
      {F : ℝ → ℝ | ∃ C : ℝ, C ∈ (Set.univ : RealSet) ∧
        ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ onUnit x →
          F x = finalPrimitive C x} := by
  sorry

end Exercise2158
