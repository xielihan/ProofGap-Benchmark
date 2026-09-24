import Mathlib

noncomputable section

namespace Exercise2196

abbrev RealSet := Set ℝ
def PosRealSet : Set ℝ := {x | 0 < x}
def PosIntegerSet : Set ℤ := {n | 0 < n}
def NonNegIntegerSet : Set ℕ := Set.univ
def Icc (a b : ℝ) : Set ℝ := Set.Icc a b

axiom BoundedFuncOn : (ℝ → ℝ) → Set ℝ → Prop
axiom ContinuousFuncAt : (ℝ → ℝ) → ℝ → Prop
axiom OscillationOn : (ℝ → ℝ) → Set ℝ → ℝ
axiom FiniteSet : Set ℝ → Prop
axiom IntegrableFuncOn : (ℝ → ℝ) → Set ℝ → Prop
axiom MeshSmall : (ℕ → ℝ) → ℝ → Prop
axiom Partition01 : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → Prop
axiom taggedSum : (ℕ → ℝ) → (ℕ → ℝ) → ℤ → ℕ → ℝ
axiom tailOscSum : (ℕ → ℝ) → (ℕ → ℝ) → ℤ → ℕ → ℝ
axiom headOscSum : (ℕ → ℝ) → (ℕ → ℝ) → ℤ → ℝ
axiom headLenSum : (ℕ → ℝ) → ℤ → ℝ
axiom riemannOscLimitZero : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → Prop

def fFormula (f : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, t ∈ Icc 0 1 ∧ t ≠ 0 → f t = (1 / t) * ⌊1 / t⌋) ∧ f 0 = 0

def discontinuitySet : Set ℝ := {0} ∪ {t : ℝ | ∃ n : ℤ, n ∈ PosIntegerSet ∧ 2 ≤ n ∧ t = 1 / (n : ℝ)}

-- Exercise 2196, gap 1
theorem proof_gap_exercise_2196_1
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hf : fFormula f) :
    BoundedFuncOn f (Icc 0 1) := by
  sorry

-- Exercise 2196, gap 2
theorem proof_gap_exercise_2196_2
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hf : fFormula f) (hbdd : BoundedFuncOn f (Icc 0 1)) :
    ∀ t : ℝ, t ∈ Icc 0 1 → (¬ ContinuousFuncAt f t ↔ t ∈ discontinuitySet) := by
  sorry

-- Exercise 2196, gap 3
theorem proof_gap_exercise_2196_3
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hf : fFormula f) (hbdd : BoundedFuncOn f (Icc 0 1))
    (hdisc : ∀ t : ℝ, t ∈ Icc 0 1 → (¬ ContinuousFuncAt f t ↔ t ∈ discontinuitySet)) :
    ∀ α β : ℝ, α ∈ (Set.univ : RealSet) ∧ β ∈ (Set.univ : RealSet) ∧
      0 ≤ α ∧ α ≤ β ∧ β ≤ 1 → OscillationOn f (Icc α β) ≤ 1 := by
  sorry

-- Exercise 2196, gap 4
theorem proof_gap_exercise_2196_4
    (f : ℝ → ℝ)
    (hdisc : ∀ t : ℝ, t ∈ Icc 0 1 → (¬ ContinuousFuncAt f t ↔ t ∈ discontinuitySet)) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      FiniteSet {t : ℝ | t ∈ Icc (ε / 3) 1 ∧ ¬ ContinuousFuncAt f t} := by
  sorry

-- Exercise 2196, gap 5
theorem proof_gap_exercise_2196_5
    (f : ℝ → ℝ)
    (hfinite : ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      FiniteSet {t : ℝ | t ∈ Icc (ε / 3) 1 ∧ ¬ ContinuousFuncAt f t}) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      IntegrableFuncOn f (Icc (ε / 3) 1) := by
  sorry

-- Exercise 2196, gap 6
theorem proof_gap_exercise_2196_6
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hint : ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      IntegrableFuncOn f (Icc (ε / 3) 1)) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∃ η : ℝ, η ∈ (Set.univ : RealSet) ∧ η ∈ PosRealSet ∧
          ∀ α β : ℝ, α ∈ (Set.univ : RealSet) ∧ β ∈ (Set.univ : RealSet) ∧
            Icc α β ⊆ Icc (ε / 3) 1 ∧ d < η →
              taggedSum ω Δx 0 n < ε / 3 := by
  sorry

-- Exercise 2196, gap 7
theorem proof_gap_exercise_2196_7
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
        ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
          ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ x i₀.toNat ≤ ε / 3 := by
  sorry

-- Exercise 2196, gap 8
theorem proof_gap_exercise_2196_8
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
        ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
          ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ ε / 3 < x (i₀ + 1).toNat := by
  sorry

-- Exercise 2196, gap 9
theorem proof_gap_exercise_2196_9
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ tailOscSum ω Δx i₀ n < ε / 3 := by
  sorry

-- Exercise 2196, gap 10
theorem proof_gap_exercise_2196_10
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧
              headOscSum ω Δx i₀ ≤ headLenSum Δx i₀ := by
  sorry

-- Exercise 2196, gap 11
theorem proof_gap_exercise_2196_11
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ headLenSum Δx i₀ < (2 * ε) / 3 := by
  sorry

-- Exercise 2196, gap 12
theorem proof_gap_exercise_2196_12
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ headOscSum ω Δx i₀ < (2 * ε) / 3 := by
  sorry

-- Exercise 2196, gap 13
theorem proof_gap_exercise_2196_13
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧
              taggedSum ω Δx 0 n = headOscSum ω Δx i₀ + tailOscSum ω Δx i₀ n := by
  sorry

-- Exercise 2196, gap 14
theorem proof_gap_exercise_2196_14
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧
              headOscSum ω Δx i₀ + tailOscSum ω Δx i₀ n < ε := by
  sorry

-- Exercise 2196, gap 15
theorem proof_gap_exercise_2196_15
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            taggedSum ω Δx 0 n < ε := by
  sorry

-- Exercise 2196, gap 16
theorem proof_gap_exercise_2196_16
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        riemannOscLimitZero ω Δx d := by
  sorry

-- Exercise 2196, gap 17
theorem proof_gap_exercise_2196_17
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hlim : ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 → riemannOscLimitZero ω Δx d) :
    IntegrableFuncOn f (Icc 0 1) := by
  sorry

-- Exercise 2196, gap 18
theorem proof_gap_exercise_2196_18
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hint : IntegrableFuncOn f (Icc 0 1)) :
    IntegrableFuncOn f (Icc 0 1) := by
  sorry

end Exercise2196
