import Mathlib

open Filter
open scoped Topology

noncomputable section

namespace Exercise2196

abbrev RealSet := Set ℝ
def PosRealSet : Set ℝ := {x | 0 < x}
def PosIntegerSet : Set ℤ := {n | 0 < n}
def NonNegIntegerSet : Set ℕ := Set.univ
def Icc (a b : ℝ) : Set ℝ := Set.Icc a b

def BoundedFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := ∃ M : ℝ, ∀ x ∈ s, |f x| ≤ M
def ContinuousFuncAt (f : ℝ → ℝ) (x : ℝ) : Prop := ContinuousAt f x
noncomputable def OscillationOn (f : ℝ → ℝ) (s : Set ℝ) : ℝ := sSup ((fun p : ℝ × ℝ => |f p.1 - f p.2|) '' (s ×ˢ s))
def FiniteSet (s : Set ℝ) : Prop := s.Finite
def IntegrableFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := MeasureTheory.IntegrableOn f s
def MeshSmall (x : ℕ → ℝ) (δ : ℝ) : Prop := ∀ i : ℕ, |x (i + 1) - x i| < δ
def Partition01 (x Δx : ℕ → ℝ) (n : ℕ) : Prop := x 0 = 0 ∧ x n = 1 ∧ ∀ i : ℕ, i < n → x i < x (i + 1) ∧ Δx i = x (i + 1) - x i
noncomputable def taggedSum (ω Δx : ℕ → ℝ) (_ : ℤ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ω i * Δx i
noncomputable def tailOscSum (ω Δx : ℕ → ℝ) (i₀ : ℤ) (n : ℕ) : ℝ := ∑ i ∈ (Finset.range n).filter (fun (i : ℕ) => i₀ + 1 ≤ (i : ℤ)), ω i * Δx i
noncomputable def headOscSum (ω Δx : ℕ → ℝ) (i₀ : ℤ) : ℝ := ∑ i ∈ (Finset.range (i₀.toNat + 1)), ω i * Δx i
noncomputable def headLenSum (Δx : ℕ → ℝ) (i₀ : ℤ) : ℝ := ∑ i ∈ (Finset.range (i₀.toNat + 1)), Δx i
def riemannOscLimitZero (ω Δx : ℕ → ℝ) (_d : ℝ) : Prop := Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ω i * Δx i) atTop (𝓝 0)

def fFormula (f : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, t ∈ Icc 0 1 ∧ t ≠ 0 → f t = (1 / t) * ⌊1 / t⌋) ∧ f 0 = 0

def discontinuitySet : Set ℝ := {0} ∪ {t : ℝ | ∃ n : ℤ, n ∈ PosIntegerSet ∧ 2 ≤ n ∧ t = 1 / (n : ℝ)}

theorem proof_gap_exercise_2196_1
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hf : fFormula f) :
    BoundedFuncOn f (Icc 0 1) := by
  sorry

theorem proof_gap_exercise_2196_2
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hf : fFormula f) (hbdd : BoundedFuncOn f (Icc 0 1)) :
    ∀ t : ℝ, t ∈ Icc 0 1 → (¬ ContinuousFuncAt f t ↔ t ∈ discontinuitySet) := by
  sorry

theorem proof_gap_exercise_2196_3
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hf : fFormula f) (hbdd : BoundedFuncOn f (Icc 0 1))
    (hdisc : ∀ t : ℝ, t ∈ Icc 0 1 → (¬ ContinuousFuncAt f t ↔ t ∈ discontinuitySet)) :
    ∀ α β : ℝ, α ∈ (Set.univ : RealSet) ∧ β ∈ (Set.univ : RealSet) ∧
      0 ≤ α ∧ α ≤ β ∧ β ≤ 1 → OscillationOn f (Icc α β) ≤ 1 := by
  sorry

theorem proof_gap_exercise_2196_4
    (f : ℝ → ℝ)
    (hdisc : ∀ t : ℝ, t ∈ Icc 0 1 → (¬ ContinuousFuncAt f t ↔ t ∈ discontinuitySet)) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      FiniteSet {t : ℝ | t ∈ Icc (ε / 3) 1 ∧ ¬ ContinuousFuncAt f t} := by
  sorry

theorem proof_gap_exercise_2196_5
    (f : ℝ → ℝ)
    (hfinite : ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      FiniteSet {t : ℝ | t ∈ Icc (ε / 3) 1 ∧ ¬ ContinuousFuncAt f t}) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      IntegrableFuncOn f (Icc (ε / 3) 1) := by
  sorry

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

theorem proof_gap_exercise_2196_7
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
        ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
          ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ x i₀.toNat ≤ ε / 3 := by
  sorry

theorem proof_gap_exercise_2196_8
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
      ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
        ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
          ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ ε / 3 < x (i₀ + 1).toNat := by
  sorry

theorem proof_gap_exercise_2196_9
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ tailOscSum ω Δx i₀ n < ε / 3 := by
  sorry

theorem proof_gap_exercise_2196_10
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧
              headOscSum ω Δx i₀ ≤ headLenSum Δx i₀ := by
  sorry

theorem proof_gap_exercise_2196_11
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ headLenSum Δx i₀ < (2 * ε) / 3 := by
  sorry

theorem proof_gap_exercise_2196_12
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧ headOscSum ω Δx i₀ < (2 * ε) / 3 := by
  sorry

theorem proof_gap_exercise_2196_13
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧
              taggedSum ω Δx 0 n = headOscSum ω Δx i₀ + tailOscSum ω Δx i₀ n := by
  sorry

theorem proof_gap_exercise_2196_14
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            ∃ i₀ : ℤ, i₀ ∈ (Set.univ : Set ℤ) ∧
              headOscSum ω Δx i₀ + tailOscSum ω Δx i₀ n < ε := by
  sorry

theorem proof_gap_exercise_2196_15
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 ∧ ε ≤ 3 →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ ∈ PosRealSet ∧
          ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 ∧ Partition01 x Δx n ∧ d < δ →
            taggedSum ω Δx 0 n < ε := by
  sorry

theorem proof_gap_exercise_2196_16
    (x Δx ω : ℕ → ℝ) (d : ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        riemannOscLimitZero ω Δx d := by
  sorry

theorem proof_gap_exercise_2196_17
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hlim : ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 → riemannOscLimitZero ω Δx d) :
    IntegrableFuncOn f (Icc 0 1) := by
  sorry

theorem proof_gap_exercise_2196_18
    (f : ℝ → ℝ) (x Δx ω : ℕ → ℝ) (d : ℝ)
    (hint : IntegrableFuncOn f (Icc 0 1)) :
    IntegrableFuncOn f (Icc 0 1) := by
  sorry

end Exercise2196
