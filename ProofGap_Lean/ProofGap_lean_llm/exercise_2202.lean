import Mathlib

noncomputable section

namespace Exercise2202

abbrev RealSet := Set ℝ
def NonNegIntegerSet : Set ℕ := Set.univ
def PosIntegerSet : Set ℕ := {n | 0 < n}
def Icc (a b : ℝ) : Set ℝ := Set.Icc a b

def Defined (φ : ℝ → ℝ) (s : Set ℝ) : Prop := ∀ x ∈ s, ∃ y : ℝ, φ x = y
def ContinuousFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := ContinuousOn f s
def UniformContinuousFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, |x - y| < δ → |f x - f y| < ε
def IntegrableFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := MeasureTheory.IntegrableOn f s
noncomputable def OscillationOn (f : ℝ → ℝ) (s : Set ℝ) : ℝ := sSup ((fun p : ℝ × ℝ => |f p.1 - f p.2|) '' (s ×ˢ s))
noncomputable def mesh (x : ℕ → ℝ) (n : ℕ) : ℝ := sSup ((fun i : ℕ => |x (i + 1) - x i|) '' {i : ℕ | i < n})
noncomputable def sumOsc (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, OscillationOn f (Icc (x i) (x (i + 1))) * (x (i + 1) - x i)
noncomputable def sumOn (s : Set ℤ) (u : ℤ → ℝ) : ℝ := by
  classical
  exact ∑ i ∈ (Finset.Icc ((-1000 : ℤ)) (1000 : ℤ)).filter (fun i => i ∈ s), u i

def compOn (φ f g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ x ∈ Icc a b → g x = φ (f x)

def rangeBound (f : ℝ → ℝ) (a b A B : ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ x ∈ Icc a b → A ≤ f x ∧ f x ≤ B

def firstGroup (f : ℝ → ℝ) (x : ℕ → ℝ) (η : ℝ) (n : ℕ) : Set ℤ :=
  {i | 0 ≤ i ∧ i < (n : ℤ) ∧ OscillationOn f (Icc (x i.toNat) (x (i + 1).toNat)) < η}

def secondGroup (f : ℝ → ℝ) (x : ℕ → ℝ) (η : ℝ) (n : ℕ) : Set ℤ :=
  {i | 0 ≤ i ∧ i < (n : ℤ) ∧ η ≤ OscillationOn f (Icc (x i.toNat) (x (i + 1).toNat))}

theorem proof_gap_exercise_2202_1
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ)
    (hAB : A < B) (hab : a < b)
    (hdef : Defined φ (Icc A B)) (hcont : ContinuousFuncOn φ (Icc A B))
    (hint : IntegrableFuncOn f (Icc a b))
    (hrange : rangeBound f a b A B) (hcomp : compOn φ f g a b) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      UniformContinuousFuncOn φ (Icc A B) := by
  sorry

theorem proof_gap_exercise_2202_2
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ)
    (hab : a < b)
    (huc : ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      UniformContinuousFuncOn φ (Icc A B)) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∃ η : ℝ, η ∈ (Set.univ : RealSet) ∧ η > 0 ∧
        ∀ u v : ℝ, u ∈ (Set.univ : RealSet) ∧ u ∈ Icc A B ∧
          v ∈ (Set.univ : RealSet) ∧ v ∈ Icc A B ∧ |u - v| < η →
            |φ u - φ v| < ε / (2 * (b - a)) := by
  sorry

theorem proof_gap_exercise_2202_3
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ)
    (hint : IntegrableFuncOn f (Icc a b))
    (hOmega : ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      Ω = OscillationOn φ (Icc A B)) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ η : ℝ, η ∈ (Set.univ : RealSet) ∧ η > 0 ∧
          (Ω > 0 → ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
            ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              sumOsc f x n < (η * ε) / (2 * Ω)) := by
  sorry

theorem proof_gap_exercise_2202_4
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          ∃ I₁ : Set ℤ, I₁ ⊆ (Set.univ : Set ℤ) ∧
          ∃ I₂ : Set ℤ, I₂ ⊆ (Set.univ : Set ℤ) ∧
            (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              sumOsc g x n =
                sumOn I₁ (fun j => OscillationOn g (Icc (x j.toNat) (x (j + 1).toNat)) *
                  (x (j + 1).toNat - x j.toNat)) +
                sumOn I₂ (fun j => OscillationOn g (Icc (x j.toNat) (x (j + 1).toNat)) *
                  (x (j + 1).toNat - x j.toNat))) := by
  sorry

theorem proof_gap_exercise_2202_5
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          ∃ I₁ : Set ℤ, I₁ ⊆ (Set.univ : Set ℤ) ∧
            (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              sumOn I₁ (fun j => OscillationOn g (Icc (x j.toNat) (x (j + 1).toNat)) *
                (x (j + 1).toNat - x j.toNat)) <
              ε / (2 * (b - a)) * sumOn I₁ (fun j => x (j + 1).toNat - x j.toNat)) := by
  sorry

theorem proof_gap_exercise_2202_6
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          ∃ I₂ : Set ℤ, I₂ ⊆ (Set.univ : Set ℤ) ∧
            (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              sumOn I₂ (fun j => OscillationOn g (Icc (x j.toNat) (x (j + 1).toNat)) *
                (x (j + 1).toNat - x j.toNat)) ≤
              Ω * sumOn I₂ (fun j => x (j + 1).toNat - x j.toNat)) := by
  sorry

theorem proof_gap_exercise_2202_7
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ η : ℝ, η ∈ (Set.univ : RealSet) ∧ η > 0 ∧
          ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
            (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              (η * ε) / (2 * Ω) > sumOsc f x n) := by
  sorry

theorem proof_gap_exercise_2202_8
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ η : ℝ, η ∈ (Set.univ : RealSet) ∧ η > 0 ∧
          ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          ∃ I₂ : Set ℤ, I₂ ⊆ (Set.univ : Set ℤ) ∧
            (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              sumOsc f x n ≥ η * sumOn I₂ (fun j => x (j + 1).toNat - x j.toNat)) := by
  sorry

theorem proof_gap_exercise_2202_9
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          ∃ I₂ : Set ℤ, I₂ ⊆ (Set.univ : Set ℤ) ∧
            (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              sumOn I₂ (fun j => x (j + 1).toNat - x j.toNat) < ε / (2 * Ω)) := by
  sorry

theorem proof_gap_exercise_2202_10
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          ∃ I₁ : Set ℤ, I₁ ⊆ (Set.univ : Set ℤ) ∧
            (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
              sumOn I₁ (fun j => x (j + 1).toNat - x j.toNat) ≤ b - a) := by
  sorry

theorem proof_gap_exercise_2202_11
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
            sumOsc g x n < ε / (2 * (b - a)) * (b - a) + Ω * (ε / (2 * Ω))) := by
  sorry

theorem proof_gap_exercise_2202_12
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ) :
    ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
            sumOsc g x n < ε) := by
  sorry

theorem proof_gap_exercise_2202_13
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ)
    (hsmall : ∀ ε : ℝ, ε ∈ (Set.univ : RealSet) ∧ ε > 0 →
      ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
        ∃ δ : ℝ, δ ∈ (Set.univ : RealSet) ∧ δ > 0 ∧
          (Ω > 0 → ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ mesh x n < δ →
            sumOsc g x n < ε)) :
    IntegrableFuncOn g (Icc a b) := by
  sorry

theorem proof_gap_exercise_2202_14
    (φ f g : ℝ → ℝ) (a b A B Ω ω : ℝ) (x : ℕ → ℝ)
    (hint : IntegrableFuncOn g (Icc a b)) :
    IntegrableFuncOn g (Icc a b) := by
  sorry

end Exercise2202
