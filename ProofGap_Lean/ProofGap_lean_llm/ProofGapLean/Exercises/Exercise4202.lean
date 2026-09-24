import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4202

noncomputable section

open MeasureTheory

def OrderedCoordinates {n : ℕ} (x : ℝ) (v : Fin n → ℝ) : Prop :=
  0 ≤ x ∧
    (∀ i, 0 ≤ v i) ∧
    (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
    (∀ i, v i ≤ x)

def ambientBox (n : ℕ) (x : ℝ) : Set (Fin n → ℝ) :=
  {v | ∀ i, 0 ≤ v i ∧ v i ≤ x}

def orderedSimplex (n : ℕ) (x : ℝ) : Set (Fin n → ℝ) :=
  {v | OrderedCoordinates x v}

def forwardSimplex (n : ℕ) (x : ℝ) : Set (Fin n → ℝ) :=
  {v |
    0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x)}

def reverseSimplex (n : ℕ) (x : ℝ) : Set (Fin n → ℝ) :=
  {v |
    (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x}

def simplexIntegral (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ v in orderedSimplex n x, f v

def forwardIntegral (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ v in forwardSimplex n x, f v

def reverseIntegral (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ v in reverseSimplex n x, f v

theorem gap1 (n : ℕ) (x : ℝ) (hn : 2 ≤ n) :
    forwardSimplex n x ⊆ ambientBox n x := by
  intro v hv
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x) at hv
  change ∀ i, 0 ≤ v i ∧ v i ≤ x
  intro i
  exact ⟨hv.2.1 i, hv.2.2.2 i⟩

theorem gap2 (n : ℕ) (x : ℝ) (hn : 2 ≤ n) :
    reverseSimplex n x ⊆ ambientBox n x := by
  intro v hv
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x at hv
  change ∀ i, 0 ≤ v i ∧ v i ≤ x
  intro i
  exact ⟨hv.2.2.1 i, hv.1 i⟩

theorem gap3
    (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (ambientBox n x)) :
    ContinuousOn f (forwardSimplex n x) := by
  apply hf.mono
  intro v hv
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x) at hv
  change ∀ i, 0 ≤ v i ∧ v i ≤ x
  intro i
  exact ⟨hv.2.1 i, hv.2.2.2 i⟩

theorem gap4
    (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (ambientBox n x)) :
    ContinuousOn f (reverseSimplex n x) := by
  apply hf.mono
  intro v hv
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x at hv
  change ∀ i, 0 ≤ v i ∧ v i ≤ x
  intro i
  exact ⟨hv.2.2.1 i, hv.1 i⟩

theorem gap5
    (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ) (hn : 2 ≤ n)
    (hf : ContinuousOn f (ambientBox n x)) :
    simplexIntegral n x f = forwardIntegral n x f := by
  rfl

theorem gap6
    (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ) (hn : 2 ≤ n)
    (hf : ContinuousOn f (ambientBox n x)) :
    simplexIntegral n x f = reverseIntegral n x f := by
  have hsets : orderedSimplex n x = reverseSimplex n x := by
    ext v
    change OrderedCoordinates x v ↔
      ((∀ i, v i ≤ x) ∧
        (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
        (∀ i, 0 ≤ v i) ∧
        0 ≤ x)
    unfold OrderedCoordinates
    constructor
    · intro hv
      exact ⟨hv.2.2.2, hv.2.2.1, hv.2.1, hv.1⟩
    · intro hv
      exact ⟨hv.2.2.2, hv.2.2.1, hv.2.1, hv.1⟩
  unfold simplexIntegral reverseIntegral
  rw [hsets]

theorem gap7
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    ∀ i, 0 ≤ v i := by
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x) at hv
  exact hv.2.1

theorem gap8
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    ∀ i j : Fin n, i.val ≤ j.val → v j ≤ v i := by
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x) at hv
  exact hv.2.2.1

theorem gap9
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    ∀ i j k : Fin n,
      i.val ≤ j.val → j.val ≤ k.val → v k ≤ v i := by
  intro i j k hij hjk
  exact gap8 hv i k (le_trans hij hjk)

theorem gap10
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    ∀ i j k l : Fin n,
      i.val ≤ j.val → j.val ≤ k.val → k.val ≤ l.val → v l ≤ v i := by
  intro i j k l hij hjk hkl
  exact gap8 hv i l (le_trans (le_trans hij hjk) hkl)

theorem gap11
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    ∀ i j : Fin n, i.val + 1 = j.val → v j ≤ v i := by
  intro i j hij
  apply gap8 hv i j
  have hlt : i.val < j.val := by
    rw [← hij]
    exact Nat.lt_succ_self i.val
  exact Nat.le_of_lt hlt

theorem gap12
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    ∀ i, v i ≤ x := by
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x) at hv
  exact hv.2.2.2

theorem gap13
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    0 ≤ x := by
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x) at hv
  exact hv.1

theorem gap14
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ forwardSimplex n x) :
    v ∈ reverseSimplex n x := by
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x) at hv
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x
  exact ⟨hv.2.2.2, hv.2.2.1, hv.2.1, hv.1⟩

theorem gap15
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    ∀ i, 0 ≤ v i := by
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x at hv
  exact hv.2.2.1

theorem gap16
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    ∀ i j : Fin n, i.val ≤ j.val → v j ≤ v i := by
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x at hv
  exact hv.2.1

theorem gap17
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    ∀ i j k : Fin n,
      i.val ≤ j.val → j.val ≤ k.val → v k ≤ v i := by
  intro i j k hij hjk
  exact gap16 hv i k (le_trans hij hjk)

theorem gap18
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    ∀ i j k l : Fin n,
      i.val ≤ j.val → j.val ≤ k.val → k.val ≤ l.val → v l ≤ v i := by
  intro i j k l hij hjk hkl
  exact gap16 hv i l (le_trans (le_trans hij hjk) hkl)

theorem gap19
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    ∀ i j : Fin n, i.val + 1 = j.val → v j ≤ v i := by
  intro i j hij
  apply gap16 hv i j
  have hlt : i.val < j.val := by
    rw [← hij]
    exact Nat.lt_succ_self i.val
  exact Nat.le_of_lt hlt

theorem gap20
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    ∀ i, v i ≤ x := by
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x at hv
  exact hv.1

theorem gap21
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    0 ≤ x := by
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x at hv
  exact hv.2.2.2

theorem gap22
    {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ reverseSimplex n x) :
    v ∈ forwardSimplex n x := by
  change (∀ i, v i ≤ x) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, 0 ≤ v i) ∧
      0 ≤ x at hv
  change 0 ≤ x ∧
      (∀ i, 0 ≤ v i) ∧
      (∀ i j, i.val ≤ j.val → v j ≤ v i) ∧
      (∀ i, v i ≤ x)
  exact ⟨hv.2.2.2, hv.2.2.1, hv.2.1, hv.1⟩

theorem gap23 (n : ℕ) (x : ℝ) :
    forwardSimplex n x = reverseSimplex n x := by
  ext v
  constructor
  · exact gap14
  · exact gap22

theorem gap24
    (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (ambientBox n x)) :
    forwardIntegral n x f = reverseIntegral n x f := by
  unfold forwardIntegral reverseIntegral
  rw [gap23 n x]

theorem gap25
    (n : ℕ) (x : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (ambientBox n x)) :
    forwardIntegral n x f = reverseIntegral n x f := by
  exact gap24 n x f hf

end

end ProofGap.Exercise4202
