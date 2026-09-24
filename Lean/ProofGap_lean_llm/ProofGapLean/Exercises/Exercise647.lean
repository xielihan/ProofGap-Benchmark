import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise647

noncomputable section

def IsOrder (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ K ≥ 0, ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
    |f x| ≤ K * x ^ n

/-- Exercise 647, gap 1; represent `O(x^n)` by an explicit eventual bound. -/
theorem gap1 (f : ℝ → ℝ) (n : ℕ) (C K : ℝ)
    (h : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), |f x| ≤ K * x ^ n) :
    ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      |C * f x| ≤ (|C| * K) * x ^ n := by
  filter_upwards [h] with x hx
  rw [abs_mul]
  calc
    |C| * |f x| ≤ |C| * (K * x ^ n) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg C)
    _ = (|C| * K) * x ^ n := by ring

/-- Exercise 647, gap 2; finiteness becomes existence of a real bound. -/
theorem gap2 (C K : ℝ) (hK : 0 ≤ K) :
    ∃ M ≥ 0, |C| * K ≤ M := by
  refine ⟨|C| * K, mul_nonneg (abs_nonneg C) hK, ?_⟩
  exact le_rfl

/-- Exercise 647, gap 3. -/
theorem gap3 (f : ℝ → ℝ) (n : ℕ) (C : ℝ)
    (hf : IsOrder f n) :
    ∃ K ≥ 0, ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      |C * f x| ≤ K * x ^ n := by
  rcases hf with ⟨K, hK, hf⟩
  refine ⟨|C| * K, mul_nonneg (abs_nonneg C) hK, ?_⟩
  exact gap1 f n C K hf

/-- Exercise 647, gap 4; interpret equality of big-O symbols as closure under scalar multiplication. -/
theorem gap4 (f : ℝ → ℝ) (n : ℕ) (C : ℝ)
    (hf : IsOrder f n) :
    IsOrder (fun x => C * f x) n := by
  exact gap3 f n C hf

/-- Exercise 647, gap 5; state the eventual triangle bound. -/
theorem gap5 (f g : ℝ → ℝ) (n m : ℕ) (hnm : n < m)
    (hf : IsOrder f n) (hg : IsOrder g m) :
    ∃ K ≥ 0, ∀ᶠ x in nhdsWithin 0 (Set.Ioo 0 1),
      |f x + g x| ≤ K * x ^ n := by
  rcases hf with ⟨K₁, hK₁, hf⟩
  rcases hg with ⟨K₂, hK₂, hg⟩
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi 0 := by
    intro x hx
    exact hx.1
  have hf' : ∀ᶠ x in nhdsWithin 0 (Set.Ioo 0 1),
      |f x| ≤ K₁ * x ^ n :=
    (nhdsWithin_mono 0 hsub) hf
  have hg' : ∀ᶠ x in nhdsWithin 0 (Set.Ioo 0 1),
      |g x| ≤ K₂ * x ^ m :=
    (nhdsWithin_mono 0 hsub) hg
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
  filter_upwards [hf', hg', self_mem_nhdsWithin] with x hfx hgx hx
  have hpow : x ^ m ≤ x ^ n :=
    pow_le_pow_of_le_one hx.1.le hx.2.le (Nat.le_of_lt hnm)
  have htri : |f x + g x| ≤ |f x| + |g x| := by
    apply (abs_le).2
    constructor
    · linarith [neg_abs_le (f x), neg_abs_le (g x)]
    · linarith [le_abs_self (f x), le_abs_self (g x)]
  calc
    |f x + g x| ≤ |f x| + |g x| := htri
    _ ≤ K₁ * x ^ n + K₂ * x ^ m := add_le_add hfx hgx
    _ ≤ K₁ * x ^ n + K₂ * x ^ n :=
      add_le_add_right (mul_le_mul_of_nonneg_left hpow hK₂) _
    _ = (K₁ + K₂) * x ^ n := by ring

/-- Exercise 647, gap 6; the two finite big-O bounds combine to one finite bound. -/
theorem gap6 (K₁ K₂ : ℝ) (h₁ : 0 ≤ K₁) (h₂ : 0 ≤ K₂) :
    ∃ K ≥ 0, K₁ + K₂ ≤ K := by
  refine ⟨K₁ + K₂, add_nonneg h₁ h₂, ?_⟩
  exact le_rfl

/-- Exercise 647, gap 7. -/
theorem gap7 (f g : ℝ → ℝ) (n m : ℕ) (hnm : n < m)
    (hf : IsOrder f n) (hg : IsOrder g m) :
    ∃ K ≥ 0, ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      |f x + g x| ≤ K * x ^ n := by
  rcases gap5 f g n m hnm hf hg with ⟨K, hK, hbound⟩
  have hnear : ∀ᶠ x : ℝ in nhds 0, x < 1 :=
    Iio_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)
  have hnhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 := by
    exact inf_le_left
  have hlt : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x < 1 :=
    hnhds hnear
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with x hx hx1
    exact ⟨hx, hx1⟩
  have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤
      nhdsWithin 0 (Set.Ioo 0 1) := by
    change nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤
      nhds 0 ⊓ Filter.principal (Set.Ioo 0 1)
    refine le_inf ?_ ?_
    · exact inf_le_left
    · exact Filter.le_principal_iff.mpr hmem
  exact ⟨K, hK, hle hbound⟩

/-- Exercise 647, gap 8; interpret equality of big-O symbols as the sum closure rule. -/
theorem gap8 (f g : ℝ → ℝ) (n m : ℕ) (hnm : n < m)
    (hf : IsOrder f n) (hg : IsOrder g m) :
    IsOrder (fun x => f x + g x) n := by
  exact gap7 f g n m hnm hf hg

/-- Exercise 647, gap 9; state the product of eventual bounds. -/
theorem gap9 (f g : ℝ → ℝ) (n m : ℕ)
    (hf : IsOrder f n) (hg : IsOrder g m) :
    ∃ K ≥ 0, ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      |f x * g x| ≤ K * x ^ (n + m) := by
  rcases hf with ⟨K₁, hK₁, hf⟩
  rcases hg with ⟨K₂, hK₂, hg⟩
  refine ⟨K₁ * K₂, mul_nonneg hK₁ hK₂, ?_⟩
  filter_upwards [hf, hg] with x hfx hgx
  calc
    |f x * g x| = |f x| * |g x| := by rw [abs_mul]
    _ ≤ (K₁ * x ^ n) * (K₂ * x ^ m) :=
      mul_le_mul hfx hgx (abs_nonneg (g x))
        (le_trans (abs_nonneg (f x)) hfx)
    _ = (K₁ * K₂) * x ^ (n + m) := by
      rw [pow_add]
      ring

/-- Exercise 647, gap 10. -/
theorem gap10 (K₁ K₂ : ℝ) (h₁ : 0 ≤ K₁) (h₂ : 0 ≤ K₂) :
    ∃ K ≥ 0, K₁ * K₂ ≤ K := by
  refine ⟨K₁ * K₂, mul_nonneg h₁ h₂, ?_⟩
  exact le_rfl

/-- Exercise 647, gap 11. -/
theorem gap11 (f g : ℝ → ℝ) (n m : ℕ)
    (hf : IsOrder f n) (hg : IsOrder g m) :
    ∃ K ≥ 0, ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      |f x * g x| ≤ K * x ^ (n + m) := by
  exact gap9 f g n m hf hg

/-- Exercise 647, gap 12; interpret equality of big-O symbols as the product closure rule. -/
theorem gap12 (f g : ℝ → ℝ) (n m : ℕ)
    (hf : IsOrder f n) (hg : IsOrder g m) :
    IsOrder (fun x => f x * g x) (n + m) := by
  exact gap11 f g n m hf hg

/-- Exercise 647, gap 13; corrected package of the three big-O closure rules. -/
theorem gap13 (f g : ℝ → ℝ) (n m : ℕ) (C : ℝ)
    (hf : IsOrder f n) (hg : IsOrder g m) :
    IsOrder (fun x => C * f x) n ∧
      (n < m → IsOrder (fun x => f x + g x) n) ∧
      IsOrder (fun x => f x * g x) (n + m) := by
  constructor
  · exact gap4 f n C hf
  constructor
  · intro hnm
    exact gap8 f g n m hnm hf hg
  · exact gap12 f g n m hf hg

end

end ProofGap.Exercise647
