import ProofGapLean.Prelude.Elementary

/-!
# Exercise 29

Semantic formalization of Exercise 29, gaps 1,...,7.
-/

namespace ProofGap.Exercise29

noncomputable section

def Original (x : ℝ) : Prop :=
  |x * (1 - x)| < (0.05 : ℝ)

def Lower30 : ℝ := (5 - Real.sqrt 30) / 10
def Upper30 : ℝ := (5 + Real.sqrt 30) / 10
def Lower20 : ℝ := (5 - Real.sqrt 20) / 10
def Upper20 : ℝ := (5 + Real.sqrt 20) / 10

private lemma lower30_lt_upper30 : Lower30 < Upper30 := by
  unfold Lower30 Upper30
  have hs : 0 < Real.sqrt 30 := Real.sqrt_pos.2 (by norm_num)
  linarith

private lemma lower20_lt_upper20 : Lower20 < Upper20 := by
  unfold Lower20 Upper20
  have hs : 0 < Real.sqrt 20 := Real.sqrt_pos.2 (by norm_num)
  linarith

private lemma factor30 (x : ℝ) :
    (x - Lower30) * (x - Upper30) =
      x ^ 2 - x - (1 / 20 : ℝ) := by
  unfold Lower30 Upper30
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)
  nlinarith

private lemma factor20 (x : ℝ) :
    (x - Lower20) * (x - Upper20) =
      x ^ 2 - x + (1 / 20 : ℝ) := by
  unfold Lower20 Upper20
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 20)
  nlinarith

/-- Exercise 29, gap 1; the omitted original inequality is explicit. -/
theorem gap1
    (x : ℝ)
    (h0 : Original x) :
    |x - x ^ 2| < (1 / 20 : ℝ) := by
  unfold Original at h0
  norm_num at h0 ⊢
  calc
    |x - x ^ 2| = |x * (1 - x)| := by
      congr 1
      ring
    _ = |x| * |1 - x| := abs_mul x (1 - x)
    _ < 1 / 20 := h0

/-- Exercise 29, gap 2; the source's `∨` is repaired to `∧`. -/
theorem gap2
    (x : ℝ)
    (h1 : |x - x ^ 2| < (1 / 20 : ℝ)) :
    x ^ 2 - x + (1 / 20 : ℝ) > 0 ∧
      x ^ 2 - x - (1 / 20 : ℝ) < 0 := by
  rcases abs_lt.mp h1 with ⟨hl, hu⟩
  constructor <;> linarith

/-- Exercise 29, gap 3. -/
theorem gap3
    (x : ℝ)
    (h2 : x ^ 2 - x + (1 / 20 : ℝ) > 0 ∧
      x ^ 2 - x - (1 / 20 : ℝ) < 0) :
    Lower30 < x := by
  by_contra hnot
  have hxL : x ≤ Lower30 := le_of_not_gt hnot
  have hxU : x < Upper30 := hxL.trans_lt lower30_lt_upper30
  have hprod : 0 ≤ (x - Lower30) * (x - Upper30) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  rw [factor30] at hprod
  linarith [h2.2]

/-- Exercise 29, gap 4. -/
theorem gap4
    (x : ℝ)
    (h2 : x ^ 2 - x + (1 / 20 : ℝ) > 0 ∧
      x ^ 2 - x - (1 / 20 : ℝ) < 0)
    (h3 : Lower30 < x) :
    x < Upper30 := by
  by_contra hnot
  have hxU : Upper30 ≤ x := le_of_not_gt hnot
  have hprod : 0 ≤ (x - Lower30) * (x - Upper30) :=
    mul_nonneg (by linarith) (by linarith)
  rw [factor30] at hprod
  linarith [h2.2]

/-- Exercise 29, gap 5. -/
theorem gap5
    (x : ℝ)
    (h3 : Lower30 < x)
    (h4 : x < Upper30) :
    Lower30 < Upper30 := by
  exact h3.trans h4

/-- Exercise 29, gap 6. -/
theorem gap6
    (x : ℝ)
    (h2 : x ^ 2 - x + (1 / 20 : ℝ) > 0 ∧
      x ^ 2 - x - (1 / 20 : ℝ) < 0) :
    Upper20 < x ∨ x < Lower20 := by
  by_contra hnot
  rcases not_or.mp hnot with ⟨hnotUpper, hnotLower⟩
  have hxUpper : x ≤ Upper20 := le_of_not_gt hnotUpper
  have hxLower : Lower20 ≤ x := le_of_not_gt hnotLower
  have hprod : (x - Lower20) * (x - Upper20) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  rw [factor20] at hprod
  linarith [h2.1]

/-- Exercise 29, gap 7. -/
theorem gap7
    (x : ℝ)
    (h3 : Lower30 < x)
    (h4 : x < Upper30)
    (h6 : Upper20 < x ∨ x < Lower20) :
    x ∈ {y : ℝ |
      (Lower30 < y ∧ y < Lower20) ∨
      (Upper20 < y ∧ y < Upper30)} ↔ Original x := by
  have houterProd : (x - Lower30) * (x - Upper30) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hminus : x ^ 2 - x - (1 / 20 : ℝ) < 0 := by
    rw [← factor30]
    exact houterProd
  have hplus : 0 < x ^ 2 - x + (1 / 20 : ℝ) := by
    rcases h6 with hright | hleft
    · have hprod : 0 < (x - Lower20) * (x - Upper20) :=
        mul_pos (by linarith [lower20_lt_upper20]) (by linarith)
      rwa [factor20] at hprod
    · have hprod : 0 < (x - Lower20) * (x - Upper20) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith [lower20_lt_upper20])
      rwa [factor20] at hprod
  have horiginal : Original x := by
    unfold Original
    rw [show x * (1 - x) = x - x ^ 2 by ring]
    apply abs_lt.mpr
    constructor <;> norm_num <;> linarith
  have hmem :
      (Lower30 < x ∧ x < Lower20) ∨
        (Upper20 < x ∧ x < Upper30) := by
    rcases h6 with hright | hleft
    · exact Or.inr ⟨hright, h4⟩
    · exact Or.inl ⟨h3, hleft⟩
  change ((Lower30 < x ∧ x < Lower20) ∨
    (Upper20 < x ∧ x < Upper30)) ↔ Original x
  exact ⟨fun _ => horiginal, fun _ => hmem⟩

end

end ProofGap.Exercise29
