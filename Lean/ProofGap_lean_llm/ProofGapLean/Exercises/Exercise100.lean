import ProofGapLean.Prelude.Analysis

open Filter

namespace ProofGap.Exercise100

noncomputable section

def x (n : ℕ) : ℝ :=
  (n : ℝ) + 100 / (n : ℝ)

def squareForm (n : ℕ) : ℝ :=
  (Real.sqrt n - 10 / Real.sqrt n) ^ 2 + 20

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

/-- Exercise 100, gap 1; the rewrite requires positive n. -/
theorem gap1 :
    ∀ n : ℕ, 0 < n → x n = squareForm n := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hs_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  unfold x squareForm
  field_simp [ne_of_gt hs]
  rw [hs_sq]
  ring

/-- Exercise 100, gap 2. -/
theorem gap2 :
    ∀ n : ℕ, squareForm n ≥ 20 := by
  intro n
  unfold squareForm
  nlinarith [sq_nonneg (Real.sqrt n - 10 / Real.sqrt n)]

/-- Exercise 100, gap 3. -/
theorem gap3 :
    ∀ n : ℕ, 0 < n → x n ≥ 20 := by
  intro n hn
  rw [gap1 n hn]
  exact gap2 n

/-- Exercise 100, gap 4. -/
theorem gap4 :
    x 10 = 20 := by
  norm_num [x]

/-- Exercise 100, gap 5. -/
theorem gap5 :
    IsLeast values 20 := by
  constructor
  · exact ⟨10, by omega, gap4.symm⟩
  · intro v hv
    rcases hv with ⟨n, hn, rfl⟩
    exact gap3 n hn

/-- Exercise 100, gap 6. -/
theorem gap6 :
    sInf values = 20 := by
  exact gap5.csInf_eq

/-- Exercise 100, gap 7; +∞ supremum means unbounded above. -/
theorem gap7 :
    ¬ BddAbove values := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max B 0)
  have hnB : B < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnposR : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have hxmem : x n ∈ values := ⟨n, hnpos, rfl⟩
  have hxgt : (n : ℝ) < x n := by
    unfold x
    have : 0 < 100 / (n : ℝ) := div_pos (by norm_num) hnposR
    linarith
  linarith [hB hxmem]

/-- Exercise 100, gap 8; liminf +∞ follows from divergence. -/
theorem gap8 :
    Tendsto x atTop (atTop : Filter ℝ) := by
  apply tendsto_atTop.2
  intro B
  have hev : ∀ᶠ n : ℕ in atTop, B ≤ (n : ℝ) :=
    tendsto_atTop.1 tendsto_natCast_atTop_atTop B
  filter_upwards [hev] with n hn
  unfold x
  have hnonneg : 0 ≤ 100 / (n : ℝ) := by positivity
  linarith

/-- Exercise 100, gap 9; limsup +∞ follows from divergence. -/
theorem gap9 :
    Tendsto x atTop (atTop : Filter ℝ) := by
  exact gap8

/-- Exercise 100, gap 10. -/
theorem gap10 :
    Tendsto x atTop (atTop : Filter ℝ) := by
  exact gap8

end

end ProofGap.Exercise100
