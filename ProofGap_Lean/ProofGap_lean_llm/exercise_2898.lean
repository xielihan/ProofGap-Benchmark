import Mathlib

noncomputable section

namespace ProofGapBatch5

abbrev SeqR := ℕ → ℝ

def nthRoot (n : ℕ) (x : ℝ) : ℝ := x ^ (1 / (n : ℝ))

def ratioLiminf (a : SeqR) : ℝ :=
  sSup {b : ℝ | ∀ᶠ n in Filter.atTop, b ≤ |a n / a (n + 1)|}

def ratioLimsup (a : SeqR) : ℝ :=
  sInf {b : ℝ | ∀ᶠ n in Filter.atTop, |a n / a (n + 1)| ≤ b}

def rootLimit (a : SeqR) (A : ℝ) : Prop :=
  Tendsto (fun n : ℕ => nthRoot n |a n|) Filter.atTop (𝓝 A)

def HasPowerSeriesRadius (a : SeqR) (R : ℝ) : Prop :=
  0 ≤ R ∧
    (∀ r : ℝ, 0 ≤ r → r < R → Summable (fun n : ℕ => |a n| * r ^ n)) ∧
    (∀ r : ℝ, R < r → ¬ Summable (fun n : ℕ => |a n| * r ^ n))

namespace exercise_2898

variable (a : SeqR) (x0 l L R l1 L1 A : ℝ)

theorem proof_gap_exercise_2898_1
    (hnz : ∃ m0 : ℕ, 0 < m0 ∧ ∀ n : ℕ, m0 < n → a n * a (n + 1) ≠ 0)
    (hl : l = ratioLiminf a) (hL : L = ratioLimsup a)
    (h0l : 0 ≤ l) (hlL : l ≤ L) (hR : HasPowerSeriesRadius a R)
    (hl1 : l1 = 1 / l) (hL1 : L1 = 1 / L) :
    L1 ≤ l1 := by
  sorry

theorem proof_gap_exercise_2898_2
    (hprev : L1 ≤ l1) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ δ1 δ2 : ℝ, 0 < δ1 ∧ 0 < δ2 ∧ δ2 < 1 ∧
        1 / (1 + δ1) = 1 - ε / 2 ∧ 1 / (1 - δ2) = 1 + ε / 2 := by
  sorry

theorem proof_gap_exercise_2898_3
    (hnz : ∃ m0 : ℕ, 0 < m0 ∧ ∀ n : ℕ, m0 < n → a n * a (n + 1) ≠ 0)
    (hl : l = ratioLiminf a) (hL : L = ratioLimsup a)
    (hl1 : l1 = 1 / l) (hL1 : L1 = 1 / L) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, m < n →
        L1 * (1 - ε / 2) < |a (n + 1)| / |a n| ∧
        |a (n + 1)| / |a n| < l1 * (1 + ε / 2) := by
  sorry

theorem proof_gap_exercise_2898_4
    (hratio : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, m < n →
        L1 * (1 - ε / 2) < |a (n + 1)| / |a n| ∧
        |a (n + 1)| / |a n| < l1 * (1 + ε / 2)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, m < n →
        |a n| / |a m| < (l1 * (1 + ε / 2)) ^ (n - m) := by
  sorry

theorem proof_gap_exercise_2898_5
    (hratio : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, m < n →
        L1 * (1 - ε / 2) < |a (n + 1)| / |a n| ∧
        |a (n + 1)| / |a n| < l1 * (1 + ε / 2)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, m < n →
        (L1 * (1 - ε / 2)) ^ (n - m) < |a n| / |a m| := by
  sorry

theorem proof_gap_exercise_2898_6 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, 0 < m ∧ ∃ n0 : ℕ, 0 < n0 ∧ m < n0 ∧
        ∀ n : ℕ, n0 ≤ n →
          nthRoot n (|a m| / l1 ^ m) < 1 + (ε / 2) / (1 + ε / 2) := by
  sorry

theorem proof_gap_exercise_2898_7 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, 0 < m ∧ ∃ n1 : ℕ, 0 < n1 ∧ m < n1 ∧
        ∀ n : ℕ, n1 ≤ n →
          1 - (ε / 2) / (1 - ε / 2) < nthRoot n (|a m| / L1 ^ m) := by
  sorry

theorem proof_gap_exercise_2898_8 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ n0 n1 : ℕ, 0 < n0 ∧ 0 < n1 ∧
        ∀ n : ℕ, max n0 n1 ≤ n →
          nthRoot n |a n| / l1 < 1 + ε ∧
          1 - ε < nthRoot n |a n| / L1 := by
  sorry

theorem proof_gap_exercise_2898_9
    (hA : rootLimit a A) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → L1 * (1 - ε) ≤ A := by
  sorry

theorem proof_gap_exercise_2898_10
    (hA : rootLimit a A) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → A ≤ l1 * (1 + ε) := by
  sorry

theorem proof_gap_exercise_2898_11
    (hR : HasPowerSeriesRadius a R) (hA : rootLimit a A) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → 1 / (l1 * (1 + ε)) ≤ R := by
  sorry

theorem proof_gap_exercise_2898_12
    (hR : HasPowerSeriesRadius a R) (hA : rootLimit a A) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → R ≤ 1 / (L1 * (1 - ε)) := by
  sorry

theorem proof_gap_exercise_2898_13
    (hl1 : l1 = 1 / l)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 → 1 / (l1 * (1 + ε)) ≤ R) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → l / (1 + ε) ≤ R := by
  sorry

theorem proof_gap_exercise_2898_14
    (hL1 : L1 = 1 / L)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 → R ≤ 1 / (L1 * (1 - ε))) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → R ≤ L / (1 - ε) := by
  sorry

theorem proof_gap_exercise_2898_15
    (hlower : ∀ ε : ℝ, 0 < ε → ε < 1 → l / (1 + ε) ≤ R) :
    l ≤ R := by
  sorry

theorem proof_gap_exercise_2898_16
    (hupper : ∀ ε : ℝ, 0 < ε → ε < 1 → R ≤ L / (1 - ε)) :
    R ≤ L := by
  sorry

theorem proof_gap_exercise_2898_17
    (hlR : l ≤ R) (hRL : R ≤ L) :
    l ≤ R ∧ R ≤ L := by
  sorry

end exercise_2898

end ProofGapBatch5
