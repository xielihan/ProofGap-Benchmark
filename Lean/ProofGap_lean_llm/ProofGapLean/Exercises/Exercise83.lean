import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace ProofGap.Exercise83

noncomputable section

def x (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, Real.sin (i : ℝ) / (2 : ℝ) ^ i

def tail (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (n + 1) m, Real.sin (i : ℝ) / (2 : ℝ) ^ i

def geometricTail (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m - n), 1 / (2 : ℝ) ^ j

def IsCauchy (u : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m → |u m - u n| < ε

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/-- Source: `proof_gap/exercise_83/1.txt`; the sine tail is explicit. -/
theorem gap1 :
    ∀ m n : ℕ, n < m → |x m - x n| = |tail n m| := by
  intro m n hnm
  congr 1
  unfold x tail
  simp_rw [← Finset.Ico_add_one_right_eq_Icc]
  have hconsecutive := Finset.sum_Ico_consecutive
    (fun i => Real.sin (i : ℝ) / (2 : ℝ) ^ i)
    (show 1 ≤ n + 1 by omega) (show n + 1 ≤ m + 1 by omega)
  linarith

/-- Source: `proof_gap/exercise_83/2.txt`; the geometric sum is explicit. -/
theorem gap2 :
    ∀ m n : ℕ, n < m →
      |tail n m| ≤ 1 / (2 : ℝ) ^ (n + 1) * geometricTail n m := by
  intro m n hnm
  have htriangle :
      |tail n m| ≤ ∑ i ∈ Finset.Icc (n + 1) m, 1 / (2 : ℝ) ^ i := by
    unfold tail
    calc
      |∑ i ∈ Finset.Icc (n + 1) m, Real.sin (i : ℝ) / (2 : ℝ) ^ i| ≤
          ∑ i ∈ Finset.Icc (n + 1) m,
            |Real.sin (i : ℝ) / (2 : ℝ) ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Icc (n + 1) m, 1 / (2 : ℝ) ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  calc
    |tail n m| ≤ ∑ i ∈ Finset.Icc (n + 1) m, 1 / (2 : ℝ) ^ i :=
      htriangle
    _ = 1 / (2 : ℝ) ^ (n + 1) * geometricTail n m := by
      unfold geometricTail
      rw [← Finset.Ico_add_one_right_eq_Icc]
      rw [Finset.sum_Ico_eq_sum_range]
      have hlen : m + 1 - (n + 1) = m - n := by omega
      rw [hlen, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      field_simp

/-- Source: `proof_gap/exercise_83/3.txt`. -/
theorem gap3 :
    ∀ m n : ℕ, n < m →
      1 / (2 : ℝ) ^ (n + 1) * geometricTail n m <
        1 / (2 : ℝ) ^ (n + 1) * (1 / (1 - 1 / 2)) := by
  intro m n hnm
  have hkpos : 0 < m - n := by omega
  have hsum :
      geometricTail n m =
        (1 - (1 / 2 : ℝ) ^ (m - n)) / (1 - (1 / 2 : ℝ)) := by
    unfold geometricTail
    simpa only [one_div, inv_pow, Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico' (x := (1 / 2 : ℝ)) (m := 0) (n := m - n)
        (by norm_num) (by omega))
  have hgeom : geometricTail n m < 1 / (1 - 1 / 2) := by
    rw [hsum]
    norm_num
    have hp : 0 < (1 / 2 : ℝ) ^ (m - n) := by positivity
    linarith
  have hcoef : 0 < 1 / (2 : ℝ) ^ (n + 1) := by positivity
  exact mul_lt_mul_of_pos_left hgeom hcoef

/-- Source: `proof_gap/exercise_83/4.txt`. -/
theorem gap4 :
    ∀ m n : ℕ, n < m →
      1 / (2 : ℝ) ^ (n + 1) * (1 / (1 - 1 / 2)) =
        1 / (2 : ℝ) ^ n := by
  intro m n _
  norm_num
  rw [pow_succ]
  field_simp

/-- Source: `proof_gap/exercise_83/5.txt`. -/
theorem gap5 :
    ∀ m n : ℕ, n < m → |x m - x n| < 1 / (2 : ℝ) ^ n := by
  intro m n hnm
  rw [gap1 m n hnm]
  exact lt_of_le_of_lt (gap2 m n hnm) <|
    (gap3 m n hnm).trans_eq (gap4 m n hnm)

/-- Source: `proof_gap/exercise_83/6.txt`; N depends on ε. -/
theorem gap6 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 1 / (2 : ℝ) ^ n < ε := by
  intro ε hε
  have hp :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n < ε :=
    hp.eventually (Iio_mem_nhds hε)
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [one_div, inv_pow] using hN n (by omega)

/-- Source: `proof_gap/exercise_83/7.txt`; N depends on ε. -/
theorem gap7 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m → |x m - x n| < ε := by
  intro ε hε
  rcases gap6 ε hε with ⟨N, hN⟩
  exact ⟨N, fun m n hn hnm => lt_trans (gap5 m n hnm) (hN n hn)⟩

/-- Source: `proof_gap/exercise_83/8.txt`. -/
theorem gap8 (h : IsCauchy x) : IsCauchy x := by
  exact h

/-- Source: `proof_gap/exercise_83/9.txt`. -/
theorem gap9 (h : IsCauchy x) : Convergent x := by
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N + 1, ?_⟩
    intro m hm n hn
    by_cases hmn : m = n
    · subst m
      simpa using hε
    · rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have htail := hN n m (by omega) hlt
        simpa [Real.dist_eq, abs_sub_comm] using htail
      · have htail := hN m n (by omega) hgt
        simpa [Real.dist_eq] using htail
  exact cauchySeq_tendsto_of_complete hcauchy

/-- Source: `proof_gap/exercise_83/10.txt`. -/
theorem gap10 (h : Convergent x) : Convergent x := by
  exact h

end

end ProofGap.Exercise83
