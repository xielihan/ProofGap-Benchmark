import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise390

noncomputable section

def f (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2)
def rangeOnPositive : Set ℝ :=
  {y | ∃ x ∈ Set.Ioi (0 : ℝ), y = f x}

/-- Source: `proof_gap/exercise_390/1.txt`. -/
theorem gap1 : StrictMonoOn f (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hdx : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hdy : 0 < 1 + y ^ 2 := by
    nlinarith [sq_nonneg y]
  have hprod : x * y < 1 := by
    calc
      x * y < 1 * y := mul_lt_mul_of_pos_right hx.2 hy.1
      _ = y := one_mul y
      _ < 1 := hy.2
  have hfactor : 0 < (y - x) * (1 - x * y) :=
    mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hprod)
  unfold f
  apply (div_lt_div_iff₀ hdx hdy).2
  nlinarith [hfactor]

/-- Source: `proof_gap/exercise_390/2.txt`. -/
theorem gap2 : StrictAntiOn f (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hdx : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hdy : 0 < 1 + y ^ 2 := by
    nlinarith [sq_nonneg y]
  have hprod : 1 < x * y := by
    calc
      1 < y := hy
      _ = 1 * y := (one_mul y).symm
      _ < x * y := mul_lt_mul_of_pos_right hx hy0
  have hfactor : 0 < (y - x) * (x * y - 1) :=
    mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hprod)
  unfold f
  apply (div_lt_div_iff₀ hdy hdx).2
  nlinarith [hfactor]

/-- Source: `proof_gap/exercise_390/3.txt`. -/
theorem gap3 : f 1 = 1 := by
  norm_num [f]

/-- Source: `proof_gap/exercise_390/4.txt`. -/
theorem gap4 : sInf rangeOnPositive = 0 := by
  have hnonempty : rangeOnPositive.Nonempty := by
    refine ⟨f 1, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  have hnonneg : ∀ y ∈ rangeOnPositive, 0 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hden : 0 < 1 + x ^ 2 := by
      nlinarith [sq_nonneg x]
    unfold f
    exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt hx)) (le_of_lt hden)
  have hbdd : BddBelow rangeOnPositive := ⟨0, hnonneg⟩
  apply le_antisymm
  · by_contra h
    have hspos : 0 < sInf rangeOnPositive := lt_of_not_ge h
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / sInf rangeOnPositive)
    have hnpos : 0 < (n : ℝ) :=
      lt_trans (div_pos (by norm_num) hspos) hn
    have htwo : 2 < (n : ℝ) * sInf rangeOnPositive :=
      (div_lt_iff₀ hspos).mp hn
    have hstep :
        0 < (n : ℝ) * ((n : ℝ) * sInf rangeOnPositive - 2) :=
      mul_pos hnpos (sub_pos.mpr htwo)
    have hnmem : f (n : ℝ) ∈ rangeOnPositive :=
      ⟨(n : ℝ), hnpos, rfl⟩
    have hden : 0 < 1 + (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    have hflt : f (n : ℝ) < sInf rangeOnPositive := by
      unfold f
      apply (div_lt_iff₀ hden).2
      nlinarith [hstep]
    exact (not_lt_of_ge (csInf_le hbdd hnmem)) hflt
  · exact le_csInf hnonempty hnonneg

/-- Source: `proof_gap/exercise_390/5.txt`. -/
theorem gap5 : sSup rangeOnPositive = f 1 := by
  have hnonempty : rangeOnPositive.Nonempty := by
    refine ⟨f 1, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  have hupper : ∀ y ∈ rangeOnPositive, y ≤ f 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [gap3]
    have hden : 0 < 1 + x ^ 2 := by
      nlinarith [sq_nonneg x]
    unfold f
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (x - 1)]
  have hbdd : BddAbove rangeOnPositive := ⟨f 1, hupper⟩
  have hone_mem : f 1 ∈ rangeOnPositive :=
    ⟨1, by norm_num, rfl⟩
  exact le_antisymm (csSup_le hnonempty hupper) (le_csSup hbdd hone_mem)

/-- Source: `proof_gap/exercise_390/6.txt`. -/
theorem gap6 : f 1 = 1 := by
  exact gap3

/-- Source: `proof_gap/exercise_390/7.txt`. -/
theorem gap7 : sSup rangeOnPositive = 1 := by
  calc
    sSup rangeOnPositive = f 1 := gap5
    _ = 1 := gap3

end

end ProofGap.Exercise390
