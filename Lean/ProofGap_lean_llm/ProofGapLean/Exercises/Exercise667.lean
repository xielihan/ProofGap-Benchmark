import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise667

noncomputable section

def f (x : ℝ) : ℝ := 1 / x
def δ (ε x₀ : ℝ) : ℝ := ε * x₀ ^ 2 / (1 + ε * |x₀|)

/-- Source: `proof_gap/exercise_667/1.txt`; exclude the two zero denominators. -/
private theorem delta_lt_abs (ε x₀ : ℝ) (hε : 0 < ε) (hx₀ : x₀ ≠ 0) :
    δ ε x₀ < |x₀| := by
  have hx₀pos : 0 < |x₀| := abs_pos.mpr hx₀
  have hden : 0 < 1 + ε * |x₀| := by
    have hm : 0 ≤ ε * |x₀| :=
      mul_nonneg (le_of_lt hε) (abs_nonneg _)
    linarith
  unfold δ
  apply (div_lt_iff₀ hden).2
  nlinarith [sq_abs x₀]

theorem gap1 (x x₀ : ℝ) (hx : x ≠ 0) (hx₀ : x₀ ≠ 0) :
    |f x - f x₀| = |x - x₀| / (|x| * |x₀|) := by
  unfold f
  have hid : 1 / x - 1 / x₀ = -(x - x₀) / (x * x₀) := by
    field_simp [hx, hx₀] <;> ring
  rw [hid, abs_div, abs_neg, abs_mul]

/-- Source: `proof_gap/exercise_667/2.txt`. -/
theorem gap2 (x x₀ : ℝ) : |x₀| - |x| ≤ |x - x₀| := by
  calc
    |x₀| - |x| ≤ |x₀ - x| := abs_sub_abs_le_abs_sub x₀ x
    _ = |x - x₀| := abs_sub_comm _ _

/-- Source: `proof_gap/exercise_667/3.txt`. -/
theorem gap3 (x x₀ : ℝ) : |x₀| - |x - x₀| ≤ |x| := by
  linarith [gap2 x x₀]

/-- Source: `proof_gap/exercise_667/4.txt`; add `x₀≠0`. -/
theorem gap4 (x x₀ : ℝ) (hx₀ : x₀ ≠ 0)
    (h : |x - x₀| < |x₀|) :
    |f x - f x₀| ≤
      |x - x₀| / (|x₀| ^ 2 - |x₀| * |x - x₀|) := by
  have htri := gap3 x x₀
  have hxpos : 0 < |x| := by linarith
  have hx : x ≠ 0 := abs_pos.mp hxpos
  have hx₀pos : 0 < |x₀| := abs_pos.mpr hx₀
  have ht : 0 ≤ |x - x₀| := abs_nonneg _
  have hdenpos : 0 < |x₀| ^ 2 - |x₀| * |x - x₀| := by
    have hm := mul_pos hx₀pos (sub_pos.mpr h)
    nlinarith
  have hprodpos : 0 < |x| * |x₀| := mul_pos hxpos hx₀pos
  have hdenle :
      |x₀| ^ 2 - |x₀| * |x - x₀| ≤ |x| * |x₀| := by
    have hm : 0 ≤ |x₀| * (|x| - (|x₀| - |x - x₀|)) :=
      mul_nonneg (le_of_lt hx₀pos) (sub_nonneg.mpr htri)
    nlinarith
  rw [gap1 x x₀ hx hx₀]
  apply (div_le_div_iff₀ hprodpos hdenpos).2
  exact mul_le_mul_of_nonneg_left hdenle ht

/-- Source: `proof_gap/exercise_667/5.txt`. -/
theorem gap5 (x x₀ ε : ℝ)
    (hbound : |f x - f x₀| ≤
      |x - x₀| / (|x₀| ^ 2 - |x₀| * |x - x₀|))
    (hsmall : |x - x₀| /
      (|x₀| ^ 2 - |x₀| * |x - x₀|) < ε) :
    |f x - f x₀| < ε := by
  exact lt_of_le_of_lt hbound hsmall

/-- Source: `proof_gap/exercise_667/6.txt`; positivity of `ε` and `x₀≠0` are required. -/
theorem gap6 (x x₀ ε : ℝ) (hε : 0 < ε) (hx₀ : x₀ ≠ 0)
    (h : |x - x₀| < δ ε x₀) :
    |x - x₀| / (|x₀| ^ 2 - |x₀| * |x - x₀|) < ε := by
  have hx₀pos : 0 < |x₀| := abs_pos.mpr hx₀
  have hδlt := delta_lt_abs ε x₀ hε hx₀
  have hdist : |x - x₀| < |x₀| := lt_trans h hδlt
  have hdenbase : 0 < 1 + ε * |x₀| := by
    have hm : 0 ≤ ε * |x₀| :=
      mul_nonneg (le_of_lt hε) (abs_nonneg _)
    linarith
  have hcross :
      |x - x₀| * (1 + ε * |x₀|) < ε * x₀ ^ 2 := by
    apply (lt_div_iff₀ hdenbase).mp
    simpa [δ] using h
  have hdenpos :
      0 < |x₀| ^ 2 - |x₀| * |x - x₀| := by
    have hm := mul_pos hx₀pos (sub_pos.mpr hdist)
    nlinarith
  apply (div_lt_iff₀ hdenpos).2
  nlinarith [sq_abs x₀]

/-- Source: `proof_gap/exercise_667/7.txt`. -/
theorem gap7 (x x₀ ε : ℝ) (hε : 0 < ε) (hx₀ : x₀ ≠ 0)
    (h : |x - x₀| < δ ε x₀) :
    |f x - f x₀| < ε := by
  have hdist : |x - x₀| < |x₀| :=
    lt_trans h (delta_lt_abs ε x₀ hε hx₀)
  exact gap5 x x₀ ε (gap4 x x₀ hx₀ hdist) (gap6 x x₀ ε hε hx₀ h)

/-- Source: `proof_gap/exercise_667/8.txt`. -/
theorem gap8 (ε x₀ : ℝ) :
    δ ε x₀ = ε * x₀ ^ 2 / (1 + ε * |x₀|) := by
  rfl

/-- Source: `proof_gap/exercise_667/9.txt`; add the missing positivity and nonzero hypotheses. -/
theorem gap9 (ε x₀ : ℝ) (hε : 0 < ε) (hx₀ : x₀ ≠ 0) :
    0 < ε * x₀ ^ 2 / (1 + ε * |x₀|) := by
  have hs : 0 < x₀ ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr hx₀
  have hden : 0 < 1 + ε * |x₀| := by
    have hm : 0 ≤ ε * |x₀| :=
      mul_nonneg (le_of_lt hε) (abs_nonneg _)
    linarith
  exact div_pos (mul_pos hε hs) hden

/-- Source: `proof_gap/exercise_667/10.txt`; add the missing positivity and nonzero hypotheses. -/
theorem gap10 (ε x₀ : ℝ) (hε : 0 < ε) (hx₀ : x₀ ≠ 0) :
    0 < δ ε x₀ := by
  simpa [δ] using gap9 ε x₀ hε hx₀

/-- Source: `proof_gap/exercise_667/11.txt`; replace informal `≈` by the exact correction factor. -/
theorem gap11 (ε x₀ : ℝ) (hε : ε = 0.001) (hx₀ : x₀ ≠ 0) :
    δ ε x₀ / (ε * x₀ ^ 2) = 1 / (1 + ε * |x₀|) := by
  have hεpos : 0 < ε := by
    rw [hε]
    norm_num
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have hsne : x₀ ^ 2 ≠ 0 := pow_ne_zero 2 hx₀
  have hdenpos : 0 < 1 + ε * |x₀| := by
    have hm : 0 ≤ ε * |x₀| :=
      mul_nonneg (le_of_lt hεpos) (abs_nonneg _)
    linarith
  unfold δ
  field_simp [hεne, hsne, ne_of_gt hdenpos] <;> ring

/-- Source: `proof_gap/exercise_667/12.txt`; correct the rounded value to the exact value dictated by `δ`. -/
theorem gap12 : δ 0.001 0.1 = (1 / 100010 : ℝ) := by
  norm_num [δ, abs_of_nonneg]

/-- Source: `proof_gap/exercise_667/13.txt`; correct the rounded value to the exact value dictated by `δ`. -/
theorem gap13 : δ 0.001 0.01 = (1 / 10000100 : ℝ) := by
  norm_num [δ, abs_of_nonneg]

/-- Source: `proof_gap/exercise_667/14.txt`; correct the rounded value to the exact value dictated by `δ`. -/
theorem gap14 : δ 0.001 0.001 = (1 / 1000001000 : ℝ) := by
  norm_num [δ, abs_of_nonneg]

/-- Source: `proof_gap/exercise_667/15.txt`; state failure of uniform continuity on `(0,1)` with both points in the domain. -/
theorem gap15 :
    ¬ ∃ d > 0, ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ x₀ ∈ Set.Ioo (0 : ℝ) 1,
      |x - x₀| < d → |f x - f x₀| < 0.001 := by
  rintro ⟨d, hd, hU⟩
  let x : ℝ := d / (2 * (1 + d))
  have hq : 0 < 1 + d := by linarith
  have hden : 0 < 2 * (1 + d) := mul_pos (by norm_num) hq
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos hd hden
  have hxhalf : x < 1 / 2 := by
    dsimp [x]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hxone : x < 1 := by linarith
  have h2xpos : 0 < 2 * x := mul_pos (by norm_num) hxpos
  have h2xone : 2 * x < 1 := by nlinarith
  have hxd : x < d := by
    dsimp [x]
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_nonneg d]
  have hdist : |x - 2 * x| < d := by
    rw [show x - 2 * x = -x by ring, abs_neg, abs_of_pos hxpos]
    exact hxd
  have hcontra :=
    hU x ⟨hxpos, hxone⟩ (2 * x) ⟨h2xpos, h2xone⟩ hdist
  have hdiff : f x - f (2 * x) = (1 + d) / d := by
    dsimp [f, x]
    field_simp [ne_of_gt hd, ne_of_gt hq] <;> ring
  have hval : |f x - f (2 * x)| = (1 + d) / d := by
    rw [hdiff, abs_of_pos (div_pos hq hd)]
  rw [hval] at hcontra
  have hgt : 1 < (1 + d) / d := by
    apply (lt_div_iff₀ hd).2
    linarith
  norm_num at hcontra
  linarith

end

end ProofGap.Exercise667
