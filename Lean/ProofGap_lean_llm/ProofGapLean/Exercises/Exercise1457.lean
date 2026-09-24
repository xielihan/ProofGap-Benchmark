import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1457

noncomputable section

def P (x : ℝ) : ℝ := x * (x - 1) ^ 2 * (x + 2)
def cneg : ℝ := (-1 - Real.sqrt 3) / 2
def cpos : ℝ := (-1 + Real.sqrt 3) / 2

def uniformNorm : ℝ :=
  sSup {y : ℝ | ∃ x ∈ Set.Icc (-2 : ℝ) 1, y = |P x|}

def ApproxWithin (a b ε : ℝ) : Prop := |a - b| < ε

private lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
  simpa using (Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num))

private lemma sqrt_three_cube : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
  calc
    (Real.sqrt 3) ^ 3 = Real.sqrt 3 * (Real.sqrt 3) ^ 2 := by ring
    _ = 3 * Real.sqrt 3 := by rw [sqrt_three_sq]; ring

private lemma sqrt_three_fourth : (Real.sqrt 3) ^ 4 = (9 : ℝ) := by
  calc
    (Real.sqrt 3) ^ 4 = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
    _ = 9 := by rw [sqrt_three_sq]; norm_num

private lemma sqrt_three_bounds :
    (1 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  constructor <;> nlinarith [sqrt_three_sq, Real.sqrt_nonneg (3 : ℝ)]

private lemma cneg_mem_Icc : cneg ∈ Set.Icc (-2 : ℝ) 1 := by
  rcases sqrt_three_bounds with ⟨hlo, hu⟩
  unfold cneg
  constructor <;> linarith

private lemma cpos_mem_Icc : cpos ∈ Set.Icc (-2 : ℝ) 1 := by
  rcases sqrt_three_bounds with ⟨hlo, hu⟩
  unfold cpos
  constructor <;> linarith

private lemma cneg_abs_value :
    |P cneg| = (9 + 6 * Real.sqrt 3) / 4 := by
  have hp : P cneg = -((9 + 6 * Real.sqrt 3) / 4) := by
    unfold P cneg
    ring_nf
    simp only [sqrt_three_fourth, sqrt_three_cube, sqrt_three_sq]
    ring
  rw [hp, abs_neg, abs_of_nonneg]
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

private lemma P_abs_le_cneg (x : ℝ) (hx : x ∈ Set.Icc (-2 : ℝ) 1) :
    |P x| ≤ |P cneg| := by
  rw [cneg_abs_value]
  rcases sqrt_three_bounds with ⟨hsone, hstwo⟩
  rcases le_total x 0 with hxzero | hxzero
  · have hP : P x ≤ 0 := by
      unfold P
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hxzero (sq_nonneg (x - 1)))
        (by linarith [hx.1])
    rw [abs_of_nonpos hP]
    have hqeq :
        x ^ 2 - (1 + Real.sqrt 3) * x + 3 * Real.sqrt 3 / 2 =
          (x - (1 + Real.sqrt 3) / 2) ^ 2 + (Real.sqrt 3 - 1) := by
      ring_nf
      simp only [sqrt_three_sq]
      ring
    have hq :
        0 ≤ x ^ 2 - (1 + Real.sqrt 3) * x + 3 * Real.sqrt 3 / 2 := by
      rw [hqeq]
      exact add_nonneg (sq_nonneg _) (sub_nonneg.mpr hsone)
    have hfac :
        0 ≤ (x - cneg) ^ 2 *
          (x ^ 2 - (1 + Real.sqrt 3) * x + 3 * Real.sqrt 3 / 2) :=
      mul_nonneg (sq_nonneg _) hq
    have hid :
        P x + (9 + 6 * Real.sqrt 3) / 4 =
          (x - cneg) ^ 2 *
            (x ^ 2 - (1 + Real.sqrt 3) * x + 3 * Real.sqrt 3 / 2) := by
      unfold P cneg
      ring_nf
      simp only [sqrt_three_cube, sqrt_three_sq]
      ring
    linarith
  · have hP : 0 ≤ P x := by
      unfold P
      exact mul_nonneg
        (mul_nonneg hxzero (sq_nonneg (x - 1)))
        (by linarith)
    rw [abs_of_nonneg hP]
    have ha0 : 0 ≤ x * (x + 2) :=
      mul_nonneg hxzero (by linarith)
    have ha3 : x * (x + 2) ≤ 3 := by
      have hf : 0 ≤ (1 - x) * (x + 3) :=
        mul_nonneg (by linarith [hx.2]) (by linarith)
      nlinarith
    have hb0 : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
    have hb1 : (x - 1) ^ 2 ≤ 1 := by
      have hf : 0 ≤ x * (2 - x) :=
        mul_nonneg hxzero (by linarith [hx.2])
      nlinarith
    calc
      P x = (x * (x + 2)) * (x - 1) ^ 2 := by unfold P; ring
      _ ≤ 3 * (x - 1) ^ 2 := mul_le_mul_of_nonneg_right ha3 hb0
      _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left hb1 (by norm_num)
      _ ≤ (9 + 6 * Real.sqrt 3) / 4 := by nlinarith

theorem gap1 (x : ℝ) :
    deriv P x = 2 * (x - 1) * (2 * x ^ 2 + 2 * x - 1) := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x :=
    hid.sub_const 1
  have hsquare : HasDerivAt (fun y : ℝ => (y - 1) ^ 2)
      (2 * (x - 1)) x := by
    simpa only [pow_two, one_mul, mul_one, two_mul] using hsub.mul hsub
  have hfirst : HasDerivAt (fun y : ℝ => y * (y - 1) ^ 2)
      ((x - 1) ^ 2 + x * (2 * (x - 1))) x := by
    simpa only [one_mul] using hid.mul hsquare
  have hP : HasDerivAt P
      (((x - 1) ^ 2 + x * (2 * (x - 1))) * (x + 2) +
        x * (x - 1) ^ 2) x := by
    change HasDerivAt (fun y : ℝ => y * (y - 1) ^ 2 * (y + 2))
      (((x - 1) ^ 2 + x * (2 * (x - 1))) * (x + 2) +
        x * (x - 1) ^ 2) x
    simpa only [mul_one] using hfirst.mul (hid.add_const 2)
  rw [hP.deriv]
  ring

theorem gap2 (x : ℝ) (hzero : deriv P x = 0) :
    x = 1 ∨ x = cpos ∨ x = cneg := by
  rw [gap1] at hzero
  rcases mul_eq_zero.mp hzero with hlin | hquad
  · left
    rcases mul_eq_zero.mp hlin with htwo | hx
    · norm_num at htwo
    · linarith
  · right
    have hs := sqrt_three_sq
    have hn := Real.sqrt_nonneg (3 : ℝ)
    have hy : (2 * x + 1) ^ 2 = 3 := by
      nlinarith
    by_cases hsign : 0 ≤ 2 * x + 1
    · left
      have heq : 2 * x + 1 = Real.sqrt 3 := by
        nlinarith
      unfold cpos
      linarith
    · right
      have hyneg : 2 * x + 1 ≤ 0 := le_of_not_ge hsign
      have heq : 2 * x + 1 = -Real.sqrt 3 := by
        nlinarith
      unfold cneg
      linarith

theorem gap3 :
    uniformNorm = max (max |P (-2)| |P 1|) (max |P cneg| |P cpos|) := by
  unfold uniformNorm
  apply le_antisymm
  · apply csSup_le
    · refine ⟨|P 0|, ?_⟩
      exact ⟨0, by constructor <;> norm_num, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact (P_abs_le_cneg x hx).trans
        ((le_max_left _ _).trans (le_max_right _ _))
  · have hB : BddAbove
        {y : ℝ | ∃ x ∈ Set.Icc (-2 : ℝ) 1, y = |P x|} := by
      refine ⟨|P cneg|, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact P_abs_le_cneg x hx
    apply max_le
    · apply max_le
      · apply le_csSup hB
        exact ⟨(-2 : ℝ), by constructor <;> norm_num, rfl⟩
      · apply le_csSup hB
        exact ⟨(1 : ℝ), by constructor <;> norm_num, rfl⟩
    · apply max_le
      · apply le_csSup hB
        exact ⟨cneg, cneg_mem_Icc, rfl⟩
      · apply le_csSup hB
        exact ⟨cpos, cpos_mem_Icc, rfl⟩

theorem gap4 :
    uniformNorm = |P cneg| := by
  rw [gap3]
  apply le_antisymm
  · apply max_le
    · apply max_le
      · exact P_abs_le_cneg (-2) (by constructor <;> norm_num)
      · exact P_abs_le_cneg 1 (by constructor <;> norm_num)
    · apply max_le
      · exact le_rfl
      · exact P_abs_le_cneg cpos cpos_mem_Icc
  · exact (le_max_left _ _).trans (le_max_right _ _)

theorem gap5 :
    |P cneg| = (9 + 6 * Real.sqrt 3) / 4 := by
  exact cneg_abs_value

theorem gap6 :
    ApproxWithin ((9 + 6 * Real.sqrt 3) / 4) 4.85 0.01 := by
  have hs := sqrt_three_sq
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hlo : (1732 : ℝ) / 1000 < Real.sqrt 3 := by
    nlinarith
  have hu : Real.sqrt 3 < (1733 : ℝ) / 1000 := by
    nlinarith
  unfold ApproxWithin
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap7 :
    ApproxWithin uniformNorm 4.85 0.01 := by
  rw [gap4, gap5]
  exact gap6

end

end ProofGap.Exercise1457
