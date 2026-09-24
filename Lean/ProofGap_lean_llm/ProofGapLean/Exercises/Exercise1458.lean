import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1458

noncomputable section

def P (q x : ℝ) : ℝ := x ^ 2 + q

def uniformError (q : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1, y = |P q x|}

def IsBest (q : ℝ) : Prop := ∀ q' : ℝ, uniformError q ≤ uniformError q'

private theorem uniformError_eq_aux (q : ℝ) :
    uniformError q = max |q| |1 + q| := by
  unfold uniformError
  have hbound :
      ∀ y ∈ {y : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1, y = |P q x|},
        y ≤ max |q| |1 + q| := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have hxprod : 0 ≤ (1 - x) * (x + 1) := by
      apply mul_nonneg (sub_nonneg.mpr hx.2)
      linarith [hx.1]
    have hx_sq_le : x ^ 2 ≤ 1 := by
      nlinarith [hxprod]
    have hid :
        P q x = (1 - x ^ 2) * q + x ^ 2 * (1 + q) := by
      simp only [P]
      ring
    calc
      |P q x| = |(1 - x ^ 2) * q + x ^ 2 * (1 + q)| := by rw [hid]
      _ ≤ |(1 - x ^ 2) * q| + |x ^ 2 * (1 + q)| := abs_add_le _ _
      _ = (1 - x ^ 2) * |q| + x ^ 2 * |1 + q| := by
        simp only [abs_mul,
          abs_of_nonneg (sub_nonneg.mpr hx_sq_le),
          abs_of_nonneg hx_sq_nonneg]
      _ ≤ (1 - x ^ 2) * max |q| |1 + q| +
          x ^ 2 * max |q| |1 + q| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _)
            (sub_nonneg.mpr hx_sq_le))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hx_sq_nonneg)
      _ = max |q| |1 + q| := by ring
  apply le_antisymm
  · apply csSup_le
    · refine ⟨|P q 0|, ?_⟩
      exact ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
    · exact hbound
  · have hbdd :
        BddAbove {y : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1, y = |P q x|} := by
      refine ⟨max |q| |1 + q|, ?_⟩
      intro y hy
      exact hbound y hy
    apply max_le
    · apply le_csSup hbdd
      refine ⟨0, ?_, ?_⟩
      · constructor <;> norm_num
      · simp [P]
    · apply le_csSup hbdd
      refine ⟨1, ?_, ?_⟩
      · constructor <;> norm_num
      · norm_num [P]

theorem gap1 (q x : ℝ) :
    deriv (P q) x = 2 * x := by
  change deriv (fun y : ℝ => y ^ 2 + q) x = 2 * x
  simpa using (((hasDerivAt_id x).pow 2).add_const q).deriv

theorem gap2 (q x : ℝ) (hzero : deriv (P q) x = 0) :
    x = 0 := by
  rw [gap1] at hzero
  linarith

theorem gap3 (q : ℝ) :
    uniformError q = max (max |P q 0| |P q 1|) |P q (-1)| := by
  simpa [P, max_assoc] using uniformError_eq_aux q

theorem gap4 (q : ℝ) :
    max (max |P q 0| |P q 1|) |P q (-1)| = max |q| |1 + q| := by
  simp [P]

theorem gap5 (q : ℝ) :
    uniformError q = max |q| |1 + q| := by
  exact uniformError_eq_aux q

theorem gap6 (q : ℝ) (heq : |q| = |1 + q|) :
    IsBest q := by
  intro q'
  rw [uniformError_eq_aux, uniformError_eq_aux]
  have hq : q = -(1 / 2 : ℝ) := by
    rcases (abs_eq_abs.mp heq) with h | h
    · linarith
    · linarith
  have hleft : max |q| |1 + q| = (1 / 2 : ℝ) := by
    rw [hq]
    norm_num
  rw [hleft]
  have htri : (1 : ℝ) ≤ |q'| + |1 + q'| := by
    calc
      (1 : ℝ) = |(1 + q') - q'| := by
        rw [show (1 + q') - q' = (1 : ℝ) by ring, abs_one]
      _ ≤ |1 + q'| + |q'| := abs_sub _ _
      _ = |q'| + |1 + q'| := by ring
  linarith [le_max_left |q'| |1 + q'|,
    le_max_right |q'| |1 + q'|]

theorem gap7 (q : ℝ) (hq : q = -(1 / 2 : ℝ)) :
    |q| = |1 + q| := by
  subst q
  norm_num

theorem gap8 (q : ℝ) (hq : q = -(1 / 2 : ℝ)) :
    IsBest q := by
  exact gap6 q (gap7 q hq)

theorem gap9 (q : ℝ) :
    q ∈ ({-(1 / 2 : ℝ)} : Set ℝ) → IsBest q := by
  intro hq
  have hq' : q = -(1 / 2 : ℝ) := by
    simpa using hq
  exact gap8 q hq'

end

end ProofGap.Exercise1458
