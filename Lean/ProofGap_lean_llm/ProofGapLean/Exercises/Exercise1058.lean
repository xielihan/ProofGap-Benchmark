import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1058

noncomputable section

def y (x : ℝ) : ℝ := 2 * Real.sin x
def solutionSet : Set ℝ :=
  {x | |x| < Real.pi / 3 ∨
    2 * Real.pi / 3 < |x| ∧ |x| ≤ Real.pi}

private theorem abs_cos_gt_half_iff (x : ℝ)
    (hlower : -Real.pi ≤ x) (hupper : x ≤ Real.pi) :
    |Real.cos x| > 1 / 2 ↔
      |x| < Real.pi / 3 ∨
        2 * Real.pi / 3 < |x| ∧ |x| ≤ Real.pi := by
  have hxabs_nonneg : 0 ≤ |x| := abs_nonneg x
  have hxabs_le_pi : |x| ≤ Real.pi := (abs_le).2 ⟨hlower, hupper⟩
  have hxmem : |x| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hxabs_nonneg, hxabs_le_pi⟩
  have hamem : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hbmem : 2 * Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcosa : Real.cos (Real.pi / 3) = (1 / 2 : ℝ) :=
    Real.cos_pi_div_three
  have hcosb : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    calc
      Real.cos (2 * Real.pi / 3) =
          Real.cos (Real.pi - Real.pi / 3) := by congr 1 <;> ring
      _ = -Real.cos (Real.pi / 3) := by rw [Real.cos_pi_sub]
      _ = -(1 / 2 : ℝ) := by rw [hcosa]
  constructor
  · intro h
    by_cases hc : 0 ≤ Real.cos x
    · have hpos : (1 / 2 : ℝ) < Real.cos x := by
        simpa [abs_of_nonneg hc] using h
      have hpos_abs : (1 / 2 : ℝ) < Real.cos |x| := by
        simpa only [Real.cos_abs] using hpos
      left
      by_contra hnot
      have hat : Real.pi / 3 ≤ |x| := le_of_not_gt hnot
      have hcos_le : Real.cos |x| ≤ Real.cos (Real.pi / 3) := by
        rcases hat.eq_or_lt with heq | hlt
        · rw [← heq]
        · exact (Real.strictAntiOn_cos hamem hxmem hlt).le
      rw [hcosa] at hcos_le
      linarith
    · have hcneg : Real.cos x < 0 := lt_of_not_ge hc
      have hneg : Real.cos x < -(1 / 2 : ℝ) := by
        have habs : (1 / 2 : ℝ) < -Real.cos x := by
          simpa [abs_of_nonpos hcneg.le] using h
        linarith
      have hneg_abs : Real.cos |x| < -(1 / 2 : ℝ) := by
        simpa only [Real.cos_abs] using hneg
      right
      refine ⟨?_, hxabs_le_pi⟩
      by_contra hnot
      have htb : |x| ≤ 2 * Real.pi / 3 := le_of_not_gt hnot
      have hcos_ge : Real.cos (2 * Real.pi / 3) ≤ Real.cos |x| := by
        rcases htb.eq_or_lt with heq | hlt
        · rw [heq]
        · exact (Real.strictAntiOn_cos hxmem hbmem hlt).le
      rw [hcosb] at hcos_ge
      linarith
  · intro h
    rcases h with hlt | hgt
    · have hcmp := Real.strictAntiOn_cos hxmem hamem hlt
      rw [hcosa] at hcmp
      have hxcmp : (1 / 2 : ℝ) < Real.cos x := by
        simpa only [Real.cos_abs] using hcmp
      exact lt_of_lt_of_le hxcmp (le_abs_self (Real.cos x))
    · have hcmp := Real.strictAntiOn_cos hbmem hxmem hgt.1
      rw [hcosb] at hcmp
      have hxcmp : Real.cos x < -(1 / 2 : ℝ) := by
        simpa only [Real.cos_abs] using hcmp
      have hneg : (1 / 2 : ℝ) < -Real.cos x := by
        linarith
      exact lt_of_lt_of_le hneg (neg_le_abs (Real.cos x))

theorem gap1 (x : ℝ) :
    deriv y x = 2 * Real.cos x := by
  change deriv (fun t : ℝ => 2 * Real.sin t) x = 2 * Real.cos x
  exact ((Real.hasDerivAt_sin x).const_mul 2).deriv

theorem gap2 (x : ℝ) (hcos : |Real.cos x| > 1 / 2) :
    |deriv y x| > 1 := by
  rw [gap1, abs_mul]
  norm_num at hcos ⊢
  linarith

theorem gap3 (x : ℝ) (hcos : |Real.cos x| > 1 / 2) :
    |deriv y x| > 1 := by
  exact gap2 x hcos

theorem gap4 (x : ℝ) (hlower : -Real.pi ≤ x) (hupper : x ≤ Real.pi) :
    |deriv y x| > 1 ↔
      |x| < Real.pi / 3 ∨
        2 * Real.pi / 3 < |x| ∧ |x| ≤ Real.pi := by
  constructor
  · intro hder
    have hcos : |Real.cos x| > 1 / 2 := by
      rw [gap1, abs_mul] at hder
      norm_num at hder ⊢
      linarith
    exact (abs_cos_gt_half_iff x hlower hupper).mp hcos
  · intro hx
    apply gap2 x
    exact (abs_cos_gt_half_iff x hlower hupper).mpr hx

theorem gap5 (x : ℝ) (hlower : -Real.pi ≤ x) (hupper : x ≤ Real.pi) :
    x ∈ solutionSet ↔ |deriv y x| > 1 := by
  simpa [solutionSet] using (gap4 x hlower hupper).symm

end

end ProofGap.Exercise1058
