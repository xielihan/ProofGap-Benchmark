import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1415

noncomputable section

def y (x : ℝ) := (x - 1) ^ 3

theorem gap1 (x : ℝ) : deriv y x = 3 * (x - 1) ^ 2 := by
  unfold y
  convert
    (((hasDerivAt_id x).sub_const 1).pow 3).deriv using 1 <;>
    simp only [id_eq] <;> ring
theorem gap2 (x : ℝ) : 0 ≤ 3 * (x - 1) ^ 2 := by
  positivity
theorem gap3 (x : ℝ) (hx : x ≠ 1) : 0 < deriv y x := by
  rw [gap1]
  have hs : 0 < (x - 1) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  nlinarith
theorem gap4 : StrictMono y := by
  intro a b hab
  unfold y
  exact (show Odd 3 by decide).strictMono_pow (by linarith)
theorem gap5 : ¬ ∃ x : ℝ, IsMaxOn y Set.univ x := by
  rintro ⟨x, hx⟩
  rw [isMaxOn_iff] at hx
  have hle := hx (x + 1) (Set.mem_univ _)
  have hlt := gap4 (show x < x + 1 by linarith)
  linarith
theorem gap6 : ¬ ∃ x : ℝ, IsMinOn y Set.univ x := by
  rintro ⟨x, hx⟩
  rw [isMinOn_iff] at hx
  have hle := hx (x - 1) (Set.mem_univ _)
  have hlt := gap4 (show x - 1 < x by linarith)
  linarith

end
end ProofGap.Exercise1415
