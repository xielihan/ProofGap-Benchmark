import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1593_3

noncomputable section

def y (x : ℝ) := Real.exp x - (1 + x + x ^ 2 / 2)
def axis (_x : ℝ) : ℝ := 0
def iterDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (iterDeriv n f)
def ContactOrder (f g : ℝ → ℝ) (x₀ : ℝ) (m : ℕ) : Prop :=
  (∀ k ≤ m, iterDeriv k f x₀ = iterDeriv k g x₀) ∧
    iterDeriv (m + 1) f x₀ ≠ iterDeriv (m + 1) g x₀

private theorem iterDeriv_axis_eq (n : ℕ) : iterDeriv n axis = axis := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iterDeriv]
      rw [ih]
      funext x
      exact (hasDerivAt_const x (0 : ℝ)).deriv

theorem gap1 (x : ℝ) : deriv y x = Real.exp x - 1 - x := by
  unfold y
  have hid : HasDerivAt (fun z : ℝ => z) 1 x := by
    simpa only [id_eq] using hasDerivAt_id x
  have hmul : HasDerivAt (fun z : ℝ => z * z) (x + x) x := by
    convert hid.mul hid using 1 <;> ring
  have hquad : HasDerivAt (fun z : ℝ => z ^ 2 / 2) x x := by
    convert hmul.div_const 2 using 1 <;> ring
  have hpoly :
      HasDerivAt (fun z : ℝ => 1 + z + z ^ 2 / 2) (1 + x) x := by
    convert
      (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add hquad) using 1 <;>
      ring
  convert ((Real.hasDerivAt_exp x).sub hpoly).deriv using 1 <;> ring
theorem gap2 (x : ℝ) : deriv (deriv y) x = Real.exp x - 1 := by
  have hy : deriv y = fun z : ℝ => Real.exp z - 1 - z := by
    funext z
    exact gap1 z
  rw [hy]
  convert
    (((Real.hasDerivAt_exp x).sub (hasDerivAt_const x (1 : ℝ))).sub
      (hasDerivAt_id x)).deriv using 1 <;> ring
theorem gap3 (x : ℝ) : deriv (deriv (deriv y)) x = Real.exp x := by
  have hy : deriv (deriv y) = fun z : ℝ => Real.exp z - 1 := by
    funext z
    exact gap2 z
  rw [hy]
  convert
    ((Real.hasDerivAt_exp x).sub (hasDerivAt_const x (1 : ℝ))).deriv using 1 <;> ring
theorem gap4 : deriv y 0 = deriv (deriv y) 0 := by
  rw [gap1, gap2, Real.exp_zero]
  norm_num
theorem gap5 : deriv (deriv y) 0 = 0 := by
  rw [gap2, Real.exp_zero]
  norm_num
theorem gap6 : deriv y 0 = 0 := by
  calc
    deriv y 0 = deriv (deriv y) 0 := gap4
    _ = 0 := gap5
theorem gap7 : deriv (deriv (deriv y)) 0 = 1 := by
  rw [gap3, Real.exp_zero]
theorem gap8 : (1 : ℝ) ≠ 0 := by
  norm_num
theorem gap9 : deriv (deriv (deriv y)) 0 ≠ 0 := by
  simpa [gap7] using gap8
theorem gap10 : ContactOrder y axis 0 2 := by
  unfold ContactOrder
  constructor
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl
    · simp [iterDeriv, y, axis]
    · rw [iterDeriv_axis_eq]
      simpa [iterDeriv, axis] using gap6
    · rw [iterDeriv_axis_eq]
      simpa [iterDeriv, axis] using gap5
  · rw [iterDeriv_axis_eq]
    simpa [iterDeriv, axis] using gap9

end
end ProofGap.Exercise1593_3
