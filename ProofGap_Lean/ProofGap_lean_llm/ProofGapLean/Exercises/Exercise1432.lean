import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1432

noncomputable section

def y (x : ℝ) : ℝ := x + 1 / x

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    deriv y x = 1 - 1 / x ^ 2 := by
  have hrecip : HasDerivAt (fun z : ℝ => 1 / z) (-1 / x ^ 2) x := by
    simpa [one_div] using (hasDerivAt_id x).inv hx
  unfold y
  convert ((hasDerivAt_id x).add hrecip).deriv using 1 <;> ring

theorem gap2 (x : ℝ) (hx : x = -1 ∨ x = 1) :
    deriv y x = 0 := by
  rcases hx with rfl | rfl <;> norm_num [gap1]

theorem gap3 (x : ℝ) (hx : x < -1) : 0 < deriv y x := by
  have hx0 : x ≠ 0 := by linarith
  rw [gap1 x hx0]
  have hs : 1 < x ^ 2 := by nlinarith
  have hp : 0 < x ^ 2 := by linarith
  have hd : 1 / x ^ 2 < 1 := by
    apply (div_lt_one hp).2
    simpa using hs
  linarith

theorem gap4 (x : ℝ) (h₁ : -1 < x) (h₂ : x < 0) :
    deriv y x < 0 := by
  have hx0 : x ≠ 0 := by linarith
  rw [gap1 x hx0]
  have hs : x ^ 2 < 1 := by nlinarith
  have hp : 0 < x ^ 2 := by nlinarith
  have hd : 1 < 1 / x ^ 2 := by
    apply (lt_div_iff₀ hp).2
    simpa using hs
  linarith

theorem gap5 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1) :
    deriv y x < 0 := by
  have hx0 : x ≠ 0 := by linarith
  rw [gap1 x hx0]
  have hs : x ^ 2 < 1 := by nlinarith
  have hp : 0 < x ^ 2 := by nlinarith
  have hd : 1 < 1 / x ^ 2 := by
    apply (lt_div_iff₀ hp).2
    simpa using hs
  linarith

theorem gap6 (x : ℝ) (hx : 1 < x) : 0 < deriv y x := by
  have hx0 : x ≠ 0 := by linarith
  rw [gap1 x hx0]
  have hs : 1 < x ^ 2 := by nlinarith
  have hp : 0 < x ^ 2 := by linarith
  have hd : 1 / x ^ 2 < 1 := by
    apply (div_lt_one hp).2
    simpa using hs
  linarith

theorem gap7 : IsLocalMax y (-1) := by
  show ∀ᶠ z in nhds (-1 : ℝ), y z ≤ y (-1)
  refine Filter.Eventually.mono
    (Iio_mem_nhds (show (-1 : ℝ) < 0 by norm_num)) ?_
  intro x hx
  change x < 0 at hx
  have hx0 : x ≠ 0 := ne_of_lt hx
  have hdiv : (x + 1) ^ 2 / x ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (sq_nonneg (x + 1)) (le_of_lt hx)
  calc
    y x = (x + 1) ^ 2 / x - 2 := by
      rw [y]
      field_simp [hx0]
      <;> ring
    _ ≤ -2 := by linarith
    _ = y (-1) := by norm_num [y]

theorem gap8 : y (-1) = -2 := by
  norm_num [y]

theorem gap9 : IsLocalMin y 1 := by
  show ∀ᶠ z in nhds (1 : ℝ), y 1 ≤ y z
  refine Filter.Eventually.mono
    (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_
  intro x hx
  change 0 < x at hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hdiv : 0 ≤ (x - 1) ^ 2 / x :=
    div_nonneg (sq_nonneg (x - 1)) (le_of_lt hx)
  calc
    y 1 = 2 := by norm_num [y]
    _ ≤ (x - 1) ^ 2 / x + 2 := by linarith
    _ = y x := by
      rw [y]
      field_simp [hx0]
      <;> ring

theorem gap10 : y 1 = 2 := by
  norm_num [y]

end
end ProofGap.Exercise1432
