import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise598_2

noncomputable section

def f (x : ℝ) : ℝ := 2 * x / (1 + x)

/-- Source: `proof_gap/exercise_598_2/1.txt`. -/
theorem gap1 (x : ℝ) (hx : 0 < x) : 0 < f x := by
  unfold f
  have hden : 0 < 1 + x := by linarith
  exact div_pos (mul_pos (by linarith) hx) hden

/-- Source: `proof_gap/exercise_598_2/2.txt`. -/
theorem gap2 (x : ℝ) (hx : 0 < x) : f x < 2 := by
  unfold f
  have hden : 0 < 1 + x := by linarith
  apply (div_lt_iff₀ hden).2
  linarith

/-- Source: `proof_gap/exercise_598_2/3.txt`. -/
theorem gap3 (x : ℝ) (hx : 0 < x) : (0 : ℝ) < 2 := by
  linarith

/-- Source: `proof_gap/exercise_598_2/4.txt`. -/
theorem gap4 : Filter.Tendsto f Filter.atTop (nhds 2) := by
  have hshift : Filter.Tendsto (fun x : ℝ => 1 + x) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    refine Filter.eventually_atTop.2 ?_
    exact ⟨b, fun a ha => by linarith⟩
  have hinv : Filter.Tendsto (fun x : ℝ => (1 + x)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hlim :
      Filter.Tendsto (fun x : ℝ => 2 - 2 * (1 + x)⁻¹)
        Filter.atTop (nhds 2) := by
    simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv))
  apply hlim.congr'
  refine Filter.eventually_atTop.2 ?_
  refine ⟨0, ?_⟩
  intro x hx
  dsimp [f]
  have hne : 1 + x ≠ 0 := ne_of_gt (by linarith)
  field_simp [hne]
  ring

/-- Source: `proof_gap/exercise_598_2/5.txt`. -/
theorem gap5 : Filter.Tendsto f Filter.atTop (nhds 2) := by
  exact gap4

end

end ProofGap.Exercise598_2
