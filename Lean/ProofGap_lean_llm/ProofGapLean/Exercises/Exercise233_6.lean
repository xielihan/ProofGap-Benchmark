import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise233_6

noncomputable section

def f (x : ℝ) : ℝ := Real.sqrt (Real.tan x)

def IsLeastPositivePeriod (g : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ Function.Periodic g T ∧
    ∀ T', 0 < T' → Function.Periodic g T' → T ≤ T'

/-- Source: `proof_gap/exercise_233_6/1.txt`. -/
theorem gap1 : Function.Periodic f Real.pi := by
  intro x
  unfold f
  rw [Real.tan_add_pi]

/-- Source: `proof_gap/exercise_233_6/2.txt`; represent `min` by the least-positive-period predicate. -/
theorem gap2 : IsLeastPositivePeriod f Real.pi := by
  refine ⟨Real.pi_pos, gap1, ?_⟩
  intro T hT hper
  by_contra hnot
  have hTpi : T < Real.pi := lt_of_not_ge hnot
  let x : ℝ := Real.pi / 2 - T / 2
  have hx_pos : 0 < x := by
    dsimp [x]
    linarith
  have hx_lt : x < Real.pi / 2 := by
    dsimp [x]
    linarith
  have hsinx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx_pos (by linarith [Real.pi_pos])
  have hcosx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx_lt⟩
  have htanx : 0 < Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    positivity
  have hfx : 0 < f x := by
    unfold f
    exact Real.sqrt_pos.2 htanx
  have hsum : x + T = Real.pi / 2 + T / 2 := by
    dsimp [x]
    ring
  have hy_lt_pi : Real.pi / 2 + T / 2 < Real.pi := by
    linarith
  have hsiny : 0 < Real.sin (Real.pi / 2 + T / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hy_lt_pi
  have hcosy : Real.cos (Real.pi / 2 + T / 2) < 0 := by
    rw [Real.cos_add]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [zero_mul, one_mul, zero_sub]
    exact neg_lt_zero.mpr (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have htany : Real.tan (Real.pi / 2 + T / 2) < 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_neg_of_pos_of_neg hsiny hcosy
  have hfy : f (x + T) = 0 := by
    rw [hsum]
    unfold f
    exact Real.sqrt_eq_zero_of_nonpos (le_of_lt htany)
  have heq : f (x + T) = f x := hper x
  linarith

end

end ProofGap.Exercise233_6
