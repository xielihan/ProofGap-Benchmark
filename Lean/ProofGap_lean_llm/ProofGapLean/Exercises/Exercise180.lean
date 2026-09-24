import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

namespace ProofGap.Exercise180

noncomputable section

def arccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x
def y (x : ℝ) : ℝ := arccot x / Real.pi
def valueSet : Set ℝ := Set.range y

/-- Source: `proof_gap/exercise_180/1.txt`. -/
theorem gap1 : Continuous y := by
  unfold y arccot
  exact (continuous_const.sub Real.continuous_arctan).div_const _

/-- Source: `proof_gap/exercise_180/2.txt`. -/
theorem gap2 : StrictAnti y := by
  intro a b hab
  unfold y arccot
  apply (div_lt_div_iff_of_pos_right Real.pi_pos).2
  have h := Real.arctan_strictMono hab
  linarith

/-- Source: `proof_gap/exercise_180/3.txt`. -/
theorem gap3 : Tendsto arccot atBot (𝓝 Real.pi) := by
  have hatan : Tendsto Real.arctan atBot (𝓝 (-(Real.pi / 2))) :=
    Real.tendsto_arctan_atBot.mono_right inf_le_left
  unfold arccot
  convert tendsto_const_nhds.sub hatan using 1 <;> ring

/-- Source: `proof_gap/exercise_180/4.txt`. -/
theorem gap4 : Tendsto y atBot (𝓝 1) := by
  unfold y
  convert gap3.div_const Real.pi using 1
  field_simp [Real.pi_ne_zero]

/-- Source: `proof_gap/exercise_180/5.txt`. -/
theorem gap5 : Tendsto arccot atTop (𝓝 0) := by
  have hatan : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  unfold arccot
  convert tendsto_const_nhds.sub hatan using 1 <;> ring

/-- Source: `proof_gap/exercise_180/6.txt`. -/
theorem gap6 : Tendsto y atTop (𝓝 0) := by
  unfold y
  simpa using gap5.div_const Real.pi

/-- Source: `proof_gap/exercise_180/7.txt`; replace the free family `E_x`. -/
theorem gap7 : valueSet = Set.Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    have hatan := Real.arctan_mem_Ioo x
    unfold y arccot
    constructor
    · apply (div_pos_iff).2
      apply Or.inl
      constructor
      · ring_nf at hatan ⊢
        linarith [hatan.2]
      · exact Real.pi_pos
    · apply (div_lt_iff₀ Real.pi_pos).2
      ring_nf at hatan ⊢
      linarith [hatan.1]
  · rintro ⟨ht0, ht1⟩
    let u : ℝ := Real.pi / 2 - Real.pi * t
    have hulo : -(Real.pi / 2) < u := by
      dsimp [u]
      nlinarith [Real.pi_pos]
    have huhi : u < Real.pi / 2 := by
      dsimp [u]
      nlinarith [Real.pi_pos]
    refine ⟨Real.tan u, ?_⟩
    unfold y arccot
    rw [Real.arctan_tan hulo huhi]
    dsimp [u]
    field_simp [Real.pi_ne_zero]
    ring

end

end ProofGap.Exercise180
