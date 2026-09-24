import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace ProofGap.Exercise653_1

def p (x : ℝ) : ℝ := 2 * x - 3 * x ^ 3 + x ^ 5

/-- Source: `proof_gap/exercise_653_1/1.txt`. -/
theorem gap1 :
    Filter.Tendsto (fun x : ℝ => p x / (2 * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hlim :
      Filter.Tendsto
        (fun x : ℝ => 1 - (3 / 2 : ℝ) * x ^ 2 + (1 / 2 : ℝ) * x ^ 4)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hcont :
        ContinuousAt
          (fun x : ℝ => 1 - (3 / 2 : ℝ) * x ^ 2 + (1 / 2 : ℝ) * x ^ 4) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  unfold p
  field_simp [hx0]

/-- Source: `proof_gap/exercise_653_1/2.txt`. -/
theorem gap2 :
    Asymptotics.IsEquivalent (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      p (fun x : ℝ => 2 * x) := by
  have hne :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 2 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) hx0
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).2 gap1

/-- Source: `proof_gap/exercise_653_1/3.txt`; unpack the singleton pair. -/
theorem gap3 (C : ℝ) (n : ℕ) (h : (C, n) = (2, 1)) :
    Asymptotics.IsEquivalent (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      p (fun x => C * x ^ n) := by
  have hC : C = 2 := congrArg Prod.fst h
  have hn : n = 1 := congrArg Prod.snd h
  subst C
  subst n
  simpa using gap2

end ProofGap.Exercise653_1
