import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise413

noncomputable section

def original (x : ℝ) : ℝ :=
  ((1 + x) ^ 5 - (1 + 5 * x)) / (x ^ 2 + x ^ 5)
def expanded (x : ℝ) : ℝ :=
  (x ^ 5 + 5 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2) /
    (x ^ 2 + x ^ 5)
def cancelled (x : ℝ) : ℝ :=
  (x ^ 3 + 5 * x ^ 2 + 10 * x + 10) / (x ^ 3 + 1)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 413, gap 1. -/
theorem gap1 : HasLimitAt original 0 10 ↔ HasLimitAt expanded 0 10 := by
  have h : original = expanded := by
    funext x
    unfold original expanded
    congr 1
    ring
  rw [h]

/-- Exercise 413, gap 2. -/
theorem gap2 : HasLimitAt expanded 0 10 ↔ HasLimitAt cancelled 0 10 := by
  have h_eq :
      expanded =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa using hx
    unfold expanded cancelled
    field_simp [hx0]
    <;> ring
  constructor
  · intro h
    exact h.congr' h_eq
  · intro h
    exact h.congr' h_eq.symm

/-- Exercise 413, gap 3. -/
theorem gap3 : HasLimitAt cancelled 0 10 := by
  unfold HasLimitAt
  have hcont : ContinuousAt cancelled 0 := by
    unfold cancelled
    refine ContinuousAt.div₀ ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · norm_num
  simpa [cancelled] using hcont.tendsto.mono_left inf_le_left

/-- Exercise 413, gap 4. -/
theorem gap4 : HasLimitAt original 0 10 := by
  rw [gap1, gap2]
  exact gap3

end

end ProofGap.Exercise413
