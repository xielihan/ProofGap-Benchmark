import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise840

noncomputable section

def y (α x : ℝ) : ℝ :=
  (x * Real.sin α + Real.cos α) *
    (x * Real.cos α - Real.sin α)

def stationarySet (α : ℝ) : Set ℝ := {x | deriv (y α) x = 0}

/-- Exercise 840, gap 1; the source's biconditional equated
`y'=0` with `y'=formula`; state the intended derivative formula. -/
theorem gap1 (α x : ℝ) :
    HasDerivAt (y α)
      (Real.sin α * (x * Real.cos α - Real.sin α) +
        Real.cos α * (x * Real.sin α + Real.cos α)) x := by
  unfold y
  convert
    ((((hasDerivAt_id x).mul_const (Real.sin α)).add_const (Real.cos α)).mul
      (((hasDerivAt_id x).mul_const (Real.cos α)).sub_const (Real.sin α))) using 1 <;>
    simp only [id_eq] <;> ring

/-- Exercise 840, gap 2; remove the malformed stationary
biconditional and retain the trigonometric simplification. -/
theorem gap2 (α x : ℝ) :
    Real.sin α * (x * Real.cos α - Real.sin α) +
        Real.cos α * (x * Real.sin α + Real.cos α) =
      x * Real.sin (2 * α) + Real.cos (2 * α) := by
  have hs := Real.sin_add α α
  have hc := Real.cos_add α α
  rw [← two_mul α] at hs hc
  rw [hs, hc]
  ring

/-- Exercise 840, gap 3; state the simplified derivative
formula. -/
theorem gap3 (α x : ℝ) :
    HasDerivAt (y α) (x * Real.sin (2 * α) + Real.cos (2 * α)) x := by
  simpa only [gap2 α x] using gap1 α x

/-- Exercise 840, gap 4. -/
theorem gap4 (α x : ℝ) (hstat : deriv (y α) x = 0) :
    x * Real.sin (2 * α) + Real.cos (2 * α) = 0 := by
  rw [(gap3 α x).deriv] at hstat
  exact hstat

/-- Exercise 840, gap 5; add the stationary equation. -/
theorem gap5 (α x : ℝ) (hs : Real.sin (2 * α) ≠ 0)
    (hstat : x * Real.sin (2 * α) + Real.cos (2 * α) = 0) :
    x = -Real.cos (2 * α) / Real.sin (2 * α) := by
  apply (eq_div_iff hs).2
  linarith

/-- Exercise 840, gap 6. -/
theorem gap6 (α : ℝ) (hs : Real.sin (2 * α) ≠ 0) :
    -Real.cos (2 * α) / Real.sin (2 * α) = -Real.cot (2 * α) := by
  rw [Real.cot_eq_cos_div_sin]
  ring

/-- Exercise 840, gap 7. -/
theorem gap7 (α x : ℝ) (hs : Real.sin (2 * α) ≠ 0)
    (hstat : x * Real.sin (2 * α) + Real.cos (2 * α) = 0) :
    x = -Real.cot (2 * α) := by
  calc
    x = -Real.cos (2 * α) / Real.sin (2 * α) := gap5 α x hs hstat
    _ = -Real.cot (2 * α) := gap6 α hs

/-- Exercise 840, gap 8; replace `±1` by a disjunction. -/
theorem gap8 (α : ℝ) (hs : Real.sin (2 * α) = 0) :
    Real.cos (2 * α) = 1 ∨ Real.cos (2 * α) = -1 := by
  have hc : Real.cos (2 * α) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * α)]
  have hfactor :
      (Real.cos (2 * α) - 1) * (Real.cos (2 * α) + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    linarith
  · right
    linarith

/-- Exercise 840, gap 9; the literal claim `±1=0` is
false; state the intended contradiction with the stationary equation. -/
theorem gap9 (α x : ℝ) (hs : Real.sin (2 * α) = 0)
    (hstat : x * Real.sin (2 * α) + Real.cos (2 * α) = 0) :
    False := by
  have hc : Real.cos (2 * α) = 0 := by
    simpa [hs] using hstat
  rcases gap8 α hs with h | h <;> linarith

/-- Exercise 840, gap 10; retain the stationary premise
whose contradiction is intended. -/
theorem gap10 (α x : ℝ) (hs : Real.sin (2 * α) = 0) :
    deriv (y α) x = 0 → False := by
  intro hstat
  exact gap9 α x hs (gap4 α x hstat)

/-- Exercise 840, gap 11; make the conditional singleton
set explicit. -/
theorem gap11 (α : ℝ) :
    stationarySet α =
      if Real.sin (2 * α) = 0 then ∅ else {-Real.cot (2 * α)} := by
  ext x
  change (deriv (y α) x = 0) ↔
    x ∈ (if Real.sin (2 * α) = 0 then ∅ else {-Real.cot (2 * α)})
  by_cases hs : Real.sin (2 * α) = 0
  · simpa [hs] using (gap10 α x hs)
  · rw [if_neg hs]
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hstat
      exact gap7 α x hs (gap4 α x hstat)
    · intro hx
      rw [(gap3 α x).deriv, hx, ← gap6 α hs]
      field_simp [hs] <;> ring

end

end ProofGap.Exercise840
