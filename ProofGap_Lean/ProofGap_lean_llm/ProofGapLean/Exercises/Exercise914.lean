import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise914

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arccos ((1 - x) / Real.sqrt 2)

def expandedDerivative (x : ℝ) : ℝ :=
  (-1 / Real.sqrt (1 - ((1 - x) / Real.sqrt 2) ^ 2)) *
    (-1 / Real.sqrt 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 + 2 * x - x ^ 2)

/-- Exercise 914, gap 1; the hypothesis places the
arccosine argument strictly between `-1` and `1`. -/
theorem gap1 (x : ℝ) (hx : (1 - x) ^ 2 < 2) :
    HasDerivAt y (expandedDerivative x) x := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have harg : (1 - x) / Real.sqrt 2 ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · rw [lt_div_iff₀ hs]
      nlinarith
    · rw [div_lt_iff₀ hs]
      nlinarith
  have hinner :
      HasDerivAt (fun z : ℝ => (1 - z) / Real.sqrt 2)
        (-1 / Real.sqrt 2) x := by
    simpa using
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).div_const
        (Real.sqrt 2))
  have houter :
      HasDerivAt Real.arccos
        (-(1 / Real.sqrt (1 - ((1 - x) / Real.sqrt 2) ^ 2)))
        ((1 - x) / Real.sqrt 2) :=
    Real.hasDerivAt_arccos (ne_of_gt harg.1) (ne_of_lt harg.2)
  simpa [y, expandedDerivative, Function.comp_def, neg_div, one_div] using
    houter.comp x hinner

/-- Exercise 914, gap 2; the same strict inequality makes
the simplified radicand positive. -/
theorem gap2 (x : ℝ) (hx : (1 - x) ^ 2 < 2) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrad :
      (1 - ((1 - x) / Real.sqrt 2) ^ 2) * 2 =
        1 + 2 * x - x ^ 2 := by
    rw [div_pow, hs2]
    ring
  have hB : 0 < 1 + 2 * x - x ^ 2 := by
    nlinarith [hx]
  have hA : 0 < 1 - ((1 - x) / Real.sqrt 2) ^ 2 := by
    nlinarith [hrad, hB]
  have hprod_sq :
      (Real.sqrt (1 - ((1 - x) / Real.sqrt 2) ^ 2) * Real.sqrt 2) ^ 2 =
        (Real.sqrt (1 + 2 * x - x ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hA), hs2,
      Real.sq_sqrt (le_of_lt hB)]
    exact hrad
  have hprod :
      Real.sqrt (1 - ((1 - x) / Real.sqrt 2) ^ 2) * Real.sqrt 2 =
        Real.sqrt (1 + 2 * x - x ^ 2) := by
    have hp :
        0 ≤ Real.sqrt (1 - ((1 - x) / Real.sqrt 2) ^ 2) * Real.sqrt 2 :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hb : 0 ≤ Real.sqrt (1 + 2 * x - x ^ 2) := Real.sqrt_nonneg _
    nlinarith [hprod_sq]
  rw [← hprod]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hA), ne_of_gt hs]

/-- Exercise 914, gap 3; retain the nonsingular arccosine
domain. -/
theorem gap3 (x : ℝ) (hx : (1 - x) ^ 2 < 2) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise914
