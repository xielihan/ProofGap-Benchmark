import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise920

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arccos (1 / x)

def expandedDerivative (x : ℝ) : ℝ :=
  (-1 / Real.sqrt (1 - (1 / x) ^ 2)) * (-1 / x ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / (|x| * Real.sqrt (x ^ 2 - 1))

/-- Source: `proof_gap/exercise_920/1.txt`; `|x| > 1` puts `1/x` strictly
inside the arccosine domain and excludes the reciprocal pole. -/
theorem gap1 (x : ℝ) (hx : 1 < |x|) :
    HasDerivAt y (expandedDerivative x) x := by
  have habspos : 0 < |x| := lt_trans zero_lt_one hx
  have hx0 : x ≠ 0 := abs_pos.mp habspos
  have huabs : |1 / x| < 1 := by
    rw [abs_div, abs_one]
    exact (div_lt_one habspos).2 hx
  have hu_bounds : (-1 : ℝ) < 1 / x ∧ 1 / x < 1 := abs_lt.mp huabs
  have hprod :
      0 < (1 - 1 / x) * (1 + 1 / x) :=
    mul_pos (sub_pos.mpr hu_bounds.2) (by linarith [hu_bounds.1])
  have harg : 0 < 1 - (1 / x) ^ 2 := by
    nlinarith [hprod]
  have hsqrt0 : Real.sqrt (1 - (1 / x) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg)
  have hlocal :
      (fun z : ℝ => Real.sin (Real.arcsin z)) =ᶠ[nhds (1 / x)]
        (fun z : ℝ => z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu_bounds] with z hz
    exact Real.sin_arcsin (le_of_lt hz.1) (le_of_lt hz.2)
  have hsin :
      HasDerivAt Real.sin (Real.sqrt (1 - (1 / x) ^ 2))
        (Real.arcsin (1 / x)) := by
    simpa only [Real.cos_arcsin] using
      Real.hasDerivAt_sin (Real.arcsin (1 / x))
  have harcsin_base :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - (1 / x) ^ 2)) (1 / x) := by
    have h := hsin.of_local_left_inverse
      Real.continuous_arcsin.continuousAt hsqrt0
      (by simpa only [Function.comp_apply, id_eq] using hlocal)
    simpa only [one_div] using h
  have hrecip :
      HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
    simpa [one_div] using (hasDerivAt_id x).inv hx0
  have harcsin :
      HasDerivAt (fun t : ℝ => Real.arcsin (1 / t))
        ((1 / Real.sqrt (1 - (1 / x) ^ 2)) * (-1 / x ^ 2)) x := by
    exact harcsin_base.comp x hrecip
  have hcoef :
      -((1 / Real.sqrt (1 - (1 / x) ^ 2)) * (-1 / x ^ 2)) =
        expandedDerivative x := by
    unfold expandedDerivative
    ring
  simpa only [y, Real.arccos_eq_pi_div_two_sub_arcsin, hcoef] using
    harcsin.const_sub (Real.pi / 2)

/-- Source: `proof_gap/exercise_920/2.txt`; the absolute value is retained
when extracting `sqrt (x^2)` on both components of the domain. -/
theorem gap2 (x : ℝ) (hx : 1 < |x|) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have habspos : 0 < |x| := lt_trans zero_lt_one hx
  have hx0 : x ≠ 0 := abs_pos.mp habspos
  have hxsq : 1 < x ^ 2 := by
    calc
      1 < |x| ^ 2 := by
        nlinarith [sq_nonneg (|x| - 1)]
      _ = x ^ 2 := sq_abs x
  have hx2pos : 0 < x ^ 2 := lt_trans zero_lt_one hxsq
  have harg_eq :
      1 - (1 / x) ^ 2 = (x ^ 2 - 1) / x ^ 2 := by
    field_simp [hx0]
  have harg : 0 < 1 - (1 / x) ^ 2 := by
    rw [harg_eq]
    exact div_pos (sub_pos.mpr hxsq) hx2pos
  have hdiff : 0 < x ^ 2 - 1 := sub_pos.mpr hxsq
  have hApos : 0 < Real.sqrt (1 - (1 / x) ^ 2) :=
    Real.sqrt_pos.2 harg
  have hBpos : 0 < Real.sqrt (x ^ 2 - 1) :=
    Real.sqrt_pos.2 hdiff
  have hA2 :
      Real.sqrt (1 - (1 / x) ^ 2) ^ 2 = 1 - (1 / x) ^ 2 :=
    Real.sq_sqrt (le_of_lt harg)
  have hB2 :
      Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hdiff)
  have hrel :
      (1 - (1 / x) ^ 2) * x ^ 2 = x ^ 2 - 1 := by
    rw [harg_eq]
    field_simp [hx0]
  have hsquares :
      (Real.sqrt (1 - (1 / x) ^ 2) * |x|) ^ 2 =
        Real.sqrt (x ^ 2 - 1) ^ 2 := by
    calc
      (Real.sqrt (1 - (1 / x) ^ 2) * |x|) ^ 2 =
          Real.sqrt (1 - (1 / x) ^ 2) ^ 2 * |x| ^ 2 := by ring
      _ = (1 - (1 / x) ^ 2) * x ^ 2 := by rw [hA2, sq_abs x]
      _ = x ^ 2 - 1 := hrel
      _ = Real.sqrt (x ^ 2 - 1) ^ 2 := hB2.symm
  have hAzB :
      Real.sqrt (1 - (1 / x) ^ 2) * |x| =
        Real.sqrt (x ^ 2 - 1) := by
    have hleft :
        0 ≤ Real.sqrt (1 - (1 / x) ^ 2) * |x| :=
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have hright : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
    nlinarith [hsquares]
  have hden :
      Real.sqrt (1 - (1 / x) ^ 2) * x ^ 2 =
        |x| * Real.sqrt (x ^ 2 - 1) := by
    calc
      Real.sqrt (1 - (1 / x) ^ 2) * x ^ 2 =
          Real.sqrt (1 - (1 / x) ^ 2) * |x| ^ 2 := by rw [sq_abs x]
      _ = |x| * (Real.sqrt (1 - (1 / x) ^ 2) * |x|) := by ring
      _ = |x| * Real.sqrt (x ^ 2 - 1) := by rw [hAzB]
  have hA0 : Real.sqrt (1 - (1 / x) ^ 2) ≠ 0 := ne_of_gt hApos
  calc
    (-1 / Real.sqrt (1 - (1 / x) ^ 2)) * (-1 / x ^ 2) =
        1 / (Real.sqrt (1 - (1 / x) ^ 2) * x ^ 2) := by
      field_simp [hA0, hx0]
    _ = 1 / (|x| * Real.sqrt (x ^ 2 - 1)) := by rw [hden]

/-- Source: `proof_gap/exercise_920/3.txt`; retain the two real branches
`x < -1` and `x > 1`. -/
theorem gap3 (x : ℝ) (hx : 1 < |x|) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise920
