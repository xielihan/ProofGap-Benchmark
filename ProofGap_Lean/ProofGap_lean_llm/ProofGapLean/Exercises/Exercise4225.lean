import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4225

noncomputable section

open scoped Interval

def astroid (a : ℝ) : Set (ℝ × ℝ) :=
  {p |
    Real.rpow |p.1| (2 / 3 : ℝ) + Real.rpow |p.2| (2 / 3 : ℝ) =
      Real.rpow a (2 / 3 : ℝ)}

def firstQuadrantCurve (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ astroid a ∧ 0 ≤ p.1 ∧ 0 ≤ p.2}

def upperBranch (a x : ℝ) : ℝ :=
  Real.rpow
    (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
    (3 / 2 : ℝ)

def weight (x y : ℝ) : ℝ :=
  Real.rpow |x| (4 / 3 : ℝ) + Real.rpow |y| (4 / 3 : ℝ)

def cartesianSpeed (a x : ℝ) : ℝ :=
  Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ)

def curveMap (a t : ℝ) : ℝ × ℝ :=
  (a * Real.cos t ^ 3, a * Real.sin t ^ 3)

def quarterImage (a : ℝ) : Set (ℝ × ℝ) :=
  curveMap a '' Set.Icc 0 (Real.pi / 2)

def rawParamSpeed (a t : ℝ) : ℝ :=
  Real.sqrt
    (9 * a ^ 2 * Real.cos t ^ 4 * Real.sin t ^ 2 +
      9 * a ^ 2 * Real.sin t ^ 4 * Real.cos t ^ 2)

def paramSpeed (a t : ℝ) : ℝ :=
  3 * a * Real.cos t * Real.sin t

def weightedLength (a : ℝ) : ℝ :=
  4 *
    ∫ x in (0 : ℝ)..a,
      weight x (upperBranch a x) * cartesianSpeed a x

private theorem trigWeightedIntegral (a : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi / 2,
      (Real.cos t ^ 4 + Real.sin t ^ 4) *
        (3 * a * Real.cos t * Real.sin t)) = a := by
  let F : ℝ → ℝ := fun t => (a / 2) * (Real.sin t ^ 6 - Real.cos t ^ 6)
  have hd : ∀ t : ℝ, HasDerivAt F
      ((Real.cos t ^ 4 + Real.sin t ^ 4) *
        (3 * a * Real.cos t * Real.sin t)) t := by
    intro t
    dsimp [F]
    convert (((Real.hasDerivAt_sin t).pow 6).sub
      ((Real.hasDerivAt_cos t).pow 6)).const_mul (a / 2) using 1 <;> ring
  have hc : Continuous
      (fun t : ℝ => (Real.cos t ^ 4 + Real.sin t ^ 4) *
        (3 * a * Real.cos t * Real.sin t)) := by
    have hc1 : Continuous (fun t : ℝ => Real.cos t ^ 4 + Real.sin t ^ 4) :=
      (Real.continuous_cos.pow 4).add (Real.continuous_sin.pow 4)
    have hc2 : Continuous (fun t : ℝ => 3 * a * Real.cos t * Real.sin t) :=
      (continuous_const.mul Real.continuous_cos).mul Real.continuous_sin
    exact hc1.mul hc2
  have hi : IntervalIntegrable
      (fun t : ℝ => (Real.cos t ^ 4 + Real.sin t ^ 4) *
        (3 * a * Real.cos t * Real.sin t)) MeasureTheory.volume 0 (Real.pi / 2) := by
    exact hc.intervalIntegrable 0 (Real.pi / 2)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) hi
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2,
      (Real.cos t ^ 4 + Real.sin t ^ 4) *
        (3 * a * Real.cos t * Real.sin t)) = F (Real.pi / 2) - F 0 := heq
    _ = a := by simp [F]

private theorem sinFiveCosIntegral :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 5 * Real.cos t) = (1 / 6 : ℝ) := by
  let F : ℝ → ℝ := fun t => Real.sin t ^ 6 / 6
  have hd : ∀ t : ℝ, HasDerivAt F (Real.sin t ^ 5 * Real.cos t) t := by
    intro t
    dsimp [F]
    convert ((Real.hasDerivAt_sin t).pow 6).div_const 6 using 1 <;> ring
  have hc : Continuous (fun t : ℝ => Real.sin t ^ 5 * Real.cos t) :=
    (Real.continuous_sin.pow 5).mul Real.continuous_cos
  have hi : IntervalIntegrable (fun t : ℝ => Real.sin t ^ 5 * Real.cos t)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    exact hc.intervalIntegrable 0 (Real.pi / 2)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) hi
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 5 * Real.cos t) =
        F (Real.pi / 2) - F 0 := heq
    _ = (1 / 6 : ℝ) := by norm_num [F]

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    cartesianSpeed a x =
      Real.sqrt (1 + deriv (upperBranch a) x ^ 2) := by
  unfold cartesianSpeed
  have hu : 0 < Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ) := by
    apply sub_pos.mpr
    exact Real.rpow_lt_rpow (le_of_lt hx) hxa (by norm_num)
  have hxder := Real.hasDerivAt_rpow_const (p := (2 / 3 : ℝ)) (Or.inl (ne_of_gt hx))
  have huder := (hasDerivAt_const x (Real.rpow a (2 / 3 : ℝ))).sub hxder
  have houter := Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl (ne_of_gt hu))
  have hcomp := houter.comp x huder
  have hbranch : HasDerivAt (upperBranch a)
      (3 / 2 * Real.rpow
          (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
          (3 / 2 - 1 : ℝ) *
        (0 - 2 / 3 * Real.rpow x (2 / 3 - 1 : ℝ))) x := by
    simpa [upperBranch, Function.comp_def] using hcomp
  rw [hbranch.deriv]
  have ha13 : 0 < Real.rpow a (1 / 3 : ℝ) := Real.rpow_pos_of_pos ha _
  have hx13 : 0 < Real.rpow x (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx _
  have ha_sq : Real.rpow a (2 / 3 : ℝ) = Real.rpow a (1 / 3 : ℝ) ^ 2 := by
    calc
      Real.rpow a (2 / 3 : ℝ) = Real.rpow a (1 / 3 + 1 / 3 : ℝ) := by norm_num
      _ = Real.rpow a (1 / 3 : ℝ) * Real.rpow a (1 / 3 : ℝ) := Real.rpow_add ha _ _
      _ = Real.rpow a (1 / 3 : ℝ) ^ 2 := by ring
  have hx_sq : Real.rpow x (2 / 3 : ℝ) = Real.rpow x (1 / 3 : ℝ) ^ 2 := by
    calc
      Real.rpow x (2 / 3 : ℝ) = Real.rpow x (1 / 3 + 1 / 3 : ℝ) := by norm_num
      _ = Real.rpow x (1 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ) := Real.rpow_add hx _ _
      _ = Real.rpow x (1 / 3 : ℝ) ^ 2 := by ring
  have hroot_sq :
      Real.rpow (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) (1 / 2 : ℝ) ^ 2 =
        Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ) := by
    calc
      Real.rpow (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) (1 / 2 : ℝ) ^ 2 =
          Real.rpow (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) (1 / 2 : ℝ) *
            Real.rpow (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) (1 / 2 : ℝ) := by ring
      _ = Real.rpow (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) (1 / 2 + 1 / 2 : ℝ) :=
        (Real.rpow_add hu _ _).symm
      _ = Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ) := by norm_num
  have hxneg : Real.rpow x (-(1 / 3 : ℝ)) = (Real.rpow x (1 / 3 : ℝ))⁻¹ := by
    have hdiv : Real.rpow x (-(1 / 3 : ℝ)) = 1 / Real.rpow x (1 / 3 : ℝ) := by
      apply (eq_div_iff (ne_of_gt hx13)).2
      calc
        Real.rpow x (-(1 / 3 : ℝ)) * Real.rpow x (1 / 3 : ℝ) =
            Real.rpow x (-(1 / 3) + 1 / 3 : ℝ) := (Real.rpow_add hx _ _).symm
        _ = 1 := by norm_num
    simpa [one_div] using hdiv
  norm_num only at hbranch ⊢
  rw [hxneg]
  have hsq :
      (Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ)) ^ 2 =
        1 +
          (3 / 2 *
              Real.rpow
                (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
                (1 / 2 : ℝ) *
            (0 - 2 / 3 * (Real.rpow x (1 / 3 : ℝ))⁻¹)) ^ 2 := by
    field_simp [ne_of_gt hx13]
    nlinarith [ha_sq, hx_sq, hroot_sq]
  have hsqrt_sq :
      (Real.sqrt
          (1 +
            (3 / 2 *
                Real.rpow
                  (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
                  (1 / 2 : ℝ) *
              (0 - 2 / 3 * (Real.rpow x (1 / 3 : ℝ))⁻¹)) ^ 2)) ^ 2 =
        1 +
          (3 / 2 *
              Real.rpow
                (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
                (1 / 2 : ℝ) *
            (0 - 2 / 3 * (Real.rpow x (1 / 3 : ℝ))⁻¹)) ^ 2 := by
    apply Real.sq_sqrt
    positivity
  have hquot_nonneg :
      0 ≤ Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ) := by positivity
  nlinarith [Real.sqrt_nonneg
    (1 +
      (3 / 2 *
          Real.rpow
            (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
            (1 / 2 : ℝ) *
        (0 - 2 / 3 * (Real.rpow x (1 / 3 : ℝ))⁻¹)) ^ 2)]

theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    Real.sqrt (1 + deriv (upperBranch a) x ^ 2) =
      Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ) := by
  calc
    Real.sqrt (1 + deriv (upperBranch a) x ^ 2) = cartesianSpeed a x :=
      (gap1 a x ha hx hxa).symm
    _ = Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ) := rfl

theorem gap3 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    cartesianSpeed a x =
      Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ) := by
  rfl

theorem gap4 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      4 *
        ∫ x in (0 : ℝ)..a,
          (Real.rpow x (4 / 3 : ℝ) +
              (Real.rpow a (2 / 3 : ℝ) -
                Real.rpow x (2 / 3 : ℝ)) ^ 2) *
            (Real.rpow a (1 / 3 : ℝ) /
              Real.rpow x (1 / 3 : ℝ)) := by
  unfold weightedLength
  congr 1
  apply intervalIntegral.integral_congr
  intro x hxI
  have hxI' : x ∈ Set.Icc (0 : ℝ) a := by
    simpa [Set.uIcc_of_le (le_of_lt ha)] using hxI
  have hx0 : 0 ≤ x := hxI'.1
  have hxa : x ≤ a := hxI'.2
  have hinner : 0 ≤ Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ) := by
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow hx0 hxa (by norm_num)
  have hu_nonneg : 0 ≤ upperBranch a x := Real.rpow_nonneg hinner _
  have hu_pow : Real.rpow (upperBranch a x) (4 / 3 : ℝ) =
      (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) ^ 2 := by
    unfold upperBranch
    calc
      Real.rpow
          (Real.rpow
            (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
            (3 / 2 : ℝ))
          (4 / 3 : ℝ) =
          Real.rpow
            (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
            ((3 / 2 : ℝ) * (4 / 3 : ℝ)) :=
        (Real.rpow_mul hinner (3 / 2 : ℝ) (4 / 3 : ℝ)).symm
      _ = Real.rpow
          (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ))
          (2 : ℝ) := by norm_num
      _ = (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) ^ 2 := by
        simpa using Real.rpow_natCast
          (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) 2
  change
    (Real.rpow |x| (4 / 3 : ℝ) + Real.rpow |upperBranch a x| (4 / 3 : ℝ)) *
        (Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ)) = _
  rw [abs_of_nonneg hx0, abs_of_nonneg hu_nonneg, hu_pow]

theorem gap5 (a : ℝ) (ha : 0 < a) :
    4 *
        (∫ x in (0 : ℝ)..a,
          (Real.rpow x (4 / 3 : ℝ) +
              (Real.rpow a (2 / 3 : ℝ) -
                Real.rpow x (2 / 3 : ℝ)) ^ 2) *
            (Real.rpow a (1 / 3 : ℝ) /
              Real.rpow x (1 / 3 : ℝ))) =
      4 * Real.rpow a (1 / 3 : ℝ) *
        ∫ x in (0 : ℝ)..a,
          2 * x + Real.rpow a (4 / 3 : ℝ) *
              Real.rpow x (-1 / 3 : ℝ) -
            2 * Real.rpow a (2 / 3 : ℝ) *
              Real.rpow x (1 / 3 : ℝ) := by
  have hint :
      (∫ x in (0 : ℝ)..a,
        (Real.rpow x (4 / 3 : ℝ) +
            (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) ^ 2) *
          (Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ))) =
        ∫ x in (0 : ℝ)..a,
          Real.rpow a (1 / 3 : ℝ) *
            (2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
              2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hxI
    have hxI' : x ∈ Set.Icc (0 : ℝ) a := by
      simpa [Set.uIcc_of_le (le_of_lt ha)] using hxI
    have hx0 : 0 ≤ x := hxI'.1
    change
      (Real.rpow x (4 / 3 : ℝ) +
          (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) ^ 2) *
        (Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ)) =
      Real.rpow a (1 / 3 : ℝ) *
        (2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
          2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ))
    rcases hx0.eq_or_lt with rfl | hx
    · simp
    · have hxx13 : 0 < Real.rpow x (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx _
      have ha23 : Real.rpow a (2 / 3 : ℝ) = Real.rpow a (1 / 3 : ℝ) ^ 2 := by
        calc
          Real.rpow a (2 / 3 : ℝ) = Real.rpow a (1 / 3 + 1 / 3 : ℝ) := by norm_num
          _ = Real.rpow a (1 / 3 : ℝ) * Real.rpow a (1 / 3 : ℝ) := Real.rpow_add ha _ _
          _ = Real.rpow a (1 / 3 : ℝ) ^ 2 := by ring
      have hx23 : Real.rpow x (2 / 3 : ℝ) = Real.rpow x (1 / 3 : ℝ) ^ 2 := by
        calc
          Real.rpow x (2 / 3 : ℝ) = Real.rpow x (1 / 3 + 1 / 3 : ℝ) := by norm_num
          _ = Real.rpow x (1 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ) := Real.rpow_add hx _ _
          _ = Real.rpow x (1 / 3 : ℝ) ^ 2 := by ring
      have ha43 : Real.rpow a (4 / 3 : ℝ) = Real.rpow a (1 / 3 : ℝ) ^ 4 := by
        calc
          Real.rpow a (4 / 3 : ℝ) = Real.rpow a (2 / 3 + 2 / 3 : ℝ) := by norm_num
          _ = Real.rpow a (2 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) := Real.rpow_add ha _ _
          _ = Real.rpow a (1 / 3 : ℝ) ^ 4 := by rw [ha23]; ring
      have hx43 : Real.rpow x (4 / 3 : ℝ) = Real.rpow x (1 / 3 : ℝ) ^ 4 := by
        calc
          Real.rpow x (4 / 3 : ℝ) = Real.rpow x (2 / 3 + 2 / 3 : ℝ) := by norm_num
          _ = Real.rpow x (2 / 3 : ℝ) * Real.rpow x (2 / 3 : ℝ) := Real.rpow_add hx _ _
          _ = Real.rpow x (1 / 3 : ℝ) ^ 4 := by rw [hx23]; ring
      have hxone : Real.rpow x (1 / 3 : ℝ) ^ 3 = x := by
        calc
          Real.rpow x (1 / 3 : ℝ) ^ 3 =
              Real.rpow x (1 / 3 : ℝ) * Real.rpow x (2 / 3 : ℝ) := by
                rw [hx23]
                ring
          _ = Real.rpow x (1 / 3 + 2 / 3 : ℝ) :=
            (Real.rpow_add hx _ _).symm
          _ = x := by norm_num
      have hxn13 : Real.rpow x (-(1 / 3 : ℝ)) = (Real.rpow x (1 / 3 : ℝ))⁻¹ := by
        have hdiv : Real.rpow x (-(1 / 3 : ℝ)) = 1 / Real.rpow x (1 / 3 : ℝ) := by
          apply (eq_div_iff (ne_of_gt hxx13)).2
          calc
            Real.rpow x (-(1 / 3 : ℝ)) * Real.rpow x (1 / 3 : ℝ) =
                Real.rpow x (-(1 / 3) + 1 / 3 : ℝ) := (Real.rpow_add hx _ _).symm
            _ = 1 := by norm_num
        simpa [one_div] using hdiv
      have hxn13' : Real.rpow x (-1 / 3 : ℝ) = (Real.rpow x (1 / 3 : ℝ))⁻¹ := by
        convert hxn13 using 1 <;> norm_num
      have htwo :
          (2 : ℝ) * x = 2 * Real.rpow x (1 / 3 : ℝ) ^ 3 :=
        congrArg (fun z : ℝ => 2 * z) hxone.symm
      rw [ha23, hx23, ha43, hx43, hxn13', htwo]
      field_simp [ne_of_gt hxx13]
      ring
  calc
    4 * (∫ x in (0 : ℝ)..a,
        (Real.rpow x (4 / 3 : ℝ) +
            (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) ^ 2) *
          (Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ))) =
        4 * (∫ x in (0 : ℝ)..a,
          Real.rpow a (1 / 3 : ℝ) *
            (2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
              2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ))) := by rw [hint]
    _ = 4 * Real.rpow a (1 / 3 : ℝ) *
        ∫ x in (0 : ℝ)..a,
          2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
            2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    4 * Real.rpow a (1 / 3 : ℝ) *
        (∫ x in (0 : ℝ)..a,
          2 * x + Real.rpow a (4 / 3 : ℝ) *
              Real.rpow x (-1 / 3 : ℝ) -
            2 * Real.rpow a (2 / 3 : ℝ) *
              Real.rpow x (1 / 3 : ℝ)) =
      4 * Real.rpow a (7 / 3 : ℝ) := by
  have hmInt : IntervalIntegrable (fun x : ℝ => Real.rpow x (-1 / 3 : ℝ))
      MeasureTheory.volume 0 a := by
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpInt : IntervalIntegrable (fun x : ℝ => Real.rpow x (1 / 3 : ℝ))
      MeasureTheory.volume 0 a := by
    exact intervalIntegral.intervalIntegrable_rpow (by norm_num)
  have hlin : IntervalIntegrable (fun x : ℝ => 2 * x)
      MeasureTheory.volume 0 a := by
    have hc : Continuous (fun x : ℝ => (2 : ℝ) * x) :=
      continuous_const.mul continuous_id
    exact hc.intervalIntegrable 0 a
  have hmval :
      (∫ x in (0 : ℝ)..a, Real.rpow x (-1 / 3 : ℝ)) =
        (3 / 2 : ℝ) * Real.rpow a (2 / 3 : ℝ) := by
    norm_num [integral_rpow, ha.le] <;> ring
  have hpval :
      (∫ x in (0 : ℝ)..a, Real.rpow x (1 / 3 : ℝ)) =
        (3 / 4 : ℝ) * Real.rpow a (4 / 3 : ℝ) := by
    norm_num [integral_rpow, ha.le] <;> ring
  have hlinval : (∫ x in (0 : ℝ)..a, 2 * x) = a ^ 2 := by
    let F : ℝ → ℝ := fun x => x ^ 2
    have hd : ∀ x : ℝ, HasDerivAt F (2 * x) x := by
      intro x
      simpa [F, Function.id_def, mul_comm] using (hasDerivAt_id x).pow 2
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) hlin
    calc
      (∫ x in (0 : ℝ)..a, 2 * x) = F a - F 0 := heq
      _ = a ^ 2 := by norm_num [F]
  have hprod :
      Real.rpow a (4 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) = a ^ 2 := by
    calc
      Real.rpow a (4 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) =
          Real.rpow a (4 / 3 + 2 / 3 : ℝ) := (Real.rpow_add ha _ _).symm
      _ = Real.rpow a (2 : ℝ) := by norm_num
      _ = a ^ 2 := by simpa using Real.rpow_natCast a 2
  have hInt :
      (∫ x in (0 : ℝ)..a,
        2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
          2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ)) = a ^ 2 := by
    calc
      (∫ x in (0 : ℝ)..a,
        2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
          2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ)) =
          (∫ x in (0 : ℝ)..a, 2 * x) +
            (∫ x in (0 : ℝ)..a,
              Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ)) -
            (∫ x in (0 : ℝ)..a,
              2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ)) := by
        rw [intervalIntegral.integral_sub
          (hlin.add (hmInt.const_mul (Real.rpow a (4 / 3 : ℝ))))
          (hpInt.const_mul (2 * Real.rpow a (2 / 3 : ℝ)))]
        rw [intervalIntegral.integral_add hlin
          (hmInt.const_mul (Real.rpow a (4 / 3 : ℝ)))]
      _ = a ^ 2 +
            Real.rpow a (4 / 3 : ℝ) *
              (∫ x in (0 : ℝ)..a, Real.rpow x (-1 / 3 : ℝ)) -
            (2 * Real.rpow a (2 / 3 : ℝ)) *
              (∫ x in (0 : ℝ)..a, Real.rpow x (1 / 3 : ℝ)) := by
        rw [hlinval, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ = a ^ 2 := by
        rw [hmval, hpval]
        nlinarith [hprod]
  have ha_sq : a ^ 2 = Real.rpow a (2 : ℝ) := by
    simpa using (Real.rpow_natCast a 2).symm
  have hpow : Real.rpow a (1 / 3 : ℝ) * a ^ 2 = Real.rpow a (7 / 3 : ℝ) := by
    rw [ha_sq]
    calc
      Real.rpow a (1 / 3 : ℝ) * Real.rpow a (2 : ℝ) =
          Real.rpow a (1 / 3 + 2 : ℝ) := (Real.rpow_add ha _ _).symm
      _ = Real.rpow a (7 / 3 : ℝ) := by norm_num
  calc
    4 * Real.rpow a (1 / 3 : ℝ) *
        (∫ x in (0 : ℝ)..a,
          2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
            2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ)) =
        4 * Real.rpow a (1 / 3 : ℝ) * a ^ 2 := by rw [hInt]
    _ = 4 * (Real.rpow a (1 / 3 : ℝ) * a ^ 2) := by ring
    _ = 4 * Real.rpow a (7 / 3 : ℝ) := by rw [hpow]

theorem gap7 (a : ℝ) (ha : 0 < a) :
    weightedLength a = 4 * Real.rpow a (7 / 3 : ℝ) := by
  calc
    weightedLength a =
        4 *
          ∫ x in (0 : ℝ)..a,
            (Real.rpow x (4 / 3 : ℝ) +
                (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) ^ 2) *
              (Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ)) := gap4 a ha
    _ = 4 * Real.rpow a (1 / 3 : ℝ) *
          ∫ x in (0 : ℝ)..a,
            2 * x + Real.rpow a (4 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) -
              2 * Real.rpow a (2 / 3 : ℝ) * Real.rpow x (1 / 3 : ℝ) := gap5 a ha
    _ = 4 * Real.rpow a (7 / 3 : ℝ) := gap6 a ha

theorem gap8 (a : ℝ) (ha : 0 < a) :
    firstQuadrantCurve a = quarterImage a := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [firstQuadrantCurve, quarterImage, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_Icc, curveMap]
  constructor
  · rintro ⟨hcurve, hx, hy⟩
    let A := Real.rpow a (2 / 3 : ℝ)
    let X := Real.rpow x (2 / 3 : ℝ)
    let Y := Real.rpow y (2 / 3 : ℝ)
    have hA : 0 < A := Real.rpow_pos_of_pos ha _
    have hX : 0 ≤ X := Real.rpow_nonneg hx _
    have hY : 0 ≤ Y := Real.rpow_nonneg hy _
    have hsum : X + Y = A := by
      simpa [astroid, abs_of_nonneg hx, abs_of_nonneg hy, A, X, Y] using hcurve
    let u := Real.sqrt (X / A)
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu1 : u ≤ 1 := by
      have hXA : X ≤ A := by nlinarith
      have hquot : X / A ≤ 1 := (div_le_one hA).2 hXA
      have hs : Real.sqrt (X / A) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hquot
      simpa [u] using hs
    refine ⟨Real.arccos u, ?_, ?_⟩
    · constructor
      · exact Real.arccos_nonneg u
      · simpa using Real.arccos_le_pi_div_two.mpr hu0
    · have hcos : Real.cos (Real.arccos u) = u := Real.cos_arccos (by linarith) (by linarith)
      have hsin0 : 0 ≤ Real.sin (Real.arccos u) := Real.sin_nonneg_of_nonneg_of_le_pi
        (Real.arccos_nonneg u) (Real.arccos_le_pi u)
      have hu_sq : u ^ 2 = X / A := by
        dsimp [u]
        rw [Real.sq_sqrt]
        exact div_nonneg hX hA.le
      have huA : A * u ^ 2 = X := by
        rw [hu_sq]
        field_simp [ne_of_gt hA]
      have hsin_sq : Real.sin (Real.arccos u) ^ 2 = Y / A := by
        have htrig := Real.sin_sq_add_cos_sq (Real.arccos u)
        rw [hcos] at htrig
        field_simp [ne_of_gt hA] at hu_sq ⊢
        nlinarith
      have hsA : A * Real.sin (Real.arccos u) ^ 2 = Y := by
        rw [hsin_sq]
        field_simp [ne_of_gt hA]
      have hA3 : A ^ 3 = a ^ 2 := by
        dsimp [A]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ha)]
        norm_num
      have hX3 : X ^ 3 = x ^ 2 := by
        dsimp [X]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
        norm_num
      have hY3 : Y ^ 3 = y ^ 2 := by
        dsimp [Y]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
        norm_num
      apply Prod.ext
      · simp only [Prod.fst]
        rw [hcos]
        have hsq : (a * u ^ 3) ^ 2 = x ^ 2 := by
          calc
            (a * u ^ 3) ^ 2 = a ^ 2 * (u ^ 2) ^ 3 := by ring
            _ = A ^ 3 * (u ^ 2) ^ 3 := by rw [hA3]
            _ = (A * u ^ 2) ^ 3 := by ring
            _ = X ^ 3 := by rw [huA]
            _ = x ^ 2 := hX3
        have hleft0 : 0 ≤ a * u ^ 3 := by positivity
        nlinarith
      · simp only [Prod.snd]
        have hsq : (a * Real.sin (Real.arccos u) ^ 3) ^ 2 = y ^ 2 := by
          calc
            (a * Real.sin (Real.arccos u) ^ 3) ^ 2 =
                a ^ 2 * (Real.sin (Real.arccos u) ^ 2) ^ 3 := by ring
            _ = A ^ 3 * (Real.sin (Real.arccos u) ^ 2) ^ 3 := by rw [hA3]
            _ = (A * Real.sin (Real.arccos u) ^ 2) ^ 3 := by ring
            _ = Y ^ 3 := by rw [hsA]
            _ = y ^ 2 := hY3
        have hleft0 : 0 ≤ a * Real.sin (Real.arccos u) ^ 3 := by positivity
        nlinarith
  · rintro ⟨t, ⟨ht0, ht1⟩, heq⟩
    have hxEq : a * Real.cos t ^ 3 = x := congrArg Prod.fst heq
    have hyEq : a * Real.sin t ^ 3 = y := congrArg Prod.snd heq
    rw [← hxEq, ← hyEq]
    have hs : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [ht1, Real.pi_pos])
    have hc : 0 ≤ Real.cos t := by
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht0, Real.pi_pos], ht1⟩
    have hax : 0 ≤ a * Real.cos t ^ 3 := mul_nonneg (le_of_lt ha) (pow_nonneg hc _)
    have hay : 0 ≤ a * Real.sin t ^ 3 := mul_nonneg (le_of_lt ha) (pow_nonneg hs _)
    refine ⟨?_, hax, hay⟩
    change Real.rpow |a * Real.cos t ^ 3| (2 / 3 : ℝ) +
        Real.rpow |a * Real.sin t ^ 3| (2 / 3 : ℝ) = Real.rpow a (2 / 3 : ℝ)
    rw [abs_of_nonneg hax, abs_of_nonneg hay]
    have hmulx : Real.rpow (a * Real.cos t ^ 3) (2 / 3 : ℝ) =
        Real.rpow a (2 / 3 : ℝ) * Real.rpow (Real.cos t ^ 3) (2 / 3 : ℝ) :=
      Real.mul_rpow (le_of_lt ha) (pow_nonneg hc _)
    have hmuly : Real.rpow (a * Real.sin t ^ 3) (2 / 3 : ℝ) =
        Real.rpow a (2 / 3 : ℝ) * Real.rpow (Real.sin t ^ 3) (2 / 3 : ℝ) :=
      Real.mul_rpow (le_of_lt ha) (pow_nonneg hs _)
    rw [hmulx, hmuly]
    have hc3 : Real.rpow (Real.cos t) (3 : ℝ) = Real.cos t ^ 3 := by
      simpa using Real.rpow_natCast (Real.cos t) 3
    have hs3 : Real.rpow (Real.sin t) (3 : ℝ) = Real.sin t ^ 3 := by
      simpa using Real.rpow_natCast (Real.sin t) 3
    have hc_pow : Real.rpow (Real.cos t ^ 3) (2 / 3 : ℝ) = Real.cos t ^ 2 := by
      calc
        Real.rpow (Real.cos t ^ 3) (2 / 3 : ℝ) =
            Real.rpow (Real.rpow (Real.cos t) (3 : ℝ)) (2 / 3 : ℝ) := by rw [hc3]
        _ = Real.rpow (Real.cos t) ((3 : ℝ) * (2 / 3 : ℝ)) :=
          (Real.rpow_mul hc (3 : ℝ) (2 / 3 : ℝ)).symm
        _ = Real.rpow (Real.cos t) (2 : ℝ) := by norm_num
        _ = Real.cos t ^ 2 := by simpa using Real.rpow_natCast (Real.cos t) 2
    have hs_pow : Real.rpow (Real.sin t ^ 3) (2 / 3 : ℝ) = Real.sin t ^ 2 := by
      calc
        Real.rpow (Real.sin t ^ 3) (2 / 3 : ℝ) =
            Real.rpow (Real.rpow (Real.sin t) (3 : ℝ)) (2 / 3 : ℝ) := by rw [hs3]
        _ = Real.rpow (Real.sin t) ((3 : ℝ) * (2 / 3 : ℝ)) :=
          (Real.rpow_mul hs (3 : ℝ) (2 / 3 : ℝ)).symm
        _ = Real.rpow (Real.sin t) (2 : ℝ) := by norm_num
        _ = Real.sin t ^ 2 := by simpa using Real.rpow_natCast (Real.sin t) 2
    rw [hc_pow, hs_pow]
    calc
      Real.rpow a (2 / 3 : ℝ) * Real.cos t ^ 2 +
          Real.rpow a (2 / 3 : ℝ) * Real.sin t ^ 2 =
          Real.rpow a (2 / 3 : ℝ) *
            (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = Real.rpow a (2 / 3 : ℝ) := by rw [Real.sin_sq_add_cos_sq]; ring

theorem gap9 (a t : ℝ) :
    rawParamSpeed a t =
      Real.sqrt
        (9 * a ^ 2 * Real.cos t ^ 4 * Real.sin t ^ 2 +
          9 * a ^ 2 * Real.sin t ^ 4 * Real.cos t ^ 2) := by
  rfl

theorem gap10 (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    rawParamSpeed a t = paramSpeed a t := by
  unfold rawParamSpeed paramSpeed
  have hs : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos t := by
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hprod : 0 ≤ 3 * a * Real.cos t * Real.sin t := by positivity
  have hid :
      9 * a ^ 2 * Real.cos t ^ 4 * Real.sin t ^ 2 +
          9 * a ^ 2 * Real.sin t ^ 4 * Real.cos t ^ 2 =
        (3 * a * Real.cos t * Real.sin t) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hid, Real.sqrt_sq hprod]

theorem gap11 (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paramSpeed a t = 3 * a * Real.cos t * Real.sin t := by
  rfl

theorem gap12 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      4 * Real.rpow a (4 / 3 : ℝ) *
        ∫ t in (0 : ℝ)..Real.pi / 2,
          (Real.cos t ^ 4 + Real.sin t ^ 4) *
            (3 * a * Real.cos t * Real.sin t) := by
  have hp : Real.rpow a (4 / 3 : ℝ) * a = Real.rpow a (7 / 3 : ℝ) := by
    calc
      Real.rpow a (4 / 3 : ℝ) * a =
          Real.rpow a (4 / 3 : ℝ) * Real.rpow a (1 : ℝ) := by
            congr 1
            exact (Real.rpow_one a).symm
      _ = Real.rpow a (4 / 3 + 1 : ℝ) := (Real.rpow_add ha _ _).symm
      _ = Real.rpow a (7 / 3 : ℝ) := by norm_num
  rw [trigWeightedIntegral a, gap7 a ha]
  calc
    4 * Real.rpow a (7 / 3 : ℝ) =
        4 * (Real.rpow a (4 / 3 : ℝ) * a) := by rw [hp]
    _ = 4 * Real.rpow a (4 / 3 : ℝ) * a := by ring

theorem gap13 (a : ℝ) (ha : 0 < a) :
    4 * Real.rpow a (4 / 3 : ℝ) *
        (∫ t in (0 : ℝ)..Real.pi / 2,
          (Real.cos t ^ 4 + Real.sin t ^ 4) *
            (3 * a * Real.cos t * Real.sin t)) =
      24 * Real.rpow a (7 / 3 : ℝ) *
        ∫ t in (0 : ℝ)..Real.pi / 2,
          Real.sin t ^ 5 * Real.cos t := by
  have hp : Real.rpow a (4 / 3 : ℝ) * a = Real.rpow a (7 / 3 : ℝ) := by
    calc
      Real.rpow a (4 / 3 : ℝ) * a =
          Real.rpow a (4 / 3 : ℝ) * Real.rpow a (1 : ℝ) := by
            congr 1
            exact (Real.rpow_one a).symm
      _ = Real.rpow a (4 / 3 + 1 : ℝ) := (Real.rpow_add ha _ _).symm
      _ = Real.rpow a (7 / 3 : ℝ) := by norm_num
  rw [trigWeightedIntegral a, sinFiveCosIntegral]
  calc
    4 * Real.rpow a (4 / 3 : ℝ) * a =
        4 * (Real.rpow a (4 / 3 : ℝ) * a) := by ring
    _ = 4 * Real.rpow a (7 / 3 : ℝ) := by rw [hp]
    _ = 24 * Real.rpow a (7 / 3 : ℝ) * (1 / 6 : ℝ) := by ring

theorem gap14 (a : ℝ) (ha : 0 < a) :
    24 * Real.rpow a (7 / 3 : ℝ) *
        (∫ t in (0 : ℝ)..Real.pi / 2,
          Real.sin t ^ 5 * Real.cos t) =
      4 * Real.rpow a (7 / 3 : ℝ) := by
  rw [sinFiveCosIntegral]
  ring

theorem gap15 (a : ℝ) (ha : 0 < a) :
    weightedLength a = 4 * Real.rpow a (7 / 3 : ℝ) := by
  exact gap7 a ha

end

end ProofGap.Exercise4225
