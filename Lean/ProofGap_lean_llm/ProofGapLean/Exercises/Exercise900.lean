import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise900

noncomputable section

def root (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)
def y (x : ℝ) : ℝ :=
  ((2 + 3 * x ^ 2) / x ^ 4) * root x +
    3 * Real.log ((1 + root x) / x)

def expandedDerivative (x : ℝ) : ℝ :=
  ((6 * x ^ 5 - 4 * x ^ 3 * (2 + 3 * x ^ 2)) / x ^ 8) * root x -
    x * (2 + 3 * x ^ 2) / (x ^ 4 * root x) +
    (3 / (1 + root x)) * (-(x / root x)) - 3 / x

def finalDerivative (x : ℝ) : ℝ := -8 / (x ^ 5 * root x)

theorem gap1 (x : ℝ) (hx0 : 0 < x) (hx1 : x ^ 2 < 1) :
    deriv y x = expandedDerivative x := by
  have hrad : 0 < 1 - x ^ 2 := by
    linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hrpos : 0 < root x := by
    rw [root]
    exact Real.sqrt_pos.2 hrad
  have hrne : root x ≠ 0 := ne_of_gt hrpos
  have hplus : 1 + root x ≠ 0 := by
    linarith
  have hr2 : root x ^ 2 = 1 - x ^ 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt hrad)
  have hinner :
      HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hpowderiv :
      HasDerivAt (fun z : ℝ => z ^ (1 / 2 : ℝ))
        ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1))
        (1 - x ^ 2) := by
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hrad))
  have hpow :
      (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1) = (root x)⁻¹ := by
    calc
      (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1) =
          (1 - x ^ 2) ^ (-(1 / 2 : ℝ)) := by norm_num
      _ = ((1 - x ^ 2) ^ (1 / 2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hrad)]
      _ = (root x)⁻¹ := by
        unfold root
        rw [Real.sqrt_eq_rpow]
  have hrootRaw :
      HasDerivAt root
        (((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1)) * (-2 * x)) x := by
    unfold root
    simpa only [Real.sqrt_eq_rpow, Function.comp_apply] using
      hpowderiv.comp x hinner
  have hrootCoeff :
      ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1)) * (-2 * x) =
        -x / root x := by
    rw [hpow]
    field_simp [hrne]
  have hroot : HasDerivAt root (-x / root x) x := by
    rw [← hrootCoeff]
    exact hrootRaw
  have hnum :
      HasDerivAt (fun t : ℝ => 2 + 3 * t ^ 2) (6 * x) x := by
    convert
      (hasDerivAt_const x (2 : ℝ)).add
        ((hasDerivAt_const x (3 : ℝ)).mul ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hden : HasDerivAt (fun t : ℝ => t ^ 4) (4 * x ^ 3) x := by
    convert (hasDerivAt_id x).pow 4 using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hfracRaw := hnum.div hden (pow_ne_zero 4 hxne)
  have hfracCoeff :
      (6 * x * x ^ 4 - (2 + 3 * x ^ 2) * (4 * x ^ 3)) / (x ^ 4) ^ 2 =
        (6 * x ^ 5 - 4 * x ^ 3 * (2 + 3 * x ^ 2)) / x ^ 8 := by
    field_simp [hxne]
  have hfrac :
      HasDerivAt (fun t : ℝ => (2 + 3 * t ^ 2) / t ^ 4)
        ((6 * x ^ 5 - 4 * x ^ 3 * (2 + 3 * x ^ 2)) / x ^ 8) x := by
    rw [← hfracCoeff]
    exact hfracRaw
  have hp :
      HasDerivAt (fun t : ℝ => 1 + root t) (-x / root x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hroot using 1 <;>
      ring_nf
  have hq :
      HasDerivAt (fun t : ℝ => (1 + root t) / t)
        (-(1 + root x) / (root x * x ^ 2)) x := by
    convert hp.div (hasDerivAt_id x) hxne using 1 <;>
      simp only [id_eq] <;>
      field_simp [hxne, hrne] <;>
      nlinarith [hr2]
  have hq0 : (1 + root x) / x ≠ 0 := div_ne_zero hplus hxne
  have hlogbase :
      HasDerivAt
        (fun t : ℝ => 3 * Real.log ((1 + root t) / t))
        (-3 / (root x * x)) x := by
    convert (hasDerivAt_const x (3 : ℝ)).mul (hq.log hq0) using 1 <;>
      field_simp [hxne, hrne, hplus] <;>
      ring_nf
  have hlog :
      HasDerivAt
        (fun t : ℝ => 3 * Real.log ((1 + root t) / t))
        ((3 / (1 + root x)) * (-(x / root x)) - 3 / x) x := by
    convert hlogbase using 1
    field_simp [hxne, hrne, hplus]
    nlinarith [hr2]
  have hall : HasDerivAt y (expandedDerivative x) x := by
    unfold y expandedDerivative
    convert (hfrac.mul hroot).add hlog using 1 <;>
      field_simp [hxne, hrne, hplus] <;>
      ring_nf
  exact hall.deriv

theorem gap2 (x : ℝ) (hx0 : 0 < x) (hx1 : x ^ 2 < 1) :
    expandedDerivative x = finalDerivative x := by
  have hrad : 0 < 1 - x ^ 2 := by
    linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hrpos : 0 < root x := by
    rw [root]
    exact Real.sqrt_pos.2 hrad
  have hrne : root x ≠ 0 := ne_of_gt hrpos
  have hplus : 1 + root x ≠ 0 := by
    linarith
  have hr2 : root x ^ 2 = 1 - x ^ 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt hrad)
  have hr3 : root x ^ 3 = root x * (1 - x ^ 2) := by
    calc
      root x ^ 3 = root x * root x ^ 2 := by ring
      _ = root x * (1 - x ^ 2) := by rw [hr2]
  unfold expandedDerivative finalDerivative
  field_simp [hxne, hrne, hplus]
  ring_nf
  simp only [hr3, hr2]
  ring

theorem gap3 (x : ℝ) (hx0 : 0 < x) (hx1 : x ^ 2 < 1) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hx0 hx1).trans (gap2 x hx0 hx1)

end

end ProofGap.Exercise900
