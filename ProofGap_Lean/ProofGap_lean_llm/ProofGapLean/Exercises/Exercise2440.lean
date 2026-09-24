import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace ProofGap.Exercise2440
noncomputable section

open Set
open scoped Interval

def astroidY (a x : ℝ) : ℝ :=
  Real.rpow (Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)) (3 / 2 : ℝ)
def arcIntegrand (a x : ℝ) : ℝ := Real.rpow (a / x) (1 / 3 : ℝ)
def s (a : ℝ) : ℝ := 4 * ∫ x in (0 : ℝ)..a, arcIntegrand a x

private theorem rpow_div_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (p : ℝ) :
    Real.rpow (x / y) p = Real.rpow x p / Real.rpow y p := by
  calc
    Real.rpow (x / y) p =
        Real.exp (Real.log (x / y) * p) :=
      Real.rpow_def_of_pos (div_pos hx hy) _
    _ = Real.exp ((Real.log x - Real.log y) * p) := by
      rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
    _ = Real.exp (Real.log x * p - Real.log y * p) := by ring
    _ = Real.exp (Real.log x * p) / Real.exp (Real.log y * p) := by
      rw [Real.exp_sub]
    _ = Real.rpow x p / Real.rpow y p :=
      congrArg₂ (fun u v : ℝ => u / v)
        (Real.rpow_def_of_pos hx p).symm
        (Real.rpow_def_of_pos hy p).symm

private theorem rpow_neg_pos {x : ℝ} (hx : 0 < x) (p : ℝ) :
    Real.rpow x (-p) = (Real.rpow x p)⁻¹ := by
  calc
    Real.rpow x (-p) = Real.exp (Real.log x * (-p)) :=
      Real.rpow_def_of_pos hx _
    _ = Real.exp (-(Real.log x * p)) := by ring
    _ = (Real.exp (Real.log x * p))⁻¹ := by rw [Real.exp_neg]
    _ = (Real.rpow x p)⁻¹ :=
      congrArg (fun u : ℝ => u⁻¹)
        (Real.rpow_def_of_pos hx p).symm

private theorem rpow_add_pos {x : ℝ} (hx : 0 < x) (p q : ℝ) :
    Real.rpow x (p + q) = Real.rpow x p * Real.rpow x q := by
  calc
    Real.rpow x (p + q) = Real.exp (Real.log x * (p + q)) :=
      Real.rpow_def_of_pos hx _
    _ = Real.exp (Real.log x * p + Real.log x * q) := by ring
    _ = Real.exp (Real.log x * p) * Real.exp (Real.log x * q) := by
      rw [Real.exp_add]
    _ = Real.rpow x p * Real.rpow x q :=
      congrArg₂ (fun u v : ℝ => u * v)
        (Real.rpow_def_of_pos hx p).symm
        (Real.rpow_def_of_pos hx q).symm

private theorem rpow_rpow_pos {x : ℝ} (hx : 0 < x) (p q : ℝ) :
    Real.rpow (Real.rpow x p) q = Real.rpow x (p * q) := by
  have hlog : Real.log (Real.rpow x p) = Real.log x * p := by
    calc
      Real.log (Real.rpow x p) =
          Real.log (Real.exp (Real.log x * p)) :=
        congrArg Real.log (Real.rpow_def_of_pos hx p)
      _ = Real.log x * p := Real.log_exp _
  calc
    Real.rpow (Real.rpow x p) q =
        Real.exp (Real.log (Real.rpow x p) * q) :=
      Real.rpow_def_of_pos (Real.rpow_pos_of_pos hx p) _
    _ = Real.exp ((Real.log x * p) * q) :=
      congrArg (fun t : ℝ => Real.exp (t * q)) hlog
    _ = Real.exp (Real.log x * (p * q)) := by ring
    _ = Real.rpow x (p * q) :=
      (Real.rpow_def_of_pos hx _).symm

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : x ∈ Ioo 0 a) :
    HasDerivAt (astroidY a)
      (-Real.rpow (astroidY a x / x) (1 / 3 : ℝ)) x := by
  unfold astroidY
  have hx0 : 0 < x := hx.1
  have hpow :
      Real.rpow x (2 / 3 : ℝ) < Real.rpow a (2 / 3 : ℝ) :=
    Real.rpow_lt_rpow (le_of_lt hx0) hx.2 (by norm_num)
  let u : ℝ :=
    Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)
  have hu : 0 < u := by
    change 0 < Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)
    exact sub_pos.mpr hpow
  have hdx :
      HasDerivAt (fun z : ℝ => Real.rpow z (2 / 3 : ℝ))
        ((2 / 3 : ℝ) * Real.rpow x ((2 / 3 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (p := (2 / 3 : ℝ))
      (Or.inl (ne_of_gt hx0))
  have hinner :
      HasDerivAt
        (fun z : ℝ =>
          Real.rpow a (2 / 3 : ℝ) - Real.rpow z (2 / 3 : ℝ))
        (-((2 / 3 : ℝ) * Real.rpow x ((2 / 3 : ℝ) - 1))) x := by
    simpa only [zero_sub] using
      (hasDerivAt_const (x := x) (c := Real.rpow a (2 / 3 : ℝ))).sub hdx
  have houter :
      HasDerivAt (fun t : ℝ => Real.rpow t (3 / 2 : ℝ))
        ((3 / 2 : ℝ) * Real.rpow u ((3 / 2 : ℝ) - 1)) u :=
    Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
      (Or.inl (ne_of_gt hu))
  have hcomp := houter.comp x hinner
  have hnested :
      Real.rpow (Real.rpow u (3 / 2 : ℝ)) (1 / 3 : ℝ) =
        Real.rpow u (1 / 2 : ℝ) := by
    calc
      Real.rpow (Real.rpow u (3 / 2 : ℝ)) (1 / 3 : ℝ) =
          Real.rpow u ((3 / 2 : ℝ) * (1 / 3 : ℝ)) :=
        rpow_rpow_pos hu _ _
      _ = Real.rpow u (1 / 2 : ℝ) := by norm_num
  have hslope :
      Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ) =
        Real.rpow u (1 / 2 : ℝ) / Real.rpow x (1 / 3 : ℝ) := by
    calc
      Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ) =
          Real.rpow (Real.rpow u (3 / 2 : ℝ)) (1 / 3 : ℝ) /
            Real.rpow x (1 / 3 : ℝ) :=
        rpow_div_pos (Real.rpow_pos_of_pos hu _) hx0 _
      _ = Real.rpow u (1 / 2 : ℝ) / Real.rpow x (1 / 3 : ℝ) := by
        rw [hnested]
  have hxneg :
      Real.rpow x ((2 / 3 : ℝ) - 1) =
        1 / Real.rpow x (1 / 3 : ℝ) := by
    calc
      Real.rpow x ((2 / 3 : ℝ) - 1) =
          Real.rpow x (-(1 / 3 : ℝ)) := by
        congr 1
        norm_num
      _ = 1 / Real.rpow x (1 / 3 : ℝ) := by
        simpa only [one_div] using rpow_neg_pos hx0 (1 / 3 : ℝ)
  change HasDerivAt
    (fun z : ℝ =>
      Real.rpow
        (Real.rpow a (2 / 3 : ℝ) - Real.rpow z (2 / 3 : ℝ))
        (3 / 2 : ℝ))
    (-Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ)) x
  convert hcomp using 1
  rw [hslope, hxneg]
  ring_nf

theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : x ∈ Ioo 0 a) :
    Real.sqrt
        (1 + (-Real.rpow (astroidY a x / x) (1 / 3 : ℝ)) ^ 2) =
      arcIntegrand a x := by
  have hx0 : 0 < x := hx.1
  have hpow :
      Real.rpow x (2 / 3 : ℝ) < Real.rpow a (2 / 3 : ℝ) :=
    Real.rpow_lt_rpow (le_of_lt hx0) hx.2 (by norm_num)
  let u : ℝ :=
    Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)
  have hu : 0 < u := by
    change 0 < Real.rpow a (2 / 3 : ℝ) - Real.rpow x (2 / 3 : ℝ)
    exact sub_pos.mpr hpow
  have hy : 0 < Real.rpow u (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hu _
  have hq : 0 < Real.rpow u (3 / 2 : ℝ) / x := div_pos hy hx0
  have har : 0 < a / x := div_pos ha hx0
  have hslope_sq :
      (Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ)) ^ 2 =
        u / Real.rpow x (2 / 3 : ℝ) := by
    calc
      (Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ) *
            Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ) := by ring
      _ = Real.rpow (Real.rpow u (3 / 2 : ℝ) / x)
            ((1 / 3 : ℝ) + (1 / 3 : ℝ)) :=
        (rpow_add_pos hq _ _).symm
      _ = Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (2 / 3 : ℝ) := by
        congr 1
        norm_num
      _ = Real.rpow (Real.rpow u (3 / 2 : ℝ)) (2 / 3 : ℝ) /
            Real.rpow x (2 / 3 : ℝ) :=
        rpow_div_pos hy hx0 _
      _ = Real.rpow u ((3 / 2 : ℝ) * (2 / 3 : ℝ)) /
            Real.rpow x (2 / 3 : ℝ) := by
        rw [rpow_rpow_pos hu]
      _ = u / Real.rpow x (2 / 3 : ℝ) := by norm_num
  have hratio_sq :
      (Real.rpow (a / x) (1 / 3 : ℝ)) ^ 2 =
        Real.rpow a (2 / 3 : ℝ) / Real.rpow x (2 / 3 : ℝ) := by
    calc
      (Real.rpow (a / x) (1 / 3 : ℝ)) ^ 2 =
          Real.rpow (a / x) (1 / 3 : ℝ) *
            Real.rpow (a / x) (1 / 3 : ℝ) := by ring
      _ = Real.rpow (a / x) ((1 / 3 : ℝ) + (1 / 3 : ℝ)) :=
        (rpow_add_pos har _ _).symm
      _ = Real.rpow (a / x) (2 / 3 : ℝ) := by
        congr 1
        norm_num
      _ = Real.rpow a (2 / 3 : ℝ) / Real.rpow x (2 / 3 : ℝ) :=
        rpow_div_pos ha hx0 _
  have hfrac :
      1 + u / Real.rpow x (2 / 3 : ℝ) =
        Real.rpow a (2 / 3 : ℝ) / Real.rpow x (2 / 3 : ℝ) := by
    have hden : Real.rpow x (2 / 3 : ℝ) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hx0 _)
    dsimp [u]
    field_simp
    ring
  have hsq :
      1 + (-Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ)) ^ 2 =
        (Real.rpow (a / x) (1 / 3 : ℝ)) ^ 2 := by
    calc
      1 + (-Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ)) ^ 2 =
          1 + (Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ)) ^ 2 := by
            ring
      _ = 1 + u / Real.rpow x (2 / 3 : ℝ) := by rw [hslope_sq]
      _ = Real.rpow a (2 / 3 : ℝ) / Real.rpow x (2 / 3 : ℝ) := hfrac
      _ = (Real.rpow (a / x) (1 / 3 : ℝ)) ^ 2 := hratio_sq.symm
  unfold astroidY arcIntegrand
  change Real.sqrt
      (1 + (-Real.rpow (Real.rpow u (3 / 2 : ℝ) / x) (1 / 3 : ℝ)) ^ 2) =
    Real.rpow (a / x) (1 / 3 : ℝ)
  rw [hsq, Real.sqrt_sq_eq_abs]
  exact abs_of_pos (Real.rpow_pos_of_pos har _)

theorem gap3 (a : ℝ) (ha : 0 < a) :
    s a = 4 * ∫ x in (0 : ℝ)..a, arcIntegrand a x := by
  rfl

theorem gap4 (a : ℝ) (ha : 0 < a) :
    4 * (∫ x in (0 : ℝ)..a, arcIntegrand a x) = 6 * a := by
  have hcongr :
      (∫ x in (0 : ℝ)..a, arcIntegrand a x) =
        ∫ x in (0 : ℝ)..a,
          Real.rpow a (1 / 3 : ℝ) * Real.rpow x (-(1 / 3 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hxmem
    have hxmem' := hxmem
    rw [uIcc_of_le ha.le] at hxmem'
    by_cases hxzero : x = 0
    · subst x
      norm_num [arcIntegrand]
    · have hx0 : 0 < x := lt_of_le_of_ne hxmem'.1 (Ne.symm hxzero)
      unfold arcIntegrand
      rw [rpow_div_pos ha hx0]
      have hnegx :
          Real.rpow x (-(1 / 3 : ℝ)) =
            (Real.rpow x (1 / 3 : ℝ))⁻¹ :=
        rpow_neg_pos hx0 (1 / 3 : ℝ)
      change
        Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ) =
          Real.rpow a (1 / 3 : ℝ) * Real.rpow x (-(1 / 3 : ℝ))
      calc
        Real.rpow a (1 / 3 : ℝ) / Real.rpow x (1 / 3 : ℝ) =
            Real.rpow a (1 / 3 : ℝ) *
              (Real.rpow x (1 / 3 : ℝ))⁻¹ :=
          div_eq_mul_inv _ _
        _ = Real.rpow a (1 / 3 : ℝ) *
              Real.rpow x (-(1 / 3 : ℝ)) := by rw [hnegx]
  have hp :
      (∫ x in (0 : ℝ)..a, Real.rpow x (-(1 / 3 : ℝ))) =
        (3 / 2 : ℝ) * Real.rpow a (2 / 3 : ℝ) := by
    norm_num [integral_rpow, ha, ha.le] <;> ring_nf
  have hcombine :
      Real.rpow a (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ) = a := by
    rw [← rpow_add_pos ha]
    norm_num
  rw [hcongr, intervalIntegral.integral_const_mul, hp]
  calc
    4 *
        (Real.rpow a (1 / 3 : ℝ) *
          ((3 / 2 : ℝ) * Real.rpow a (2 / 3 : ℝ))) =
      6 * (Real.rpow a (1 / 3 : ℝ) * Real.rpow a (2 / 3 : ℝ)) := by
        ring
    _ = 6 * a := by rw [hcombine]

theorem gap5 (a : ℝ) (ha : 0 < a) :
    s a = 6 * a := by
  rw [gap3 a ha, gap4 a ha]

end
end ProofGap.Exercise2440
