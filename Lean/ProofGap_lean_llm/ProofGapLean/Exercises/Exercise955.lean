import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise955

noncomputable section

def root (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 4)

def y (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt 2) *
      Real.arctan (x * Real.sqrt 2 / root x) -
    1 / (4 * Real.sqrt 2) *
      Real.log ((root x - x * Real.sqrt 2) /
        (root x + x * Real.sqrt 2))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt 2) *
      (1 / (1 + 2 * x ^ 2 / (1 + x ^ 4))) *
      ((Real.sqrt 2 * root x -
          2 * Real.sqrt 2 * x ^ 4 / root x) / (1 + x ^ 4)) -
    1 / (4 * Real.sqrt 2) *
      ((2 * x ^ 3 / root x - Real.sqrt 2) /
          (root x - x * Real.sqrt 2) -
        (2 * x ^ 3 / root x + Real.sqrt 2) /
          (root x + x * Real.sqrt 2))

def finalDerivative (x : ℝ) : ℝ := root x / (1 - x ^ 4)

private lemma sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

private lemma root_sq (x : ℝ) : (root x) ^ 2 = 1 + x ^ 4 := by
  simpa only [root] using
    Real.sq_sqrt (show 0 ≤ (1 + x ^ 4 : ℝ) by positivity)

private lemma root_pos (x : ℝ) : 0 < root x := by
  simpa only [root] using
    Real.sqrt_pos.2 (show 0 < (1 + x ^ 4 : ℝ) by positivity)

private lemma root_linear_pos (x : ℝ) (hx : x ^ 2 ≠ 1) :
    0 < root x - x * Real.sqrt 2 ∧
      0 < root x + x * Real.sqrt 2 := by
  have hxsq : (x * Real.sqrt 2) ^ 2 = 2 * x ^ 2 := by
    calc
      (x * Real.sqrt 2) ^ 2 = x ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 2 * x ^ 2 := by rw [sqrt_two_sq]; ring
  have hdiff : 0 < (root x) ^ 2 - (x * Real.sqrt 2) ^ 2 := by
    calc
      (root x) ^ 2 - (x * Real.sqrt 2) ^ 2 =
          (1 + x ^ 4) - 2 * x ^ 2 := by rw [root_sq, hxsq]
      _ = (x ^ 2 - 1) ^ 2 := by ring
      _ > 0 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  have hprod :
      0 < (root x - x * Real.sqrt 2) *
        (root x + x * Real.sqrt 2) := by
    nlinarith
  rcases mul_pos_iff.mp hprod with h | h
  · exact h
  · nlinarith [root_pos x]

private lemma hasDerivAt_root (x : ℝ) :
    HasDerivAt root (2 * x ^ 3 / root x) x := by
  have hp : 0 < (1 + x ^ 4 : ℝ) := by positivity
  have hinner :
      HasDerivAt (fun z : ℝ => 1 + z ^ 4) (4 * x ^ 3) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 4) using 1 <;>
      norm_num <;> ring
  have hsqrt :
      HasDerivAt
        (fun z : ℝ => Real.sqrt (1 + z ^ 4))
        ((1 / (2 * Real.sqrt (1 + x ^ 4))) * (4 * x ^ 3)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x hinner
  unfold root
  convert hsqrt using 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 hp)] <;> ring

theorem gap1 (x : ℝ) (hx : x ^ 2 ≠ 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hr0 : root x ≠ 0 := ne_of_gt (root_pos x)
  rcases root_linear_pos x hx with ⟨hminus, hplus⟩
  have hminus0 : root x - x * Real.sqrt 2 ≠ 0 := ne_of_gt hminus
  have hplus0 : root x + x * Real.sqrt 2 ≠ 0 := ne_of_gt hplus
  have hlinear :
      HasDerivAt (fun z : ℝ => z * Real.sqrt 2) (Real.sqrt 2) x := by
    simpa using
      (hasDerivAt_id x).mul (hasDerivAt_const x (Real.sqrt 2))
  have hu0 := hlinear.div (hasDerivAt_root x) hr0
  have hu :
      HasDerivAt (fun z : ℝ => z * Real.sqrt 2 / root z)
        ((Real.sqrt 2 * root x -
            2 * Real.sqrt 2 * x ^ 4 / root x) / (1 + x ^ 4)) x := by
    convert hu0 using 1 <;>
      rw [root_sq] <;> ring
  have harg_sq :
      (x * Real.sqrt 2 / root x) ^ 2 =
        2 * x ^ 2 / (1 + x ^ 4) := by
    calc
      (x * Real.sqrt 2 / root x) ^ 2 =
          x ^ 2 * (Real.sqrt 2) ^ 2 / (root x) ^ 2 := by ring
      _ = x ^ 2 * 2 / (1 + x ^ 4) := by
        rw [sqrt_two_sq, root_sq]
      _ = 2 * x ^ 2 / (1 + x ^ 4) := by ring
  have hatan0 :=
    (Real.hasDerivAt_arctan
      (x * Real.sqrt 2 / root x)).comp x hu
  have hatan :
      HasDerivAt
        (fun z : ℝ => Real.arctan (z * Real.sqrt 2 / root z))
        ((1 / (1 + 2 * x ^ 2 / (1 + x ^ 4))) *
          ((Real.sqrt 2 * root x -
              2 * Real.sqrt 2 * x ^ 4 / root x) / (1 + x ^ 4))) x := by
    convert hatan0 using 1 <;>
      rw [harg_sq] <;> ring
  have ha :
      HasDerivAt (fun z : ℝ => root z - z * Real.sqrt 2)
        (2 * x ^ 3 / root x - Real.sqrt 2) x :=
    (hasDerivAt_root x).sub hlinear
  have hb :
      HasDerivAt (fun z : ℝ => root z + z * Real.sqrt 2)
        (2 * x ^ 3 / root x + Real.sqrt 2) x :=
    (hasDerivAt_root x).add hlinear
  have hratio0 :
      (root x - x * Real.sqrt 2) / (root x + x * Real.sqrt 2) ≠ 0 :=
    div_ne_zero hminus0 hplus0
  have hlog0 :=
    (Real.hasDerivAt_log hratio0).comp x (ha.div hb hplus0)
  have hlog :
      HasDerivAt
        (fun z : ℝ => Real.log
          ((root z - z * Real.sqrt 2) /
            (root z + z * Real.sqrt 2)))
        ((2 * x ^ 3 / root x - Real.sqrt 2) /
            (root x - x * Real.sqrt 2) -
          (2 * x ^ 3 / root x + Real.sqrt 2) /
            (root x + x * Real.sqrt 2)) x := by
    convert hlog0 using 1 <;>
      field_simp [hr0, hminus0, hplus0] <;> ring
  change HasDerivAt
    (fun z : ℝ =>
      1 / (2 * Real.sqrt 2) *
          Real.arctan (z * Real.sqrt 2 / root z) -
        1 / (4 * Real.sqrt 2) *
          Real.log ((root z - z * Real.sqrt 2) /
            (root z + z * Real.sqrt 2)))
    (1 / (2 * Real.sqrt 2) *
        (1 / (1 + 2 * x ^ 2 / (1 + x ^ 4))) *
        ((Real.sqrt 2 * root x -
            2 * Real.sqrt 2 * x ^ 4 / root x) / (1 + x ^ 4)) -
      1 / (4 * Real.sqrt 2) *
        ((2 * x ^ 3 / root x - Real.sqrt 2) /
            (root x - x * Real.sqrt 2) -
          (2 * x ^ 3 / root x + Real.sqrt 2) /
            (root x + x * Real.sqrt 2))) x
  convert
    (hatan.const_mul (1 / (2 * Real.sqrt 2))).sub
      (hlog.const_mul (1 / (4 * Real.sqrt 2))) using 1 <;> ring

theorem gap2 (x : ℝ) (hx : x ^ 2 ≠ 1) :
    expandedDerivative x = finalDerivative x := by
  have hr2 := root_sq x
  have hs2 := sqrt_two_sq
  have hr0 : root x ≠ 0 := ne_of_gt (root_pos x)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hA0 : 1 + x ^ 4 ≠ 0 := by positivity
  have htp : 1 + x ^ 2 ≠ 0 := by positivity
  have ht : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hxm : x ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hsq0 : (x ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hxm
  have hfinal : 1 - x ^ 4 ≠ 0 := by
    have hm : (1 - x ^ 2) * (1 + x ^ 2) ≠ 0 := mul_ne_zero ht htp
    intro h
    apply hm
    calc
      (1 - x ^ 2) * (1 + x ^ 2) = 1 - x ^ 4 := by ring
      _ = 0 := h
  rcases root_linear_pos x hx with ⟨hminus, hplus⟩
  have hminus0 : root x - x * Real.sqrt 2 ≠ 0 := ne_of_gt hminus
  have hplus0 : root x + x * Real.sqrt 2 ≠ 0 := ne_of_gt hplus
  have hden : 1 + 2 * x ^ 2 / (1 + x ^ 4) ≠ 0 := by positivity
  have hQ :
      1 / (1 + 2 * x ^ 2 / (1 + x ^ 4)) =
        (1 + x ^ 4) / (1 + x ^ 2) ^ 2 := by
    field_simp [hA0, hden, htp]
    ring
  have hU :
      (Real.sqrt 2 * root x -
          2 * Real.sqrt 2 * x ^ 4 / root x) / (1 + x ^ 4) =
        Real.sqrt 2 * (1 - x ^ 4) /
          (root x * (1 + x ^ 4)) := by
    field_simp [hr0, hA0]
    rw [hr2]
    ring
  have hfirst :
      1 / (2 * Real.sqrt 2) *
          (1 / (1 + 2 * x ^ 2 / (1 + x ^ 4))) *
          ((Real.sqrt 2 * root x -
              2 * Real.sqrt 2 * x ^ 4 / root x) / (1 + x ^ 4)) =
        (1 - x ^ 2) / (2 * root x * (1 + x ^ 2)) := by
    rw [hQ, hU]
    field_simp [hs0, hr0, hA0, htp]
    ring
  have hab :
      (root x - x * Real.sqrt 2) *
          (root x + x * Real.sqrt 2) =
        (x ^ 2 - 1) ^ 2 := by
    calc
      (root x - x * Real.sqrt 2) *
          (root x + x * Real.sqrt 2) =
          (root x) ^ 2 - (x * Real.sqrt 2) ^ 2 := by ring
      _ = (root x) ^ 2 - 2 * x ^ 2 := by
        rw [show (x * Real.sqrt 2) ^ 2 =
          x ^ 2 * (Real.sqrt 2) ^ 2 by ring, hs2]
        ring
      _ = (x ^ 2 - 1) ^ 2 := by
        rw [hr2]
        ring
  have hscaled :
      -2 * Real.sqrt 2 * (root x) ^ 2 =
        -2 * Real.sqrt 2 * (1 + x ^ 4) := by
    rw [hr2]
  have hnum :
      (2 * x ^ 3 / root x - Real.sqrt 2) *
          (root x + x * Real.sqrt 2) -
        (2 * x ^ 3 / root x + Real.sqrt 2) *
          (root x - x * Real.sqrt 2) =
        -2 * Real.sqrt 2 * (1 - x ^ 4) / root x := by
    field_simp [hr0]
    nlinarith [hscaled]
  have hB :
      (2 * x ^ 3 / root x - Real.sqrt 2) /
          (root x - x * Real.sqrt 2) -
        (2 * x ^ 3 / root x + Real.sqrt 2) /
          (root x + x * Real.sqrt 2) =
        -2 * Real.sqrt 2 * (1 - x ^ 4) /
          (root x * (x ^ 2 - 1) ^ 2) := by
    calc
      (2 * x ^ 3 / root x - Real.sqrt 2) /
            (root x - x * Real.sqrt 2) -
          (2 * x ^ 3 / root x + Real.sqrt 2) /
            (root x + x * Real.sqrt 2) =
          ((2 * x ^ 3 / root x - Real.sqrt 2) *
              (root x + x * Real.sqrt 2) -
            (2 * x ^ 3 / root x + Real.sqrt 2) *
              (root x - x * Real.sqrt 2)) /
            ((root x - x * Real.sqrt 2) *
              (root x + x * Real.sqrt 2)) := by
                field_simp [hminus0, hplus0]
      _ = (-2 * Real.sqrt 2 * (1 - x ^ 4) / root x) /
          (x ^ 2 - 1) ^ 2 := by rw [hnum, hab]
      _ = -2 * Real.sqrt 2 * (1 - x ^ 4) /
          (root x * (x ^ 2 - 1) ^ 2) := by
            rw [div_div]
  have hsecond :
      -(1 / (4 * Real.sqrt 2) *
        ((2 * x ^ 3 / root x - Real.sqrt 2) /
            (root x - x * Real.sqrt 2) -
          (2 * x ^ 3 / root x + Real.sqrt 2) /
            (root x + x * Real.sqrt 2))) =
        (1 + x ^ 2) / (2 * root x * (1 - x ^ 2)) := by
    rw [hB]
    field_simp [hs0, hr0, ht, hxm, hsq0, hfinal] <;> ring
  have hsum :
      (1 - x ^ 2) / (2 * root x * (1 + x ^ 2)) +
          (1 + x ^ 2) / (2 * root x * (1 - x ^ 2)) =
        (1 + x ^ 4) / (root x * (1 - x ^ 4)) := by
    field_simp [hr0, ht, htp, hfinal] <;> ring
  unfold expandedDerivative finalDerivative
  rw [hfirst]
  change (1 - x ^ 2) / (2 * root x * (1 + x ^ 2)) +
      (-(1 / (4 * Real.sqrt 2) *
        ((2 * x ^ 3 / root x - Real.sqrt 2) /
            (root x - x * Real.sqrt 2) -
          (2 * x ^ 3 / root x + Real.sqrt 2) /
            (root x + x * Real.sqrt 2)))) =
    root x / (1 - x ^ 4)
  rw [hsecond, hsum]
  rw [← hr2]
  field_simp [hr0, hfinal] <;> ring

theorem gap3 (x : ℝ) (hx : x ^ 2 ≠ 1) :
    HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x hx] using gap1 x hx

end

end ProofGap.Exercise955
