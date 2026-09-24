import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise956

noncomputable section

def arccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x

def y956 (x : ℝ) : ℝ :=
  x * Real.sqrt (1 - x ^ 2) / (1 + x ^ 2) -
    3 / Real.sqrt 2 *
      arccot (x * Real.sqrt 2 / Real.sqrt (1 - x ^ 2))

def y957 (x : ℝ) : ℝ :=
  Real.arccos (Real.sin (x ^ 2) - Real.cos (x ^ 2))

def expanded956 (x : ℝ) : ℝ :=
  ((Real.sqrt (1 - x ^ 2) - x ^ 2 / Real.sqrt (1 - x ^ 2)) *
        (1 + x ^ 2) -
      2 * x ^ 2 * Real.sqrt (1 - x ^ 2)) /
      (1 + x ^ 2) ^ 2 +
    3 / (Real.sqrt 2 * (1 + 2 * x ^ 2 / (1 - x ^ 2))) *
      ((Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
          Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) /
        (1 - x ^ 2))

def final956 (x : ℝ) : ℝ :=
  4 / ((x ^ 2 + 1) ^ 2 * Real.sqrt (1 - x ^ 2))

def expanded957 (x : ℝ) : ℝ :=
  -(1 / Real.sqrt
      (1 - (Real.sin (x ^ 2) - Real.cos (x ^ 2)) ^ 2)) *
    (2 * x) * (Real.cos (x ^ 2) + Real.sin (x ^ 2))

def final957 (x : ℝ) : ℝ :=
  -(2 * x * (Real.sin (x ^ 2) + Real.cos (x ^ 2)) /
    Real.sqrt (Real.sin (2 * x ^ 2)))

private theorem expanded956_eq_final956_aux (x : ℝ) (hx : |x| < 1) :
    expanded956 x = final956 x := by
  rcases abs_lt.mp hx with ⟨hxneg, hxpos⟩
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hxpos) (by linarith)
  have hq : 0 < 1 - x ^ 2 := by
    nlinarith [hprod]
  have hq0 : 1 - x ^ 2 ≠ 0 := ne_of_gt hq
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hp0 : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hr0 : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num))
  have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  have hsqa :
      x ^ 2 * Real.sqrt (1 - x ^ 2) ^ 2 =
        x ^ 2 * (1 - x ^ 2) :=
    congrArg (fun z : ℝ => x ^ 2 * z) hsq
  have hD : 0 < 1 + 2 * x ^ 2 / (1 - x ^ 2) := by
    have hnonneg : 0 ≤ 2 * x ^ 2 / (1 - x ^ 2) :=
      div_nonneg (mul_nonneg (by norm_num) (sq_nonneg x)) (le_of_lt hq)
    linarith
  have hD0 : 1 + 2 * x ^ 2 / (1 - x ^ 2) ≠ 0 := ne_of_gt hD
  have hdiff :
      Real.sqrt (1 - x ^ 2) - x ^ 2 / Real.sqrt (1 - x ^ 2) =
        (1 - 2 * x ^ 2) / Real.sqrt (1 - x ^ 2) := by
    field_simp [hs0] <;> nlinarith [hsq]
  have hsum :
      Real.sqrt (1 - x ^ 2) + x ^ 2 / Real.sqrt (1 - x ^ 2) =
        1 / Real.sqrt (1 - x ^ 2) := by
    field_simp [hs0] <;> nlinarith [hsq]
  have hD_eq :
      1 + 2 * x ^ 2 / (1 - x ^ 2) =
        (1 + x ^ 2) / (1 - x ^ 2) := by
    field_simp [hq0] <;> ring
  have hnum :
      Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
          Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2) =
        Real.sqrt 2 / Real.sqrt (1 - x ^ 2) := by
    calc
      Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
          Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2) =
          Real.sqrt 2 *
            (Real.sqrt (1 - x ^ 2) +
              x ^ 2 / Real.sqrt (1 - x ^ 2)) := by ring
      _ = Real.sqrt 2 * (1 / Real.sqrt (1 - x ^ 2)) := by rw [hsum]
      _ = Real.sqrt 2 / Real.sqrt (1 - x ^ 2) := by ring
  have hfirst :
      ((Real.sqrt (1 - x ^ 2) -
            x ^ 2 / Real.sqrt (1 - x ^ 2)) * (1 + x ^ 2) -
          2 * x ^ 2 * Real.sqrt (1 - x ^ 2)) /
          (1 + x ^ 2) ^ 2 =
        (1 - 3 * x ^ 2) /
          ((1 + x ^ 2) ^ 2 * Real.sqrt (1 - x ^ 2)) := by
    rw [hdiff]
    field_simp [hs0, hp0] <;> nlinarith [hsq, hsqa]
  have hsecond :
      3 / (Real.sqrt 2 * (1 + 2 * x ^ 2 / (1 - x ^ 2))) *
          ((Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
              Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) /
            (1 - x ^ 2)) =
        3 / (Real.sqrt (1 - x ^ 2) * (1 + x ^ 2)) := by
    rw [hD_eq, hnum]
    field_simp [hs0, hr0, hq0, hp0, hD0] <;> ring
  unfold expanded956 final956
  rw [hfirst, hsecond]
  field_simp [hs0, hp0] <;> ring

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y956 (expanded956 x) x := by
  rcases abs_lt.mp hx with ⟨hxneg, hxpos⟩
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hxpos) (by linarith)
  have hq : 0 < 1 - x ^ 2 := by
    nlinarith [hprod]
  have hq0 : 1 - x ^ 2 ≠ 0 := ne_of_gt hq
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hp0 : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hr0 : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num))
  have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  have hrsq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
    simpa using Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hD : 0 < 1 + 2 * x ^ 2 / (1 - x ^ 2) := by
    have hn : 0 ≤ 2 * x ^ 2 / (1 - x ^ 2) :=
      div_nonneg (mul_nonneg (by norm_num) (sq_nonneg x)) (le_of_lt hq)
    linarith
  have hD0 : 1 + 2 * x ^ 2 / (1 - x ^ 2) ≠ 0 := ne_of_gt hD
  have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa [id, pow_two, mul_comm] using (hasDerivAt_id x).pow 2
  have hinner :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub hpow using 1 <;> ring
  have hsqrt :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    have hs := (Real.hasDerivAt_sqrt hq0).comp x hinner
    convert hs using 1
    field_simp [hs0] <;> ring
  have hnum :
      HasDerivAt (fun z : ℝ => z * Real.sqrt (1 - z ^ 2))
        (Real.sqrt (1 - x ^ 2) -
          x ^ 2 / Real.sqrt (1 - x ^ 2)) x := by
    have hn := (hasDerivAt_id x).mul hsqrt
    convert hn using 1
    simp only [id_eq]
    ring
  have hden :
      HasDerivAt (fun z : ℝ => 1 + z ^ 2) (2 * x) x :=
    hpow.const_add 1
  have hfirst :
      HasDerivAt
        (fun z : ℝ => z * Real.sqrt (1 - z ^ 2) / (1 + z ^ 2))
        (((Real.sqrt (1 - x ^ 2) -
              x ^ 2 / Real.sqrt (1 - x ^ 2)) * (1 + x ^ 2) -
            2 * x ^ 2 * Real.sqrt (1 - x ^ 2)) /
          (1 + x ^ 2) ^ 2) x := by
    convert hnum.div hden hp0 using 1 <;> ring
  have hxn :
      HasDerivAt (fun z : ℝ => z * Real.sqrt 2) (Real.sqrt 2) x := by
    have hn := (hasDerivAt_id x).mul
      (hasDerivAt_const x (Real.sqrt 2))
    simpa [id] using hn
  have ht :
      HasDerivAt
        (fun z : ℝ => z * Real.sqrt 2 / Real.sqrt (1 - z ^ 2))
        ((Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
            Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) /
          (1 - x ^ 2)) x := by
    have hd := hxn.div hsqrt hs0
    convert hd using 1
    field_simp [hs0]
    nlinarith [hsq]
  have ht_sq :
      (x * Real.sqrt 2 / Real.sqrt (1 - x ^ 2)) ^ 2 =
        2 * x ^ 2 / (1 - x ^ 2) := by
    calc
      (x * Real.sqrt 2 / Real.sqrt (1 - x ^ 2)) ^ 2 =
          x ^ 2 * Real.sqrt 2 ^ 2 /
            Real.sqrt (1 - x ^ 2) ^ 2 := by ring
      _ = x ^ 2 * 2 / (1 - x ^ 2) := by rw [hrsq, hsq]
      _ = 2 * x ^ 2 / (1 - x ^ 2) := by ring
  have hatan :
      HasDerivAt
        (fun z : ℝ => Real.arctan
          (z * Real.sqrt 2 / Real.sqrt (1 - z ^ 2)))
        (1 / (1 + 2 * x ^ 2 / (1 - x ^ 2)) *
          ((Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
              Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) /
            (1 - x ^ 2))) x := by
    have ha := (Real.hasDerivAt_arctan
      (x * Real.sqrt 2 / Real.sqrt (1 - x ^ 2))).comp x ht
    simpa only [ht_sq] using ha
  have hacot :
      HasDerivAt
        (fun z : ℝ => arccot
          (z * Real.sqrt 2 / Real.sqrt (1 - z ^ 2)))
        (-(1 / (1 + 2 * x ^ 2 / (1 - x ^ 2))) *
          ((Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
              Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) /
            (1 - x ^ 2))) x := by
    unfold arccot
    convert (hasDerivAt_const x (Real.pi / 2)).sub hatan using 1 <;> ring
  have hcoef :
      (((Real.sqrt (1 - x ^ 2) -
              x ^ 2 / Real.sqrt (1 - x ^ 2)) * (1 + x ^ 2) -
            2 * x ^ 2 * Real.sqrt (1 - x ^ 2)) /
          (1 + x ^ 2) ^ 2) -
        (3 / Real.sqrt 2) *
          (-(1 / (1 + 2 * x ^ 2 / (1 - x ^ 2))) *
            ((Real.sqrt 2 * Real.sqrt (1 - x ^ 2) +
                Real.sqrt 2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) /
              (1 - x ^ 2))) = expanded956 x := by
    unfold expanded956
    field_simp [hr0, hD0, hq0, hs0, hp0]
    ring
  unfold y956
  convert hfirst.sub
    ((hasDerivAt_const x (3 / Real.sqrt 2)).mul hacot) using 1
  simpa using hcoef.symm

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    expanded956 x = final956 x := by
  exact expanded956_eq_final956_aux x hx

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y956 (final956 x) x := by
  rw [← expanded956_eq_final956_aux x hx]
  exact gap1 x hx

theorem gap4 (x : ℝ)
    (hx : |Real.sin (x ^ 2) - Real.cos (x ^ 2)| < 1) :
    HasDerivAt y957 (expanded957 x) x := by
  have ht : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa [id, pow_two, mul_comm] using (hasDerivAt_id x).pow 2
  have hu :
      HasDerivAt
        (fun z : ℝ => Real.sin (z ^ 2) - Real.cos (z ^ 2))
        (2 * x * (Real.cos (x ^ 2) + Real.sin (x ^ 2))) x := by
    convert
      ((Real.hasDerivAt_sin (x ^ 2)).comp x ht).sub
        ((Real.hasDerivAt_cos (x ^ 2)).comp x ht) using 1 <;> ring
  rcases abs_lt.mp hx with ⟨hneg, hpos⟩
  have hne_neg : Real.sin (x ^ 2) - Real.cos (x ^ 2) ≠ -1 :=
    ne_of_gt hneg
  have hne_pos : Real.sin (x ^ 2) - Real.cos (x ^ 2) ≠ 1 :=
    ne_of_lt hpos
  unfold y957 expanded957
  have ha := (Real.hasDerivAt_arccos hne_neg hne_pos).comp x hu
  convert ha using 1 <;> ring

theorem gap5 (x : ℝ)
    (hx : |Real.sin (x ^ 2) - Real.cos (x ^ 2)| < 1) :
    expanded957 x = final957 x := by
  have htrig :
      1 - (Real.sin (x ^ 2) - Real.cos (x ^ 2)) ^ 2 =
        Real.sin (2 * x ^ 2) := by
    rw [Real.sin_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (x ^ 2)]
  unfold expanded957 final957
  rw [htrig]
  ring

theorem gap6 (x : ℝ)
    (hx : |Real.sin (x ^ 2) - Real.cos (x ^ 2)| < 1) :
    HasDerivAt y957 (final957 x) x := by
  rw [← gap5 x hx]
  exact gap4 x hx

end

end ProofGap.Exercise956
