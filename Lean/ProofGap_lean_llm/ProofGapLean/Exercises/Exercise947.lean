import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise947

noncomputable section

def fourthRoot (t : ℝ) : ℝ := Real.rpow t (1 / 4 : ℝ)

def y (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
      Real.log ((fourthRoot (1 + x ^ 4) + x) /
        (fourthRoot (1 + x ^ 4) - x)) -
    (1 / 2 : ℝ) * Real.arctan (fourthRoot (1 + x ^ 4) / x)

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
      ((1 + x ^ 3 / fourthRoot ((1 + x ^ 4) ^ 3)) /
          (fourthRoot (1 + x ^ 4) + x) -
        (x ^ 3 / fourthRoot ((1 + x ^ 4) ^ 3) - 1) /
          (fourthRoot (1 + x ^ 4) - x)) -
    (1 / 2 : ℝ) *
      (1 / (1 + (fourthRoot (1 + x ^ 4) / x) ^ 2)) *
      ((x ^ 4 / fourthRoot ((1 + x ^ 4) ^ 3) -
          fourthRoot (1 + x ^ 4)) / x ^ 2)

def finalDerivative (x : ℝ) : ℝ := 1 / fourthRoot (1 + x ^ 4)

private lemma fourthRoot_facts (x : ℝ) :
    0 < fourthRoot (1 + x ^ 4) ∧
      fourthRoot (1 + x ^ 4) ^ 4 = 1 + x ^ 4 ∧
      0 < fourthRoot ((1 + x ^ 4) ^ 3) ∧
      fourthRoot ((1 + x ^ 4) ^ 3) =
        fourthRoot (1 + x ^ 4) ^ 3 := by
  have ha : 0 < 1 + x ^ 4 := by positivity
  have ha3 : 0 < (1 + x ^ 4) ^ 3 := by positivity
  have hrpos : 0 < fourthRoot (1 + x ^ 4) := by
    unfold fourthRoot
    exact Real.rpow_pos_of_pos ha _
  have hspos : 0 < fourthRoot ((1 + x ^ 4) ^ 3) := by
    unfold fourthRoot
    exact Real.rpow_pos_of_pos ha3 _
  have hr4 : fourthRoot (1 + x ^ 4) ^ 4 = 1 + x ^ 4 := by
    unfold fourthRoot
    calc
      Real.rpow (1 + x ^ 4) (1 / 4 : ℝ) ^ 4 =
          Real.rpow (Real.rpow (1 + x ^ 4) (1 / 4 : ℝ)) (4 : ℝ) := by
            exact (Real.rpow_natCast _ 4).symm
      _ = Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) * 4) := by
            exact (Real.rpow_mul (le_of_lt ha) _ _).symm
      _ = 1 + x ^ 4 := by norm_num
  have hcube :
      fourthRoot ((1 + x ^ 4) ^ 3) =
        fourthRoot (1 + x ^ 4) ^ 3 := by
    unfold fourthRoot
    calc
      Real.rpow ((1 + x ^ 4) ^ 3) (1 / 4 : ℝ) =
          Real.rpow (Real.rpow (1 + x ^ 4) (3 : ℝ)) (1 / 4 : ℝ) := by
            congr 1
            exact (Real.rpow_natCast _ 3).symm
      _ = Real.rpow (1 + x ^ 4) ((3 : ℝ) * (1 / 4 : ℝ)) := by
            exact (Real.rpow_mul (le_of_lt ha) _ _).symm
      _ = Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) * 3) := by
            congr 1
            ring
      _ = Real.rpow (Real.rpow (1 + x ^ 4) (1 / 4 : ℝ)) (3 : ℝ) := by
            exact Real.rpow_mul (le_of_lt ha) _ _
      _ = Real.rpow (1 + x ^ 4) (1 / 4 : ℝ) ^ 3 := by
            exact Real.rpow_natCast _ 3
  exact ⟨hrpos, hr4, hspos, hcube⟩

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  rcases fourthRoot_facts x with ⟨hrpos, hr4, hspos, hcube⟩
  have ha : 0 < 1 + x ^ 4 := by positivity
  have hquarter3 :
      Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) * 3) =
        fourthRoot ((1 + x ^ 4) ^ 3) := by
    calc
      Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) * 3) =
          Real.rpow (Real.rpow (1 + x ^ 4) (1 / 4 : ℝ)) (3 : ℝ) := by
            exact Real.rpow_mul (le_of_lt ha) _ _
      _ = Real.rpow (1 + x ^ 4) (1 / 4 : ℝ) ^ 3 := by
            exact Real.rpow_natCast _ 3
      _ = fourthRoot ((1 + x ^ 4) ^ 3) := by
            simpa [fourthRoot] using hcube.symm
  have hneg :
      Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) - 1) =
        1 / fourthRoot ((1 + x ^ 4) ^ 3) := by
    calc
      Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) - 1) =
          Real.rpow (1 + x ^ 4) (-((1 / 4 : ℝ) * 3)) := by
            congr 1
            norm_num
      _ = (Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) * 3))⁻¹ := by
            exact Real.rpow_neg (le_of_lt ha) ((1 / 4 : ℝ) * 3)
      _ = 1 / fourthRoot ((1 + x ^ 4) ^ 3) := by
            rw [hquarter3]
            simp [one_div]
  have hbase :
      HasDerivAt (fun z : ℝ => 1 + z ^ 4) (4 * x ^ 3) x := by
    convert ((hasDerivAt_id x).pow 4).const_add 1 using 1 <;>
      simp only [id_eq] <;> ring
  have hpow :
      HasDerivAt (fun t : ℝ => Real.rpow t (1 / 4 : ℝ))
        ((1 / 4 : ℝ) * Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) - 1))
        (1 + x ^ 4) := by
    simpa using
      (Real.hasDerivAt_rpow_const
        (x := 1 + x ^ 4) (p := (1 / 4 : ℝ))
        (Or.inl (ne_of_gt ha)))
  have hcoeff :
      ((1 / 4 : ℝ) * Real.rpow (1 + x ^ 4) ((1 / 4 : ℝ) - 1)) *
          (4 * x ^ 3) =
        x ^ 3 / fourthRoot ((1 + x ^ 4) ^ 3) := by
    rw [hneg]
    ring
  have hroot :
      HasDerivAt (fun z : ℝ => fourthRoot (1 + z ^ 4))
        (x ^ 3 / fourthRoot ((1 + x ^ 4) ^ 3)) x := by
    convert hpow.comp x hbase using 1
    exact hcoeff.symm
  have hp : fourthRoot (1 + x ^ 4) + x ≠ 0 := by
    intro h
    have heq : fourthRoot (1 + x ^ 4) = -x := by linarith
    have hp4 : fourthRoot (1 + x ^ 4) ^ 4 = x ^ 4 := by
      rw [heq]
      ring
    nlinarith [hr4]
  have hm : fourthRoot (1 + x ^ 4) - x ≠ 0 := by
    intro h
    have heq : fourthRoot (1 + x ^ 4) = x := by linarith
    rw [heq] at hr4
    nlinarith [hr4]
  have hplus := hroot.add (hasDerivAt_id x)
  have hminus := hroot.sub (hasDerivAt_id x)
  have hquot := hplus.div hminus hm
  have hq :
      (fourthRoot (1 + x ^ 4) + x) /
          (fourthRoot (1 + x ^ 4) - x) ≠ 0 :=
    div_ne_zero hp hm
  have hlog := (Real.hasDerivAt_log hq).comp x hquot
  have hlog' :
      HasDerivAt
        (fun z : ℝ =>
          Real.log ((fourthRoot (1 + z ^ 4) + z) /
            (fourthRoot (1 + z ^ 4) - z)))
        ((1 + x ^ 3 / fourthRoot ((1 + x ^ 4) ^ 3)) /
            (fourthRoot (1 + x ^ 4) + x) -
          (x ^ 3 / fourthRoot ((1 + x ^ 4) ^ 3) - 1) /
            (fourthRoot (1 + x ^ 4) - x)) x := by
    convert hlog using 1 <;>
      simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply,
        Pi.div_apply, id_eq]
    field_simp [hp, hm, ne_of_gt hspos] <;> ring
  have hratio :
      HasDerivAt (fun z : ℝ => fourthRoot (1 + z ^ 4) / z)
        ((x ^ 3 / fourthRoot ((1 + x ^ 4) ^ 3) * x -
            fourthRoot (1 + x ^ 4)) / x ^ 2) x := by
    simpa only [id_eq, mul_one] using
      hroot.div (hasDerivAt_id x) hx
  have hatan := hratio.arctan
  have hatan' :
      HasDerivAt
        (fun z : ℝ => Real.arctan (fourthRoot (1 + z ^ 4) / z))
        ((1 / (1 + (fourthRoot (1 + x ^ 4) / x) ^ 2)) *
          ((x ^ 4 / fourthRoot ((1 + x ^ 4) ^ 3) -
            fourthRoot (1 + x ^ 4)) / x ^ 2)) x := by
    convert hatan using 1 <;> ring
  unfold y expandedDerivative
  simpa only [Pi.sub_apply, mul_assoc] using
    (hlog'.const_mul (1 / 4 : ℝ)).sub
      (hatan'.const_mul (1 / 2 : ℝ))

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  rcases fourthRoot_facts x with ⟨hrpos, hr4, hspos, hcube⟩
  have hp : fourthRoot (1 + x ^ 4) + x ≠ 0 := by
    intro h
    have heq : fourthRoot (1 + x ^ 4) = -x := by linarith
    have hp4 : fourthRoot (1 + x ^ 4) ^ 4 = x ^ 4 := by
      rw [heq]
      ring
    nlinarith [hr4]
  have hm : fourthRoot (1 + x ^ 4) - x ≠ 0 := by
    intro h
    have heq : fourthRoot (1 + x ^ 4) = x := by linarith
    rw [heq] at hr4
    nlinarith [hr4]
  have hden :
      1 + (fourthRoot (1 + x ^ 4) / x) ^ 2 ≠ 0 := by
    positivity
  have hsum :
      x ^ 2 + fourthRoot (1 + x ^ 4) ^ 2 ≠ 0 := by
    positivity
  unfold expandedDerivative finalDerivative
  rw [hcube]
  field_simp [hx, hp, hm, ne_of_gt hrpos, hden, hsum] <;>
    nlinarith [hr4]

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise947
