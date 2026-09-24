import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2421
noncomputable section

open scoped Interval

def csc (x : ℝ) : ℝ := 1 / Real.sin x
def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def area (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ φ in Real.pi / 4..Real.pi / 2,
      p ^ 2 / (1 - Real.cos φ) ^ 2

def antiderivative (p u : ℝ) : ℝ :=
  -(p ^ 2 / 4) * (cot u + (1 / 3 : ℝ) * cot u ^ 3)

theorem gap1 (p : ℝ) :
    area p =
      (1 / 2 : ℝ) *
        ∫ φ in Real.pi / 4..Real.pi / 2,
          p ^ 2 / (1 - Real.cos φ) ^ 2 := by
  rfl

theorem gap2 (p : ℝ) :
    (1 / 2 : ℝ) *
        (∫ φ in Real.pi / 4..Real.pi / 2,
          p ^ 2 / (1 - Real.cos φ) ^ 2) =
      p ^ 2 / 4 *
        ∫ u in Real.pi / 8..Real.pi / 4, csc u ^ 4 := by
  let f : ℝ → ℝ := fun φ => p ^ 2 / (1 - Real.cos φ) ^ 2
  have hpoint (u : ℝ) :
      f (2 * u) = p ^ 2 / 4 * csc u ^ 4 := by
    have htrig : 1 - Real.cos (2 * u) = 2 * Real.sin u ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq u]
    dsimp [f]
    rw [htrig]
    unfold csc
    by_cases hs : Real.sin u = 0
    · simp [hs]
    · field_simp [hs]
      <;> ring
  have hscale :
      (∫ u in Real.pi / 8..Real.pi / 4, f (2 * u)) =
        (1 / 2 : ℝ) * ∫ φ in Real.pi / 4..Real.pi / 2, f φ := by
    have h := intervalIntegral.integral_comp_mul_left
      (f := f) (a := Real.pi / 8) (b := Real.pi / 4)
      (c := (2 : ℝ)) (by norm_num)
    norm_num [smul_eq_mul] at h ⊢
    convert h using 1 <;> ring
  change (1 / 2 : ℝ) * (∫ φ in Real.pi / 4..Real.pi / 2, f φ) = _
  calc
    (1 / 2 : ℝ) * (∫ φ in Real.pi / 4..Real.pi / 2, f φ) =
        ∫ u in Real.pi / 8..Real.pi / 4, f (2 * u) := hscale.symm
    _ = ∫ u in Real.pi / 8..Real.pi / 4, p ^ 2 / 4 * csc u ^ 4 := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hpoint u
    _ = p ^ 2 / 4 * ∫ u in Real.pi / 8..Real.pi / 4, csc u ^ 4 := by
      simp only [intervalIntegral.integral_const_mul, smul_eq_mul]

theorem gap3 (p : ℝ) :
    area p =
      p ^ 2 / 4 * ∫ u in Real.pi / 8..Real.pi / 4, csc u ^ 4 := by
  rw [gap1 p, gap2 p]

theorem gap4 (p : ℝ) :
    p ^ 2 / 4 * (∫ u in Real.pi / 8..Real.pi / 4, csc u ^ 4) =
      antiderivative p (Real.pi / 4) -
        antiderivative p (Real.pi / 8) := by
  have hab : Real.pi / 8 ≤ Real.pi / 4 := by
    nlinarith [Real.pi_pos]
  have hsin_ne (u : ℝ)
      (hu : u ∈ Set.uIcc (Real.pi / 8) (Real.pi / 4)) :
      Real.sin u ≠ 0 := by
    rw [Set.uIcc_of_le hab] at hu
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos, hu.1]
    · nlinarith [Real.pi_pos, hu.2]
  have hcsc : ContinuousOn csc (Set.uIcc (Real.pi / 8) (Real.pi / 4)) := by
    unfold csc
    exact continuousOn_const.div Real.continuous_sin.continuousOn hsin_ne
  have hcont : ContinuousOn
      (fun u => p ^ 2 / 4 * csc u ^ 4)
      (Set.uIcc (Real.pi / 8) (Real.pi / 4)) := by
    exact continuousOn_const.mul (hcsc.pow 4)
  have hderiv (u : ℝ)
      (hu : u ∈ Set.uIcc (Real.pi / 8) (Real.pi / 4)) :
      HasDerivAt (antiderivative p) (p ^ 2 / 4 * csc u ^ 4) u := by
    have hs : Real.sin u ≠ 0 := hsin_ne u hu
    have hcot : HasDerivAt cot (-(csc u ^ 2)) u := by
      unfold cot
      convert (Real.hasDerivAt_cos u).div (Real.hasDerivAt_sin u) hs using 1
      unfold csc
      field_simp [hs]
      nlinarith [Real.sin_sq_add_cos_sq u]
    have hid : csc u ^ 2 = 1 + cot u ^ 2 := by
      unfold csc cot
      field_simp [hs]
      nlinarith [Real.sin_sq_add_cos_sq u]
    have hid4 : csc u ^ 4 = (1 + cot u ^ 2) ^ 2 := by
      calc
        csc u ^ 4 = (csc u ^ 2) ^ 2 := by ring
        _ = (1 + cot u ^ 2) ^ 2 := by rw [hid]
    have hout :=
      (hcot.add ((hcot.pow 3).const_mul (1 / 3 : ℝ))).const_mul
        (-(p ^ 2 / 4))
    simpa only [antiderivative] using
      hout.congr_deriv (by rw [hid4, hid]; ring)
  have hfund :
      (∫ u in Real.pi / 8..Real.pi / 4, p ^ 2 / 4 * csc u ^ 4) =
        antiderivative p (Real.pi / 4) -
          antiderivative p (Real.pi / 8) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable
  calc
    p ^ 2 / 4 * (∫ u in Real.pi / 8..Real.pi / 4, csc u ^ 4) =
        ∫ u in Real.pi / 8..Real.pi / 4, p ^ 2 / 4 * csc u ^ 4 := by
      symm
      simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
    _ = antiderivative p (Real.pi / 4) -
        antiderivative p (Real.pi / 8) := hfund

theorem gap5 (p : ℝ) :
    antiderivative p (Real.pi / 4) -
        antiderivative p (Real.pi / 8) =
      p ^ 2 / 6 * (4 * Real.sqrt 2 + 3) := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by
    norm_num
  have hcot4 : cot (Real.pi / 4) = 1 := by
    rw [cot, Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp [hsqrt_ne]
  have hcot8 : cot (Real.pi / 8) = Real.sqrt 2 + 1 := by
    let x : ℝ := Real.pi / 8
    have hxpos : 0 < x := by
      dsimp [x]
      nlinarith [Real.pi_pos]
    have hxlt : x < Real.pi := by
      dsimp [x]
      nlinarith [Real.pi_pos]
    have hsinpos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hxpos hxlt
    have hcospos : 0 < Real.cos x := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> dsimp [x] <;> nlinarith [Real.pi_pos]
    have hangle : 2 * x = Real.pi / 4 := by
      dsimp [x]
      ring
    have hprod :
        2 * Real.sin x * Real.cos x = Real.sqrt 2 / 2 := by
      calc
        2 * Real.sin x * Real.cos x = Real.sin (2 * x) := by
          rw [Real.sin_two_mul]
        _ = Real.sin (Real.pi / 4) := by rw [hangle]
        _ = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have hcos2 := Real.cos_two_mul x
    rw [hangle, Real.cos_pi_div_four] at hcos2
    have hdiff :
        Real.cos x ^ 2 - Real.sin x ^ 2 = Real.sqrt 2 / 2 := by
      nlinarith [hcos2, Real.sin_sq_add_cos_sq x]
    have hrel :
        Real.cos x ^ 2 - Real.sin x ^ 2 =
          2 * Real.sin x * Real.cos x := by
      nlinarith [hdiff, hprod]
    have hcs : Real.sin x < Real.cos x := by
      nlinarith [hdiff, hsinpos, hcospos, hsqrt_pos]
    have hsq1 :
        (Real.cos x - Real.sin x) ^ 2 = 2 * Real.sin x ^ 2 := by
      nlinarith [hrel]
    have hsq2 :
        (Real.sqrt 2 * Real.sin x) ^ 2 = 2 * Real.sin x ^ 2 := by
      calc
        (Real.sqrt 2 * Real.sin x) ^ 2 =
            Real.sqrt 2 ^ 2 * Real.sin x ^ 2 := by ring
        _ = 2 * Real.sin x ^ 2 := by rw [hsqrt_sq]
    have hroot :
        Real.cos x - Real.sin x = Real.sqrt 2 * Real.sin x := by
      nlinarith [hsq1, hsq2, hcs, hsqrt_pos, hsinpos]
    change Real.cos x / Real.sin x = Real.sqrt 2 + 1
    apply (div_eq_iff (ne_of_gt hsinpos)).2
    nlinarith [hroot]
  have hsqrt_cube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt_sq]
  have hcube :
      (Real.sqrt 2 + 1) ^ 3 = 7 + 5 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2 + 1) ^ 3 =
          Real.sqrt 2 ^ 3 + 3 * Real.sqrt 2 ^ 2 +
            3 * Real.sqrt 2 + 1 := by ring
      _ = 7 + 5 * Real.sqrt 2 := by rw [hsqrt_cube, hsqrt_sq]; ring
  rw [antiderivative, antiderivative, hcot4, hcot8, hcube]
  ring

theorem gap6 (p : ℝ) :
    area p = p ^ 2 / 6 * (4 * Real.sqrt 2 + 3) := by
  rw [gap3 p, gap4 p, gap5 p]

end
end ProofGap.Exercise2421
