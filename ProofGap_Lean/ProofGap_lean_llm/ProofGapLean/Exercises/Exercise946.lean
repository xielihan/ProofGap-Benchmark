import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace ProofGap.Exercise946

noncomputable section

def y (x : ℝ) : ℝ :=
  (3 - x) / 2 * Real.sqrt (1 - 2 * x - x ^ 2) +
    2 * Real.arcsin ((1 + x) / Real.sqrt 2)

def expandedDerivative (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.sqrt (1 - 2 * x - x ^ 2) -
    (3 - x) / 2 * ((1 + x) / Real.sqrt (1 - 2 * x - x ^ 2)) +
    2 * (1 / (Real.sqrt 2 *
      Real.sqrt (1 - ((1 + x) / Real.sqrt 2) ^ 2)))

def finalDerivative (x : ℝ) : ℝ :=
  x ^ 2 / Real.sqrt (1 - 2 * x - x ^ 2)

private theorem arcsinRadicand_eq (x : ℝ) :
    1 - ((1 + x) / Real.sqrt 2) ^ 2 =
      (1 - 2 * x - x ^ 2) / 2 := by
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [div_pow, hsqrt2_sq]
  ring

theorem gap1 (x : ℝ) (hx : 0 < 1 - 2 * x - x ^ 2) :
    HasDerivAt y (expandedDerivative x) x := by
  unfold y expandedDerivative
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have hinner_pos :
      0 < 1 - ((1 + x) / Real.sqrt 2) ^ 2 := by
    rw [arcsinRadicand_eq]
    nlinarith
  have hsqrtq_ne : Real.sqrt (1 - 2 * x - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hx)
  have hsqrtinner_ne :
      Real.sqrt (1 - ((1 + x) / Real.sqrt 2) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hinner_pos)
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hconst1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x 1
  have hconst2 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 x :=
    hasDerivAt_const x 2
  have hconst3 : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 x :=
    hasDerivAt_const x 3
  have hpoly :
      HasDerivAt (fun t : ℝ => 1 - 2 * t - t ^ 2) (-2 - 2 * x) x := by
    convert ((hconst1.sub (hconst2.mul hid)).sub (hid.pow 2)) using 1 <;>
      ring
  have hlinear :
      HasDerivAt (fun t : ℝ => (3 - t) / 2) (-(1 / 2 : ℝ)) x := by
    convert (hconst3.sub hid).div_const 2 using 1 <;> ring
  have hrpow_condition :
      (1 - 2 * x - x ^ 2 ≠ 0) ∨ (1 : ℝ) ≤ (1 / 2 : ℝ) :=
    Or.inl (ne_of_gt hx)
  have hrpow :
      HasDerivAt (fun z : ℝ => z ^ (1 / 2 : ℝ))
        ((1 / 2 : ℝ) *
          (1 - 2 * x - x ^ 2) ^ ((1 / 2 : ℝ) - 1))
        (1 - 2 * x - x ^ 2) := by
    simpa [mul_comm] using
      (Real.hasDerivAt_rpow_const hrpow_condition)
  have hrpow_coeff :
      (1 / 2 : ℝ) *
          (1 - 2 * x - x ^ 2) ^ ((1 / 2 : ℝ) - 1) =
        1 / (2 * Real.sqrt (1 - 2 * x - x ^ 2)) := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_neg (le_of_lt hx)]
    rw [← Real.sqrt_eq_rpow]
    field_simp [hsqrtq_ne]
  have hsqrt_base :
      HasDerivAt (fun z : ℝ => Real.sqrt z)
        (1 / (2 * Real.sqrt (1 - 2 * x - x ^ 2)))
        (1 - 2 * x - x ^ 2) := by
    rw [← hrpow_coeff]
    simpa only [Real.sqrt_eq_rpow] using hrpow
  have hsqrt :
      HasDerivAt
        (fun t : ℝ => Real.sqrt (1 - 2 * t - t ^ 2))
        (-(1 + x) / Real.sqrt (1 - 2 * x - x ^ 2)) x := by
    convert hsqrt_base.comp x hpoly using 1 <;>
      field_simp [hsqrtq_ne] <;>
      ring
  have hmain :
      HasDerivAt
        (fun t : ℝ =>
          (3 - t) / 2 * Real.sqrt (1 - 2 * t - t ^ 2))
        (-(1 / 2 : ℝ) * Real.sqrt (1 - 2 * x - x ^ 2) -
          (3 - x) / 2 *
            ((1 + x) / Real.sqrt (1 - 2 * x - x ^ 2))) x := by
    convert hlinear.mul hsqrt using 1 <;> ring
  have harg :
      HasDerivAt (fun t : ℝ => (1 + t) / Real.sqrt 2)
        (1 / Real.sqrt 2) x := by
    convert (hconst1.add hid).div_const (Real.sqrt 2) using 1 <;> ring
  have hne_neg_one : (1 + x) / Real.sqrt 2 ≠ -1 := by
    intro h
    rw [h] at hinner_pos
    norm_num at hinner_pos
  have hne_one : (1 + x) / Real.sqrt 2 ≠ 1 := by
    intro h
    rw [h] at hinner_pos
    norm_num at hinner_pos
  have harcsin :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - ((1 + x) / Real.sqrt 2) ^ 2))
        ((1 + x) / Real.sqrt 2) := by
    exact Real.hasDerivAt_arcsin hne_neg_one hne_one
  have harc :
      HasDerivAt
        (fun t : ℝ => 2 * Real.arcsin ((1 + t) / Real.sqrt 2))
        (2 * (1 / (Real.sqrt 2 *
          Real.sqrt (1 - ((1 + x) / Real.sqrt 2) ^ 2)))) x := by
    convert (harcsin.comp x harg).const_mul 2 using 1 <;>
      field_simp [hsqrt2_ne, hsqrtinner_ne] <;>
      ring
  convert hmain.add harc using 1 <;> ring

theorem gap2 (x : ℝ) (hx : 0 < 1 - 2 * x - x ^ 2) :
    expandedDerivative x = finalDerivative x := by
  have hsqrtq_ne : Real.sqrt (1 - 2 * x - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hx)
  have hsqrtq_sq :
      (Real.sqrt (1 - 2 * x - x ^ 2)) ^ 2 = 1 - 2 * x - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hx)
  have hmul :
      Real.sqrt 2 * Real.sqrt (1 - ((1 + x) / Real.sqrt 2) ^ 2) =
        Real.sqrt (1 - 2 * x - x ^ 2) := by
    rw [arcsinRadicand_eq]
    calc
      Real.sqrt 2 * Real.sqrt ((1 - 2 * x - x ^ 2) / 2) =
          Real.sqrt (2 * ((1 - 2 * x - x ^ 2) / 2)) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt (1 - 2 * x - x ^ 2) := by
            congr 1 <;> ring
  unfold expandedDerivative finalDerivative
  rw [hmul]
  field_simp [hsqrtq_ne] <;> nlinarith [hsqrtq_sq]

theorem gap3 (x : ℝ) (hx : 0 < 1 - 2 * x - x ^ 2) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise946
