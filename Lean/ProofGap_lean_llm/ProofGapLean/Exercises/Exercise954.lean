import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace ProofGap.Exercise954

noncomputable section

def root (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 2)

def y (x : ℝ) : ℝ :=
  1 / (4 * Real.sqrt 3) *
      Real.log ((root x - x * Real.sqrt 3) /
        (root x + x * Real.sqrt 3)) +
    (1 / 2 : ℝ) * Real.arctan (root x / x)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (4 * Real.sqrt 3) *
      ((x / root x - Real.sqrt 3) / (root x - x * Real.sqrt 3) -
        (x / root x + Real.sqrt 3) / (root x + x * Real.sqrt 3)) +
    (1 / 2 : ℝ) * (1 / (1 + (x ^ 2 + 2) / x ^ 2)) *
      ((x ^ 2 / root x - root x) / x ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / ((x ^ 4 - 1) * root x)

private lemma root_linear_factors_ne (x : ℝ) (hx : |x| < 1) :
    root x - x * Real.sqrt 3 ≠ 0 ∧
      root x + x * Real.sqrt 3 ≠ 0 := by
  have hxlower : -1 < x := (abs_lt.mp hx).1
  have hxupper : x < 1 := (abs_lt.mp hx).2
  have hone_sub : 0 < 1 - x := by linarith
  have hone_add : 0 < 1 + x := by linarith
  have hx_sq_lt : x ^ 2 < 1 := by
    nlinarith [mul_pos hone_sub hone_add]
  have hrad : 0 < x ^ 2 + 2 := by positivity
  have hr_sq : root x ^ 2 = x ^ 2 + 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt hrad)
  have hs_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqx : (x * Real.sqrt 3) ^ 2 = 3 * x ^ 2 := by
    rw [mul_pow, hs_sq]
    ring
  constructor
  · intro hzero
    have heq : root x = x * Real.sqrt 3 := by linarith
    have hcontra : 3 * x ^ 2 = x ^ 2 + 2 := by
      calc
        3 * x ^ 2 = (x * Real.sqrt 3) ^ 2 := hsqx.symm
        _ = root x ^ 2 := by rw [heq]
        _ = x ^ 2 + 2 := hr_sq
    nlinarith
  · intro hzero
    have heq : root x = -(x * Real.sqrt 3) := by linarith
    have hcontra : 3 * x ^ 2 = x ^ 2 + 2 := by
      calc
        3 * x ^ 2 = (x * Real.sqrt 3) ^ 2 := hsqx.symm
        _ = (-(x * Real.sqrt 3)) ^ 2 := by ring
        _ = root x ^ 2 := by rw [heq]
        _ = x ^ 2 + 2 := hr_sq
    nlinarith

theorem gap1 (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hrad : 0 < x ^ 2 + 2 := by positivity
  have hr_sq : root x ^ 2 = x ^ 2 + 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt hrad)
  have hrpos : 0 < root x := by
    unfold root
    exact Real.sqrt_pos.2 hrad
  have hr0 : root x ≠ 0 := ne_of_gt hrpos
  obtain ⟨hminus, hplus⟩ := root_linear_factors_ne x hx
  have hpoly : HasDerivAt (fun z : ℝ => z ^ 2 + 2) (2 * x) x := by
    simpa using (((hasDerivAt_id x).pow 2).add_const (2 : ℝ))
  have hrootRaw :
      HasDerivAt (fun z : ℝ => Real.sqrt (z ^ 2 + 2))
        (1 / (2 * Real.sqrt (x ^ 2 + 2)) * (2 * x)) x :=
    (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hpoly
  have hroot : HasDerivAt root (x / root x) x := by
    unfold root
    convert hrootRaw using 1
    field_simp [ne_of_gt (Real.sqrt_pos.2 hrad)]
  have hleft :
      HasDerivAt (fun z : ℝ => root z - z * Real.sqrt 3)
        (x / root x - Real.sqrt 3) x := by
    simpa using hroot.sub ((hasDerivAt_id x).mul_const (Real.sqrt 3))
  have hright :
      HasDerivAt (fun z : ℝ => root z + z * Real.sqrt 3)
        (x / root x + Real.sqrt 3) x := by
    simpa using hroot.add ((hasDerivAt_id x).mul_const (Real.sqrt 3))
  have hdiv :
      HasDerivAt
        (fun z : ℝ =>
          (root z - z * Real.sqrt 3) / (root z + z * Real.sqrt 3))
        (((x / root x - Real.sqrt 3) * (root x + x * Real.sqrt 3) -
            (root x - x * Real.sqrt 3) *
              (x / root x + Real.sqrt 3)) /
          (root x + x * Real.sqrt 3) ^ 2) x := by
    simpa using hleft.div hright hplus
  have hlogRaw := hdiv.log (div_ne_zero hminus hplus)
  have hlog :
      HasDerivAt
        (fun z : ℝ => Real.log
          ((root z - z * Real.sqrt 3) / (root z + z * Real.sqrt 3)))
        ((x / root x - Real.sqrt 3) / (root x - x * Real.sqrt 3) -
          (x / root x + Real.sqrt 3) / (root x + x * Real.sqrt 3)) x := by
    convert hlogRaw using 1
    field_simp [hminus, hplus] <;> ring
  have hquot :
      HasDerivAt (fun z : ℝ => root z / z)
        ((x ^ 2 / root x - root x) / x ^ 2) x := by
    convert hroot.div (hasDerivAt_id x) hx0 using 1 <;>
      simp only [id_eq] <;> ring
  have hq_sq :
      (root x / x) ^ 2 = (x ^ 2 + 2) / x ^ 2 := by
    rw [div_pow, hr_sq]
  let q : ℝ → ℝ := fun z => root z / z
  have hquotQ :
      HasDerivAt q ((x ^ 2 / root x - root x) / x ^ 2) x := by
    simpa [q] using hquot
  have hatanRawQ :
      HasDerivAt (fun z : ℝ => Real.arctan (q z))
        (1 / (1 + (q x) ^ 2) *
          ((x ^ 2 / root x - root x) / x ^ 2)) x :=
    (Real.hasDerivAt_arctan (q x)).comp x hquotQ
  have hatanRaw :
      HasDerivAt (fun z : ℝ => Real.arctan (root z / z))
        (1 / (1 + (root x / x) ^ 2) *
          ((x ^ 2 / root x - root x) / x ^ 2)) x := by
    simpa [q] using hatanRawQ
  have hatan :
      HasDerivAt (fun z : ℝ => Real.arctan (root z / z))
        (1 / (1 + (x ^ 2 + 2) / x ^ 2) *
          ((x ^ 2 / root x - root x) / x ^ 2)) x := by
    convert hatanRaw using 1
    rw [hq_sq]
  have htotal :=
    (hlog.const_mul (1 / (4 * Real.sqrt 3))).add
      (hatan.const_mul (1 / 2 : ℝ))
  unfold y
  convert htotal using 1 <;> unfold expandedDerivative <;> ring

theorem gap2 (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hxlower : -1 < x := (abs_lt.mp hx).1
  have hxupper : x < 1 := (abs_lt.mp hx).2
  have hone_sub : 0 < 1 - x := by linarith
  have hone_add : 0 < 1 + x := by linarith
  have hx_sq_lt : x ^ 2 < 1 := by
    nlinarith [mul_pos hone_sub hone_add]
  have hrad : 0 < x ^ 2 + 2 := by positivity
  have hr_sq : root x ^ 2 = x ^ 2 + 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt hrad)
  have hrpos : 0 < root x := by
    unfold root
    exact Real.sqrt_pos.2 hrad
  have hr0 : root x ≠ 0 := ne_of_gt hrpos
  have hs_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := by positivity
  obtain ⟨hminus, hplus⟩ := root_linear_factors_ne x hx
  have hxm1 : x ^ 2 - 1 ≠ 0 := by nlinarith
  have hone : 1 - x ^ 2 ≠ 0 := by nlinarith
  have hxp1 : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
  have hx4lt : x ^ 4 < 1 := by
    have hp : 0 < (1 - x ^ 2) * (1 + x ^ 2) := by
      exact mul_pos (by linarith) (by positivity)
    nlinarith
  have hx4ne : x ^ 4 - 1 ≠ 0 := by nlinarith
  have hAB :
      (root x - x * Real.sqrt 3) * (root x + x * Real.sqrt 3) =
        2 * (1 - x ^ 2) := by
    calc
      (root x - x * Real.sqrt 3) * (root x + x * Real.sqrt 3) =
          root x ^ 2 - (x * Real.sqrt 3) ^ 2 := by ring
      _ = 2 * (1 - x ^ 2) := by
        rw [hr_sq, mul_pow, hs_sq]
        ring
  have hlogNum :
      (x / root x - Real.sqrt 3) * (root x + x * Real.sqrt 3) -
          (x / root x + Real.sqrt 3) * (root x - x * Real.sqrt 3) =
        -4 * Real.sqrt 3 / root x := by
    calc
      (x / root x - Real.sqrt 3) * (root x + x * Real.sqrt 3) -
          (x / root x + Real.sqrt 3) * (root x - x * Real.sqrt 3) =
          2 * Real.sqrt 3 * (x ^ 2 - root x ^ 2) / root x := by
            field_simp [hr0] <;> ring
      _ = -4 * Real.sqrt 3 / root x := by
        rw [hr_sq]
        ring
  have hlogInner :
      (x / root x - Real.sqrt 3) / (root x - x * Real.sqrt 3) -
          (x / root x + Real.sqrt 3) / (root x + x * Real.sqrt 3) =
        2 * Real.sqrt 3 / (root x * (x ^ 2 - 1)) := by
    calc
      (x / root x - Real.sqrt 3) / (root x - x * Real.sqrt 3) -
          (x / root x + Real.sqrt 3) / (root x + x * Real.sqrt 3) =
          ((x / root x - Real.sqrt 3) * (root x + x * Real.sqrt 3) -
            (x / root x + Real.sqrt 3) * (root x - x * Real.sqrt 3)) /
            ((root x - x * Real.sqrt 3) *
              (root x + x * Real.sqrt 3)) := by
                field_simp [hminus, hplus] <;> ring
      _ = (-4 * Real.sqrt 3 / root x) / (2 * (1 - x ^ 2)) := by
        rw [hlogNum, hAB]
      _ = 2 * Real.sqrt 3 / (root x * (x ^ 2 - 1)) := by
        field_simp [hr0, hxm1, hone] <;> ring
  have hlogPart :
      1 / (4 * Real.sqrt 3) *
          ((x / root x - Real.sqrt 3) / (root x - x * Real.sqrt 3) -
            (x / root x + Real.sqrt 3) / (root x + x * Real.sqrt 3)) =
        1 / (2 * root x * (x ^ 2 - 1)) := by
    rw [hlogInner]
    field_simp [hs0, hr0, hxm1] <;> ring
  have hatanNum : x ^ 2 / root x - root x = -2 / root x := by
    calc
      x ^ 2 / root x - root x =
          (x ^ 2 - root x ^ 2) / root x := by
            field_simp [hr0] <;> ring
      _ = -2 / root x := by
        rw [hr_sq]
        ring
  have hatanDen :
      1 + (x ^ 2 + 2) / x ^ 2 =
        2 * (x ^ 2 + 1) / x ^ 2 := by
    field_simp [hx0] <;> ring
  have hatanPart :
      (1 / 2 : ℝ) * (1 / (1 + (x ^ 2 + 2) / x ^ 2)) *
          ((x ^ 2 / root x - root x) / x ^ 2) =
        -1 / (2 * root x * (x ^ 2 + 1)) := by
    rw [hatanNum, hatanDen]
    field_simp [hx0, hr0, hxp1] <;> ring
  unfold expandedDerivative finalDerivative
  rw [hlogPart, hatanPart]
  field_simp [hr0, hxm1, hxp1, hx4ne] <;> ring

theorem gap3 (x : ℝ) (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx hx0]
  exact gap1 x hx hx0

end

end ProofGap.Exercise954
