import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped Interval

namespace ProofGap.Exercise2544

noncomputable section

def speed (t : ℝ) : ℝ :=
  10 * Real.sqrt (1 - 16 / 25 * Real.sin t ^ 2)
def normalizedSpeed (t : ℝ) : ℝ :=
  Real.sqrt (1 - 16 / 25 * Real.sin t ^ 2)
def quarterIntegral : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi / 2, normalizedSpeed t
def perimeter : ℝ := 40 * quarterIntegral
def mesh (i : ℕ) : ℝ := Real.pi * i / 12
def sample (i : ℕ) : ℝ := normalizedSpeed (mesh i)
def roundedQuarter : ℝ :=
  Real.pi / 36 * (1 + 0.6 + 3.913 + 3.293 + 2.539 + 1.833 + 1.442)

private theorem sqrt_twentyFive : Real.sqrt (25 : ℝ) = 5 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

private def upperPoly (y : ℝ) : ℝ :=
  1 - y / 2 - y ^ 2 / 8 - y ^ 3 / 16 - 5 * y ^ 4 / 128 -
    7 * y ^ 5 / 256 - 21 * y ^ 6 / 1024

private def lowerPoly (y : ℝ) : ℝ := upperPoly y - 275 * y ^ 7 / 6144

private theorem lowerPoly_le_sqrt_le_upperPoly (y : ℝ)
    (hy0 : 0 ≤ y) (hyM : y ≤ 16 / 25) :
    lowerPoly y ≤ Real.sqrt (1 - y) ∧ Real.sqrt (1 - y) ≤ upperPoly y := by
  have hy1 : y ≤ 1 := hyM.trans (by norm_num)
  have hbase : 0 ≤ 1 - y := sub_nonneg.mpr hy1
  have hpow2 : y ^ 2 ≤ (16 / 25 : ℝ) ^ 2 := pow_le_pow_left₀ hy0 hyM 2
  have hpow3 : y ^ 3 ≤ (16 / 25 : ℝ) ^ 3 := pow_le_pow_left₀ hy0 hyM 3
  have hpow4 : y ^ 4 ≤ (16 / 25 : ℝ) ^ 4 := pow_le_pow_left₀ hy0 hyM 4
  have hpow5 : y ^ 5 ≤ (16 / 25 : ℝ) ^ 5 := pow_le_pow_left₀ hy0 hyM 5
  have hpow6 : y ^ 6 ≤ (16 / 25 : ℝ) ^ 6 := pow_le_pow_left₀ hy0 hyM 6
  have hpow7 : y ^ 7 ≤ (16 / 25 : ℝ) ^ 7 := pow_le_pow_left₀ hy0 hyM 7
  norm_num at hpow2 hpow3 hpow4 hpow5 hpow6 hpow7
  have hL : 0 ≤ lowerPoly y := by
    unfold lowerPoly upperPoly
    nlinarith
  have hU : 0 ≤ upperPoly y := by
    unfold lowerPoly upperPoly at hL
    unfold upperPoly
    have hy7 : 0 ≤ y ^ 7 := pow_nonneg hy0 7
    nlinarith
  have hsqrtSq : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt hbase
  constructor
  · apply (sq_le_sq₀ hL (Real.sqrt_nonneg _)).mp
    rw [hsqrtSq]
    have hQ :
        75625 * y ^ 7 + 69300 * y ^ 6 + 108276 * y ^ 5 +
          174336 * y ^ 4 + 299904 * y ^ 3 + 599808 * y ^ 2 +
          2069760 * y - 2162688 ≤ 0 := by
      nlinarith
    have hfactor : lowerPoly y ^ 2 - (1 - y) =
        y ^ 7 *
          (75625 * y ^ 7 + 69300 * y ^ 6 + 108276 * y ^ 5 +
            174336 * y ^ 4 + 299904 * y ^ 3 + 599808 * y ^ 2 +
            2069760 * y - 2162688) / 37748736 := by
      unfold lowerPoly upperPoly
      ring
    have hprod : y ^ 7 *
        (75625 * y ^ 7 + 69300 * y ^ 6 + 108276 * y ^ 5 +
          174336 * y ^ 4 + 299904 * y ^ 3 + 599808 * y ^ 2 +
          2069760 * y - 2162688) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hy0 7) hQ
    have hdiff : lowerPoly y ^ 2 - (1 - y) ≤ 0 := by
      rw [hfactor]
      exact div_nonpos_of_nonpos_of_nonneg hprod (by norm_num)
    linarith
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) hU).mp
    rw [hsqrtSq]
    have hfactor : upperPoly y ^ 2 - (1 - y) =
        y ^ 7 *
          (441 * y ^ 5 + 1176 * y ^ 4 + 2464 * y ^ 3 +
            4928 * y ^ 2 + 10560 * y + 33792) / 1048576 := by
      unfold upperPoly
      ring
    have hpoly : 0 ≤
        441 * y ^ 5 + 1176 * y ^ 4 + 2464 * y ^ 3 +
          4928 * y ^ 2 + 10560 * y + 33792 := by positivity
    have hprod : 0 ≤ y ^ 7 *
        (441 * y ^ 5 + 1176 * y ^ 4 + 2464 * y ^ 3 +
          4928 * y ^ 2 + 10560 * y + 33792) :=
      mul_nonneg (pow_nonneg hy0 7) hpoly
    have hdiff : 0 ≤ upperPoly y ^ 2 - (1 - y) := by
      rw [hfactor]
      exact div_nonneg hprod (by norm_num)
    linarith

private theorem integral_sin_pow_add_two (n : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ (n + 2)) =
      ((n + 1 : ℕ) : ℝ) / (n + 2) *
        ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ n := by
  rw [integral_sin_pow]
  simp

private theorem integral_sin_pow_two :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 2) = Real.pi / 4 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 2) =
        (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 0 := by
      convert integral_sin_pow_add_two 0 using 1 <;> norm_num
    _ = Real.pi / 4 := by simp; ring

private theorem integral_sin_pow_four :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 4) = 3 * Real.pi / 16 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 4) =
        (3 / 4 : ℝ) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 2 := by
      convert integral_sin_pow_add_two 2 using 1 <;> norm_num
    _ = 3 * Real.pi / 16 := by rw [integral_sin_pow_two]; ring

private theorem integral_sin_pow_six :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 6) = 5 * Real.pi / 32 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 6) =
        (5 / 6 : ℝ) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 4 := by
      convert integral_sin_pow_add_two 4 using 1 <;> norm_num
    _ = 5 * Real.pi / 32 := by rw [integral_sin_pow_four]; ring

private theorem integral_sin_pow_eight :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 8) = 35 * Real.pi / 256 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 8) =
        (7 / 8 : ℝ) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 6 := by
      convert integral_sin_pow_add_two 6 using 1 <;> norm_num
    _ = 35 * Real.pi / 256 := by rw [integral_sin_pow_six]; ring

private theorem integral_sin_pow_ten :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 10) = 63 * Real.pi / 512 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 10) =
        (9 / 10 : ℝ) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 8 := by
      convert integral_sin_pow_add_two 8 using 1 <;> norm_num
    _ = 63 * Real.pi / 512 := by rw [integral_sin_pow_eight]; ring

private theorem integral_sin_pow_twelve :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 12) = 231 * Real.pi / 2048 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 12) =
        (11 / 12 : ℝ) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 10 := by
      convert integral_sin_pow_add_two 10 using 1 <;> norm_num
    _ = 231 * Real.pi / 2048 := by rw [integral_sin_pow_ten]; ring

private theorem integral_sin_pow_fourteen :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 14) = 429 * Real.pi / 4096 := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 14) =
        (13 / 14 : ℝ) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin t ^ 12 := by
      convert integral_sin_pow_add_two 12 using 1 <;> norm_num
    _ = 429 * Real.pi / 4096 := by rw [integral_sin_pow_twelve]; ring

private theorem integral_sub_continuous {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..Real.pi / 2, (f t - g t)) =
      (∫ t in (0 : ℝ)..Real.pi / 2, f t) -
        ∫ t in (0 : ℝ)..Real.pi / 2, g t :=
  intervalIntegral.integral_sub
    (hf.intervalIntegrable 0 (Real.pi / 2))
    (hg.intervalIntegrable 0 (Real.pi / 2))

private theorem integral_upperPoly :
    (∫ t in (0 : ℝ)..Real.pi / 2,
      upperPoly (16 / 25 * Real.sin t ^ 2)) =
        198449109 / 488281250 * Real.pi := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2,
      upperPoly (16 / 25 * Real.sin t ^ 2)) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          1 - 8 / 25 * Real.sin t ^ 2 -
            32 / 625 * Real.sin t ^ 4 -
            256 / 15625 * Real.sin t ^ 6 -
            512 / 78125 * Real.sin t ^ 8 -
            28672 / 9765625 * Real.sin t ^ 10 -
            344064 / 244140625 * Real.sin t ^ 12 := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold upperPoly
      ring
    _ = 198449109 / 488281250 * Real.pi := by
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      simp only [intervalIntegral.integral_const_mul, integral_sin_pow_two,
        integral_sin_pow_four, integral_sin_pow_six, integral_sin_pow_eight,
        integral_sin_pow_ten, integral_sin_pow_twelve]
      simp
      ring

private theorem integral_lowerPoly :
    (∫ t in (0 : ℝ)..Real.pi / 2,
      lowerPoly (16 / 25 * Real.sin t ^ 2)) =
        198348437 / 488281250 * Real.pi := by
  calc
    (∫ t in (0 : ℝ)..Real.pi / 2,
      lowerPoly (16 / 25 * Real.sin t ^ 2)) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          (1 - 8 / 25 * Real.sin t ^ 2 -
            32 / 625 * Real.sin t ^ 4 -
            256 / 15625 * Real.sin t ^ 6 -
            512 / 78125 * Real.sin t ^ 8 -
            28672 / 9765625 * Real.sin t ^ 10 -
            344064 / 244140625 * Real.sin t ^ 12) -
            1441792 / 732421875 * Real.sin t ^ 14 := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold lowerPoly upperPoly
      ring
    _ = 198348437 / 488281250 * Real.pi := by
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      rw [integral_sub_continuous (by fun_prop) (by fun_prop)]
      simp only [intervalIntegral.integral_const_mul, integral_sin_pow_two,
        integral_sin_pow_four, integral_sin_pow_six, integral_sin_pow_eight,
        integral_sin_pow_ten, integral_sin_pow_twelve, integral_sin_pow_fourteen]
      simp
      ring

private theorem quarterIntegral_bounds :
    198348437 / 488281250 * Real.pi ≤ quarterIntegral ∧
      quarterIntegral ≤ 198449109 / 488281250 * Real.pi := by
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hLowerCont : Continuous (fun t : ℝ =>
      lowerPoly (16 / 25 * Real.sin t ^ 2)) := by
    unfold lowerPoly upperPoly
    fun_prop
  have hSpeedCont : Continuous normalizedSpeed := by
    unfold normalizedSpeed
    fun_prop
  have hUpperCont : Continuous (fun t : ℝ =>
      upperPoly (16 / 25 * Real.sin t ^ 2)) := by
    unfold upperPoly
    fun_prop
  have hLowerInt : IntervalIntegrable
      (fun t : ℝ => lowerPoly (16 / 25 * Real.sin t ^ 2)) volume 0 (Real.pi / 2) :=
    hLowerCont.intervalIntegrable 0 (Real.pi / 2)
  have hSpeedInt : IntervalIntegrable normalizedSpeed volume 0 (Real.pi / 2) :=
    hSpeedCont.intervalIntegrable 0 (Real.pi / 2)
  have hUpperInt : IntervalIntegrable
      (fun t : ℝ => upperPoly (16 / 25 * Real.sin t ^ 2)) volume 0 (Real.pi / 2) :=
    hUpperCont.intervalIntegrable 0 (Real.pi / 2)
  have hLower :
      (∫ t in (0 : ℝ)..Real.pi / 2,
        lowerPoly (16 / 25 * Real.sin t ^ 2)) ≤
          ∫ t in (0 : ℝ)..Real.pi / 2, normalizedSpeed t := by
    apply intervalIntegral.integral_mono_on hab hLowerInt hSpeedInt
    intro t ht
    have hy0 : 0 ≤ (16 / 25 : ℝ) * Real.sin t ^ 2 := by positivity
    have hcoef : (0 : ℝ) ≤ 16 / 25 := by norm_num
    have hyM : (16 / 25 : ℝ) * Real.sin t ^ 2 ≤ 16 / 25 := by
      simpa using mul_le_mul_of_nonneg_left (Real.sin_sq_le_one t) hcoef
    simpa [normalizedSpeed] using
      (lowerPoly_le_sqrt_le_upperPoly
        ((16 / 25 : ℝ) * Real.sin t ^ 2) hy0 hyM).1
  have hUpper :
      (∫ t in (0 : ℝ)..Real.pi / 2, normalizedSpeed t) ≤
        ∫ t in (0 : ℝ)..Real.pi / 2,
          upperPoly (16 / 25 * Real.sin t ^ 2) := by
    apply intervalIntegral.integral_mono_on hab hSpeedInt hUpperInt
    intro t ht
    have hy0 : 0 ≤ (16 / 25 : ℝ) * Real.sin t ^ 2 := by positivity
    have hcoef : (0 : ℝ) ≤ 16 / 25 := by norm_num
    have hyM : (16 / 25 : ℝ) * Real.sin t ^ 2 ≤ 16 / 25 := by
      simpa using mul_le_mul_of_nonneg_left (Real.sin_sq_le_one t) hcoef
    simpa [normalizedSpeed] using
      (lowerPoly_le_sqrt_le_upperPoly
        ((16 / 25 : ℝ) * Real.sin t ^ 2) hy0 hyM).2
  rw [integral_lowerPoly] at hLower
  rw [integral_upperPoly] at hUpper
  simpa [quarterIntegral] using And.intro hLower hUpper

theorem gap1 (t : ℝ) : speed t = 10 * normalizedSpeed t := by rfl
theorem gap2 (t : ℝ) :
    speed t = 10 * Real.sqrt (1 - 16 / 25 * Real.sin t ^ 2) := by rfl
theorem gap3 (t : ℝ) : speed t = 10 * normalizedSpeed t := by rfl
theorem gap4 : perimeter = 4 * ∫ t in (0 : ℝ)..Real.pi / 2, speed t := by
  unfold perimeter quarterIntegral speed normalizedSpeed
  rw [intervalIntegral.integral_const_mul]
  ring
theorem gap5 :
    4 * (∫ t in (0 : ℝ)..Real.pi / 2, speed t) =
      40 * quarterIntegral := by
  unfold speed quarterIntegral normalizedSpeed
  rw [intervalIntegral.integral_const_mul]
  ring
theorem gap6 : perimeter = 40 * quarterIntegral := by rfl
theorem gap7 : ∃ h : ℝ, h = Real.pi / 12 := by
  exact ⟨Real.pi / 12, rfl⟩
theorem gap8 :
    Real.sin (Real.pi / 12) ^ 2 = (2 - Real.sqrt 3) / 4 := by
  rw [← show Real.pi / 3 - Real.pi / 4 = Real.pi / 12 by ring, Real.sin_sub,
    Real.sin_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_three,
    Real.sin_pi_div_four]
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith
theorem gap9 :
    Real.sin (5 * Real.pi / 12) ^ 2 = (2 + Real.sqrt 3) / 4 := by
  rw [← show Real.pi / 6 + Real.pi / 4 = 5 * Real.pi / 12 by ring, Real.sin_add,
    Real.sin_pi_div_six, Real.cos_pi_div_four, Real.cos_pi_div_six,
    Real.sin_pi_div_four]
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith
theorem gap10 : mesh 0 = 0 := by
  simp [mesh]
theorem gap11 : sample 0 = 1 := by
  norm_num [sample, mesh, normalizedSpeed]
theorem gap12 : mesh 1 = Real.pi / 12 := by
  norm_num [mesh]
theorem gap13 :
    4 * sample 1 =
      4 * Real.sqrt (1 - 16 / 25 * (1 / 4) * (2 - Real.sqrt 3)) := by
  unfold sample normalizedSpeed
  rw [gap12, gap8]
  congr 2
  ring
theorem gap14 :
    |4 * Real.sqrt (1 - 16 / 25 * (1 / 4) * (2 - Real.sqrt 3)) -
      3.913| < 0.001 := by
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs3lo : (173 / 100 : ℝ) < Real.sqrt 3 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  have hs3hi : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hq : 0 ≤ (1 - 4 / 25 * (2 - Real.sqrt 3) : ℝ) := by
    norm_num
    nlinarith
  have hzlo : (489 / 500 : ℝ) < Real.sqrt (1 - 4 / 25 * (2 - Real.sqrt 3)) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hzhi : Real.sqrt (1 - 4 / 25 * (2 - Real.sqrt 3)) < (1957 / 2000 : ℝ) := by
    apply (Real.sqrt_lt' (by norm_num)).2
    nlinarith
  rw [abs_lt]
  constructor <;> norm_num <;> linarith
theorem gap15 : mesh 2 = Real.pi / 6 := by
  norm_num [mesh]
  ring
theorem gap16 :
    2 * sample 2 = 2 * Real.sqrt (1 - 16 / 25 * (1 / 4)) := by
  unfold sample normalizedSpeed
  rw [gap15, Real.sin_pi_div_six]
  congr 2
  ring
theorem gap17 :
    |2 * Real.sqrt (1 - 16 / 25 * (1 / 4)) - 1.833| < 0.001 := by
  have hz : (Real.sqrt (21 : ℝ)) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hznonneg := Real.sqrt_nonneg (21 : ℝ)
  rw [abs_lt]
  constructor <;> norm_num [sqrt_twentyFive] <;> nlinarith
theorem gap18 : mesh 3 = Real.pi / 4 := by
  norm_num [mesh]
  ring
theorem gap19 :
    4 * sample 3 = 4 * Real.sqrt (1 - 16 / 25 * (1 / 2)) := by
  unfold sample normalizedSpeed
  rw [gap18, Real.sin_pi_div_four]
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  congr 2
  nlinarith
theorem gap20 :
    |4 * Real.sqrt (1 - 16 / 25 * (1 / 2)) - 3.298| < 0.001 := by
  have hz : (Real.sqrt (17 : ℝ)) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hznonneg := Real.sqrt_nonneg (17 : ℝ)
  rw [abs_lt]
  constructor <;> norm_num [sqrt_twentyFive] <;> nlinarith
theorem gap21 : mesh 4 = Real.pi / 3 := by
  norm_num [mesh]
  ring
theorem gap22 :
    2 * sample 4 = 2 * Real.sqrt (1 - 16 / 25 * (3 / 4)) := by
  unfold sample normalizedSpeed
  rw [gap21, Real.sq_sin_pi_div_three]
theorem gap23 :
    |2 * Real.sqrt (1 - 16 / 25 * (3 / 4)) - 1.442| < 0.001 := by
  have hz : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hznonneg := Real.sqrt_nonneg (13 : ℝ)
  rw [abs_lt]
  constructor <;> norm_num [sqrt_twentyFive] <;> nlinarith
theorem gap24 : mesh 5 = 5 * Real.pi / 12 := by
  norm_num [mesh]
  ring
theorem gap25 :
    4 * sample 5 =
      4 * Real.sqrt (1 - 16 / 25 * (1 / 4) * (2 + Real.sqrt 3)) := by
  unfold sample normalizedSpeed
  rw [gap24, gap9]
  congr 2
  ring
theorem gap26 :
    |4 * Real.sqrt (1 - 16 / 25 * (1 / 4) * (2 + Real.sqrt 3)) -
      2.539| < 0.001 := by
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs3lo : (173 / 100 : ℝ) < Real.sqrt 3 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  have hs3hi : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hq : 0 ≤ (1 - 4 / 25 * (2 + Real.sqrt 3) : ℝ) := by
    norm_num
    nlinarith
  have hzlo : (1269 / 2000 : ℝ) < Real.sqrt (1 - 4 / 25 * (2 + Real.sqrt 3)) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hzhi : Real.sqrt (1 - 4 / 25 * (2 + Real.sqrt 3)) < (127 / 200 : ℝ) := by
    apply (Real.sqrt_lt' (by norm_num)).2
    nlinarith
  rw [abs_lt]
  constructor <;> norm_num <;> linarith
theorem gap27 : mesh 6 = Real.pi / 2 := by
  norm_num [mesh]
  ring
theorem gap28 : sample 6 = Real.sqrt (1 - 16 / 25) := by
  unfold sample normalizedSpeed
  rw [gap27, Real.sin_pi_div_two]
  ring_nf
theorem gap29 : Real.sqrt (1 - 16 / 25) = 0.6 := by
  have h9 : Real.sqrt (9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have h25 : Real.sqrt (25 : ℝ) = 5 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [h9, h25]
theorem gap30 : |quarterIntegral - roundedQuarter| < 0.001 := by
  rcases quarterIntegral_bounds with ⟨hLower, hUpper⟩
  rw [abs_lt]
  constructor
  · unfold roundedQuarter
    norm_num
    nlinarith [Real.pi_pos]
  · unfold roundedQuarter
    norm_num
    nlinarith [Real.pi_lt_d2]
theorem gap31 : |roundedQuarter - 1.276| < 0.001 := by
  rw [abs_lt]
  unfold roundedQuarter
  norm_num
  constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4]
theorem gap32 : |quarterIntegral - 1.276| < 0.001 := by
  rcases quarterIntegral_bounds with ⟨hLower, hUpper⟩
  rw [abs_lt]
  norm_num
  constructor
  · nlinarith [Real.pi_gt_d4]
  · nlinarith [Real.pi_lt_d4]
theorem gap33 : perimeter = 40 * quarterIntegral := by rfl
theorem gap34 : |40 * quarterIntegral - 40 * 1.276| < 0.04 := by
  have h := gap32
  rw [abs_lt] at h ⊢
  norm_num at h ⊢
  constructor <;> nlinarith [h.1, h.2]
theorem gap35 : (40 * 1.276 : ℝ) = 51.04 := by norm_num
theorem gap36 : |perimeter - 51.04| < 0.04 := by
  rw [gap33, ← gap35]
  exact gap34

end

end ProofGap.Exercise2544
