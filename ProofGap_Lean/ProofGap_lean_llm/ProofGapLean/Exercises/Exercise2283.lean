import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

open scoped Interval

namespace ProofGap.Exercise2283

noncomputable section

def I (n : ℕ) : ℝ :=
  ∫ x in 0..Real.pi / 4, Real.tan x ^ (2 * n)

def partialAlternating (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (-1 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ)

def unrolled (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (I 0 - partialAlternating n)

private theorem cos_ne_zero_of_mem_uIcc (x : ℝ)
    (hx : x ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
    Real.cos x ≠ 0 := by
  have hle : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  rw [Set.uIcc_of_le hle] at hx
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [hx.1, Real.pi_pos]
  · nlinarith [hx.2, Real.pi_pos]

theorem gap1 (n : ℕ) (hn : 0 < n) :
    I n =
      ∫ x in 0..Real.pi / 4,
        Real.tan x ^ (2 * n - 2) *
          ((1 / Real.cos x) ^ 2 - 1) := by
  unfold I
  apply intervalIntegral.integral_congr
  intro x hx
  have hcos : Real.cos x ≠ 0 :=
    cos_ne_zero_of_mem_uIcc x hx
  have htrig :
      Real.tan x ^ 2 = (1 / Real.cos x) ^ 2 - 1 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos] <;> nlinarith [Real.sin_sq_add_cos_sq x]
  have hexp : 2 * n - 2 + 2 = 2 * n := by omega
  calc
    Real.tan x ^ (2 * n) = Real.tan x ^ (2 * n - 2 + 2) := by rw [hexp]
    _ = Real.tan x ^ (2 * n - 2) * Real.tan x ^ 2 := by rw [pow_add]
    _ = Real.tan x ^ (2 * n - 2) * ((1 / Real.cos x) ^ 2 - 1) := by rw [htrig]

theorem gap2 (n : ℕ) (hn : 0 < n) :
    (∫ x in 0..Real.pi / 4,
        Real.tan x ^ (2 * n - 2) * ((1 / Real.cos x) ^ 2 - 1)) =
      (∫ x in 0..Real.pi / 4,
          Real.tan x ^ (2 * n - 2) * deriv Real.tan x) -
        I (n - 1) := by
  have hderiv (x : ℝ)
      (hx : x ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
      deriv Real.tan x = (1 / Real.cos x) ^ 2 := by
    simpa [div_pow] using
      (Real.hasDerivAt_tan (x := x) (cos_ne_zero_of_mem_uIcc x hx)).deriv
  have htan_cont :
      ContinuousOn Real.tan (Set.uIcc (0 : ℝ) (Real.pi / 4)) := by
    intro x hx
    exact
      (Real.hasDerivAt_tan (x := x) (cos_ne_zero_of_mem_uIcc x hx)).continuousAt.continuousWithinAt
  have hsec_cont :
      ContinuousOn (fun x : ℝ => (1 / Real.cos x) ^ 2)
        (Set.uIcc (0 : ℝ) (Real.pi / 4)) :=
    (continuousOn_const.div Real.continuous_cos.continuousOn
      (fun x hx => cos_ne_zero_of_mem_uIcc x hx)).pow 2
  have hderiv_cont :
      ContinuousOn (deriv Real.tan)
        (Set.uIcc (0 : ℝ) (Real.pi / 4)) :=
    hsec_cont.congr (fun x hx => hderiv x hx)
  have hF :
      IntervalIntegrable
        (fun x : ℝ => Real.tan x ^ (2 * n - 2) * deriv Real.tan x)
        MeasureTheory.volume 0 (Real.pi / 4) :=
    ((htan_cont.pow (2 * n - 2)).mul hderiv_cont).intervalIntegrable
  have hG :
      IntervalIntegrable
        (fun x : ℝ => Real.tan x ^ (2 * (n - 1)))
        MeasureTheory.volume 0 (Real.pi / 4) :=
    (htan_cont.pow (2 * (n - 1))).intervalIntegrable
  have hexp : 2 * (n - 1) = 2 * n - 2 := by omega
  calc
    (∫ x in 0..Real.pi / 4,
        Real.tan x ^ (2 * n - 2) * ((1 / Real.cos x) ^ 2 - 1)) =
        ∫ x in 0..Real.pi / 4,
          (Real.tan x ^ (2 * n - 2) * deriv Real.tan x -
            Real.tan x ^ (2 * (n - 1))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change
        Real.tan x ^ (2 * n - 2) * ((1 / Real.cos x) ^ 2 - 1) =
          Real.tan x ^ (2 * n - 2) * deriv Real.tan x -
            Real.tan x ^ (2 * (n - 1))
      rw [hderiv x hx, hexp]
      ring
    _ = (∫ x in 0..Real.pi / 4,
          Real.tan x ^ (2 * n - 2) * deriv Real.tan x) -
        (∫ x in 0..Real.pi / 4,
          Real.tan x ^ (2 * (n - 1))) :=
      intervalIntegral.integral_sub hF hG
    _ = (∫ x in 0..Real.pi / 4,
          Real.tan x ^ (2 * n - 2) * deriv Real.tan x) - I (n - 1) := by
      rfl

theorem gap3 (n : ℕ) (hn : 0 < n) :
    (∫ x in 0..Real.pi / 4,
        Real.tan x ^ (2 * n - 2) * deriv Real.tan x) - I (n - 1) =
      1 / ((2 * n - 1 : ℕ) : ℝ) - I (n - 1) := by
  have hp : 0 < 2 * n - 1 := by omega
  have hpm : (2 * n - 1) - 1 = 2 * n - 2 := by omega
  have hpcast : (((2 * n - 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hderiv (x : ℝ)
      (hx : x ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
      deriv Real.tan x = (1 / Real.cos x) ^ 2 := by
    simpa [div_pow] using
      (Real.hasDerivAt_tan (x := x) (cos_ne_zero_of_mem_uIcc x hx)).deriv
  have htan_cont :
      ContinuousOn Real.tan (Set.uIcc (0 : ℝ) (Real.pi / 4)) := by
    intro x hx
    exact
      (Real.hasDerivAt_tan (x := x) (cos_ne_zero_of_mem_uIcc x hx)).continuousAt.continuousWithinAt
  have hsec_cont :
      ContinuousOn (fun x : ℝ => (1 / Real.cos x) ^ 2)
        (Set.uIcc (0 : ℝ) (Real.pi / 4)) :=
    (continuousOn_const.div Real.continuous_cos.continuousOn
      (fun x hx => cos_ne_zero_of_mem_uIcc x hx)).pow 2
  have hderiv_cont :
      ContinuousOn (deriv Real.tan)
        (Set.uIcc (0 : ℝ) (Real.pi / 4)) :=
    hsec_cont.congr (fun x hx => hderiv x hx)
  have hInt :
      IntervalIntegrable
        (fun x : ℝ => Real.tan x ^ (2 * n - 2) * deriv Real.tan x)
        MeasureTheory.volume 0 (Real.pi / 4) :=
    ((htan_cont.pow (2 * n - 2)).mul hderiv_cont).intervalIntegrable
  have hprim (x : ℝ)
      (hx : x ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
      HasDerivAt
        (fun y : ℝ => Real.tan y ^ (2 * n - 1) /
          (((2 * n - 1 : ℕ) : ℝ)))
        (Real.tan x ^ (2 * n - 2) * deriv Real.tan x) x := by
    have hd :=
      ((Real.hasDerivAt_tan (x := x) (cos_ne_zero_of_mem_uIcc x hx)).pow
        (2 * n - 1)).div_const (((2 * n - 1 : ℕ) : ℝ))
    convert hd using 1
    rw [hpm, (Real.hasDerivAt_tan
      (x := x) (cos_ne_zero_of_mem_uIcc x hx)).deriv]
    field_simp [hpcast] <;> ring
  have hFTC :
      (∫ x in (0 : ℝ)..Real.pi / 4,
        Real.tan x ^ (2 * n - 2) * deriv Real.tan x) =
        Real.tan (Real.pi / 4) ^ (2 * n - 1) /
            (((2 * n - 1 : ℕ) : ℝ)) -
          Real.tan 0 ^ (2 * n - 1) /
            (((2 * n - 1 : ℕ) : ℝ)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hInt
  rw [hFTC]
  simp [Real.tan_pi_div_four, hp.ne']

theorem gap4 (n : ℕ) (hn : 0 < n) :
    I n = 1 / ((2 * n - 1 : ℕ) : ℝ) - I (n - 1) := by
  calc
    I n =
        ∫ x in 0..Real.pi / 4,
          Real.tan x ^ (2 * n - 2) * ((1 / Real.cos x) ^ 2 - 1) :=
      gap1 n hn
    _ =
        (∫ x in 0..Real.pi / 4,
          Real.tan x ^ (2 * n - 2) * deriv Real.tan x) - I (n - 1) :=
      gap2 n hn
    _ = 1 / ((2 * n - 1 : ℕ) : ℝ) - I (n - 1) :=
      gap3 n hn

theorem gap5 (n : ℕ) (hn : 0 < n) :
    I n = 1 / ((2 * n - 1 : ℕ) : ℝ) - I (n - 1) := by
  exact gap4 n hn

theorem gap6 :
    I 0 = ∫ x in 0..Real.pi / 4, (1 : ℝ) := by
  simp [I]

theorem gap7 :
    (∫ x in 0..Real.pi / 4, (1 : ℝ)) = Real.pi / 4 := by
  simp

theorem gap8 :
    I 0 = Real.pi / 4 := by
  calc
    I 0 = ∫ x in 0..Real.pi / 4, (1 : ℝ) := gap6
    _ = Real.pi / 4 := gap7

theorem gap9 (n : ℕ) (hn : 2 ≤ n) :
    I n =
      1 / ((2 * n - 1 : ℕ) : ℝ) -
        (1 / ((2 * n - 3 : ℕ) : ℝ) - I (n - 2)) := by
  have hn1 : 0 < n := by omega
  have hn2 : 0 < n - 1 := by omega
  have hden : 2 * (n - 1) - 1 = 2 * n - 3 := by omega
  have hidx : n - 1 - 1 = n - 2 := by omega
  calc
    I n = 1 / ((2 * n - 1 : ℕ) : ℝ) - I (n - 1) := gap4 n hn1
    _ = 1 / ((2 * n - 1 : ℕ) : ℝ) -
          (1 / ((2 * (n - 1) - 1 : ℕ) : ℝ) - I (n - 1 - 1)) := by
      rw [gap4 (n - 1) hn2]
    _ = 1 / ((2 * n - 1 : ℕ) : ℝ) -
          (1 / ((2 * n - 3 : ℕ) : ℝ) - I (n - 2)) := by
      rw [hden, hidx]

theorem gap10 (n : ℕ) :
    unrolled n = (-1 : ℝ) ^ n * (I 0 - partialAlternating n) := by
  rfl

theorem gap11 (n : ℕ) :
    (-1 : ℝ) ^ n * (I 0 - partialAlternating n) =
      (-1 : ℝ) ^ n * (Real.pi / 4 - partialAlternating n) := by
  rw [gap8]

theorem gap12 (n : ℕ) :
    I n = unrolled n := by
  induction n with
  | zero =>
      simp [unrolled, partialAlternating]
  | succ n ih =>
      rw [gap4 (n + 1) (by omega)]
      have hidx : n + 1 - 1 = n := by omega
      rw [hidx, ih]
      have hden : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
      rw [hden]
      have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
        rw [← pow_add]
        have he : n + n = 2 * n := by omega
        rw [he, pow_mul]
        norm_num
      have hd : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      simp only [unrolled, partialAlternating, Finset.sum_range_succ, pow_succ]
      field_simp [hd]
      nlinarith [hs]

theorem gap13 (n : ℕ) :
    I n =
      (-1 : ℝ) ^ n * (Real.pi / 4 - partialAlternating n) := by
  calc
    I n = unrolled n := gap12 n
    _ = (-1 : ℝ) ^ n * (I 0 - partialAlternating n) := gap10 n
    _ = (-1 : ℝ) ^ n * (Real.pi / 4 - partialAlternating n) := gap11 n

end

end ProofGap.Exercise2283
