import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2065
noncomputable section

def sec (x : ℝ) := 1 / Real.cos x
def xSub (a t : ℝ) :=
  2 * Real.arctan (((1 + t) / (1 - t)) * Real.tan (a / 2))
def jacobian (a t : ℝ) :=
  4 * Real.tan (a / 2) /
    (t ^ 2 * sec (a / 2) ^ 2 +
      2 * t * (Real.tan (a / 2) ^ 2 - 1) + sec (a / 2) ^ 2)
def kernel (a : ℝ) (n : ℕ) (t : ℝ) :=
  4 * t ^ n * Real.tan (a / 2) /
    (t ^ 2 * sec (a / 2) ^ 2 +
      2 * t * (Real.tan (a / 2) ^ 2 - 1) + sec (a / 2) ^ 2)
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ t ∈ U, HasDerivAt F (f t) t}
def RecurrenceFamily (U : Set ℝ) (a : ℝ) (n : ℕ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U (kernel a (n - 1)),
    ∃ H ∈ Family U (kernel a (n - 2)), ∃ C,
    ∀ t ∈ U, F t =
      2 * Real.sin a / ((n : ℝ) - 1) * t ^ (n - 1) +
        2 * Real.cos a * G t - H t + C}
def Regular (U : Set ℝ) (a : ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ Real.cos (a / 2) ≠ 0 ∧
    ∀ t ∈ U, t ≠ 1

private lemma sec_sq_identity (a : ℝ)
    (hcos : Real.cos (a / 2) ≠ 0) :
    sec (a / 2) ^ 2 = 1 + Real.tan (a / 2) ^ 2 := by
  unfold sec
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  nlinarith [Real.sin_sq_add_cos_sq (a / 2)]

private lemma denominator_identity (a t : ℝ)
    (hcos : Real.cos (a / 2) ≠ 0) :
    t ^ 2 * sec (a / 2) ^ 2 +
          2 * t * (Real.tan (a / 2) ^ 2 - 1) + sec (a / 2) ^ 2 =
      (1 - t) ^ 2 + Real.tan (a / 2) ^ 2 * (1 + t) ^ 2 := by
  rw [sec_sq_identity a hcos]
  ring

private lemma denominator_ne_zero (a t : ℝ)
    (hcos : Real.cos (a / 2) ≠ 0) (ht : t ≠ 1) :
    t ^ 2 * sec (a / 2) ^ 2 +
          2 * t * (Real.tan (a / 2) ^ 2 - 1) + sec (a / 2) ^ 2 ≠ 0 := by
  rw [denominator_identity a t hcos]
  apply ne_of_gt
  have hfirst : 0 < (1 - t) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm ht))
  have hsecond :
      0 ≤ Real.tan (a / 2) ^ 2 * (1 + t) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

private lemma denominator_ne_zero_global (a t : ℝ)
    (hcos : Real.cos (a / 2) ≠ 0)
    (htan : Real.tan (a / 2) ≠ 0) :
    t ^ 2 * sec (a / 2) ^ 2 +
          2 * t * (Real.tan (a / 2) ^ 2 - 1) + sec (a / 2) ^ 2 ≠ 0 := by
  rw [denominator_identity a t hcos]
  apply ne_of_gt
  by_cases ht : t = 1
  · subst t
    have hz : 0 < Real.tan (a / 2) ^ 2 := sq_pos_of_ne_zero htan
    norm_num
    positivity
  · have hfirst : 0 < (1 - t) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm ht))
    have hsecond :
        0 ≤ Real.tan (a / 2) ^ 2 * (1 + t) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith

private lemma continuous_kernel (a : ℝ) (n : ℕ)
    (hcos : Real.cos (a / 2) ≠ 0) : Continuous (kernel a n) := by
  by_cases htan : Real.tan (a / 2) = 0
  · have hk : kernel a n = fun _ : ℝ => 0 := by
      funext t
      simp [kernel, htan]
    rw [hk]
    exact continuous_const
  · unfold kernel
    refine Continuous.div ?_ ?_ ?_
    · exact (continuous_const.mul (continuous_id.pow n)).mul continuous_const
    · exact
        (((continuous_id.pow 2).mul continuous_const).add
          ((continuous_const.mul continuous_id).mul continuous_const)).add
          continuous_const
    · intro t
      exact denominator_ne_zero_global a t hcos htan

private lemma exists_kernel_family (U : Set ℝ) (a : ℝ) (n : ℕ)
    (hcos : Real.cos (a / 2) ≠ 0) :
    ∃ G, G ∈ Family U (kernel a n) := by
  let G : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, kernel a n s
  refine ⟨G, ?_⟩
  intro t ht
  have hcont : ContinuousAt (kernel a n) t :=
    (continuous_kernel a n hcos).continuousAt
  have hstrong := (continuous_kernel a n hcos).stronglyMeasurable
  have hmeas :
      StronglyMeasurableAtFilter (kernel a n) (nhds t)
        MeasureTheory.volume :=
    hstrong.stronglyMeasurableAtFilter
  exact intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (kernel a n) MeasureTheory.volume 0 t from
      (continuous_kernel a n hcos).intervalIntegrable
        (μ := MeasureTheory.volume) 0 t)
    hmeas hcont

private lemma recurrence_term_hasDerivAt (a : ℝ) (n : ℕ)
    (hn : 2 ≤ n) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        2 * Real.sin a / ((n : ℝ) - 1) * x ^ (n - 1))
      (2 * Real.sin a * t ^ (n - 2)) t := by
  have hnsub : 1 ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hnsub]
    norm_num
  have hne : (n : ℝ) - 1 ≠ 0 := by
    have hnreal : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n by omega)
    linarith
  convert
    ((hasDerivAt_id t).pow (n - 1)).const_mul
      (2 * Real.sin a / ((n : ℝ) - 1)) using 1
  rw [show n - 1 - 1 = n - 2 by omega, hcast]
  simp only [id_eq, mul_one]
  field_simp [hne]

private lemma kernel_recurrence_algebra (t z q s D : ℝ)
    (hs : s ≠ 0) (hD : D ≠ 0)
    (hform : D = t ^ 2 * s + 2 * t * (q ^ 2 - 1) + s) :
    4 * (z * t ^ 2) * q / D =
      4 * q / s * z -
        8 * q * (q ^ 2 - 1) * (z * t) / (s * D) -
        4 * z * q / D := by
  field_simp [hs, hD]
  rw [hform]
  ring

theorem gap1 (a t : ℝ) : xSub a t =
    2 * Real.arctan (((1 + t) / (1 - t)) * Real.tan (a / 2)) := by
  rfl
theorem gap2 (U : Set ℝ) (a : ℝ) (hU : Regular U a) :
    ∀ t ∈ U, HasDerivAt (xSub a) (jacobian a t) t := by
  intro t ht
  have hcos : Real.cos (a / 2) ≠ 0 := hU.2.2.1
  have hnt : t ≠ 1 := hU.2.2.2 t ht
  have hden : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hnt)
  have hnum : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
    simpa using
      (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
  have hdenom : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have hinner :
      HasDerivAt
        (fun s : ℝ => ((1 + s) / (1 - s)) * Real.tan (a / 2))
        (2 * Real.tan (a / 2) / (1 - t) ^ 2) t := by
    have hraw := (hnum.div hdenom hden).mul_const (Real.tan (a / 2))
    convert hraw using 1
    field_simp [hden] <;> ring
  have hout :=
    ((Real.hasDerivAt_arctan
      (((1 + t) / (1 - t)) * Real.tan (a / 2))).comp t hinner).const_mul 2
  have hy :
      1 + (((1 + t) / (1 - t)) * Real.tan (a / 2)) ^ 2 ≠ 0 := by
    positivity
  have hd := denominator_ne_zero a t hcos hnt
  have hcoef :
      2 *
          ((1 /
              (1 + (((1 + t) / (1 - t)) * Real.tan (a / 2)) ^ 2)) *
            (2 * Real.tan (a / 2) / (1 - t) ^ 2)) =
        jacobian a t := by
    unfold jacobian
    rw [denominator_identity a t hcos]
    field_simp [hden, hy, hd]
    ring
  have hout' :
      HasDerivAt (xSub a)
        (2 *
          ((1 /
              (1 + (((1 + t) / (1 - t)) * Real.tan (a / 2)) ^ 2)) *
            (2 * Real.tan (a / 2) / (1 - t) ^ 2))) t := by
    simpa only [xSub] using hout
  rw [hcoef] at hout'
  exact hout'
theorem gap3 (U : Set ℝ) (a : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hU : Regular U a) : ∀ t ∈ U,
    kernel a n t =
      4 * Real.tan (a / 2) / sec (a / 2) ^ 2 * t ^ (n - 2) -
      8 * Real.tan (a / 2) * (Real.tan (a / 2) ^ 2 - 1) * t ^ (n - 1) /
        (sec (a / 2) ^ 2 *
          (t ^ 2 * sec (a / 2) ^ 2 +
            2 * t * (Real.tan (a / 2) ^ 2 - 1) + sec (a / 2) ^ 2)) -
      kernel a (n - 2) t := by
  intro t ht
  have hcos : Real.cos (a / 2) ≠ 0 := hU.2.2.1
  have hnt : t ≠ 1 := hU.2.2.2 t ht
  have hsec : sec (a / 2) ≠ 0 := by
    unfold sec
    exact one_div_ne_zero hcos
  have hsec_sq : sec (a / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hsec
  have hd := denominator_ne_zero a t hcos hnt
  have hpow_n : t ^ n = t ^ (n - 2) * t ^ 2 := by
    calc
      t ^ n = t ^ ((n - 2) + 2) := by
        congr 1
        omega
      _ = t ^ (n - 2) * t ^ 2 := by rw [pow_add]
  have hpow_nm1 : t ^ (n - 1) = t ^ (n - 2) * t := by
    calc
      t ^ (n - 1) = t ^ ((n - 2) + 1) := by
        congr 1
        omega
      _ = t ^ (n - 2) * t := by rw [pow_add, pow_one]
  unfold kernel
  simpa only [hpow_n, hpow_nm1] using
    (kernel_recurrence_algebra
      (t := t)
      (z := t ^ (n - 2))
      (q := Real.tan (a / 2))
      (s := sec (a / 2) ^ 2)
      (D :=
        t ^ 2 * sec (a / 2) ^ 2 +
          2 * t * (Real.tan (a / 2) ^ 2 - 1) + sec (a / 2) ^ 2)
      hsec_sq hd (by rfl))
theorem gap4 (U : Set ℝ) (a : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hU : Regular U a) :
    Family U (kernel a n) = RecurrenceFamily U a n := by
  have hcos : Real.cos (a / 2) ≠ 0 := hU.2.2.1
  have hsec : sec (a / 2) ≠ 0 := by
    unfold sec
    exact one_div_ne_zero hcos
  have hsina :
      4 * Real.tan (a / 2) / sec (a / 2) ^ 2 = 2 * Real.sin a := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    rw [← show a / 2 + a / 2 = a by ring, Real.sin_add]
    field_simp [hcos]
    ring
  have hcosa :
      -(2 * (Real.tan (a / 2) ^ 2 - 1) / sec (a / 2) ^ 2) =
        2 * Real.cos a := by
    have hinvsec :
        (sec (a / 2) ^ 2)⁻¹ = Real.cos (a / 2) ^ 2 := by
      simp only [sec, one_div, inv_pow, inv_inv]
    have htanmul :
        Real.tan (a / 2) * Real.cos (a / 2) =
          Real.sin (a / 2) := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hcos]
    have hsq :
        Real.tan (a / 2) ^ 2 * Real.cos (a / 2) ^ 2 =
          Real.sin (a / 2) ^ 2 := by
      calc
        Real.tan (a / 2) ^ 2 * Real.cos (a / 2) ^ 2 =
            (Real.tan (a / 2) * Real.cos (a / 2)) ^ 2 := by ring
        _ = Real.sin (a / 2) ^ 2 := by rw [htanmul]
    have hdouble :
        Real.cos a =
          Real.cos (a / 2) ^ 2 - Real.sin (a / 2) ^ 2 := by
      calc
        Real.cos a = Real.cos (a / 2 + a / 2) := by
          congr 1
          ring
        _ = Real.cos (a / 2) ^ 2 - Real.sin (a / 2) ^ 2 := by
          rw [Real.cos_add]
          ring
    calc
      -(2 * (Real.tan (a / 2) ^ 2 - 1) / sec (a / 2) ^ 2) =
          -(2 * (Real.tan (a / 2) ^ 2 - 1) *
            (sec (a / 2) ^ 2)⁻¹) := by
        rw [div_eq_mul_inv]
      _ = -(2 * (Real.tan (a / 2) ^ 2 - 1) *
            Real.cos (a / 2) ^ 2) := by rw [hinvsec]
      _ = 2 *
          (Real.cos (a / 2) ^ 2 - Real.sin (a / 2) ^ 2) := by
        rw [← hsq]
        ring
      _ = 2 * Real.cos a := by rw [← hdouble]
  have hrec : ∀ t ∈ U,
      kernel a n t =
        2 * Real.sin a * t ^ (n - 2) +
          2 * Real.cos a * kernel a (n - 1) t - kernel a (n - 2) t := by
    intro t ht
    have hnt : t ≠ 1 := hU.2.2.2 t ht
    have hd := denominator_ne_zero a t hcos hnt
    have hmid :
        -(8 * Real.tan (a / 2) * (Real.tan (a / 2) ^ 2 - 1) *
              t ^ (n - 1) /
            (sec (a / 2) ^ 2 *
              (t ^ 2 * sec (a / 2) ^ 2 +
                2 * t * (Real.tan (a / 2) ^ 2 - 1) +
                sec (a / 2) ^ 2))) =
          2 * Real.cos a * kernel a (n - 1) t := by
      rw [← hcosa]
      unfold kernel
      field_simp [hsec, hd]
      ring
    rw [gap3 U a n hn hU t ht]
    calc
      4 * Real.tan (a / 2) / sec (a / 2) ^ 2 * t ^ (n - 2) -
            8 * Real.tan (a / 2) * (Real.tan (a / 2) ^ 2 - 1) *
                t ^ (n - 1) /
              (sec (a / 2) ^ 2 *
                (t ^ 2 * sec (a / 2) ^ 2 +
                  2 * t * (Real.tan (a / 2) ^ 2 - 1) +
                  sec (a / 2) ^ 2)) -
            kernel a (n - 2) t =
          4 * Real.tan (a / 2) / sec (a / 2) ^ 2 * t ^ (n - 2) +
            (-(8 * Real.tan (a / 2) * (Real.tan (a / 2) ^ 2 - 1) *
                t ^ (n - 1) /
              (sec (a / 2) ^ 2 *
                (t ^ 2 * sec (a / 2) ^ 2 +
                  2 * t * (Real.tan (a / 2) ^ 2 - 1) +
                  sec (a / 2) ^ 2)))) -
            kernel a (n - 2) t := by ring
      _ = 2 * Real.sin a * t ^ (n - 2) +
            2 * Real.cos a * kernel a (n - 1) t -
            kernel a (n - 2) t := by rw [hmid, hsina]
  apply Set.ext
  intro F
  constructor
  · intro hF
    rcases exists_kernel_family U a (n - 1) hcos with ⟨G, hG⟩
    let H : ℝ → ℝ := fun x =>
      2 * Real.sin a / ((n : ℝ) - 1) * x ^ (n - 1) +
        2 * Real.cos a * G x - F x
    refine ⟨G, hG, H, ?_, 0, ?_⟩
    · intro t ht
      have hp := recurrence_term_hasDerivAt a n hn t
      have hh :=
        (hp.add ((hG t ht).const_mul (2 * Real.cos a))).sub (hF t ht)
      have hcoef :
          2 * Real.sin a * t ^ (n - 2) +
                2 * Real.cos a * kernel a (n - 1) t - kernel a n t =
            kernel a (n - 2) t := by
        rw [hrec t ht]
        ring
      rw [hcoef] at hh
      simpa only [H] using hh
    · intro t ht
      dsimp [H]
      ring
  · rintro ⟨G, hG, H, hH, C, hEq⟩
    intro t ht
    let R : ℝ → ℝ := fun x =>
      2 * Real.sin a / ((n : ℝ) - 1) * x ^ (n - 1) +
        2 * Real.cos a * G x - H x + C
    have hp := recurrence_term_hasDerivAt a n hn t
    have hd :=
      (((hp.add ((hG t ht).const_mul (2 * Real.cos a))).sub (hH t ht)).add_const C)
    have hcoef :
        2 * Real.sin a * t ^ (n - 2) +
              2 * Real.cos a * kernel a (n - 1) t - kernel a (n - 2) t =
          kernel a n t := by
      exact (hrec t ht).symm
    rw [hcoef] at hd
    have hdR : HasDerivAt R (kernel a n t) t := by
      simpa only [R] using hd
    have heq : F =ᶠ[nhds t] R :=
      Filter.Eventually.mono (hU.1.mem_nhds ht) (fun x hx => hEq x hx)
    exact hdR.congr_of_eventuallyEq heq

end
end ProofGap.Exercise2065
