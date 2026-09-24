import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Positivity

open scoped Interval

namespace ProofGap.Exercise2291

noncomputable section

def u (n : ℕ) (x : ℝ) : ℝ := Real.sin ((n : ℝ) * x) / Real.sin x

def evenExpansion (k : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range k, Real.cos ((2 * j + 1 : ℕ) * x)

def evenComplexExpansion (k : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range k,
    (Complex.exp (Complex.I * ((2 * j + 1 : ℕ) : ℝ) * x) +
      Complex.exp (-Complex.I * ((2 * j + 1 : ℕ) : ℝ) * x))

def evenPrimitive (k : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range k,
    Real.sin (((2 * j + 1 : ℕ) : ℝ) * x) / ((2 * j + 1 : ℕ) : ℝ)

def oddExpansion (k : ℕ) (x : ℝ) : ℝ :=
  1 + 2 * ∑ j ∈ Finset.range k,
    Real.cos ((2 * (j + 1) : ℕ) * x)

private theorem exp_I_sub_exp_neg_I (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) -
        Complex.exp (-Complex.I * (t : ℂ)) =
      2 * Complex.I * (Real.sin t : ℂ) := by
  rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring]
  rw [show -Complex.I * (t : ℂ) = ((-t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Real.cos_neg, Real.sin_neg] <;>
    ring

private theorem exp_I_add_exp_neg_I (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) +
        Complex.exp (-Complex.I * (t : ℂ)) =
      ((2 * Real.cos t : ℝ) : ℂ) := by
  rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring]
  rw [show -Complex.I * (t : ℂ) = ((-t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Real.cos_neg, Real.sin_neg] <;>
    ring

private theorem even_sin_step (k : ℕ) (x : ℝ) :
    Real.sin (((2 * (k + 1) : ℕ) : ℝ) * x) =
      Real.sin (((2 * k : ℕ) : ℝ) * x) +
        2 * Real.sin x *
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) := by
  rw [show (((2 * (k + 1) : ℕ) : ℝ) * x) =
      (((2 * k + 1 : ℕ) : ℝ) * x) + x by
        push_cast
        ring]
  rw [show (((2 * k : ℕ) : ℝ) * x) =
      (((2 * k + 1 : ℕ) : ℝ) * x) - x by
        push_cast
        ring]
  rw [Real.sin_add, Real.sin_sub]
  ring

private theorem even_sin_identity (k : ℕ) (x : ℝ) :
    Real.sin (((2 * k : ℕ) : ℝ) * x) =
      Real.sin x * evenExpansion k x := by
  induction k with
  | zero => simp [evenExpansion]
  | succ k ih =>
      rw [even_sin_step, ih]
      simp only [evenExpansion, Finset.sum_range_succ]
      ring

private theorem odd_sin_step (k : ℕ) (x : ℝ) :
    Real.sin (((2 * (k + 1) + 1 : ℕ) : ℝ) * x) =
      Real.sin (((2 * k + 1 : ℕ) : ℝ) * x) +
        2 * Real.sin x *
          Real.cos (((2 * (k + 1) : ℕ) : ℝ) * x) := by
  rw [show (((2 * (k + 1) + 1 : ℕ) : ℝ) * x) =
      (((2 * (k + 1) : ℕ) : ℝ) * x) + x by
        push_cast
        ring]
  rw [show (((2 * k + 1 : ℕ) : ℝ) * x) =
      (((2 * (k + 1) : ℕ) : ℝ) * x) - x by
        push_cast
        ring]
  rw [Real.sin_add, Real.sin_sub]
  ring

private theorem odd_sin_identity (k : ℕ) (x : ℝ) :
    Real.sin (((2 * k + 1 : ℕ) : ℝ) * x) =
      Real.sin x * oddExpansion k x := by
  induction k with
  | zero => simp [oddExpansion]
  | succ k ih =>
      rw [odd_sin_step, ih]
      simp only [oddExpansion, Finset.sum_range_succ]
      ring

private theorem evenComplexExpansion_eq_real (k : ℕ) (x : ℝ) :
    evenComplexExpansion k x = (evenExpansion k x : ℂ) := by
  induction k with
  | zero => simp [evenComplexExpansion, evenExpansion]
  | succ k ih =>
      unfold evenComplexExpansion evenExpansion at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hterm :
          Complex.exp (Complex.I * ((2 * k + 1 : ℕ) : ℝ) * x) +
              Complex.exp (-Complex.I * ((2 * k + 1 : ℕ) : ℝ) * x) =
            ((2 * Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) := by
        convert exp_I_add_exp_neg_I
          (((2 * k + 1 : ℕ) : ℝ) * x) using 1 <;>
          push_cast <;>
          ring
      rw [hterm]
      push_cast
      ring

private theorem hasDerivAt_sin_mul_div (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.sin (a * y) / a)
      (Real.cos (a * x)) x := by
  simpa [ha] using
    (((Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x))).div_const a)

private theorem hasDerivAt_evenPrimitive (k : ℕ) (x : ℝ) :
    HasDerivAt (evenPrimitive k) (evenExpansion k x) x := by
  unfold evenPrimitive evenExpansion
  have hs :
      HasDerivAt
        (fun y : ℝ => ∑ j ∈ Finset.range k,
          Real.sin (((2 * j + 1 : ℕ) : ℝ) * y) /
            ((2 * j + 1 : ℕ) : ℝ))
        (∑ j ∈ Finset.range k,
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * x)) x := by
    have hs' :
        HasDerivAt
          (∑ j ∈ Finset.range k, fun y : ℝ =>
            Real.sin (((2 * j + 1 : ℕ) : ℝ) * y) /
              ((2 * j + 1 : ℕ) : ℝ))
          (∑ j ∈ Finset.range k,
            Real.cos (((2 * j + 1 : ℕ) : ℝ) * x)) x :=
      HasDerivAt.sum (u := Finset.range k)
        (fun j _ => hasDerivAt_sin_mul_div
          (((2 * j + 1 : ℕ) : ℝ)) x (by positivity))
    have hfun :
        (∑ j ∈ Finset.range k, fun y : ℝ =>
          Real.sin (((2 * j + 1 : ℕ) : ℝ) * y) /
            ((2 * j + 1 : ℕ) : ℝ)) =
        (fun y : ℝ => ∑ j ∈ Finset.range k,
          Real.sin (((2 * j + 1 : ℕ) : ℝ) * y) /
            ((2 * j + 1 : ℕ) : ℝ)) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hfun] at hs'
    exact hs'
  simpa using hs.const_mul 2

private theorem continuous_evenExpansion (k : ℕ) :
    Continuous (evenExpansion k) := by
  unfold evenExpansion
  fun_prop

private theorem integral_evenExpansion (k : ℕ) :
    (∫ x in 0..Real.pi, evenExpansion k x) =
      evenPrimitive k Real.pi - evenPrimitive k 0 := by
  have hderiv : deriv (evenPrimitive k) = evenExpansion k := by
    funext x
    exact (hasDerivAt_evenPrimitive k x).deriv
  rw [← hderiv]
  apply intervalIntegral.integral_deriv_eq_sub
  · intro x hx
    exact (hasDerivAt_evenPrimitive k x).differentiableAt
  · rw [hderiv]
    exact (continuous_evenExpansion k).intervalIntegrable 0 Real.pi

private def oddPrimitiveAux (k : ℕ) (x : ℝ) : ℝ :=
  x + 2 * ∑ j ∈ Finset.range k,
    Real.sin (((2 * (j + 1) : ℕ) : ℝ) * x) /
      ((2 * (j + 1) : ℕ) : ℝ)

private theorem hasDerivAt_oddPrimitiveAux (k : ℕ) (x : ℝ) :
    HasDerivAt (oddPrimitiveAux k) (oddExpansion k x) x := by
  unfold oddPrimitiveAux oddExpansion
  have hs :
      HasDerivAt
        (fun y : ℝ => ∑ j ∈ Finset.range k,
          Real.sin (((2 * (j + 1) : ℕ) : ℝ) * y) /
            ((2 * (j + 1) : ℕ) : ℝ))
        (∑ j ∈ Finset.range k,
          Real.cos (((2 * (j + 1) : ℕ) : ℝ) * x)) x := by
    have hs' :
        HasDerivAt
          (∑ j ∈ Finset.range k, fun y : ℝ =>
            Real.sin (((2 * (j + 1) : ℕ) : ℝ) * y) /
              ((2 * (j + 1) : ℕ) : ℝ))
          (∑ j ∈ Finset.range k,
            Real.cos (((2 * (j + 1) : ℕ) : ℝ) * x)) x :=
      HasDerivAt.sum (u := Finset.range k)
        (fun j _ => hasDerivAt_sin_mul_div
          (((2 * (j + 1) : ℕ) : ℝ)) x (by positivity))
    have hfun :
        (∑ j ∈ Finset.range k, fun y : ℝ =>
          Real.sin (((2 * (j + 1) : ℕ) : ℝ) * y) /
            ((2 * (j + 1) : ℕ) : ℝ)) =
        (fun y : ℝ => ∑ j ∈ Finset.range k,
          Real.sin (((2 * (j + 1) : ℕ) : ℝ) * y) /
            ((2 * (j + 1) : ℕ) : ℝ)) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hfun] at hs'
    exact hs'
  simpa using (hasDerivAt_id x).add (hs.const_mul 2)

private theorem continuous_oddExpansion (k : ℕ) :
    Continuous (oddExpansion k) := by
  unfold oddExpansion
  fun_prop

private theorem integral_oddExpansion (k : ℕ) :
    (∫ x in 0..Real.pi, oddExpansion k x) =
      oddPrimitiveAux k Real.pi - oddPrimitiveAux k 0 := by
  have hderiv : deriv (oddPrimitiveAux k) = oddExpansion k := by
    funext x
    exact (hasDerivAt_oddPrimitiveAux k x).deriv
  rw [← hderiv]
  apply intervalIntegral.integral_deriv_eq_sub
  · intro x hx
    exact (hasDerivAt_oddPrimitiveAux k x).differentiableAt
  · rw [hderiv]
    exact (continuous_oddExpansion k).intervalIntegrable 0 Real.pi

private theorem ae_sin_ne_zero :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume, Real.sin x ≠ 0 := by
  classical
  have hs : Set.Countable {x : ℝ | Real.sin x = 0} := by
    refine (Set.countable_range (fun n : ℤ => (n : ℝ) * Real.pi)).mono ?_
    intro x hx
    rcases Real.sin_eq_zero_iff.mp hx with ⟨n, hn⟩
    exact ⟨n, hn⟩
  refine MeasureTheory.ae_iff.2 ?_
  have hz :
      MeasureTheory.volume {x : ℝ | Real.sin x = 0} = 0 :=
    hs.measure_zero (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  simpa using hz

theorem gap1 (n : ℕ) (x : ℝ) (hx : Real.sin x ≠ 0) :
    (u n x : ℂ) =
      (Complex.exp (Complex.I * (n : ℝ) * x) -
          Complex.exp (-Complex.I * (n : ℝ) * x)) /
        (Complex.exp (Complex.I * x) - Complex.exp (-Complex.I * x)) := by
  have hpnum :
      Complex.I * (n : ℝ) * x =
        Complex.I * ((((n : ℝ) * x : ℝ) : ℂ)) := by
    push_cast
    ring
  have hnnum :
      -Complex.I * (n : ℝ) * x =
        -Complex.I * ((((n : ℝ) * x : ℝ) : ℂ)) := by
    push_cast
    ring
  have hpden : Complex.I * x = Complex.I * ((x : ℝ) : ℂ) := rfl
  have hnden : -Complex.I * x = -Complex.I * ((x : ℝ) : ℂ) := rfl
  rw [hpnum, hnnum, hpden, hnden, exp_I_sub_exp_neg_I,
    exp_I_sub_exp_neg_I]
  unfold u
  push_cast
  field_simp [hx]

theorem gap2 (n k : ℕ) (x : ℝ) (hn : n = 2 * k)
    (hx : Real.sin x ≠ 0) :
    (u n x : ℂ) = evenComplexExpansion k x := by
  subst n
  rw [evenComplexExpansion_eq_real]
  norm_cast
  unfold u
  rw [even_sin_identity]
  simp [hx]

theorem gap3 (n k : ℕ) (x : ℝ) (hn : n = 2 * k)
    (hx : Real.sin x ≠ 0) :
    (u n x : ℂ) = evenComplexExpansion k x := by
  exact gap2 n k x hn hx

theorem gap4 (n k : ℕ) (x : ℝ) (hn : n = 2 * k)
    (hx : Real.sin x ≠ 0) :
    u n x = evenExpansion k x := by
  subst n
  unfold u
  rw [even_sin_identity]
  simp [hx]

theorem gap5 (n k : ℕ) (hn : n = 2 * k) :
    (∫ x in 0..Real.pi, u n x) =
      evenPrimitive k Real.pi - evenPrimitive k 0 := by
  calc
    (∫ x in 0..Real.pi, u n x) =
        ∫ x in 0..Real.pi, evenExpansion k x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_sin_ne_zero] with x hx
      intro _
      exact gap4 n k x hn hx
    _ = evenPrimitive k Real.pi - evenPrimitive k 0 :=
      integral_evenExpansion k

theorem gap6 (n k : ℕ) (hn : n = 2 * k) :
    evenPrimitive k Real.pi - evenPrimitive k 0 = 0 := by
  unfold evenPrimitive
  have hpi :
      (∑ j ∈ Finset.range k,
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi) /
          ((2 * j + 1 : ℕ) : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Real.sin_nat_mul_pi]
    simp
  rw [hpi]
  simp

theorem gap7 (n k : ℕ) (hn : n = 2 * k) :
    (∫ x in 0..Real.pi, u n x) = 0 := by
  rw [gap5 n k hn, gap6 n k hn]

theorem gap8 (n k : ℕ) (x : ℝ) (hn : n = 2 * k + 1)
    (hx : Real.sin x ≠ 0) :
    u n x = oddExpansion k x := by
  subst n
  unfold u
  rw [odd_sin_identity]
  simp [hx]

theorem gap9 (n k : ℕ) (hn : n = 2 * k + 1) :
    (∫ x in 0..Real.pi, u n x) = Real.pi := by
  calc
    (∫ x in 0..Real.pi, u n x) =
        ∫ x in 0..Real.pi, oddExpansion k x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_sin_ne_zero] with x hx
      intro _
      exact gap8 n k x hn hx
    _ = oddPrimitiveAux k Real.pi - oddPrimitiveAux k 0 :=
      integral_oddExpansion k
    _ = Real.pi := by
      unfold oddPrimitiveAux
      have hpi :
          (∑ j ∈ Finset.range k,
            Real.sin (((2 * (j + 1) : ℕ) : ℝ) * Real.pi) /
              ((2 * (j + 1) : ℕ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Real.sin_nat_mul_pi]
        simp
      rw [hpi]
      simp

theorem gap10 (n : ℕ) :
    (∫ x in 0..Real.pi, u n x) =
      if Even n then 0 else Real.pi := by
  by_cases h : Even n
  · simp only [h, if_true]
    rcases h with ⟨k, hk⟩
    apply gap7 n k
    omega
  · simp only [h, if_false]
    rcases Nat.even_or_odd n with he | ho
    · exact (h he).elim
    · rcases ho with ⟨k, hk⟩
      apply gap9 n k
      omega

end

end ProofGap.Exercise2291
