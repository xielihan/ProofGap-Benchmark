import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2290

noncomputable section

def integrand (m n : ℕ) (x : ℝ) : ℝ :=
  Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n)

def quarterIntegral (m n : ℕ) : ℝ :=
  ∫ x in 0..Real.pi / 2, integrand m n x

def fullIntegral (m n : ℕ) : ℝ :=
  ∫ x in 0..2 * Real.pi, integrand m n x

def frequency (m n k l : ℕ) : ℤ :=
  2 * ((m : ℤ) + n - k - l)

def complexExpansion (m n : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ m / (2 : ℂ) ^ (2 * m + 2 * n) *
    ∑ k ∈ Finset.range (2 * m + 1),
      ∑ l ∈ Finset.range (2 * n + 1),
        (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
          (Nat.choose (2 * n) l : ℂ) *
          Complex.exp (Complex.I * (frequency m n k l : ℂ) * (x : ℂ))

def trigExpansion (m n : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ m / (2 : ℂ) ^ (2 * m + 2 * n) *
    ∑ k ∈ Finset.range (2 * m + 1),
      ∑ l ∈ Finset.range (2 * n + 1),
        (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
          (Nat.choose (2 * n) l : ℂ) *
          ((Real.cos ((frequency m n k l : ℝ) * x) : ℂ) +
            Complex.I * Real.sin ((frequency m n k l : ℝ) * x))

def zeroFrequencySum (m n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 * m + 1),
    (-1 : ℝ) ^ k * (Nat.choose (2 * m) k : ℝ) *
      (Nat.choose (2 * n) (m + n - k) : ℝ)

def closedForm (m n : ℕ) : ℝ :=
  Real.pi * (Nat.factorial (2 * m) : ℝ) * (Nat.factorial (2 * n) : ℝ) /
    (2 ^ (2 * m + 2 * n + 1) * (Nat.factorial m : ℝ) *
      (Nat.factorial n : ℝ) * (Nat.factorial (m + n) : ℝ))

private theorem quarterIntegral_symm (m n : ℕ) :
    quarterIntegral m n = quarterIntegral n m := by
  rw [quarterIntegral, quarterIntegral]
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2, integrand m n x) =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          integrand n m (Real.pi / 2 - x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp [integrand, Real.sin_pi_div_two_sub,
              Real.cos_pi_div_two_sub, mul_comm]
    _ = ∫ x in Real.pi / 2 - Real.pi / 2..Real.pi / 2 - 0,
          integrand n m x := by
            rw [intervalIntegral.integral_comp_sub_left]
    _ = ∫ x in (0 : ℝ)..Real.pi / 2, integrand n m x := by ring_nf

private theorem fullIntegral_eq_four_mul_quarter (m n : ℕ) :
    fullIntegral m n = 4 * quarterIntegral m n := by
  have hcont : Continuous (integrand m n) := by
    unfold integrand
    fun_prop
  have hmirror :
      (∫ x in Real.pi / 2..Real.pi, integrand m n x) =
        ∫ x in (0 : ℝ)..Real.pi / 2, integrand m n x := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (integrand m n) Real.pi (a := (0 : ℝ)) (b := Real.pi / 2)
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at hsub
    calc
      _ = ∫ x in (0 : ℝ)..Real.pi / 2, integrand m n (Real.pi - x) := hsub.symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [integrand, Real.sin_pi_sub, Real.cos_pi_sub, pow_mul]
  have hshift :
      (∫ x in Real.pi..2 * Real.pi, integrand m n x) =
        ∫ x in (0 : ℝ)..Real.pi, integrand m n x := by
    have hadd := intervalIntegral.integral_comp_add_right
      (integrand m n) Real.pi (a := (0 : ℝ)) (b := Real.pi)
    rw [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] at hadd
    calc
      _ = ∫ x in (0 : ℝ)..Real.pi, integrand m n (x + Real.pi) := hadd.symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [integrand, Real.sin_add_pi, Real.cos_add_pi, pow_mul]
  have hsplitQuarter := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (0 : ℝ) (Real.pi / 2))
    (hcont.intervalIntegrable (Real.pi / 2) Real.pi)
  have hsplitFull := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (0 : ℝ) Real.pi)
    (hcont.intervalIntegrable Real.pi (2 * Real.pi))
  rw [hmirror] at hsplitQuarter
  rw [hshift] at hsplitFull
  unfold fullIntegral quarterIntegral
  linarith

private theorem quarterIntegral_recurrence (m n : ℕ) (hn : 0 < n) :
    quarterIntegral m n =
      ((2 * n - 1 : ℕ) : ℝ) / (2 * ((m + n : ℕ) : ℝ)) *
        quarterIntegral m (n - 1) := by
  cases n with
  | zero => omega
  | succ r =>
      let p : ℕ := 2 * r + 1
      let q : ℕ := 2 * m + 1
      have hu : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
          HasDerivAt (fun y : ℝ => Real.cos y ^ p)
            ((p : ℝ) * Real.cos x ^ (p - 1) * (-Real.sin x)) x := by
        intro x hx
        simpa using (Real.hasDerivAt_cos x).pow p
      have hv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
          HasDerivAt (fun y : ℝ => Real.sin y ^ q)
            ((q : ℝ) * Real.sin x ^ (q - 1) * Real.cos x) x := by
        intro x hx
        simpa using (Real.hasDerivAt_sin x).pow q
      have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
        (((by fun_prop) : Continuous fun x : ℝ =>
          (p : ℝ) * Real.cos x ^ (p - 1) * (-Real.sin x)).intervalIntegrable 0
            (Real.pi / 2))
        (((by fun_prop) : Continuous fun x : ℝ =>
          (q : ℝ) * Real.sin x ^ (q - 1) * Real.cos x).intervalIntegrable 0
            (Real.pi / 2))
      have hleft :
          (∫ x in (0 : ℝ)..Real.pi / 2,
              Real.cos x ^ p *
                ((q : ℝ) * Real.sin x ^ (q - 1) * Real.cos x)) =
            (q : ℝ) * quarterIntegral m (r + 1) := by
        calc
          _ = ∫ x in (0 : ℝ)..Real.pi / 2,
                (q : ℝ) * integrand m (r + 1) x := by
                  apply intervalIntegral.integral_congr
                  intro x hx
                  simp only [integrand]
                  have hq : q - 1 = 2 * m := by simp [q]
                  have hp : 2 * (r + 1) = p + 1 := by
                    dsimp [p]
                    omega
                  rw [hq, hp]
                  rw [pow_succ]
                  ring
          _ = (q : ℝ) * quarterIntegral m (r + 1) := by
                simpa only [quarterIntegral] using
                  (intervalIntegral.integral_const_mul (a := (0 : ℝ))
                    (b := Real.pi / 2) (q : ℝ) (integrand m (r + 1)))
      have hboundary :
          Real.cos (Real.pi / 2) ^ p * Real.sin (Real.pi / 2) ^ q -
              Real.cos 0 ^ p * Real.sin 0 ^ q = 0 := by
        simp [p, q]
      have hright :
          -(∫ x in (0 : ℝ)..Real.pi / 2,
              ((p : ℝ) * Real.cos x ^ (p - 1) * (-Real.sin x)) *
                Real.sin x ^ q) =
            (p : ℝ) *
              ∫ x in (0 : ℝ)..Real.pi / 2,
                Real.sin x ^ (2 * m + 2) * Real.cos x ^ (2 * r) := by
        calc
          _ = ∫ x in (0 : ℝ)..Real.pi / 2,
                (p : ℝ) *
                  (Real.sin x ^ (2 * m + 2) * Real.cos x ^ (2 * r)) := by
                    rw [← intervalIntegral.integral_neg]
                    apply intervalIntegral.integral_congr
                    intro x hx
                    dsimp
                    have hp : p - 1 = 2 * r := by simp [p]
                    have hq : 2 * m + 2 = q + 1 := by simp [q]
                    rw [hp, hq]
                    rw [pow_succ]
                    ring
          _ = (p : ℝ) *
                ∫ x in (0 : ℝ)..Real.pi / 2,
                  Real.sin x ^ (2 * m + 2) * Real.cos x ^ (2 * r) := by
                    rw [intervalIntegral.integral_const_mul]
      have hparts :
          (q : ℝ) * quarterIntegral m (r + 1) =
            (p : ℝ) *
              ∫ x in (0 : ℝ)..Real.pi / 2,
                Real.sin x ^ (2 * m + 2) * Real.cos x ^ (2 * r) := by
        rw [hleft, hboundary, zero_sub, hright] at H
        exact H
      have hrewrite :
          (∫ x in (0 : ℝ)..Real.pi / 2,
              Real.sin x ^ (2 * m + 2) * Real.cos x ^ (2 * r)) =
            quarterIntegral m r - quarterIntegral m (r + 1) := by
        rw [quarterIntegral, quarterIntegral]
        calc
          _ = ∫ x in (0 : ℝ)..Real.pi / 2,
                (integrand m r x - integrand m (r + 1) x) := by
                  apply intervalIntegral.integral_congr
                  intro x hx
                  simp only [integrand]
                  rw [show 2 * (r + 1) = 2 * r + 2 by omega]
                  rw [pow_add (Real.sin x) (2 * m) 2,
                    pow_add (Real.cos x) (2 * r) 2]
                  have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
                    nlinarith [Real.sin_sq_add_cos_sq x]
                  rw [hs]
                  ring
          _ = (∫ x in (0 : ℝ)..Real.pi / 2, integrand m r x) -
                ∫ x in (0 : ℝ)..Real.pi / 2, integrand m (r + 1) x := by
                  have hir : IntervalIntegrable (integrand m r)
                      MeasureTheory.volume 0 (Real.pi / 2) :=
                    (((by unfold integrand; fun_prop) : Continuous (integrand m r)).intervalIntegrable
                      0 (Real.pi / 2))
                  have his : IntervalIntegrable (integrand m (r + 1))
                      MeasureTheory.volume 0 (Real.pi / 2) :=
                    (((by unfold integrand; fun_prop) : Continuous (integrand m (r + 1))).intervalIntegrable
                      0 (Real.pi / 2))
                  rw [intervalIntegral.integral_sub hir his]
      rw [hrewrite] at hparts
      dsimp [p, q] at hparts
      norm_num [Nat.cast_add, Nat.cast_mul] at hparts ⊢
      field_simp
      linarith

private theorem quarterIntegral_zero (n : ℕ) :
    quarterIntegral 0 n = closedForm 0 n := by
  induction n with
  | zero => norm_num [quarterIntegral, integrand, closedForm]
  | succ n ih =>
      rw [quarterIntegral_recurrence 0 (n + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih]
      have hfac2 : Nat.factorial (2 * (n + 1)) =
          (2 * n + 2) * (2 * n + 1) * Nat.factorial (2 * n) := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
        ring
      simp only [closedForm]
      rw [hfac2]
      norm_num [Nat.factorial_succ, pow_succ]
      field_simp
      ring

private theorem quarterIntegral_closedForm (m n : ℕ) :
    quarterIntegral m n = closedForm m n := by
  induction n with
  | zero =>
      rw [quarterIntegral_symm, quarterIntegral_zero]
      simp [closedForm, mul_comm, mul_left_comm, mul_assoc]
  | succ n ih =>
      rw [quarterIntegral_recurrence m (n + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih]
      have hfac2 : Nat.factorial (2 * (n + 1)) =
          (2 * n + 2) * (2 * n + 1) * Nat.factorial (2 * n) := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
        ring
      have hfacSum : Nat.factorial (m + (n + 1)) =
          (m + n + 1) * Nat.factorial (m + n) := by
        rw [show m + (n + 1) = (m + n) + 1 by omega, Nat.factorial_succ]
      simp only [closedForm]
      rw [hfac2, hfacSum]
      norm_num [Nat.factorial_succ, pow_succ]
      field_simp
      ring

private theorem shiftedIntegral_eq_sub (m r : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ (2 * m + 2) * Real.cos x ^ (2 * r)) =
      quarterIntegral m r - quarterIntegral m (r + 1) := by
  rw [quarterIntegral, quarterIntegral]
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
          (integrand m r x - integrand m (r + 1) x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp only [integrand]
            rw [show 2 * (r + 1) = 2 * r + 2 by omega]
            rw [pow_add (Real.sin x) (2 * m) 2,
              pow_add (Real.cos x) (2 * r) 2]
            have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
              nlinarith [Real.sin_sq_add_cos_sq x]
            rw [hs]
            ring
    _ = (∫ x in (0 : ℝ)..Real.pi / 2, integrand m r x) -
          ∫ x in (0 : ℝ)..Real.pi / 2, integrand m (r + 1) x := by
            have hir : IntervalIntegrable (integrand m r)
                MeasureTheory.volume 0 (Real.pi / 2) :=
              (((by unfold integrand; fun_prop) : Continuous (integrand m r)).intervalIntegrable
                0 (Real.pi / 2))
            have his : IntervalIntegrable (integrand m (r + 1))
                MeasureTheory.volume 0 (Real.pi / 2) :=
              (((by unfold integrand; fun_prop) : Continuous (integrand m (r + 1))).intervalIntegrable
                0 (Real.pi / 2))
            rw [intervalIntegral.integral_sub hir his]

private theorem integral_exp_int_frequency (z : ℤ) :
    (∫ x in (0 : ℝ)..2 * Real.pi,
        Complex.exp ((Complex.I * (z : ℂ)) * (x : ℂ))) =
      if z = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hz : z = 0
  · subst z
    simp
    calc
      (2 * Real.pi : ℝ) • (1 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * 1 := by
        exact Complex.real_smul
      _ = 2 * (Real.pi : ℂ) := by push_cast; ring
  · rw [if_neg hz]
    have hc : Complex.I * (z : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hz)
    rw [integral_exp_mul_complex hc]
    have hsin : Real.sin ((z : ℝ) * (2 * Real.pi)) = 0 := by
      convert Real.sin_int_mul_pi (2 * z) using 1 <;> push_cast <;> ring
    have hend :
        Complex.exp ((Complex.I * (z : ℂ)) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      calc
        _ = Complex.exp ((((z : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) := by
              congr 1
              push_cast
              ring
        _ = Complex.cos (((z : ℝ) * (2 * Real.pi) : ℝ) : ℂ) +
              Complex.sin (((z : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
                rw [Complex.exp_mul_I]
        _ = 1 := by
              rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
                Real.cos_int_mul_two_pi, hsin]
              norm_num
    rw [hend]
    simp

theorem gap1 (m n : ℕ) :
    quarterIntegral m n = (1 / 4 : ℝ) * fullIntegral m n := by
  rw [fullIntegral_eq_four_mul_quarter]
  ring

theorem gap2 (m n : ℕ) (x : ℝ) :
    (integrand m n x : ℂ) =
      ((Complex.exp (Complex.I * x) - Complex.exp (-Complex.I * x)) /
          (2 * Complex.I)) ^ (2 * m) *
        ((Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) /
          2) ^ (2 * n) := by
  have hsin : (Real.sin x : ℂ) =
      (Complex.exp (Complex.I * x) - Complex.exp (-Complex.I * x)) /
        (2 * Complex.I) := by
    rw [Complex.ofReal_sin, Complex.sin]
    rw [show -(x : ℂ) * Complex.I = -Complex.I * x by ring,
      show (x : ℂ) * Complex.I = Complex.I * x by ring]
    field_simp [Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  have hcos : (Real.cos x : ℂ) =
      (Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
    congr 3 <;> ring
  rw [integrand]
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
  rw [hsin, hcos]

theorem gap3 (m n : ℕ) (x : ℝ) :
    (integrand m n x : ℂ) = complexExpansion m n x := by
  rw [gap2]
  let ep : ℂ := Complex.exp (Complex.I * (x : ℂ))
  let em : ℂ := Complex.exp (-Complex.I * (x : ℂ))
  let S : ℂ :=
    ∑ k ∈ Finset.range (2 * m + 1),
      ∑ l ∈ Finset.range (2 * n + 1),
        (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
          (Nat.choose (2 * n) l : ℂ) *
          Complex.exp (Complex.I * (frequency m n k l : ℂ) * (x : ℂ))
  have hexp (k l : ℕ) (hk : k ≤ 2 * m) (hl : l ≤ 2 * n) :
      em ^ k * ep ^ (2 * m - k) * em ^ l * ep ^ (2 * n - l) =
        Complex.exp (Complex.I * (frequency m n k l : ℂ) * (x : ℂ)) := by
    dsimp [em, ep]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub hk, Nat.cast_sub hl]
    simp only [frequency]
    push_cast
    ring
  have hnum : (ep - em) ^ (2 * m) * (ep + em) ^ (2 * n) = S := by
    rw [show ep - em = (-em) + ep by ring, add_pow,
      show ep + em = em + ep by ring, add_pow]
    dsimp [S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hk' : k ≤ 2 * m := by
      rw [Finset.mem_range] at hk
      omega
    have hl' : l ≤ 2 * n := by
      rw [Finset.mem_range] at hl
      omega
    have hneg : (-em) ^ k = (-1 : ℂ) ^ k * em ^ k := by
      have hbase : -em = (-1 : ℂ) * em := by ring
      rw [hbase, mul_pow]
    rw [hneg]
    calc
      _ = (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
          (Nat.choose (2 * n) l : ℂ) *
            (em ^ k * ep ^ (2 * m - k) * em ^ l * ep ^ (2 * n - l)) := by ring
      _ = _ := by rw [hexp k l hk' hl']
  have hden : ((2 : ℂ) * Complex.I) ^ (2 * m) * (2 : ℂ) ^ (2 * n) =
      (-1 : ℂ) ^ m * (2 : ℂ) ^ (2 * m + 2 * n) := by
    have hIpow : Complex.I ^ (2 * m) = (-1 : ℂ) ^ m := by
      rw [pow_mul, Complex.I_sq]
    rw [mul_pow, hIpow]
    calc
      (2 : ℂ) ^ (2 * m) * (-1 : ℂ) ^ m * (2 : ℂ) ^ (2 * n) =
          (-1 : ℂ) ^ m * ((2 : ℂ) ^ (2 * m) * (2 : ℂ) ^ (2 * n)) := by ring
      _ = _ := by rw [← pow_add]
  rw [show Complex.exp (Complex.I * (x : ℂ)) = ep by rfl,
    show Complex.exp (-Complex.I * (x : ℂ)) = em by rfl]
  rw [div_pow, div_pow]
  calc
    (ep - em) ^ (2 * m) / (2 * Complex.I) ^ (2 * m) *
          ((ep + em) ^ (2 * n) / 2 ^ (2 * n)) =
        ((ep - em) ^ (2 * m) * (ep + em) ^ (2 * n)) /
          (((2 : ℂ) * Complex.I) ^ (2 * m) * (2 : ℂ) ^ (2 * n)) := by ring
    _ = S / (((2 : ℂ) * Complex.I) ^ (2 * m) * (2 : ℂ) ^ (2 * n)) := by
          rw [hnum]
    _ = (-1 : ℂ) ^ m / (2 : ℂ) ^ (2 * m + 2 * n) * S := by
          rw [hden]
          have hinv : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by
            rw [← inv_pow]
            norm_num
          rw [div_eq_mul_inv, mul_inv_rev, hinv]
          ring
    _ = complexExpansion m n x := by rfl

theorem gap4 (m n : ℕ) (x : ℝ) :
    (integrand m n x : ℂ) = trigExpansion m n x := by
  rw [gap3]
  unfold complexExpansion trigExpansion
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  let t : ℝ := (frequency m n k l : ℝ) * x
  have harg : Complex.I * (frequency m n k l : ℂ) * (x : ℂ) =
      Complex.I * (t : ℂ) := by
    dsimp [t]
    push_cast
    ring
  have heuler : Complex.exp (Complex.I * (t : ℂ)) =
      (Real.cos t : ℂ) + Complex.I * Real.sin t := by
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring,
      Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [harg, heuler]

theorem gap5 (m n : ℕ) (hmn : m ≤ n) :
    (fullIntegral m n : ℂ) =
      ∫ x in (0 : ℝ)..2 * Real.pi, trigExpansion m n x := by
  rw [fullIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  exact gap4 m n x

private theorem fullIntegral_eq_zeroFrequency (m n : ℕ) (hmn : m ≤ n)
    (hpos : 0 < m + n) :
    fullIntegral m n =
      (-1 : ℝ) ^ m * Real.pi / 2 ^ (2 * m + 2 * n - 1) *
        zeroFrequencySum m n := by
  let A : ℂ := (-1 : ℂ) ^ m / (2 : ℂ) ^ (2 * m + 2 * n)
  let c : ℕ → ℕ → ℂ := fun k l =>
    (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
      (Nat.choose (2 * n) l : ℂ)
  have hfullC : (fullIntegral m n : ℂ) =
      ∫ x in (0 : ℝ)..2 * Real.pi, complexExpansion m n x := by
    rw [fullIntegral, ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    exact gap3 m n x
  have hint :
      (∫ x in (0 : ℝ)..2 * Real.pi, complexExpansion m n x) =
        A * ∑ k ∈ Finset.range (2 * m + 1),
          ∑ l ∈ Finset.range (2 * n + 1),
            c k l * (if frequency m n k l = 0 then (2 * Real.pi : ℂ) else 0) := by
    let F : ℝ → ℂ := fun x =>
      ∑ k ∈ Finset.range (2 * m + 1),
          ∑ l ∈ Finset.range (2 * n + 1),
            c k l * Complex.exp
              (Complex.I * (frequency m n k l : ℂ) * (x : ℂ))
    change (∫ x in (0 : ℝ)..2 * Real.pi, A * F x) = _
    calc
      _ = A * (∫ x in (0 : ℝ)..2 * Real.pi, F x) :=
        intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := 2 * Real.pi) A F
      _ = _ := by
        congr 1
        dsimp [F]
        rw [intervalIntegral.integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro k hk
          rw [intervalIntegral.integral_finset_sum]
          · apply Finset.sum_congr rfl
            intro l hl
            calc
              (∫ x in (0 : ℝ)..2 * Real.pi,
                  c k l * Complex.exp
                    (Complex.I * (frequency m n k l : ℂ) * (x : ℂ))) =
                  c k l * (∫ x in (0 : ℝ)..2 * Real.pi,
                    Complex.exp (Complex.I * (frequency m n k l : ℂ) * (x : ℂ))) :=
                intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
                  (a := (0 : ℝ)) (b := 2 * Real.pi) (c k l)
                    (fun x : ℝ => Complex.exp
                      (Complex.I * (frequency m n k l : ℂ) * (x : ℂ)))
              _ = _ := by rw [integral_exp_int_frequency]
          · intro l hl
            exact (((by fun_prop) : Continuous fun x : ℝ =>
              (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
                (Nat.choose (2 * n) l : ℂ) *
                  Complex.exp (Complex.I * (frequency m n k l : ℂ) * (x : ℂ))).intervalIntegrable
                    0 (2 * Real.pi))
        · intro k hk
          exact (((by fun_prop) : Continuous fun x : ℝ =>
            ∑ l ∈ Finset.range (2 * n + 1),
              (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
                (Nat.choose (2 * n) l : ℂ) *
                  Complex.exp (Complex.I * (frequency m n k l : ℂ) * (x : ℂ))).intervalIntegrable
                    0 (2 * Real.pi))
  have hcollapse :
      (∑ k ∈ Finset.range (2 * m + 1),
          ∑ l ∈ Finset.range (2 * n + 1),
            c k l * (if frequency m n k l = 0 then (2 * Real.pi : ℂ) else 0)) =
        (zeroFrequencySum m n : ℂ) * (2 * Real.pi : ℂ) := by
    have hzeroCast : (zeroFrequencySum m n : ℂ) =
        ∑ k ∈ Finset.range (2 * m + 1),
          (-1 : ℂ) ^ k * (Nat.choose (2 * m) k : ℂ) *
            (Nat.choose (2 * n) (m + n - k) : ℂ) := by
      unfold zeroFrequencySum
      push_cast
      rfl
    rw [hzeroCast]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2m : k ≤ 2 * m := by
      rw [Finset.mem_range] at hk
      omega
    have hkmn : k ≤ m + n := by omega
    let j : ℕ := m + n - k
    have hj2n : j ≤ 2 * n := by
      dsimp [j]
      omega
    have hjmem : j ∈ Finset.range (2 * n + 1) := by
      rw [Finset.mem_range]
      omega
    have hfreqj : frequency m n k j = 0 := by
      unfold frequency
      dsimp [j]
      rw [Nat.cast_sub hkmn]
      push_cast
      ring
    rw [Finset.sum_eq_single j]
    · dsimp [c]
      rw [if_pos hfreqj]
    · intro l hl hlj
      have hfreq : frequency m n k l ≠ 0 := by
        intro hf
        apply hlj
        unfold frequency at hf
        dsimp [j]
        omega
      simp [hfreq]
    · intro hjnot
      exact (hjnot hjmem).elim
  rw [hint, hcollapse] at hfullC
  apply Complex.ofReal_injective
  push_cast
  rw [hfullC]
  dsimp [A]
  have hs : 0 < 2 * m + 2 * n := by omega
  have hpow : (2 : ℂ) ^ (2 * m + 2 * n) =
      (2 : ℂ) ^ (2 * m + 2 * n - 1) * 2 := by
    calc
      (2 : ℂ) ^ (2 * m + 2 * n) =
          (2 : ℂ) ^ ((2 * m + 2 * n - 1) + 1) := by congr 1 <;> omega
      _ = _ := by rw [pow_succ]
  rw [hpow]
  field_simp

theorem gap6 (m n : ℕ) (hmn : m ≤ n) (hpos : 0 < m + n) :
    fullIntegral m n =
      (-1 : ℝ) ^ m * Real.pi / 2 ^ (2 * m + 2 * n - 1) *
        zeroFrequencySum m n := by
  exact fullIntegral_eq_zeroFrequency m n hmn hpos

theorem gap7 (m n : ℕ) (hmn : m ≤ n) :
    (-1 : ℝ) ^ m * zeroFrequencySum m n =
      (Nat.factorial (2 * m) : ℝ) * (Nat.factorial (2 * n) : ℝ) /
        ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ) *
          (Nat.factorial (m + n) : ℝ)) := by
  by_cases hzero : m + n = 0
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst m
    subst n
    norm_num [zeroFrequencySum]
  · have hpos : 0 < m + n := Nat.pos_of_ne_zero hzero
    have hfour := fullIntegral_eq_four_mul_quarter m n
    have hclosed := quarterIntegral_closedForm m n
    have hfreq := fullIntegral_eq_zeroFrequency m n hmn hpos
    rw [hfour, hclosed] at hfreq
    unfold closedForm at hfreq
    have hpow : (2 : ℝ) ^ (2 * m + 2 * n + 1) =
        4 * (2 : ℝ) ^ (2 * m + 2 * n - 1) := by
      calc
        (2 : ℝ) ^ (2 * m + 2 * n + 1) =
            (2 : ℝ) ^ ((2 * m + 2 * n - 1) + 2) := by congr 1 <;> omega
        _ = _ := by rw [pow_add]; norm_num; ring
    rw [hpow] at hfreq
    field_simp [Real.pi_ne_zero] at hfreq ⊢
    ring_nf at hfreq ⊢
    exact hfreq.symm

theorem gap8 (m n : ℕ) :
    quarterIntegral m n = (1 / 4 : ℝ) * fullIntegral m n := by
  exact gap1 m n

theorem gap9 (m n : ℕ) :
    (1 / 4 : ℝ) * fullIntegral m n = closedForm m n := by
  rw [← gap1 m n]
  exact quarterIntegral_closedForm m n

theorem gap10 (m n : ℕ) :
    quarterIntegral m n = closedForm m n := by
  exact quarterIntegral_closedForm m n

theorem gap11 (m : ℕ) :
    quarterIntegral m 0 =
      ∫ x in 0..Real.pi / 2, Real.sin x ^ (2 * m) := by
  simp [quarterIntegral, integrand]

theorem gap12 (m : ℕ) :
    (∫ x in 0..Real.pi / 2, Real.sin x ^ (2 * m)) =
      (Nat.factorial (2 * m) : ℝ) /
          (2 ^ (2 * m) * (Nat.factorial m : ℝ) ^ 2) *
        (Real.pi / 2) := by
  rw [← gap11 m, quarterIntegral_closedForm]
  simp only [closedForm]
  norm_num
  field_simp
  ring

theorem gap13 (m : ℕ) :
    quarterIntegral m 0 =
      (Nat.factorial (2 * m) : ℝ) /
          (2 ^ (2 * m) * (Nat.factorial m : ℝ) ^ 2) *
        (Real.pi / 2) := by
  rw [gap11, gap12]

theorem gap14 (m n : ℕ) (hn : 0 < n) :
    quarterIntegral m n =
      ∫ x in 0..Real.pi / 2,
        Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n - 1) *
          deriv Real.sin x := by
  rw [quarterIntegral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hd : deriv Real.sin x = Real.cos x := (Real.hasDerivAt_sin x).deriv
  have hcos : Real.cos x ^ (2 * n) =
      Real.cos x ^ (2 * n - 1) * Real.cos x := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [integrand, hd]
  rw [hcos]
  ring

theorem gap15 (m n : ℕ) (hn : 0 < n) :
    (∫ x in 0..Real.pi / 2,
        Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n - 1) *
          deriv Real.sin x) =
      1 / ((2 * m + 1 : ℕ) : ℝ) *
        ∫ x in 0..Real.pi / 2,
          Real.cos x ^ (2 * n - 1) *
            deriv (fun y : ℝ => Real.sin y ^ (2 * m + 1)) x := by
  have hdsin : ∀ x : ℝ, deriv Real.sin x = Real.cos x := fun x =>
    (Real.hasDerivAt_sin x).deriv
  have hdpow : ∀ x : ℝ,
      deriv (fun y : ℝ => Real.sin y ^ (2 * m + 1)) x =
        (((2 * m + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * m) * Real.cos x) := by
    intro x
    convert ((Real.hasDerivAt_sin x).pow (2 * m + 1)).deriv using 1 <;> norm_num
  simp_rw [hdsin, hdpow]
  have hInt :
      (∫ x in (0 : ℝ)..Real.pi / 2,
          Real.cos x ^ (2 * n - 1) *
            (((2 * m + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * m) * Real.cos x)) =
        (((2 * m + 1 : ℕ) : ℝ) *
          ∫ x in (0 : ℝ)..Real.pi / 2,
            Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n - 1) * Real.cos x) := by
    calc
      _ = ∫ x in (0 : ℝ)..Real.pi / 2,
            (((2 * m + 1 : ℕ) : ℝ) *
              (Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n - 1) * Real.cos x)) := by
                apply intervalIntegral.integral_congr
                intro x hx
                ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hInt]
  have hne : (((2 * m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem gap16 (m n : ℕ) (hn : 0 < n) :
    quarterIntegral m n =
      1 / ((2 * m + 1 : ℕ) : ℝ) *
        ∫ x in 0..Real.pi / 2,
          Real.cos x ^ (2 * n - 1) *
            deriv (fun y : ℝ => Real.sin y ^ (2 * m + 1)) x := by
  exact (gap14 m n hn).trans (gap15 m n hn)

theorem gap17 (m n : ℕ) (hn : 0 < n) :
    quarterIntegral m n =
      ((2 * n - 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ) *
        ∫ x in 0..Real.pi / 2,
          Real.sin x ^ (2 * m + 2) * Real.cos x ^ (2 * n - 2) := by
  cases n with
  | zero => omega
  | succ r =>
      rw [show 2 * (r + 1) - 2 = 2 * r by omega, shiftedIntegral_eq_sub]
      have hrec := quarterIntegral_recurrence m (r + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hrec
      simp_rw [hrec]
      norm_num [Nat.cast_add, Nat.cast_mul]
      field_simp
      ring

theorem gap18 (m n : ℕ) (hn : 0 < n) :
    quarterIntegral m n =
      ((2 * n - 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ) *
          quarterIntegral m (n - 1) -
        ((2 * n - 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ) *
          quarterIntegral m n := by
  have hrec := quarterIntegral_recurrence m n hn
  have hcast : (((2 * n - 1 : ℕ) : ℝ)) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    norm_num
  rw [hcast] at hrec ⊢
  simp_rw [hrec]
  norm_num [Nat.cast_add, Nat.cast_mul]
  field_simp
  ring

theorem gap19 (m n : ℕ) (hn : 0 < n) :
    quarterIntegral m n =
      ((2 * n - 1 : ℕ) : ℝ) / (2 * ((m + n : ℕ) : ℝ)) *
        quarterIntegral m (n - 1) := by
  exact quarterIntegral_recurrence m n hn

theorem gap20 (m n : ℕ) :
    quarterIntegral m n = closedForm m n := by
  exact quarterIntegral_closedForm m n

end

end ProofGap.Exercise2290
