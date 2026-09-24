import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2294

noncomputable section

def originalIntegral (n : ℕ) : ℝ :=
  ∫ x in 0..Real.pi, Real.sin x ^ n * Real.sin ((n : ℝ) * x)

def frequency (n k : ℕ) : ℤ := (n : ℤ) - 2 * k

def complexSummand (n k : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
    Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) *
    (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) -
      Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))

def complexRepresentation (n : ℕ) : ℂ :=
  1 / (2 * Complex.I) ^ (n + 1) *
    ∫ x in (0 : ℝ)..Real.pi,
      ∑ k ∈ Finset.range (n + 1), complexSummand n k x

def collapsedValue (n : ℕ) : ℂ :=
  1 / ((2 : ℂ) ^ (n + 1) * Complex.I ^ (n + 1)) *
    (((-1 : ℂ) ^ n * (Real.pi : ℂ)) - (Real.pi : ℂ))

def parityValue (n : ℕ) : ℝ :=
  if Even n then 0
  else Real.pi / (2 : ℝ) ^ n * (-1 : ℝ) ^ ((n + 1) / 2 + 1)

private theorem sine_complex (x : ℝ) :
    (Real.sin x : ℂ) =
      (Complex.exp (Complex.I * x) - Complex.exp (-Complex.I * x)) /
        (2 * Complex.I) := by
  rw [Complex.ofReal_sin, Complex.sin]
  rw [show -(x : ℂ) * Complex.I = -Complex.I * x by ring,
    show (x : ℂ) * Complex.I = Complex.I * x by ring]
  field_simp [Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

private theorem sin_pow_complex_expansion (n : ℕ) (x : ℝ) :
    (Real.sin x ^ n : ℂ) =
      1 / (2 * Complex.I) ^ n *
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
            Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) := by
  let ep : ℂ := Complex.exp (Complex.I * (x : ℂ))
  let em : ℂ := Complex.exp (-Complex.I * (x : ℂ))
  have hexp (k : ℕ) (hk : k ≤ n) :
      em ^ k * ep ^ (n - k) =
        Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) := by
    dsimp [em, ep]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub hk]
    simp only [frequency]
    push_cast
    ring
  have hnum : (ep - em) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
          Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) := by
    rw [show ep - em = (-em) + ep by ring, add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      rw [Finset.mem_range] at hk
      omega
    have hneg : (-em) ^ k = (-1 : ℂ) ^ k * em ^ k := by
      have hbase : -em = (-1 : ℂ) * em := by ring
      rw [hbase, mul_pow]
    rw [hneg]
    calc
      _ = (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
          (em ^ k * ep ^ (n - k)) := by ring
      _ = _ := by rw [hexp k hk']
  rw [sine_complex, div_pow]
  rw [show Complex.exp (Complex.I * (x : ℂ)) = ep by rfl,
    show Complex.exp (-Complex.I * (x : ℂ)) = em by rfl]
  rw [hnum]
  ring

private theorem integral_exp_even_frequency (z : ℤ) :
    (∫ x in (0 : ℝ)..Real.pi,
        Complex.exp ((Complex.I * ((2 * z : ℤ) : ℂ)) * (x : ℂ))) =
      if z = 0 then (Real.pi : ℂ) else 0 := by
  by_cases hz : z = 0
  · subst z
    simp
    calc
      Real.pi • (1 : ℂ) = (Real.pi : ℂ) * 1 := by exact Complex.real_smul
      _ = (Real.pi : ℂ) := by ring
  · rw [if_neg hz]
    have h2z : (2 * z : ℤ) ≠ 0 := by omega
    have hc : Complex.I * ((2 * z : ℤ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr h2z)
    rw [integral_exp_mul_complex hc]
    have hsin : Real.sin ((z : ℝ) * (2 * Real.pi)) = 0 := by
      convert Real.sin_int_mul_pi (2 * z) using 1 <;> push_cast <;> ring
    have hend :
        Complex.exp ((Complex.I * ((2 * z : ℤ) : ℂ)) * (Real.pi : ℂ)) = 1 := by
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

private theorem sine_nat_pi_div_two (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi / 2) =
      if Even n then 0 else (-1 : ℝ) ^ ((n + 1) / 2 + 1) := by
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · rw [if_pos (even_two_mul k)]
    rw [show ((2 * k : ℕ) : ℝ) * Real.pi / 2 = (k : ℝ) * Real.pi by
      push_cast; ring]
    exact Real.sin_nat_mul_pi k
  · rw [if_neg (Nat.not_even_two_mul_add_one k)]
    rw [show ((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2 =
        (k : ℝ) * Real.pi + Real.pi / 2 by push_cast; ring,
      Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [hdiv, show k + 1 + 1 = k + 2 by omega, pow_add]
    norm_num

private theorem collapsedValue_eq_parityValue (n : ℕ) :
    collapsedValue n = (parityValue n : ℂ) := by
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · rw [parityValue, if_pos (even_two_mul k)]
    simp [collapsedValue, pow_mul]
  · have hnot : ¬Even (2 * k + 1) := Nat.not_even_two_mul_add_one k
    rw [parityValue, if_neg hnot]
    unfold collapsedValue
    have hExp : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    have hIpow : Complex.I ^ (2 * k + 1 + 1) = (-1 : ℂ) ^ (k + 1) := by
      rw [hExp, pow_mul, Complex.I_sq]
    have hnegpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
      rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_succ, pow_mul]
      norm_num
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have hinv : ((-1 : ℂ) ^ (k + 1))⁻¹ = (-1 : ℂ) ^ (k + 1) := by
      rw [← inv_pow]
      norm_num
    rw [hIpow, hnegpow, hdiv]
    push_cast
    have h2pow : (2 : ℂ) ^ (2 * k + 1 + 1) =
        (2 : ℂ) ^ (2 * k + 1) * 2 := by rw [pow_succ]
    rw [h2pow]
    rw [div_eq_mul_inv, mul_inv_rev, hinv]
    rw [show k + 1 + 1 = (k + 1) + 1 by rfl, pow_succ]
    norm_num
    ring

theorem gap1 (n : ℕ) (hn : 0 < n) :
    (originalIntegral n : ℂ) = complexRepresentation n := by
  rw [originalIntegral, ← intervalIntegral.integral_ofReal]
  unfold complexRepresentation
  let C : ℂ := 1 / (2 * Complex.I) ^ (n + 1)
  let F : ℝ → ℂ := fun x =>
    ∑ k ∈ Finset.range (n + 1), complexSummand n k x
  change (∫ x in (0 : ℝ)..Real.pi,
      ((Real.sin x ^ n * Real.sin ((n : ℝ) * x) : ℝ) : ℂ)) =
    C * ∫ x in (0 : ℝ)..Real.pi, F x
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi, C * F x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [C, F]
      rw [Complex.ofReal_mul, Complex.ofReal_pow,
        sin_pow_complex_expansion, sine_complex]
      have hnx : Complex.I * ((((n : ℝ) * x : ℝ)) : ℂ) =
          Complex.I * (n : ℂ) * (x : ℂ) := by push_cast; ring
      have hnneg : -Complex.I * ((((n : ℝ) * x : ℝ)) : ℂ) =
          -Complex.I * (n : ℂ) * (x : ℂ) := by push_cast; ring
      rw [hnx, hnneg]
      have hsum :
          (∑ k ∈ Finset.range (n + 1), complexSummand n k x) =
            (∑ k ∈ Finset.range (n + 1),
              (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
                Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ))) *
              (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) -
                Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rfl
      rw [hsum]
      let S : ℂ := ∑ k ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
          Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ))
      let E : ℂ := Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) -
        Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))
      change (1 / (2 * Complex.I) ^ n * S) * (E / (2 * Complex.I)) =
        1 / (2 * Complex.I) ^ (n + 1) * (S * E)
      rw [pow_succ]
      field_simp [Complex.I_ne_zero]
    _ = C * ∫ x in (0 : ℝ)..Real.pi, F x :=
      intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := Real.pi) C F

theorem gap2 (n : ℕ) (hn : 0 < n) :
    complexRepresentation n =
      1 / ((2 : ℂ) ^ (n + 1) * Complex.I ^ (n + 1)) *
        ((∑ k ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
              ∫ x in (0 : ℝ)..Real.pi,
                Complex.exp (Complex.I *
                  ((2 * (n : ℤ) - 2 * k : ℤ) : ℂ) * x)) -
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
              ∫ x in (0 : ℝ)..Real.pi,
                Complex.exp (-Complex.I * ((2 * k : ℕ) : ℂ) * x)) := by
  let a : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (Nat.choose n k : ℂ)
  let f₁ : ℕ → ℝ → ℂ := fun k x =>
    a k * Complex.exp
      (Complex.I * ((2 * (n : ℤ) - 2 * k : ℤ) : ℂ) * (x : ℂ))
  let f₂ : ℕ → ℝ → ℂ := fun k x =>
    a k * Complex.exp (-Complex.I * ((2 * k : ℕ) : ℂ) * (x : ℂ))
  have hpoint : ∀ x : ℝ,
      (∑ k ∈ Finset.range (n + 1), complexSummand n k x) =
        (∑ k ∈ Finset.range (n + 1), f₁ k x) -
          ∑ k ∈ Finset.range (n + 1), f₂ k x := by
    intro x
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hfirst :
        Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) *
            Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) =
          Complex.exp
            (Complex.I * ((2 * (n : ℤ) - 2 * k : ℤ) : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold frequency
      push_cast
      ring
    have hsecond :
        Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) *
            Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)) =
          Complex.exp (-Complex.I * ((2 * k : ℕ) : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold frequency
      push_cast
      ring
    dsimp [f₁, f₂, a, complexSummand]
    calc
      _ = ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ)) *
            (Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) *
              Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) -
          ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ)) *
            (Complex.exp (Complex.I * (frequency n k : ℂ) * (x : ℂ)) *
              Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))) := by ring
      _ = _ := by rw [hfirst, hsecond]
  have hsum₁ : IntervalIntegrable
      (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), f₁ k x)
      MeasureTheory.volume 0 Real.pi :=
    (((by dsimp [f₁, a]; fun_prop) : Continuous fun x : ℝ =>
      ∑ k ∈ Finset.range (n + 1), f₁ k x).intervalIntegrable 0 Real.pi)
  have hsum₂ : IntervalIntegrable
      (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), f₂ k x)
      MeasureTheory.volume 0 Real.pi :=
    (((by dsimp [f₂, a]; fun_prop) : Continuous fun x : ℝ =>
      ∑ k ∈ Finset.range (n + 1), f₂ k x).intervalIntegrable 0 Real.pi)
  have hinside :
      (∫ x in (0 : ℝ)..Real.pi,
          ∑ k ∈ Finset.range (n + 1), complexSummand n k x) =
        (∑ k ∈ Finset.range (n + 1),
            a k * ∫ x in (0 : ℝ)..Real.pi,
              Complex.exp
                (Complex.I * ((2 * (n : ℤ) - 2 * k : ℤ) : ℂ) * (x : ℂ))) -
          ∑ k ∈ Finset.range (n + 1),
            a k * ∫ x in (0 : ℝ)..Real.pi,
              Complex.exp (-Complex.I * ((2 * k : ℕ) : ℂ) * (x : ℂ)) := by
    calc
      _ = ∫ x in (0 : ℝ)..Real.pi,
            ((∑ k ∈ Finset.range (n + 1), f₁ k x) -
              ∑ k ∈ Finset.range (n + 1), f₂ k x) := by
                apply intervalIntegral.integral_congr
                intro x hx
                exact hpoint x
      _ = (∫ x in (0 : ℝ)..Real.pi,
              ∑ k ∈ Finset.range (n + 1), f₁ k x) -
            ∫ x in (0 : ℝ)..Real.pi,
              ∑ k ∈ Finset.range (n + 1), f₂ k x :=
          intervalIntegral.integral_sub hsum₁ hsum₂
      _ = (∑ k ∈ Finset.range (n + 1),
              ∫ x in (0 : ℝ)..Real.pi, f₁ k x) -
            ∑ k ∈ Finset.range (n + 1),
              ∫ x in (0 : ℝ)..Real.pi, f₂ k x := by
          rw [intervalIntegral.integral_finset_sum,
            intervalIntegral.integral_finset_sum]
          · intro k hk
            exact (((by dsimp [f₂, a]; fun_prop) : Continuous (f₂ k)).intervalIntegrable
              0 Real.pi)
          · intro k hk
            exact (((by dsimp [f₁, a]; fun_prop) : Continuous (f₁ k)).intervalIntegrable
              0 Real.pi)
      _ = _ := by
          apply congrArg₂ (· - ·)
          · apply Finset.sum_congr rfl
            intro k hk
            dsimp [f₁]
            exact intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
              (a := (0 : ℝ)) (b := Real.pi) (a k)
                (fun x : ℝ => Complex.exp
                  (Complex.I * ((2 * (n : ℤ) - 2 * k : ℤ) : ℂ) * (x : ℂ)))
          · apply Finset.sum_congr rfl
            intro k hk
            dsimp [f₂]
            exact intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
              (a := (0 : ℝ)) (b := Real.pi) (a k)
                (fun x : ℝ => Complex.exp
                  (-Complex.I * ((2 * k : ℕ) : ℂ) * (x : ℂ)))
  unfold complexRepresentation
  rw [hinside]
  dsimp [a]
  rw [mul_pow]

theorem gap3 (n : ℕ) (hn : 0 < n) :
    (originalIntegral n : ℂ) = collapsedValue n := by
  rw [gap1 n hn, gap2 n hn]
  unfold collapsedValue
  have hfirstInt (k : ℕ) :
      (∫ x in (0 : ℝ)..Real.pi,
          Complex.exp (Complex.I *
            ((2 * (n : ℤ) - 2 * k : ℤ) : ℂ) * (x : ℂ))) =
        if k = n then (Real.pi : ℂ) else 0 := by
    calc
      _ = ∫ x in (0 : ℝ)..Real.pi,
            Complex.exp
              ((Complex.I * ((2 * ((n : ℤ) - k) : ℤ) : ℂ)) * (x : ℂ)) := by
                apply intervalIntegral.integral_congr
                intro x hx
                congr 1
                push_cast
                ring
      _ = if (n : ℤ) - k = 0 then (Real.pi : ℂ) else 0 :=
        integral_exp_even_frequency ((n : ℤ) - k)
      _ = if k = n then (Real.pi : ℂ) else 0 := by
        have hiff : (n : ℤ) - k = 0 ↔ k = n := by
          constructor
          · intro h
            have hnk : (n : ℤ) = (k : ℤ) := sub_eq_zero.mp h
            exact_mod_cast hnk.symm
          · intro h
            subst k
            simp
        simp only [hiff]
  have hsecondInt (k : ℕ) :
      (∫ x in (0 : ℝ)..Real.pi,
          Complex.exp (-Complex.I * ((2 * k : ℕ) : ℂ) * (x : ℂ))) =
        if k = 0 then (Real.pi : ℂ) else 0 := by
    calc
      _ = ∫ x in (0 : ℝ)..Real.pi,
            Complex.exp
              ((Complex.I * ((2 * (-(k : ℤ)) : ℤ) : ℂ)) * (x : ℂ)) := by
                apply intervalIntegral.integral_congr
                intro x hx
                congr 1
                push_cast
                ring
      _ = if -(k : ℤ) = 0 then (Real.pi : ℂ) else 0 :=
        integral_exp_even_frequency (-(k : ℤ))
      _ = if k = 0 then (Real.pi : ℂ) else 0 := by
        have hiff : -(k : ℤ) = 0 ↔ k = 0 := by simp
        simp only [hiff]
  have hsum₁ :
      (∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
            ∫ x in (0 : ℝ)..Real.pi,
              Complex.exp (Complex.I *
                ((2 * (n : ℤ) - 2 * k : ℤ) : ℂ) * (x : ℂ))) =
        (-1 : ℂ) ^ n * (Real.pi : ℂ) := by
    rw [Finset.sum_eq_single n]
    · rw [hfirstInt, if_pos rfl]
      simp
    · intro k hk hkn
      rw [hfirstInt, if_neg hkn]
      simp
    · intro hnmem
      exfalso
      apply hnmem
      rw [Finset.mem_range]
      omega
  have hsum₂ :
      (∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) *
            ∫ x in (0 : ℝ)..Real.pi,
              Complex.exp (-Complex.I * ((2 * k : ℕ) : ℂ) * (x : ℂ))) =
        (Real.pi : ℂ) := by
    rw [Finset.sum_eq_single 0]
    · rw [hsecondInt, if_pos rfl]
      simp
    · intro k hk hk0
      rw [hsecondInt, if_neg hk0]
      simp
    · intro hzero
      exfalso
      apply hzero
      rw [Finset.mem_range]
      omega
  rw [hsum₁, hsum₂]

theorem gap4 (n : ℕ) (hn : 0 < n) :
    originalIntegral n = parityValue n := by
  apply Complex.ofReal_injective
  rw [gap3 n hn]
  exact collapsedValue_eq_parityValue n

theorem gap5 (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi / 2) =
      if Even n then 0 else (-1 : ℝ) ^ ((n + 1) / 2 + 1) := by
  exact sine_nat_pi_div_two n

theorem gap6 (n : ℕ) (hn : 0 < n) :
    originalIntegral n =
      Real.pi / (2 : ℝ) ^ n * Real.sin ((n : ℝ) * Real.pi / 2) := by
  rw [gap4 n hn]
  unfold parityValue
  rw [sine_nat_pi_div_two]
  by_cases h : Even n <;> simp [h]

theorem gap7 (n : ℕ) (hn : 0 < n) :
    originalIntegral n =
      ∫ t in -Real.pi / 2..Real.pi / 2,
        Real.cos t ^ n *
          Real.sin ((n : ℝ) * Real.pi / 2 - (n : ℝ) * t) := by
  rw [originalIntegral]
  let f : ℝ → ℝ := fun t => Real.cos t ^ n *
    Real.sin ((n : ℝ) * Real.pi / 2 - (n : ℝ) * t)
  calc
    (∫ x in (0 : ℝ)..Real.pi,
        Real.sin x ^ n * Real.sin ((n : ℝ) * x)) =
      ∫ x in (0 : ℝ)..Real.pi, f (Real.pi / 2 - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [f]
        rw [Real.cos_pi_div_two_sub]
        congr 2
        ring
    _ = ∫ t in Real.pi / 2 - Real.pi..Real.pi / 2 - 0, f t := by
      rw [intervalIntegral.integral_comp_sub_left]
    _ = ∫ t in -Real.pi / 2..Real.pi / 2, f t := by ring_nf

theorem gap8 (n : ℕ) (hn : 0 < n) :
    originalIntegral n =
      Real.sin ((n : ℝ) * Real.pi / 2) *
          (∫ t in -Real.pi / 2..Real.pi / 2,
            Real.cos t ^ n * Real.cos ((n : ℝ) * t)) -
        Real.cos ((n : ℝ) * Real.pi / 2) *
          ∫ t in -Real.pi / 2..Real.pi / 2,
            Real.cos t ^ n * Real.sin ((n : ℝ) * t) := by
  rw [gap7 n hn]
  let f : ℝ → ℝ := fun t => Real.cos t ^ n * Real.cos ((n : ℝ) * t)
  let g : ℝ → ℝ := fun t => Real.cos t ^ n * Real.sin ((n : ℝ) * t)
  have hf : IntervalIntegrable f MeasureTheory.volume
      (-Real.pi / 2) (Real.pi / 2) :=
    (((by dsimp [f]; fun_prop) : Continuous f).intervalIntegrable
      (-Real.pi / 2) (Real.pi / 2))
  have hg : IntervalIntegrable g MeasureTheory.volume
      (-Real.pi / 2) (Real.pi / 2) :=
    (((by dsimp [g]; fun_prop) : Continuous g).intervalIntegrable
      (-Real.pi / 2) (Real.pi / 2))
  calc
    (∫ t in -Real.pi / 2..Real.pi / 2,
        Real.cos t ^ n *
          Real.sin ((n : ℝ) * Real.pi / 2 - (n : ℝ) * t)) =
      ∫ t in -Real.pi / 2..Real.pi / 2,
        Real.sin ((n : ℝ) * Real.pi / 2) * f t -
          Real.cos ((n : ℝ) * Real.pi / 2) * g t := by
            apply intervalIntegral.integral_congr
            intro t ht
            dsimp [f, g]
            rw [Real.sin_sub]
            ring
    _ = (∫ t in -Real.pi / 2..Real.pi / 2,
          Real.sin ((n : ℝ) * Real.pi / 2) * f t) -
        ∫ t in -Real.pi / 2..Real.pi / 2,
          Real.cos ((n : ℝ) * Real.pi / 2) * g t := by
            rw [intervalIntegral.integral_sub (hf.const_mul _)
              (hg.const_mul _)]
    _ = Real.sin ((n : ℝ) * Real.pi / 2) *
          (∫ t in -Real.pi / 2..Real.pi / 2, f t) -
        Real.cos ((n : ℝ) * Real.pi / 2) *
          ∫ t in -Real.pi / 2..Real.pi / 2, g t := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]

theorem gap9 (n : ℕ) (hn : 0 < n) :
    originalIntegral n =
      Real.sin ((n : ℝ) * Real.pi / 2) *
        ∫ x in 0..Real.pi,
          Real.cos x ^ n * Real.cos ((n : ℝ) * x) := by
  let f : ℝ → ℝ := fun x => Real.cos x ^ n * Real.cos ((n : ℝ) * x)
  let g : ℝ → ℝ := fun x => Real.cos x ^ n * Real.sin ((n : ℝ) * x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hodd : (∫ x in -Real.pi / 2..Real.pi / 2, g x) = 0 := by
    have hnegPoint : ∀ x : ℝ, g (-x) = -g x := by
      intro x
      dsimp [g]
      rw [Real.cos_neg]
      have harg : (n : ℝ) * -x = -((n : ℝ) * x) := by ring
      rw [harg, Real.sin_neg]
      ring
    have hcomp := intervalIntegral.integral_comp_neg g
      (a := -Real.pi / 2) (b := Real.pi / 2)
    have hcomp' :
        (∫ x in -Real.pi / 2..Real.pi / 2, g (-x)) =
          ∫ x in -Real.pi / 2..Real.pi / 2, g x := by
      convert hcomp using 1 <;> ring
    have hleft :
        (∫ x in -Real.pi / 2..Real.pi / 2, g (-x)) =
          -(∫ x in -Real.pi / 2..Real.pi / 2, g x) := by
      calc
        _ = ∫ x in -Real.pi / 2..Real.pi / 2, -g x := by
              apply intervalIntegral.integral_congr
              intro x hx
              exact hnegPoint x
        _ = _ := intervalIntegral.integral_neg
    linarith
  have heven :
      (∫ x in -Real.pi / 2..Real.pi / 2, f x) =
        ∫ x in (0 : ℝ)..Real.pi, f x := by
    have hnegPoint : ∀ x : ℝ, f (-x) = f x := by
      intro x
      dsimp [f]
      rw [Real.cos_neg]
      have harg : (n : ℝ) * -x = -((n : ℝ) * x) := by ring
      rw [harg, Real.cos_neg]
    have hneg :
        (∫ x in -Real.pi / 2..0, f x) =
          ∫ x in (0 : ℝ)..Real.pi / 2, f x := by
      have hcomp := intervalIntegral.integral_comp_neg f
        (a := (0 : ℝ)) (b := Real.pi / 2)
      calc
        _ = ∫ x in (0 : ℝ)..Real.pi / 2, f (-x) := by
              convert hcomp.symm using 1 <;> ring
        _ = _ := by
              apply intervalIntegral.integral_congr
              intro x hx
              exact hnegPoint x
    have hmirrorPoint : ∀ x : ℝ, f (Real.pi - x) = f x := by
      intro x
      dsimp [f]
      rw [Real.cos_pi_sub]
      have harg : (n : ℝ) * (Real.pi - x) =
          (n : ℝ) * Real.pi - (n : ℝ) * x := by ring
      rw [harg, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      rw [neg_pow]
      norm_num
      ring_nf
      have hsign : (-1 : ℝ) ^ (n * 2) = 1 := by
        rw [mul_comm n 2, pow_mul]
        norm_num
      rw [hsign]
      ring
    have hmirror :
        (∫ x in Real.pi / 2..Real.pi, f x) =
          ∫ x in (0 : ℝ)..Real.pi / 2, f x := by
      have hcomp := intervalIntegral.integral_comp_sub_left f Real.pi
        (a := (0 : ℝ)) (b := Real.pi / 2)
      calc
        _ = ∫ x in (0 : ℝ)..Real.pi / 2, f (Real.pi - x) := by
              convert hcomp.symm using 1 <;> ring
        _ = _ := by
              apply intervalIntegral.integral_congr
              intro x hx
              exact hmirrorPoint x
    have hsplitSymm := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hf.intervalIntegrable (-Real.pi / 2) 0)
      (hf.intervalIntegrable 0 (Real.pi / 2))
    have hsplitPi := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hf.intervalIntegrable 0 (Real.pi / 2))
      (hf.intervalIntegrable (Real.pi / 2) Real.pi)
    rw [hneg] at hsplitSymm
    rw [hmirror] at hsplitPi
    linarith
  rw [gap8 n hn]
  change Real.sin ((n : ℝ) * Real.pi / 2) *
      (∫ t in -Real.pi / 2..Real.pi / 2, f t) -
        Real.cos ((n : ℝ) * Real.pi / 2) *
          (∫ t in -Real.pi / 2..Real.pi / 2, g t) = _
  rw [hodd, mul_zero, sub_zero, heven]

theorem gap10 (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi / 2) *
        (∫ x in 0..Real.pi,
          Real.cos x ^ n * Real.cos ((n : ℝ) * x)) =
      Real.pi / (2 : ℝ) ^ n * Real.sin ((n : ℝ) * Real.pi / 2) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [← gap9 (n + 1) (by omega)]
      exact gap6 (n + 1) (by omega)

theorem gap11 (n : ℕ) (hn : 0 < n) :
    originalIntegral n =
      Real.pi / (2 : ℝ) ^ n * Real.sin ((n : ℝ) * Real.pi / 2) := by
  exact gap6 n hn

end

end ProofGap.Exercise2294
