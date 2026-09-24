import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2937

noncomputable section

open scoped BigOperators Interval

def p (α β : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (α i * Real.cos ((i : ℝ) * x) +
      β i * Real.sin ((i : ℝ) * x))

def a (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 2 * α 0 else α n

def b (β : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else β n

def finiteFourierExpansion (α β : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a α 0 / 2 +
    ∑ i ∈ Finset.Icc 1 n,
      (a α i * Real.cos ((i : ℝ) * x) +
        b β i * Real.sin ((i : ℝ) * x))

private theorem _integralCosInt (k : ℤ) :
    (∫ x in (-Real.pi)..Real.pi, Real.cos ((k : ℝ) * x)) =
      if k = 0 then 2 * Real.pi else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
    ring
  · have hkR : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk
    have hd (x : ℝ) :
        HasDerivAt
          (fun y : ℝ => Real.sin ((k : ℝ) * y) / (k : ℝ))
          (Real.cos ((k : ℝ) * x)) x := by
      convert
        (((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (k : ℝ))).div_const (k : ℝ)) using 1 <;>
        field_simp
    have hc : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * x)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id)
    rw [if_neg hk]
    calc
      (∫ x in (-Real.pi)..Real.pi, Real.cos ((k : ℝ) * x)) =
          Real.sin ((k : ℝ) * Real.pi) / (k : ℝ) -
            Real.sin ((k : ℝ) * (-Real.pi)) / (k : ℝ) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => hd x) (hc.intervalIntegrable (-Real.pi) Real.pi)
      _ = 0 := by
        simp [mul_neg]

private theorem _integralSinInt (k : ℤ) :
    (∫ x in (-Real.pi)..Real.pi, Real.sin ((k : ℝ) * x)) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hkR : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk
    have hd (x : ℝ) :
        HasDerivAt
          (fun y : ℝ => -Real.cos ((k : ℝ) * y) / (k : ℝ))
          (Real.sin ((k : ℝ) * x)) x := by
      convert
        ((((Real.hasDerivAt_cos ((k : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (k : ℝ))).neg).div_const (k : ℝ)) using 1 <;>
        field_simp
    have hc : Continuous (fun x : ℝ => Real.sin ((k : ℝ) * x)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_id)
    calc
      (∫ x in (-Real.pi)..Real.pi, Real.sin ((k : ℝ) * x)) =
          -Real.cos ((k : ℝ) * Real.pi) / (k : ℝ) -
            (-Real.cos ((k : ℝ) * (-Real.pi)) / (k : ℝ)) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => hd x) (hc.intervalIntegrable (-Real.pi) Real.pi)
      _ = 0 := by
        rw [show (k : ℝ) * (-Real.pi) = -((k : ℝ) * Real.pi) by ring,
          Real.cos_neg]
        ring

private theorem _integralCosCosNat (i j : ℕ) :
    (∫ x in (-Real.pi)..Real.pi,
      Real.cos ((i : ℝ) * x) * Real.cos ((j : ℝ) * x)) =
      if i = j then (if j = 0 then 2 * Real.pi else Real.pi) else 0 := by
  let d : ℤ := (i : ℤ) - (j : ℤ)
  let s : ℤ := (i : ℤ) + (j : ℤ)
  have hargd (x : ℝ) :
      (d : ℝ) * x = (i : ℝ) * x - (j : ℝ) * x := by
    dsimp [d]
    push_cast
    ring
  have hargs (x : ℝ) :
      (s : ℝ) * x = (i : ℝ) * x + (j : ℝ) * x := by
    dsimp [s]
    push_cast
    ring
  have hd :
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x - (j : ℝ) * x)) =
        if d = 0 then 2 * Real.pi else 0 := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x - (j : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi, Real.cos ((d : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact congrArg Real.cos (hargd x).symm
      _ = if d = 0 then 2 * Real.pi else 0 := _integralCosInt d
  have hs :
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x + (j : ℝ) * x)) =
        if s = 0 then 2 * Real.pi else 0 := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x + (j : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi, Real.cos ((s : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact congrArg Real.cos (hargs x).symm
      _ = if s = 0 then 2 * Real.pi else 0 := _integralCosInt s
  have hcd : Continuous
      (fun x : ℝ => Real.cos ((i : ℝ) * x - (j : ℝ) * x)) :=
    Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).sub
        (continuous_const.mul continuous_id))
  have hcs : Continuous
      (fun x : ℝ => Real.cos ((i : ℝ) * x + (j : ℝ) * x)) :=
    Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).add
        (continuous_const.mul continuous_id))
  calc
    (∫ x in (-Real.pi)..Real.pi,
      Real.cos ((i : ℝ) * x) * Real.cos ((j : ℝ) * x)) =
        ∫ x in (-Real.pi)..Real.pi,
          (Real.cos ((i : ℝ) * x - (j : ℝ) * x) +
            Real.cos ((i : ℝ) * x + (j : ℝ) * x)) * (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.cos ((i : ℝ) * x) * Real.cos ((j : ℝ) * x) =
        (Real.cos ((i : ℝ) * x - (j : ℝ) * x) +
          Real.cos ((i : ℝ) * x + (j : ℝ) * x)) * (1 / 2 : ℝ)
      rw [Real.cos_sub, Real.cos_add]
      ring
    _ = ((if d = 0 then 2 * Real.pi else 0) +
          (if s = 0 then 2 * Real.pi else 0)) * (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_add
        (hcd.intervalIntegrable (-Real.pi) Real.pi)
        (hcs.intervalIntegrable (-Real.pi) Real.pi)]
      rw [hd, hs]
    _ = if i = j then (if j = 0 then 2 * Real.pi else Real.pi) else 0 := by
      by_cases hij : i = j
      · subst i
        by_cases hj : j = 0
        · subst j
          simp [d, s]
          ring
        · have hs0 : ((j : ℤ) + (j : ℤ)) ≠ 0 := by omega
          simp [d, s, hj, hs0]
          ring
      · have hd0 : ((i : ℤ) - (j : ℤ)) ≠ 0 := by omega
        have hs0 : ((i : ℤ) + (j : ℤ)) ≠ 0 := by omega
        simp [d, s, hij, hd0, hs0]

private theorem _integralSinSinNat (i j : ℕ) :
    (∫ x in (-Real.pi)..Real.pi,
      Real.sin ((i : ℝ) * x) * Real.sin ((j : ℝ) * x)) =
      if i = j then (if j = 0 then 0 else Real.pi) else 0 := by
  let d : ℤ := (i : ℤ) - (j : ℤ)
  let s : ℤ := (i : ℤ) + (j : ℤ)
  have hargd (x : ℝ) :
      (d : ℝ) * x = (i : ℝ) * x - (j : ℝ) * x := by
    dsimp [d]
    push_cast
    ring
  have hargs (x : ℝ) :
      (s : ℝ) * x = (i : ℝ) * x + (j : ℝ) * x := by
    dsimp [s]
    push_cast
    ring
  have hd :
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x - (j : ℝ) * x)) =
        if d = 0 then 2 * Real.pi else 0 := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x - (j : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi, Real.cos ((d : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact congrArg Real.cos (hargd x).symm
      _ = if d = 0 then 2 * Real.pi else 0 := _integralCosInt d
  have hs :
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x + (j : ℝ) * x)) =
        if s = 0 then 2 * Real.pi else 0 := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        Real.cos ((i : ℝ) * x + (j : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi, Real.cos ((s : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact congrArg Real.cos (hargs x).symm
      _ = if s = 0 then 2 * Real.pi else 0 := _integralCosInt s
  have hcd : Continuous
      (fun x : ℝ => Real.cos ((i : ℝ) * x - (j : ℝ) * x)) :=
    Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).sub
        (continuous_const.mul continuous_id))
  have hcs : Continuous
      (fun x : ℝ => Real.cos ((i : ℝ) * x + (j : ℝ) * x)) :=
    Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).add
        (continuous_const.mul continuous_id))
  calc
    (∫ x in (-Real.pi)..Real.pi,
      Real.sin ((i : ℝ) * x) * Real.sin ((j : ℝ) * x)) =
        ∫ x in (-Real.pi)..Real.pi,
          (Real.cos ((i : ℝ) * x - (j : ℝ) * x) -
            Real.cos ((i : ℝ) * x + (j : ℝ) * x)) * (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.sin ((i : ℝ) * x) * Real.sin ((j : ℝ) * x) =
        (Real.cos ((i : ℝ) * x - (j : ℝ) * x) -
          Real.cos ((i : ℝ) * x + (j : ℝ) * x)) * (1 / 2 : ℝ)
      rw [Real.cos_sub, Real.cos_add]
      ring
    _ = ((if d = 0 then 2 * Real.pi else 0) -
          (if s = 0 then 2 * Real.pi else 0)) * (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_sub
        (hcd.intervalIntegrable (-Real.pi) Real.pi)
        (hcs.intervalIntegrable (-Real.pi) Real.pi)]
      rw [hd, hs]
    _ = if i = j then (if j = 0 then 0 else Real.pi) else 0 := by
      by_cases hij : i = j
      · subst i
        by_cases hj : j = 0
        · subst j
          simp [d, s]
        · have hs0 : ((j : ℤ) + (j : ℤ)) ≠ 0 := by omega
          simp [d, s, hj, hs0]
          ring
      · have hd0 : ((i : ℤ) - (j : ℤ)) ≠ 0 := by omega
        have hs0 : ((i : ℤ) + (j : ℤ)) ≠ 0 := by omega
        simp [d, s, hij, hd0, hs0]

private theorem _integralCosSinNat (i j : ℕ) :
    (∫ x in (-Real.pi)..Real.pi,
      Real.cos ((i : ℝ) * x) * Real.sin ((j : ℝ) * x)) = 0 := by
  let s : ℤ := (i : ℤ) + (j : ℤ)
  let d : ℤ := (i : ℤ) - (j : ℤ)
  have hargs (x : ℝ) :
      (s : ℝ) * x = (i : ℝ) * x + (j : ℝ) * x := by
    dsimp [s]
    push_cast
    ring
  have hargd (x : ℝ) :
      (d : ℝ) * x = (i : ℝ) * x - (j : ℝ) * x := by
    dsimp [d]
    push_cast
    ring
  have hs :
      (∫ x in (-Real.pi)..Real.pi,
        Real.sin ((i : ℝ) * x + (j : ℝ) * x)) = 0 := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        Real.sin ((i : ℝ) * x + (j : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi, Real.sin ((s : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact congrArg Real.sin (hargs x).symm
      _ = 0 := _integralSinInt s
  have hd :
      (∫ x in (-Real.pi)..Real.pi,
        Real.sin ((i : ℝ) * x - (j : ℝ) * x)) = 0 := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        Real.sin ((i : ℝ) * x - (j : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi, Real.sin ((d : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact congrArg Real.sin (hargd x).symm
      _ = 0 := _integralSinInt d
  have hss : Continuous
      (fun x : ℝ => Real.sin ((i : ℝ) * x + (j : ℝ) * x)) :=
    Real.continuous_sin.comp
      ((continuous_const.mul continuous_id).add
        (continuous_const.mul continuous_id))
  have hsd : Continuous
      (fun x : ℝ => Real.sin ((i : ℝ) * x - (j : ℝ) * x)) :=
    Real.continuous_sin.comp
      ((continuous_const.mul continuous_id).sub
        (continuous_const.mul continuous_id))
  calc
    (∫ x in (-Real.pi)..Real.pi,
      Real.cos ((i : ℝ) * x) * Real.sin ((j : ℝ) * x)) =
        ∫ x in (-Real.pi)..Real.pi,
          (Real.sin ((i : ℝ) * x + (j : ℝ) * x) -
            Real.sin ((i : ℝ) * x - (j : ℝ) * x)) * (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.cos ((i : ℝ) * x) * Real.sin ((j : ℝ) * x) =
        (Real.sin ((i : ℝ) * x + (j : ℝ) * x) -
          Real.sin ((i : ℝ) * x - (j : ℝ) * x)) * (1 / 2 : ℝ)
      rw [Real.sin_add, Real.sin_sub]
      ring
    _ = (0 - 0) * (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_sub
        (hss.intervalIntegrable (-Real.pi) Real.pi)
        (hsd.intervalIntegrable (-Real.pi) Real.pi)]
      rw [hs, hd]
    _ = 0 := by ring

private theorem _integralSinCosNat (i j : ℕ) :
    (∫ x in (-Real.pi)..Real.pi,
      Real.sin ((i : ℝ) * x) * Real.cos ((j : ℝ) * x)) = 0 := by
  simpa [mul_comm] using _integralCosSinNat j i

private theorem _normalizedCos (α β : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
      (∑ i ∈ Finset.range (N + 1),
        (α i * Real.cos ((i : ℝ) * x) +
          β i * Real.sin ((i : ℝ) * x))) *
        Real.cos ((k : ℝ) * x)) =
      if k = 0 then 2 * α 0 else α k := by
  classical
  have hcos (i : ℕ) : Continuous (fun x : ℝ => Real.cos ((i : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin (i : ℕ) : Continuous (fun x : ℝ => Real.sin ((i : ℝ) * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hterm (i : ℕ) :
      (∫ x in (-Real.pi)..Real.pi,
        (α i * Real.cos ((i : ℝ) * x) +
          β i * Real.sin ((i : ℝ) * x)) *
          Real.cos ((k : ℝ) * x)) =
        α i * (if i = k then
          (if k = 0 then 2 * Real.pi else Real.pi) else 0) := by
    have hcc : Continuous (fun x : ℝ =>
        α i * (Real.cos ((i : ℝ) * x) * Real.cos ((k : ℝ) * x))) :=
      continuous_const.mul ((hcos i).mul (hcos k))
    have hsc : Continuous (fun x : ℝ =>
        β i * (Real.sin ((i : ℝ) * x) * Real.cos ((k : ℝ) * x))) :=
      continuous_const.mul ((hsin i).mul (hcos k))
    calc
      (∫ x in (-Real.pi)..Real.pi,
        (α i * Real.cos ((i : ℝ) * x) +
          β i * Real.sin ((i : ℝ) * x)) *
          Real.cos ((k : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi,
            α i * (Real.cos ((i : ℝ) * x) * Real.cos ((k : ℝ) * x)) +
              β i * (Real.sin ((i : ℝ) * x) * Real.cos ((k : ℝ) * x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x)) * Real.cos ((k : ℝ) * x) =
          α i * (Real.cos ((i : ℝ) * x) * Real.cos ((k : ℝ) * x)) +
            β i * (Real.sin ((i : ℝ) * x) * Real.cos ((k : ℝ) * x))
        ring
      _ = α i * (∫ x in (-Real.pi)..Real.pi,
              Real.cos ((i : ℝ) * x) * Real.cos ((k : ℝ) * x)) +
            β i * (∫ x in (-Real.pi)..Real.pi,
              Real.sin ((i : ℝ) * x) * Real.cos ((k : ℝ) * x)) := by
        rw [intervalIntegral.integral_add
          (hcc.intervalIntegrable (-Real.pi) Real.pi)
          (hsc.intervalIntegrable (-Real.pi) Real.pi)]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ = α i * (if i = k then
          (if k = 0 then 2 * Real.pi else Real.pi) else 0) := by
        rw [_integralCosCosNat, _integralSinCosNat]
        ring
  have hsum :
      (∫ x in (-Real.pi)..Real.pi,
        (∑ i ∈ Finset.range (N + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x))) *
          Real.cos ((k : ℝ) * x)) =
        ∑ i ∈ Finset.range (N + 1),
          α i * (if i = k then
            (if k = 0 then 2 * Real.pi else Real.pi) else 0) := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        (∑ i ∈ Finset.range (N + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x))) *
          Real.cos ((k : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi,
            ∑ i ∈ Finset.range (N + 1),
              (α i * Real.cos ((i : ℝ) * x) +
                β i * Real.sin ((i : ℝ) * x)) *
                Real.cos ((k : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (∑ i ∈ Finset.range (N + 1),
            (α i * Real.cos ((i : ℝ) * x) + β i * Real.sin ((i : ℝ) * x))) *
              Real.cos ((k : ℝ) * x) =
          ∑ i ∈ Finset.range (N + 1),
            (α i * Real.cos ((i : ℝ) * x) + β i * Real.sin ((i : ℝ) * x)) *
              Real.cos ((k : ℝ) * x)
        rw [Finset.sum_mul]
      _ = ∑ i ∈ Finset.range (N + 1),
          ∫ x in (-Real.pi)..Real.pi,
            (α i * Real.cos ((i : ℝ) * x) +
              β i * Real.sin ((i : ℝ) * x)) *
              Real.cos ((k : ℝ) * x) := by
        rw [intervalIntegral.integral_finset_sum _]
        intro i hi
        exact ((((continuous_const.mul (hcos i)).add
          (continuous_const.mul (hsin i))).mul (hcos k))).intervalIntegrable
            (-Real.pi) Real.pi
      _ = ∑ i ∈ Finset.range (N + 1),
          α i * (if i = k then
            (if k = 0 then 2 * Real.pi else Real.pi) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
  rw [hsum]
  have hmem : k ∈ Finset.range (N + 1) := by
    simp
    omega
  by_cases hk0 : k = 0
  · subst k
    simp
    field_simp [Real.pi_ne_zero] <;> ring
  · simp [hk0, hmem]
    field_simp [Real.pi_ne_zero] <;> ring

private theorem _normalizedSin (α β : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
      (∑ i ∈ Finset.range (N + 1),
        (α i * Real.cos ((i : ℝ) * x) +
          β i * Real.sin ((i : ℝ) * x))) *
        Real.sin ((k : ℝ) * x)) =
      if k = 0 then 0 else β k := by
  classical
  have hcos (i : ℕ) : Continuous (fun x : ℝ => Real.cos ((i : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin (i : ℕ) : Continuous (fun x : ℝ => Real.sin ((i : ℝ) * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hterm (i : ℕ) :
      (∫ x in (-Real.pi)..Real.pi,
        (α i * Real.cos ((i : ℝ) * x) +
          β i * Real.sin ((i : ℝ) * x)) *
          Real.sin ((k : ℝ) * x)) =
        β i * (if i = k then (if k = 0 then 0 else Real.pi) else 0) := by
    have hcs : Continuous (fun x : ℝ =>
        α i * (Real.cos ((i : ℝ) * x) * Real.sin ((k : ℝ) * x))) :=
      continuous_const.mul ((hcos i).mul (hsin k))
    have hss : Continuous (fun x : ℝ =>
        β i * (Real.sin ((i : ℝ) * x) * Real.sin ((k : ℝ) * x))) :=
      continuous_const.mul ((hsin i).mul (hsin k))
    calc
      (∫ x in (-Real.pi)..Real.pi,
        (α i * Real.cos ((i : ℝ) * x) +
          β i * Real.sin ((i : ℝ) * x)) *
          Real.sin ((k : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi,
            α i * (Real.cos ((i : ℝ) * x) * Real.sin ((k : ℝ) * x)) +
              β i * (Real.sin ((i : ℝ) * x) * Real.sin ((k : ℝ) * x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x)) * Real.sin ((k : ℝ) * x) =
          α i * (Real.cos ((i : ℝ) * x) * Real.sin ((k : ℝ) * x)) +
            β i * (Real.sin ((i : ℝ) * x) * Real.sin ((k : ℝ) * x))
        ring
      _ = α i * (∫ x in (-Real.pi)..Real.pi,
              Real.cos ((i : ℝ) * x) * Real.sin ((k : ℝ) * x)) +
            β i * (∫ x in (-Real.pi)..Real.pi,
              Real.sin ((i : ℝ) * x) * Real.sin ((k : ℝ) * x)) := by
        rw [intervalIntegral.integral_add
          (hcs.intervalIntegrable (-Real.pi) Real.pi)
          (hss.intervalIntegrable (-Real.pi) Real.pi)]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ = β i * (if i = k then (if k = 0 then 0 else Real.pi) else 0) := by
        rw [_integralCosSinNat, _integralSinSinNat]
        ring
  have hsum :
      (∫ x in (-Real.pi)..Real.pi,
        (∑ i ∈ Finset.range (N + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x))) *
          Real.sin ((k : ℝ) * x)) =
        ∑ i ∈ Finset.range (N + 1),
          β i * (if i = k then (if k = 0 then 0 else Real.pi) else 0) := by
    calc
      (∫ x in (-Real.pi)..Real.pi,
        (∑ i ∈ Finset.range (N + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x))) *
          Real.sin ((k : ℝ) * x)) =
          ∫ x in (-Real.pi)..Real.pi,
            ∑ i ∈ Finset.range (N + 1),
              (α i * Real.cos ((i : ℝ) * x) +
                β i * Real.sin ((i : ℝ) * x)) *
                Real.sin ((k : ℝ) * x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (∑ i ∈ Finset.range (N + 1),
            (α i * Real.cos ((i : ℝ) * x) + β i * Real.sin ((i : ℝ) * x))) *
              Real.sin ((k : ℝ) * x) =
          ∑ i ∈ Finset.range (N + 1),
            (α i * Real.cos ((i : ℝ) * x) + β i * Real.sin ((i : ℝ) * x)) *
              Real.sin ((k : ℝ) * x)
        rw [Finset.sum_mul]
      _ = ∑ i ∈ Finset.range (N + 1),
          ∫ x in (-Real.pi)..Real.pi,
            (α i * Real.cos ((i : ℝ) * x) +
              β i * Real.sin ((i : ℝ) * x)) *
              Real.sin ((k : ℝ) * x) := by
        rw [intervalIntegral.integral_finset_sum _]
        intro i hi
        exact ((((continuous_const.mul (hcos i)).add
          (continuous_const.mul (hsin i))).mul (hsin k))).intervalIntegrable
            (-Real.pi) Real.pi
      _ = ∑ i ∈ Finset.range (N + 1),
          β i * (if i = k then (if k = 0 then 0 else Real.pi) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
  rw [hsum]
  have hmem : k ∈ Finset.range (N + 1) := by
    simp
    omega
  by_cases hk0 : k = 0
  · subst k
    simp
  · simp [hk0, hmem]
    field_simp [Real.pi_ne_zero] <;> ring

private theorem _p_eq_finiteFourierExpansion
    (α β : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    p α β n x = finiteFourierExpansion α β n x := by
  classical
  let f : ℕ → ℝ := fun i =>
    α i * Real.cos ((i : ℝ) * x) + β i * Real.sin ((i : ℝ) * x)
  let g : ℕ → ℝ := fun i =>
    a α i * Real.cos ((i : ℝ) * x) + b β i * Real.sin ((i : ℝ) * x)
  have hrange :
      Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext i
    simp
    omega
  have hzero : 0 ∉ Finset.Icc 1 n := by simp
  have hsum :
      (∑ i ∈ Finset.Icc 1 n, f i) =
        ∑ i ∈ Finset.Icc 1 n, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi0 : i ≠ 0 := by omega
    simp [f, g, a, b, hi0]
  unfold p finiteFourierExpansion
  change (∑ i ∈ Finset.range (n + 1), f i) =
    a α 0 / 2 + ∑ i ∈ Finset.Icc 1 n, g i
  rw [hrange, Finset.sum_insert hzero, hsum]
  simp [f, a]

theorem gap1 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      Function.Periodic (p α β n) (2 * Real.pi) := by
  intro α β n x
  unfold p
  apply Finset.sum_congr rfl
  intro i hi
  have htrig : ∀ m : ℕ,
      Real.cos ((m : ℝ) * (2 * Real.pi)) = 1 ∧
        Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        constructor
        · rw [Nat.cast_succ, add_mul, Real.cos_add, ih.1, ih.2]
          simp
        · rw [Nat.cast_succ, add_mul, Real.sin_add, ih.1, ih.2]
          simp
  have hc :
      Real.cos ((i : ℝ) * (x + 2 * Real.pi)) =
        Real.cos ((i : ℝ) * x) := by
    rw [mul_add, Real.cos_add, (htrig i).1, (htrig i).2]
    simp
  have hs :
      Real.sin ((i : ℝ) * (x + 2 * Real.pi)) =
        Real.sin ((i : ℝ) * x) := by
    rw [mul_add, Real.sin_add, (htrig i).1, (htrig i).2]
    simp
  rw [hc, hs]

theorem gap2 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      a α 0 =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi, p α β n x := by
  intro α β n
  symm
  simpa [p] using
    (_normalizedCos α β n 0 (Nat.zero_le n))

theorem gap3 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi, p α β n x) =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
          ∑ i ∈ Finset.range (n + 1),
            (α i * Real.cos ((i : ℝ) * x) +
              β i * Real.sin ((i : ℝ) * x)) := by
  intro α β n
  rfl

theorem gap4 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
        ∑ i ∈ Finset.range (n + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x))) =
        2 * α 0 := by
  intro α β n
  simpa using
    (_normalizedCos α β n 0 (Nat.zero_le n))

theorem gap5 :
    ∀ α : ℕ → ℝ, a α 0 = 2 * α 0 := by
  intro α
  simp [a]

theorem gap6 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      a α n =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
          p α β n x * Real.cos ((n : ℝ) * x) := by
  intro α β n
  symm
  simpa [p, a] using
    (_normalizedCos α β n n le_rfl)

theorem gap7 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
        p α β n x * Real.cos ((n : ℝ) * x)) =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
          (∑ i ∈ Finset.range (n + 1),
            (α i * Real.cos ((i : ℝ) * x) +
              β i * Real.sin ((i : ℝ) * x))) *
            Real.cos ((n : ℝ) * x) := by
  intro α β n
  rfl

theorem gap8 :
    ∀ (α β : ℕ → ℝ) (n : ℕ), 0 < n →
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
        (∑ i ∈ Finset.range (n + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x))) *
          Real.cos ((n : ℝ) * x)) =
        α n := by
  intro α β n hn
  simpa [hn.ne'] using
    (_normalizedCos α β n n le_rfl)

theorem gap9 :
    ∀ (α : ℕ → ℝ) (n : ℕ), 0 < n → a α n = α n := by
  intro α n hn
  simp [a, hn.ne']

theorem gap10 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      b β n =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
          p α β n x * Real.sin ((n : ℝ) * x) := by
  intro α β n
  symm
  simpa [p, b] using
    (_normalizedSin α β n n le_rfl)

theorem gap11 :
    ∀ (α β : ℕ → ℝ) (n : ℕ),
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
        p α β n x * Real.sin ((n : ℝ) * x)) =
        1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
          (∑ i ∈ Finset.range (n + 1),
            (α i * Real.cos ((i : ℝ) * x) +
              β i * Real.sin ((i : ℝ) * x))) *
            Real.sin ((n : ℝ) * x) := by
  intro α β n
  rfl

theorem gap12 :
    ∀ (α β : ℕ → ℝ) (n : ℕ), 0 < n →
      (1 / Real.pi * ∫ x in (-Real.pi)..Real.pi,
        (∑ i ∈ Finset.range (n + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x))) *
          Real.sin ((n : ℝ) * x)) =
        β n := by
  intro α β n hn
  simpa [hn.ne'] using
    (_normalizedSin α β n n le_rfl)

theorem gap13 :
    ∀ (β : ℕ → ℝ) (n : ℕ), 0 < n → b β n = β n := by
  intro β n hn
  simp [b, hn.ne']

theorem gap14 :
    ∀ (α β : ℕ → ℝ) (n : ℕ) (x : ℝ),
      p α β n x = finiteFourierExpansion α β n x := by
  intro α β n x
  exact _p_eq_finiteFourierExpansion α β n x

theorem gap15 :
    ∀ (α β : ℕ → ℝ) (x : ℝ) (n : ℕ),
      finiteFourierExpansion α β n x = p α β n x := by
  intro α β x n
  exact (_p_eq_finiteFourierExpansion α β n x).symm

theorem gap16 :
    ∀ (α β : ℕ → ℝ) (n : ℕ) (x : ℝ),
      p α β n x =
        ∑ i ∈ Finset.range (n + 1),
          (α i * Real.cos ((i : ℝ) * x) +
            β i * Real.sin ((i : ℝ) * x)) := by
  intro α β n x
  rfl

theorem gap17 :
    ∀ (α β : ℕ → ℝ) (n : ℕ) (x : ℝ),
      p α β n x = finiteFourierExpansion α β n x := by
  intro α β n x
  exact _p_eq_finiteFourierExpansion α β n x

end

end ProofGap.Exercise2937
