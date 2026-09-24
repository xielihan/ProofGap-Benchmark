import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1025

noncomputable section

open scoped BigOperators

def S (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.sin ((k + 1 : ℝ) * x)

def T (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (k + 1 : ℝ) * Real.cos ((k + 1 : ℝ) * x)

def multipliedSum (n : ℕ) (x : ℝ) : ℝ :=
  1 / (2 * Real.sin (x / 2)) *
    ∑ k ∈ Finset.range n,
      2 * Real.sin (x / 2) * Real.sin ((k + 1 : ℝ) * x)

def telescopingSum (n : ℕ) (x : ℝ) : ℝ :=
  1 / (2 * Real.sin (x / 2)) *
    ∑ k ∈ Finset.range n,
      (Real.cos ((2 * k + 1 : ℝ) * x / 2) -
        Real.cos ((2 * k + 3 : ℝ) * x / 2))

def compactSum (n : ℕ) (x : ℝ) : ℝ :=
  (Real.cos (x / 2) - Real.cos ((2 * n + 1 : ℝ) * x / 2)) /
    (2 * Real.sin (x / 2))

def closedS (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n : ℝ) * x / 2) *
      Real.sin ((n + 1 : ℝ) * x / 2) /
    Real.sin (x / 2)

def expandedT₁ (n : ℕ) (x : ℝ) : ℝ :=
  (((n : ℝ) * Real.cos ((n : ℝ) * x / 2) *
        Real.sin ((n + 1 : ℝ) * x / 2) +
      (n + 1 : ℝ) * Real.cos ((n + 1 : ℝ) * x / 2) *
        Real.sin ((n : ℝ) * x / 2)) * Real.sin (x / 2)) /
      (2 * Real.sin (x / 2) ^ 2) -
    (Real.cos (x / 2) * Real.sin ((n : ℝ) * x / 2) *
      Real.sin ((n + 1 : ℝ) * x / 2)) /
      (2 * Real.sin (x / 2) ^ 2)

def expandedT₂ (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) *
      (Real.sin ((n + 1 : ℝ) * x / 2) *
          Real.cos ((n : ℝ) * x / 2) +
        Real.cos ((n + 1 : ℝ) * x / 2) *
          Real.sin ((n : ℝ) * x / 2)) * Real.sin (x / 2)) /
      (2 * Real.sin (x / 2) ^ 2) -
    (Real.sin ((n : ℝ) * x / 2) *
      (Real.sin ((n + 1 : ℝ) * x / 2) * Real.cos (x / 2) -
        Real.cos ((n + 1 : ℝ) * x / 2) * Real.sin (x / 2))) /
      (2 * Real.sin (x / 2) ^ 2)

def finalT (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) * Real.sin (x / 2) *
      Real.sin ((2 * n + 1 : ℝ) * x / 2) -
    Real.sin ((n : ℝ) * x / 2) ^ 2) /
    (2 * Real.sin (x / 2) ^ 2)

private theorem sineProductStep (k : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) * Real.sin ((k + 1 : ℝ) * x) =
      Real.cos ((2 * k + 1 : ℝ) * x / 2) -
        Real.cos ((2 * k + 3 : ℝ) * x / 2) := by
  rw [show ((2 * k + 1 : ℝ) * x / 2) =
        (k + 1 : ℝ) * x - x / 2 by ring,
      show ((2 * k + 3 : ℝ) * x / 2) =
        (k + 1 : ℝ) * x + x / 2 by ring,
      Real.cos_sub, Real.cos_add]
  ring

private theorem telescopingCosineSum (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n,
      (Real.cos ((2 * k + 1 : ℝ) * x / 2) -
        Real.cos ((2 * k + 3 : ℝ) * x / 2))) =
      Real.cos (x / 2) - Real.cos ((2 * n + 1 : ℝ) * x / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show (2 * (n.succ : ℝ) + 1) * x / 2 =
          (2 * (n : ℝ) + 3) * x / 2 by
            rw [Nat.cast_succ]
            ring]
      ring

private theorem compactCosineDifference (n : ℕ) (x : ℝ) :
    Real.cos (x / 2) - Real.cos ((2 * n + 1 : ℝ) * x / 2) =
      2 * Real.sin ((n : ℝ) * x / 2) *
        Real.sin ((n + 1 : ℝ) * x / 2) := by
  rw [show x / 2 =
        (n + 1 : ℝ) * x / 2 - (n : ℝ) * x / 2 by ring,
      show ((2 * n + 1 : ℝ) * x / 2) =
        (n + 1 : ℝ) * x / 2 + (n : ℝ) * x / 2 by ring,
      Real.cos_sub, Real.cos_add]
  ring

private theorem hasDerivAtSineTerm (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin ((k + 1 : ℝ) * y))
      ((k + 1 : ℝ) * Real.cos ((k + 1 : ℝ) * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => (k + 1 : ℝ) * y)
      (k + 1 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (k + 1 : ℝ)
  change HasDerivAt
    ((fun z : ℝ => Real.sin z) ∘ fun y : ℝ => (k + 1 : ℝ) * y)
    ((k + 1 : ℝ) * Real.cos ((k + 1 : ℝ) * x)) x
  convert (Real.hasDerivAt_sin ((k + 1 : ℝ) * x)).comp x hlin using 1
  ring

private theorem hasDerivAtScaledSine (c x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (c * y / 2))
      (c * Real.cos (c * x / 2) / 2) x := by
  have hlin : HasDerivAt (fun y : ℝ => c * y / 2) (c / 2) x := by
    rw [show (fun y : ℝ => c * y / 2) =
        (fun y : ℝ => (c / 2) * y) by
          funext y
          ring]
    simpa using (hasDerivAt_id x).const_mul (c / 2)
  change HasDerivAt
    ((fun z : ℝ => Real.sin z) ∘ fun y : ℝ => c * y / 2)
    (c * Real.cos (c * x / 2) / 2) x
  convert (Real.hasDerivAt_sin (c * x / 2)).comp x hlin using 1
  ring

private theorem hasDerivAtClosedForm (n : ℕ) (x : ℝ)
    (hx : Real.sin (x / 2) ≠ 0) :
    HasDerivAt (closedS n) (expandedT₁ n x) x := by
  have ha := hasDerivAtScaledSine (n : ℝ) x
  have hb := hasDerivAtScaledSine (n + 1 : ℝ) x
  have hs : HasDerivAt (fun y : ℝ => Real.sin (y / 2))
      (Real.cos (x / 2) / 2) x := by
    simpa using hasDerivAtScaledSine 1 x
  have hq := (ha.mul hb).div hs hx
  unfold closedS expandedT₁
  convert hq using 1
  simp only [Pi.mul_apply]
  field_simp [hx]

private theorem expandedSecondToFinal (n : ℕ) (x : ℝ) :
    expandedT₂ n x = finalT n x := by
  unfold expandedT₂ finalT
  have hadd :
      Real.sin ((n + 1 : ℝ) * x / 2) *
          Real.cos ((n : ℝ) * x / 2) +
        Real.cos ((n + 1 : ℝ) * x / 2) *
          Real.sin ((n : ℝ) * x / 2) =
        Real.sin ((2 * n + 1 : ℝ) * x / 2) := by
    rw [← Real.sin_add]
    congr 1
    ring
  have hsub :
      Real.sin ((n + 1 : ℝ) * x / 2) * Real.cos (x / 2) -
        Real.cos ((n + 1 : ℝ) * x / 2) * Real.sin (x / 2) =
      Real.sin ((n : ℝ) * x / 2) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  rw [hadd, hsub]
  ring

theorem gap1 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    S n x = multipliedSum n x := by
  unfold S multipliedSum
  rw [← Finset.mul_sum]
  field_simp [hx]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring

theorem gap2 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    S n x = telescopingSum n x := by
  calc
    S n x = multipliedSum n x := gap1 n x hx
    _ = telescopingSum n x := by
      unfold multipliedSum telescopingSum
      apply congrArg (fun z : ℝ => 1 / (2 * Real.sin (x / 2)) * z)
      apply Finset.sum_congr rfl
      intro k hk
      exact sineProductStep k x

theorem gap3 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    S n x = compactSum n x := by
  calc
    S n x = telescopingSum n x := gap2 n x hx
    _ = compactSum n x := by
      unfold telescopingSum compactSum
      rw [telescopingCosineSum]
      ring

theorem gap4 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    compactSum n x = closedS n x := by
  unfold compactSum closedS
  rw [compactCosineDifference]
  field_simp [hx]

theorem gap5 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    S n x = closedS n x := by
  exact (gap3 n x hx).trans (gap4 n x hx)

theorem gap6 (n : ℕ) (x : ℝ) :
    HasDerivAt (S n) (T n x) x := by
  induction n with
  | zero =>
      simpa [S, T] using (hasDerivAt_const (x := x) (c := (0 : ℝ)))
  | succ n ih =>
      have hfun :
          S (Nat.succ n) =
            S n + fun y : ℝ => Real.sin ((n + 1 : ℝ) * y) := by
        funext y
        simp [S, Finset.sum_range_succ]
      rw [hfun]
      simpa [T, Finset.sum_range_succ] using
        ih.add (hasDerivAtSineTerm n x)

theorem gap7 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    T n x = expandedT₁ n x := by
  have hcont : ContinuousAt (fun y : ℝ => Real.sin (y / 2)) x := by
    simpa using (hasDerivAtScaledSine 1 x).continuousAt
  have hne : Filter.Eventually
      (fun y : ℝ => Real.sin (y / 2) ≠ 0) (nhds x) :=
    hcont.eventually_ne hx
  have heq : Filter.EventuallyEq (nhds x) (S n) (closedS n) :=
    hne.mono (fun y hy => gap5 n y hy)
  have hclosedT : HasDerivAt (closedS n) (T n x) x :=
    (gap6 n x).congr_of_eventuallyEq heq.symm
  exact hclosedT.unique (hasDerivAtClosedForm n x hx)

theorem gap8 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    T n x = expandedT₂ n x := by
  rw [gap7 n x hx]
  unfold expandedT₁ expandedT₂
  ring

theorem gap9 (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    T n x = finalT n x := by
  calc
    T n x = expandedT₂ n x := gap8 n x hx
    _ = finalT n x := expandedSecondToFinal n x

end

end ProofGap.Exercise1025
