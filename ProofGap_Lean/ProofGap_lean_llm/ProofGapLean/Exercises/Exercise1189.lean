import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1189

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ := 1 / (x * (1 - x))

def closed (n : ℕ) (x : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) *
    (((-1 : ℝ) ^ n / x ^ (n + 1)) + 1 / (1 - x) ^ (n + 1))

private def leftTerm (n : ℕ) (x : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) * (-1 : ℝ) ^ n * (x⁻¹) ^ (n + 1)

private def rightTerm (n : ℕ) (x : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) * ((1 - x)⁻¹) ^ (n + 1)

private theorem splitValue (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    y x = 1 / x + 1 / (1 - x) := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  unfold y
  field_simp [hx0, hden]
  ring

private theorem iterDerivSucc (n : ℕ) (f : ℝ → ℝ) :
    iterDeriv (Nat.succ n) f = deriv (iterDeriv n f) := by
  simp [iterDeriv, Function.iterate_succ_apply']

private theorem hasDerivAtInvPow (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ => (z⁻¹) ^ m)
      (-(m : ℝ) * (x⁻¹) ^ (m + 1)) x := by
  induction m with
  | zero =>
      simpa using (hasDerivAt_const x (1 : ℝ))
  | succ m ih =>
      have h := ih.mul ((hasDerivAt_id x).inv hx)
      convert h using 1 <;>
        simp [pow_succ, Nat.cast_succ] <;>
        ring

private theorem hasDerivAtOneSubInvPow (m : ℕ) (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt (fun z : ℝ => ((1 - z)⁻¹) ^ m)
      ((m : ℝ) * ((1 - x)⁻¹) ^ (m + 1)) x := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  induction m with
  | zero =>
      simpa using (hasDerivAt_const x (1 : ℝ))
  | succ m ih =>
      have hbase :=
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).inv hden
      have h := ih.mul hbase
      convert h using 1 <;>
        simp [pow_succ, Nat.cast_succ] <;>
        ring

private theorem hasDerivAtLeftTerm (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (leftTerm n) (leftTerm (n + 1) x) x := by
  have h :=
    (hasDerivAtInvPow (n + 1) x hx).const_mul
      ((Nat.factorial n : ℝ) * (-1 : ℝ) ^ n)
  convert h using 1 <;>
    simp [leftTerm, Nat.factorial_succ, Nat.cast_succ, pow_succ] <;>
    ring

private theorem hasDerivAtRightTerm (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt (rightTerm n) (rightTerm (n + 1) x) x := by
  have h :=
    (hasDerivAtOneSubInvPow (n + 1) x hx).const_mul
      (Nat.factorial n : ℝ)
  convert h using 1 <;>
    simp [rightTerm, Nat.factorial_succ, Nat.cast_succ, pow_succ] <;>
    ring

private theorem iterDerivRecip (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    iterDeriv n (fun z : ℝ => 1 / z) x = leftTerm n x := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, leftTerm, div_eq_mul_inv]
  | succ n ih =>
      simp only [iterDerivSucc]
      have hlocal :
          iterDeriv n (fun z : ℝ => 1 / z) =ᶠ[nhds x] leftTerm n :=
        (eventually_ne_nhds hx).mono (fun z hz => ih z hz)
      rw [hlocal.deriv_eq]
      exact (hasDerivAtLeftTerm n x hx).deriv

private theorem iterDerivOneSubRecip (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    iterDeriv n (fun z : ℝ => 1 / (1 - z)) x = rightTerm n x := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, rightTerm, div_eq_mul_inv]
  | succ n ih =>
      simp only [iterDerivSucc]
      have hlocal :
          iterDeriv n (fun z : ℝ => 1 / (1 - z)) =ᶠ[nhds x] rightTerm n :=
        (eventually_ne_nhds hx).mono (fun z hz => ih z hz)
      rw [hlocal.deriv_eq]
      exact (hasDerivAtRightTerm n x hx).deriv

private theorem iterDerivSplit (n : ℕ) (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    iterDeriv n y x =
      iterDeriv n (fun z : ℝ => 1 / z) x +
        iterDeriv n (fun z : ℝ => 1 / (1 - z)) x := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv] using splitValue x hx0 hx1
  | succ n ih =>
      simp only [iterDerivSucc]
      have hy :
          iterDeriv n y =ᶠ[nhds x]
            (fun z : ℝ =>
              iterDeriv n (fun w : ℝ => 1 / w) z +
                iterDeriv n (fun w : ℝ => 1 / (1 - w)) z) :=
        ((eventually_ne_nhds hx0).and (eventually_ne_nhds hx1)).mono
          (fun z hz => ih z hz.1 hz.2)
      have hl :
          iterDeriv n (fun z : ℝ => 1 / z) =ᶠ[nhds x] leftTerm n :=
        (eventually_ne_nhds hx0).mono
          (fun z hz => iterDerivRecip n z hz)
      have hr :
          iterDeriv n (fun z : ℝ => 1 / (1 - z)) =ᶠ[nhds x] rightTerm n :=
        (eventually_ne_nhds hx1).mono
          (fun z hz => iterDerivOneSubRecip n z hz)
      have hs :
          (fun z : ℝ =>
              iterDeriv n (fun w : ℝ => 1 / w) z +
                iterDeriv n (fun w : ℝ => 1 / (1 - w)) z) =ᶠ[nhds x]
            (fun z : ℝ => leftTerm n z + rightTerm n z) :=
        (hl.and hr).mono
          (fun z hz => congrArg₂ (fun a b : ℝ => a + b) hz.1 hz.2)
      calc
        deriv (iterDeriv n y) x =
            deriv
              (fun z : ℝ =>
                iterDeriv n (fun w : ℝ => 1 / w) z +
                  iterDeriv n (fun w : ℝ => 1 / (1 - w)) z) x :=
          hy.deriv_eq
        _ = deriv (fun z : ℝ => leftTerm n z + rightTerm n z) x :=
          hs.deriv_eq
        _ = leftTerm (n + 1) x + rightTerm (n + 1) x := by
          simpa using
            ((hasDerivAtLeftTerm n x hx0).add
              (hasDerivAtRightTerm n x hx1)).deriv
        _ = deriv (leftTerm n) x + deriv (rightTerm n) x := by
          rw [(hasDerivAtLeftTerm n x hx0).deriv,
            (hasDerivAtRightTerm n x hx1).deriv]
        _ = deriv (iterDeriv n (fun z : ℝ => 1 / z)) x +
              deriv (iterDeriv n (fun z : ℝ => 1 / (1 - z))) x := by
          rw [hl.deriv_eq, hr.deriv_eq]

theorem gap1 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    y x = 1 / x + 1 / (1 - x) := by
  exact splitValue x hx0 hx1

theorem gap2 (n : ℕ) (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    iterDeriv n y x =
      iterDeriv n (fun z : ℝ => 1 / z) x +
        iterDeriv n (fun z : ℝ => 1 / (1 - z)) x := by
  exact iterDerivSplit n x hx0 hx1

theorem gap3 (n : ℕ) (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    iterDeriv n (fun z : ℝ => 1 / z) x +
        iterDeriv n (fun z : ℝ => 1 / (1 - z)) x =
      closed n x := by
  rw [iterDerivRecip n x hx0, iterDerivOneSubRecip n x hx1]
  simp only [closed, leftTerm, rightTerm, div_eq_mul_inv, inv_pow]
  ring

theorem gap4 (n : ℕ) (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    iterDeriv n y x = closed n x := by
  exact (gap2 n x hx0 hx1).trans (gap3 n x hx0 hx1)

end

end ProofGap.Exercise1189
