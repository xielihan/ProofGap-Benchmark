import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1188

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (a b c d x : ℝ) : ℝ := (a * x + b) / (c * x + d)

def nthClosed (n : ℕ) (a b c d x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * c ^ (n - 1) * (a * d - b * c) *
      (Nat.factorial n : ℝ) /
    (c * x + d) ^ (n + 1)

def rawNext (n : ℕ) (a b c d x : ℝ) : ℝ :=
  (-((-1 : ℝ) ^ (n - 1))) * c ^ (n - 1) * (a * d - b * c) *
      (Nat.factorial n : ℝ) * (n + 1 : ℝ) *
      (c * x + d) ^ n * c /
    (c * x + d) ^ (2 * (n + 1))

private theorem hasDerivAtAffineAux (p q x : ℝ) :
    HasDerivAt (fun z : ℝ => p * z + q) p x := by
  simpa only [zero_mul, mul_one, zero_add, add_zero] using
    (((hasDerivAt_const x p).mul (hasDerivAt_id x)).add
      (hasDerivAt_const x q))

private theorem hasDerivAtAffinePowSuccAux (m : ℕ) (c d x : ℝ) :
    HasDerivAt (fun z : ℝ => (c * z + d) ^ (m + 1))
      ((m + 1 : ℕ) * (c * x + d) ^ m * c) x := by
  induction m with
  | zero =>
      simpa only [Nat.zero_add, pow_one, Nat.cast_one, pow_zero, one_mul] using
        hasDerivAtAffineAux c d x
  | succ m ih =>
      have hmul := ih.mul (hasDerivAtAffineAux c d x)
      convert hmul using 1 <;>
        simp [pow_succ, Nat.cast_succ] <;>
        ring

private theorem firstDerivAux (a b c d x : ℝ) (h : c * x + d ≠ 0) :
    iterDeriv 1 (y a b c d) x =
      (a * (c * x + d) - c * (a * x + b)) / (c * x + d) ^ 2 := by
  have hnum : HasDerivAt (fun z : ℝ => a * z + b) a x :=
    hasDerivAtAffineAux a b x
  have hden : HasDerivAt (fun z : ℝ => c * z + d) c x :=
    hasDerivAtAffineAux c d x
  have hquot := hnum.div hden h
  change deriv (fun z : ℝ => (a * z + b) / (c * z + d)) x = _
  convert hquot.deriv using 1 <;> ring

private theorem hasDerivAtNthClosedSucc (k : ℕ) (a b c d x : ℝ)
    (h : c * x + d ≠ 0) :
    HasDerivAt (fun z : ℝ => nthClosed (k + 1) a b c d z)
      (nthClosed (k + 2) a b c d x) x := by
  let K : ℝ :=
    (-1 : ℝ) ^ k * c ^ k * (a * d - b * c) *
      (Nat.factorial (k + 1) : ℝ)
  have hpow := hasDerivAtAffinePowSuccAux (k + 1) c d x
  have hpne : (c * x + d) ^ ((k + 1) + 1) ≠ 0 :=
    pow_ne_zero _ h
  have hquot := (hasDerivAt_const x K).div hpow hpne
  convert hquot using 1 <;>
    simp [K, nthClosed, Nat.factorial_succ, pow_succ] <;>
    field_simp [h] <;>
    ring

private theorem iterDerivClosedAux (k : ℕ) (a b c d x : ℝ)
    (h : c * x + d ≠ 0) :
    iterDeriv (k + 1) (y a b c d) x =
      nthClosed (k + 1) a b c d x := by
  induction k generalizing x with
  | zero =>
      calc
        iterDeriv (0 + 1) (y a b c d) x =
            (a * (c * x + d) - c * (a * x + b)) /
              (c * x + d) ^ 2 :=
          firstDerivAux a b c d x h
        _ = nthClosed (0 + 1) a b c d x := by
          simp [nthClosed]
          ring
  | succ k ih =>
      have hden : HasDerivAt (fun z : ℝ => c * z + d) c x :=
        hasDerivAtAffineAux c d x
      have hne : ∀ᶠ z in nhds x, c * z + d ≠ 0 :=
        hden.continuousAt.eventually_ne h
      have heq :
          (fun z : ℝ => iterDeriv (k + 1) (y a b c d) z) =ᶠ[nhds x]
            (fun z : ℝ => nthClosed (k + 1) a b c d z) :=
        hne.mono (fun z hz => ih z hz)
      have hder :=
        (hasDerivAtNthClosedSucc k a b c d x h).congr_of_eventuallyEq heq
      simpa [iterDeriv, Function.iterate_succ_apply'] using hder.deriv

private theorem rawNextEqNthClosedAux (n : ℕ) (a b c d x : ℝ)
    (hn : 1 ≤ n) (h : c * x + d ≠ 0) :
    rawNext n a b c d x = nthClosed (n + 1) a b c d x := by
  cases n with
  | zero => simp at hn
  | succ k =>
      unfold rawNext nthClosed
      rw [show 2 * (Nat.succ k + 1) =
          Nat.succ k + (Nat.succ k + 2) by omega]
      rw [pow_add]
      simp [Nat.factorial_succ, pow_succ]
      field_simp [h]
      ring

theorem gap1 (a b c d x : ℝ) (h : c * x + d ≠ 0) :
    iterDeriv 1 (y a b c d) x =
      (a * (c * x + d) - c * (a * x + b)) / (c * x + d) ^ 2 := by
  exact firstDerivAux a b c d x h

theorem gap2 (a b c d x : ℝ) (h : c * x + d ≠ 0) :
    (a * (c * x + d) - c * (a * x + b)) / (c * x + d) ^ 2 =
      (a * d - b * c) / (c * x + d) ^ 2 := by
  ring

theorem gap3 (a b c d x : ℝ) (h : c * x + d ≠ 0) :
    iterDeriv 1 (y a b c d) x =
      (a * d - b * c) / (c * x + d) ^ 2 := by
  calc
    iterDeriv 1 (y a b c d) x =
        (a * (c * x + d) - c * (a * x + b)) / (c * x + d) ^ 2 :=
      gap1 a b c d x h
    _ = (a * d - b * c) / (c * x + d) ^ 2 :=
      gap2 a b c d x h

theorem gap4 (a b c d x : ℝ) (h : c * x + d ≠ 0) :
    iterDeriv 2 (y a b c d) x =
      -(2 * c * (a * d - b * c) / (c * x + d) ^ 3) := by
  calc
    iterDeriv 2 (y a b c d) x = nthClosed 2 a b c d x :=
      iterDerivClosedAux 1 a b c d x h
    _ = -(2 * c * (a * d - b * c) / (c * x + d) ^ 3) := by
      norm_num [nthClosed]
      ring

theorem gap5 (n : ℕ) (a b c d x : ℝ)
    (hn : 1 ≤ n) (h : c * x + d ≠ 0) :
    iterDeriv n (y a b c d) x = nthClosed n a b c d x := by
  cases n with
  | zero => simp at hn
  | succ k =>
      exact iterDerivClosedAux k a b c d x h

theorem gap6 (n : ℕ) (a b c d x : ℝ)
    (hn : n = 2) (h : c * x + d ≠ 0) :
    iterDeriv n (y a b c d) x = nthClosed n a b c d x := by
  subst n
  exact iterDerivClosedAux 1 a b c d x h

theorem gap7 (n : ℕ) (a b c d x : ℝ)
    (hn : 1 ≤ n) (h : c * x + d ≠ 0)
    (hformula : ∀ z, c * z + d ≠ 0 →
      iterDeriv n (y a b c d) z = nthClosed n a b c d z) :
    iterDeriv (n + 1) (y a b c d) x = rawNext n a b c d x := by
  calc
    iterDeriv (n + 1) (y a b c d) x =
        nthClosed (n + 1) a b c d x :=
      gap5 (n + 1) a b c d x (by omega) h
    _ = rawNext n a b c d x :=
      (rawNextEqNthClosedAux n a b c d x hn h).symm

theorem gap8 (n : ℕ) (a b c d x : ℝ)
    (hn : 1 ≤ n) (h : c * x + d ≠ 0) :
    rawNext n a b c d x = nthClosed (n + 1) a b c d x := by
  exact rawNextEqNthClosedAux n a b c d x hn h

theorem gap9 (n : ℕ) (a b c d x : ℝ)
    (hn : 1 ≤ n) (h : c * x + d ≠ 0)
    (hformula : ∀ z, c * z + d ≠ 0 →
      iterDeriv n (y a b c d) z = nthClosed n a b c d z) :
    iterDeriv (n + 1) (y a b c d) x =
      nthClosed (n + 1) a b c d x := by
  exact gap5 (n + 1) a b c d x (by omega) h

end

end ProofGap.Exercise1188
