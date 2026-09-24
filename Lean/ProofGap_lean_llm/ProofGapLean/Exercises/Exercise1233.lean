import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1233

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def weighted (lam : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (lam * x) * u x

def shiftedDerivative (lam : ℝ) (u : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (Nat.choose k i : ℝ) * lam ^ i * iterDeriv (k - i) u x

def differentialOperator (p : ℕ → ℝ → ℝ) (n : ℕ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), p k x * iterDeriv k u x

def shiftedOperator (p : ℕ → ℝ → ℝ) (n : ℕ) (lam : ℝ)
    (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), p k x * shiftedDerivative lam u k x

private theorem iterDeriv_exp_mul (i : ℕ) (lam x : ℝ) :
    iterDeriv i (fun t : ℝ => Real.exp (lam * t)) x =
      lam ^ i * Real.exp (lam * x) := by
  induction i generalizing x with
  | zero =>
      simp [iterDeriv]
  | succ i ih =>
      change (deriv^[Nat.succ i]) (fun t : ℝ => Real.exp (lam * t)) x = _
      rw [Function.iterate_succ_apply']
      rw [show (deriv^[i]) (fun t : ℝ => Real.exp (lam * t)) =
          fun t : ℝ => lam ^ i * Real.exp (lam * t) by
        funext y
        simpa [iterDeriv] using ih y]
      have hinner : HasDerivAt (fun t : ℝ => lam * t) lam x := by
        simpa using (hasDerivAt_id x).const_mul lam
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (lam * t))
          (Real.exp (lam * x) * lam) x :=
        (Real.hasDerivAt_exp (lam * x)).comp x hinner
      have hd : HasDerivAt (fun t : ℝ => lam ^ i * Real.exp (lam * t))
          (lam ^ i * (Real.exp (lam * x) * lam)) x :=
        hexp.const_mul (lam ^ i)
      rw [hd.deriv]
      ring

theorem gap1 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ) :
    iterDeriv k (weighted lam u) x = iterDeriv k (weighted lam u) x := by
  rfl

theorem gap2 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffAt ℝ k u x) :
    iterDeriv k (weighted lam u) x =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) *
          iterDeriv i (fun t : ℝ => Real.exp (lam * t)) x *
          iterDeriv (k - i) u x := by
  have he : ContDiffAt ℝ k (fun t : ℝ => Real.exp (lam * t)) x := by
    exact (Real.contDiff_exp.contDiffAt.of_le le_top).comp x
      (contDiffAt_const.mul contDiffAt_id)
  simpa only [weighted, iterDeriv, ← iteratedDeriv_eq_iterate] using
    (iteratedDeriv_mul he hu)

theorem gap3 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffAt ℝ k u x) :
    iterDeriv k (weighted lam u) x =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) *
          iterDeriv i (fun t : ℝ => Real.exp (lam * t)) x *
          iterDeriv (k - i) u x := by
  exact gap2 k lam x u hu

theorem gap4 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffAt ℝ k u x) :
    iterDeriv k (weighted lam u) x =
      Real.exp (lam * x) * shiftedDerivative lam u k x := by
  rw [gap2 k lam x u hu]
  unfold shiftedDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iterDeriv_exp_mul]
  ring

theorem gap5 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ) :
    shiftedDerivative lam u k x =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) * lam ^ i * iterDeriv (k - i) u x := by
  rfl

theorem gap6 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ) :
    (∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) * lam ^ i * iterDeriv (k - i) u x) =
      shiftedDerivative lam u k x := by
  rfl

theorem gap7 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ) :
    shiftedDerivative lam u k x =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) * lam ^ i * iterDeriv (k - i) u x := by
  rfl

theorem gap8 (k : ℕ) (lam x : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffAt ℝ k u x) :
    iterDeriv k (weighted lam u) x =
      Real.exp (lam * x) * shiftedDerivative lam u k x := by
  exact gap4 k lam x u hu

theorem gap9 (p : ℕ → ℝ → ℝ) (n : ℕ) (lam x : ℝ) (u : ℝ → ℝ) :
    differentialOperator p n (weighted lam u) x =
      ∑ k ∈ Finset.range (n + 1),
        p k x * iterDeriv k (weighted lam u) x := by
  rfl

theorem gap10 (p : ℕ → ℝ → ℝ) (n : ℕ) (lam x : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffAt ℝ n u x) :
    differentialOperator p n (weighted lam u) x =
      Real.exp (lam * x) *
        ∑ k ∈ Finset.range (n + 1), p k x * shiftedDerivative lam u k x := by
  unfold differentialOperator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hknENat : (k : ℕ∞) ≤ (n : ℕ∞) :=
    WithTop.coe_le_coe.mpr hkn
  have hknTop :
      ((k : ℕ∞) : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr hknENat
  have huk : ContDiffAt ℝ k u x := hu.of_le hknTop
  rw [gap4 k lam x u huk]
  ring

theorem gap11 (p : ℕ → ℝ → ℝ) (n : ℕ) (lam x : ℝ) (u : ℝ → ℝ) :
    Real.exp (lam * x) *
        (∑ k ∈ Finset.range (n + 1), p k x * shiftedDerivative lam u k x) =
      Real.exp (lam * x) * shiftedOperator p n lam u x := by
  rfl

theorem gap12 (p : ℕ → ℝ → ℝ) (n : ℕ) (lam x : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffAt ℝ n u x) :
    differentialOperator p n (weighted lam u) x =
      Real.exp (lam * x) * shiftedOperator p n lam u x := by
  calc
    differentialOperator p n (weighted lam u) x =
        Real.exp (lam * x) *
          (∑ k ∈ Finset.range (n + 1), p k x * shiftedDerivative lam u k x) :=
      gap10 p n lam x u hu
    _ = Real.exp (lam * x) * shiftedOperator p n lam u x :=
      gap11 p n lam x u

theorem gap13 (p : ℕ → ℝ → ℝ) (n : ℕ) (lam x : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffAt ℝ n u x) :
    differentialOperator p n (weighted lam u) x =
      Real.exp (lam * x) * shiftedOperator p n lam u x := by
  exact gap12 p n lam x u hu

end

end ProofGap.Exercise1233
