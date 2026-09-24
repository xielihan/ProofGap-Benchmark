import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1209

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (a : ℝ) (P : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (a * x) * P x

def leibnizSum (a : ℝ) (P : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * a ^ (n - k) * iterDeriv k P x

theorem gap1 (a : ℝ) (P : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hP : ContDiffAt ℝ n P x) :
    iterDeriv n (y a P) x = Real.exp (a * x) * leibnizSum a P n x := by
  have he : ContDiffAt ℝ n (fun t : ℝ => Real.exp (a * t)) x := by
    exact (Real.contDiff_exp.contDiffAt.of_le le_top).comp x
      (contDiffAt_const.mul contDiffAt_id)
  have h := iteratedDeriv_mul (n := n) (x := x)
    (f := P) (g := fun t : ℝ => Real.exp (a * t)) hP he
  have hy : y a P = P * fun t : ℝ => Real.exp (a * t) := by
    funext t
    simp [y, mul_comm]
  have hleib :
      iterDeriv n (y a P) x =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * iterDeriv k P x *
            iterDeriv (n - k) (fun t : ℝ => Real.exp (a * t)) x := by
    rw [hy]
    simpa only [iteratedDeriv_eq_iterate, iterDeriv, mul_assoc] using h
  rw [hleib]
  unfold leibnizSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hexp :
      iterDeriv (n - k) (fun t : ℝ => Real.exp (a * t)) x =
        a ^ (n - k) * Real.exp (a * x) := by
    have hexp' := congrFun (iteratedDeriv_exp_const_mul (n - k) a) x
    simpa only [iteratedDeriv_eq_iterate, iterDeriv] using hexp'
  rw [hexp]
  ring

end

end ProofGap.Exercise1209
