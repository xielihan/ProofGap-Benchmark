import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1193

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ := Real.sin x ^ 2

private theorem iterDeriv_sin_two_aux (k : ℕ) (x : ℝ) :
    iterDeriv k (fun z : ℝ => Real.sin (2 * z)) x =
      (2 : ℝ) ^ k * Real.sin (2 * x + (k : ℝ) / 2 * Real.pi) := by
  induction k generalizing x with
  | zero =>
      simp [iterDeriv]
  | succ k ih =>
      have hsucc :
          iterDeriv (Nat.succ k) (fun z : ℝ => Real.sin (2 * z)) x =
            deriv (iterDeriv k (fun z : ℝ => Real.sin (2 * z))) x := by
        simp only [iterDeriv, Function.iterate_succ_apply']
      have hfun :
          iterDeriv k (fun z : ℝ => Real.sin (2 * z)) =
            fun t : ℝ => (2 : ℝ) ^ k *
              Real.sin (2 * t + (k : ℝ) / 2 * Real.pi) := by
        funext t
        exact ih t
      have hinner : HasDerivAt
          (fun t : ℝ => 2 * t + (k : ℝ) / 2 * Real.pi) 2 x := by
        convert ((hasDerivAt_id x).const_mul (2 : ℝ)).add_const
          ((k : ℝ) / 2 * Real.pi) using 1 <;> ring
      have hd : HasDerivAt
          (fun t : ℝ => (2 : ℝ) ^ k *
            Real.sin (2 * t + (k : ℝ) / 2 * Real.pi))
          ((2 : ℝ) ^ k *
            (Real.cos (2 * x + (k : ℝ) / 2 * Real.pi) * 2)) x := by
        simpa only [Function.comp_apply] using
          (((Real.hasDerivAt_sin
            (2 * x + (k : ℝ) / 2 * Real.pi)).comp x hinner).const_mul
              ((2 : ℝ) ^ k))
      have hphase :
          2 * x + ((Nat.succ k : ℕ) : ℝ) / 2 * Real.pi =
            (2 * x + (k : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
        rw [Nat.cast_succ]
        ring
      rw [hsucc, hfun, hd.deriv, hphase, Real.sin_add,
        Real.cos_pi_div_two, Real.sin_pi_div_two, pow_succ]
      ring

theorem gap1 (x : ℝ) :
    iterDeriv 1 y x = 2 * Real.sin x * Real.cos x := by
  change deriv y x = 2 * Real.sin x * Real.cos x
  have hy : y = fun z : ℝ => Real.sin z * Real.sin z := by
    funext z
    simp only [y, pow_two]
  rw [hy]
  calc
    deriv (fun z : ℝ => Real.sin z * Real.sin z) x =
        Real.cos x * Real.sin x + Real.sin x * Real.cos x :=
      ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_sin x)).deriv
    _ = 2 * Real.sin x * Real.cos x := by ring

theorem gap2 (x : ℝ) :
    2 * Real.sin x * Real.cos x = Real.sin (2 * x) := by
  exact (Real.sin_two_mul x).symm

theorem gap3 (x : ℝ) :
    iterDeriv 1 y x = Real.sin (2 * x) := by
  calc
    iterDeriv 1 y x = 2 * Real.sin x * Real.cos x := gap1 x
    _ = Real.sin (2 * x) := gap2 x

theorem gap4 (n : ℕ) (x : ℝ) :
    iterDeriv n y x = iterDeriv (1 + n - 1) y x := by
  have h : 1 + n - 1 = n := by omega
  rw [h]

theorem gap5 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    iterDeriv (1 + n - 1) y x =
      iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x := by
  have hindex : 1 + n - 1 = n := by omega
  have hsucc : n - 1 + 1 = n := by omega
  have hy : deriv y = fun z : ℝ => Real.sin (2 * z) := by
    funext z
    simpa [iterDeriv] using gap3 z
  calc
    iterDeriv (1 + n - 1) y x = iterDeriv n y x := by rw [hindex]
    _ = iterDeriv (n - 1 + 1) y x := by rw [hsucc]
    _ = iterDeriv (n - 1) (deriv y) x := by
      simp only [iterDeriv, Function.iterate_succ_apply]
    _ = iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x := by rw [hy]

theorem gap6 (n : ℕ) (x : ℝ) :
    iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x =
      (2 : ℝ) ^ (n - 1) *
        Real.sin (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) := by
  exact iterDeriv_sin_two_aux (n - 1) x

theorem gap7 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ (n - 1) *
        Real.sin (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) =
      -(2 : ℝ) ^ (n - 1) *
        Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) := by
  have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hcast : (((n - 1 + 1 : ℕ) : ℝ)) = (n : ℝ) :=
    congrArg (fun m : ℕ => (m : ℝ)) hnat
  have hphase :
      2 * x + (n : ℝ) / 2 * Real.pi =
        (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
    calc
      2 * x + (n : ℝ) / 2 * Real.pi =
          2 * x + (((n - 1 + 1 : ℕ) : ℝ)) / 2 * Real.pi := by rw [hcast]
      _ = (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
  rw [hphase, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem gap8 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    iterDeriv n y x =
      -(2 : ℝ) ^ (n - 1) *
        Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) := by
  calc
    iterDeriv n y x = iterDeriv (1 + n - 1) y x := gap4 n x
    _ = iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x := gap5 n x hn
    _ = (2 : ℝ) ^ (n - 1) *
          Real.sin (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) := gap6 n x
    _ = -(2 : ℝ) ^ (n - 1) *
          Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) := gap7 n x hn

end

end ProofGap.Exercise1193
