import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1168

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x * Real.sinh x

def leibniz100 (x : ℝ) : ℝ :=
  x * nthDeriv 100 Real.sinh x +
    (Nat.choose 100 1 : ℝ) * nthDeriv 99 Real.sinh x

private theorem nthDeriv_sinh_cosh (n : ℕ) :
    nthDeriv (2 * n) Real.sinh = Real.sinh ∧
      nthDeriv (2 * n + 1) Real.sinh = Real.cosh := by
  induction n with
  | zero =>
      constructor
      · rfl
      · change deriv Real.sinh = Real.cosh
        funext x
        exact (Real.hasDerivAt_sinh x).deriv
  | succ n ih =>
      have heven : nthDeriv (2 * (n + 1)) Real.sinh = Real.sinh := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
        change deriv (nthDeriv (2 * n + 1) Real.sinh) = Real.sinh
        rw [ih.2]
        funext x
        exact (Real.hasDerivAt_cosh x).deriv
      constructor
      · exact heven
      · change deriv (nthDeriv (2 * (n + 1)) Real.sinh) = Real.cosh
        rw [heven]
        funext x
        exact (Real.hasDerivAt_sinh x).deriv

private theorem nthDeriv_y_forms (n : ℕ) :
    nthDeriv (2 * n) y =
        (fun x => x * Real.sinh x + ((2 * n : ℕ) : ℝ) * Real.cosh x) ∧
      nthDeriv (2 * n + 1) y =
        (fun x => x * Real.cosh x + ((2 * n + 1 : ℕ) : ℝ) * Real.sinh x) := by
  induction n with
  | zero =>
      constructor
      · funext x
        simp [nthDeriv, y]
      · change deriv y =
          (fun x => x * Real.cosh x + ((1 : ℕ) : ℝ) * Real.sinh x)
        funext x
        rw [show y = (fun z : ℝ => z * Real.sinh z) by rfl]
        have h :=
          ((hasDerivAt_id x : HasDerivAt (fun z : ℝ => z) 1 x).mul
            (Real.hasDerivAt_sinh x))
        convert h.deriv using 1 <;> simp [id] <;> ring
  | succ n ih =>
      have heven :
          nthDeriv (2 * (n + 1)) y =
            (fun x =>
              x * Real.sinh x + ((2 * (n + 1) : ℕ) : ℝ) * Real.cosh x) := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
        change deriv (nthDeriv (2 * n + 1) y) =
          (fun x =>
            x * Real.sinh x + ((2 * (n + 1) : ℕ) : ℝ) * Real.cosh x)
        rw [ih.2]
        funext x
        have h :=
          (((hasDerivAt_id x : HasDerivAt (fun z : ℝ => z) 1 x).mul
              (Real.hasDerivAt_cosh x)).add
            ((Real.hasDerivAt_sinh x).const_mul
              (((2 * n + 1 : ℕ) : ℝ))))
        convert h.deriv using 1 <;>
          norm_num [Nat.cast_add, Nat.cast_mul, id] <;> ring
      constructor
      · exact heven
      · change deriv (nthDeriv (2 * (n + 1)) y) =
          (fun x =>
            x * Real.cosh x + ((2 * (n + 1) + 1 : ℕ) : ℝ) * Real.sinh x)
        rw [heven]
        funext x
        have h :=
          (((hasDerivAt_id x : HasDerivAt (fun z : ℝ => z) 1 x).mul
              (Real.hasDerivAt_sinh x)).add
            ((Real.hasDerivAt_cosh x).const_mul
              (((2 * (n + 1) : ℕ) : ℝ))))
        convert h.deriv using 1 <;>
          norm_num [Nat.cast_add, Nat.cast_mul, id] <;> ring

theorem gap1 (x : ℝ) : nthDeriv 100 y x = leibniz100 x := by
  have hy := congrFun (nthDeriv_y_forms 50).1 x
  have hs100 := congrFun (nthDeriv_sinh_cosh 50).1 x
  have hs99 := congrFun (nthDeriv_sinh_cosh 49).2 x
  norm_num at hy hs100 hs99
  rw [hy]
  unfold leibniz100
  rw [hs100, hs99]
  norm_num

theorem gap2 (x : ℝ) :
    leibniz100 x = x * Real.sinh x + 100 * Real.cosh x := by
  have hs100 := congrFun (nthDeriv_sinh_cosh 50).1 x
  have hs99 := congrFun (nthDeriv_sinh_cosh 49).2 x
  norm_num at hs100 hs99
  unfold leibniz100
  rw [hs100, hs99]
  norm_num

theorem gap3 (x : ℝ) :
    nthDeriv 100 y x = x * Real.sinh x + 100 * Real.cosh x := by
  calc
    nthDeriv 100 y x = leibniz100 x := gap1 x
    _ = x * Real.sinh x + 100 * Real.cosh x := gap2 x

end

end ProofGap.Exercise1168
