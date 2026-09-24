import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3266

noncomputable section

def f (x y : ℝ) : ℝ :=
  Real.exp x * Real.sin y

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def partialXOrder (m : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv m (fun t => g t y) x

def mixedOrder (m n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv n (fun t => partialXOrder m g x t) y

private theorem iterDeriv_exp_mul_const (m : ℕ) (c x : ℝ) :
    iterDeriv m (fun t : ℝ => Real.exp t * c) x = Real.exp x * c := by
  induction m generalizing x with
  | zero =>
      rfl
  | succ m ih =>
      unfold iterDeriv
      rw [Function.iterate_succ_apply']
      have hiter : (deriv^[m]) (fun t : ℝ => Real.exp t * c) =
          (fun t : ℝ => Real.exp t * c) := by
        funext t
        exact ih t
      rw [hiter]
      exact ((Real.hasDerivAt_exp x).mul_const c).deriv

private theorem deriv_sin_add_phase (a x : ℝ) :
    deriv (fun t : ℝ => Real.sin (t + a)) x =
      Real.sin (x + (a + Real.pi / 2)) := by
  have h : HasDerivAt (fun t : ℝ => Real.sin (t + a))
      (Real.cos (x + a)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin (x + a)).comp x
        ((hasDerivAt_id x).add_const a)
  rw [h.deriv]
  simpa [add_assoc] using (Real.sin_add_pi_div_two (x + a)).symm

private theorem iterDeriv_sin_phase (n : ℕ) (x : ℝ) :
    iterDeriv n Real.sin x =
      Real.sin (x + (n : ℝ) * Real.pi / 2) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      unfold iterDeriv
      rw [Function.iterate_succ_apply']
      have hiter : (deriv^[n]) Real.sin =
          (fun t : ℝ => Real.sin (t + (n : ℝ) * Real.pi / 2)) := by
        funext t
        exact ih t
      rw [hiter]
      rw [deriv_sin_add_phase]
      apply congrArg Real.sin
      rw [Nat.cast_succ]
      ring

theorem gap1 :
    ∀ m n, mixedOrder m n f 0 0 =
      Real.exp 0 * Real.sin ((n : ℝ) * Real.pi / 2) := by
  intro m n
  have hx : (fun t : ℝ => partialXOrder m f 0 t) =
      (fun t : ℝ => Real.exp 0 * Real.sin t) := by
    funext t
    unfold partialXOrder
    change iterDeriv m (fun s : ℝ => Real.exp s * Real.sin t) 0 =
      Real.exp 0 * Real.sin t
    exact iterDeriv_exp_mul_const m (Real.sin t) 0
  unfold mixedOrder
  rw [hx]
  simp only [Real.exp_zero, one_mul]
  simpa using (iterDeriv_sin_phase n 0)

theorem gap2 :
    ∀ n, Real.exp 0 * Real.sin ((n : ℝ) * Real.pi / 2) =
      Real.sin ((n : ℝ) * Real.pi / 2) := by
  intro n
  simp

theorem gap3 :
    ∀ m n, mixedOrder m n f 0 0 =
      Real.sin ((n : ℝ) * Real.pi / 2) := by
  intro m n
  calc
    mixedOrder m n f 0 0 =
        Real.exp 0 * Real.sin ((n : ℝ) * Real.pi / 2) := gap1 m n
    _ = Real.sin ((n : ℝ) * Real.pi / 2) := gap2 n

end

end ProofGap.Exercise3266
