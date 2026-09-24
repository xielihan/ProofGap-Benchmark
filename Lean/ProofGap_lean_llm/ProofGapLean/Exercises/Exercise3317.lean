import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3317

noncomputable section

def z (n : ℕ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  x ^ n * f (y / x ^ 2)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

theorem gap1 (n : ℕ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x y, x ≠ 0 →
      x * partialX (z n f) x y + 2 * y * partialY (z n f) x y =
        x * ((n : ℝ) * x ^ (n - 1) * f (y / x ^ 2) -
          (2 * x ^ n * y / x ^ 3) * deriv f (y / x ^ 2)) +
        2 * y * (x ^ n / x ^ 2) * deriv f (y / x ^ 2) := by
  intro x y hx
  have hpow : ∀ k : ℕ, HasDerivAt (fun s : ℝ => s ^ k)
      ((k : ℝ) * x ^ (k - 1)) x := by
    intro k
    induction k with
    | zero =>
        simpa using (hasDerivAt_const x (1 : ℝ))
    | succ k ih =>
        cases k with
        | zero =>
            simpa using (hasDerivAt_id x)
        | succ k =>
            convert ih.mul (hasDerivAt_id x) using 1 <;>
              simp [pow_succ, Nat.cast_succ] <;> ring
  have hinnerX : HasDerivAt (fun s : ℝ => y / s ^ 2)
      (-2 * y / x ^ 3) x := by
    convert (hasDerivAt_const x y).div (hpow 2)
      (pow_ne_zero 2 hx) using 1 <;> field_simp [hx] <;> ring
  have hcompX : HasDerivAt (fun s : ℝ => f (y / s ^ 2))
      (deriv f (y / x ^ 2) * (-2 * y / x ^ 3)) x := by
    simpa only [Function.comp_apply] using
      HasDerivAt.comp x (hf (y / x ^ 2)).hasDerivAt hinnerX
  have hzX : HasDerivAt (fun s : ℝ => z n f s y)
      ((n : ℝ) * x ^ (n - 1) * f (y / x ^ 2) -
        (2 * x ^ n * y / x ^ 3) * deriv f (y / x ^ 2)) x := by
    unfold z
    convert (hpow n).mul hcompX using 1 <;>
      field_simp [hx] <;> ring
  have hinnerY : HasDerivAt (fun s : ℝ => s / x ^ 2)
      (1 / x ^ 2) y := by
    convert (hasDerivAt_id y).div (hasDerivAt_const y (x ^ 2))
      (pow_ne_zero 2 hx) using 1 <;> field_simp [hx] <;> ring
  have hcompY : HasDerivAt (fun s : ℝ => f (s / x ^ 2))
      (deriv f (y / x ^ 2) * (1 / x ^ 2)) y := by
    simpa only [Function.comp_apply] using
      HasDerivAt.comp y (hf (y / x ^ 2)).hasDerivAt hinnerY
  have hzY : HasDerivAt (fun s : ℝ => z n f x s)
      ((x ^ n / x ^ 2) * deriv f (y / x ^ 2)) y := by
    unfold z
    convert (hasDerivAt_const y (x ^ n)).mul hcompY using 1 <;>
      field_simp [hx] <;> ring
  have hpx : partialX (z n f) x y =
      (n : ℝ) * x ^ (n - 1) * f (y / x ^ 2) -
        (2 * x ^ n * y / x ^ 3) * deriv f (y / x ^ 2) := by
    simpa only [partialX] using hzX.deriv
  have hpy : partialY (z n f) x y =
      (x ^ n / x ^ 2) * deriv f (y / x ^ 2) := by
    simpa only [partialY] using hzY.deriv
  rw [hpx, hpy]
  ring

theorem gap2 (n : ℕ) (f : ℝ → ℝ) :
    ∀ x y, x ≠ 0 →
      x * ((n : ℝ) * x ^ (n - 1) * f (y / x ^ 2) -
          (2 * x ^ n * y / x ^ 3) * deriv f (y / x ^ 2)) +
          2 * y * (x ^ n / x ^ 2) * deriv f (y / x ^ 2) =
        (n : ℝ) * x ^ n * f (y / x ^ 2) := by
  intro x y hx
  cases n with
  | zero =>
      field_simp [hx]
      ring
  | succ n =>
      simp only [Nat.succ_sub_one]
      field_simp [hx]
      ring

theorem gap3 (n : ℕ) (f : ℝ → ℝ) :
    ∀ x y, x ≠ 0 →
      (n : ℝ) * x ^ n * f (y / x ^ 2) =
        (n : ℝ) * z n f x y := by
  intro x y hx
  simp [z, mul_assoc]

theorem gap4 (n : ℕ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x y, x ≠ 0 →
      x * partialX (z n f) x y + 2 * y * partialY (z n f) x y =
        (n : ℝ) * z n f x y := by
  intro x y hx
  calc
    x * partialX (z n f) x y + 2 * y * partialY (z n f) x y =
        x * ((n : ℝ) * x ^ (n - 1) * f (y / x ^ 2) -
          (2 * x ^ n * y / x ^ 3) * deriv f (y / x ^ 2)) +
        2 * y * (x ^ n / x ^ 2) * deriv f (y / x ^ 2) :=
      gap1 n f hf x y hx
    _ = (n : ℝ) * x ^ n * f (y / x ^ 2) := gap2 n f x y hx
    _ = (n : ℝ) * z n f x y := gap3 n f x y hx

theorem gap5 (n : ℕ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x y, x ≠ 0 →
      x * partialX (z n f) x y + 2 * y * partialY (z n f) x y =
        (n : ℝ) * z n f x y := by
  exact gap4 n f hf

end

end ProofGap.Exercise3317
