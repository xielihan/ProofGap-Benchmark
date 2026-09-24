import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise3265

noncomputable section

def u (x y z : ℝ) : ℝ :=
  x * y * z * Real.exp (x + y + z)

def separated (x y z : ℝ) : ℝ :=
  x * Real.exp x * (y * Real.exp y) * (z * Real.exp z)

def factor (x : ℝ) : ℝ := x * Real.exp x

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def partialXOrder (p : ℕ) (g : ℝ → ℝ → ℝ → ℝ)
    (x y z : ℝ) : ℝ :=
  iterDeriv p (fun t => g t y z) x

def partialYOrder (q : ℕ) (g : ℝ → ℝ → ℝ → ℝ)
    (x y z : ℝ) : ℝ :=
  iterDeriv q (fun t => g x t z) y

def partialZOrder (r : ℕ) (g : ℝ → ℝ → ℝ → ℝ)
    (x y z : ℝ) : ℝ :=
  iterDeriv r (fun t => g x y t) z

def mixedOrder (p q r : ℕ) (g : ℝ → ℝ → ℝ → ℝ)
    (x y z : ℝ) : ℝ :=
  partialZOrder r
    (fun a b c => partialYOrder q
      (fun d e f => partialXOrder p g d e f) a b c)
    x y z

def separatedDerivative (p q r : ℕ) (x y z : ℝ) : ℝ :=
  iterDeriv p factor x * iterDeriv q factor y * iterDeriv r factor z

def expandedClosed (p q r : ℕ) (x y z : ℝ) : ℝ :=
  Real.exp x * (x + p) *
    (Real.exp y * (y + q)) *
    (Real.exp z * (z + r))

def closedForm (p q r : ℕ) (x y z : ℝ) : ℝ :=
  Real.exp (x + y + z) *
    (x + p) * (y + q) * (z + r)

private theorem separated_calculus
    (p q r : ℕ) (x y z : ℝ) :
    mixedOrder p q r separated x y z = expandedClosed p q r x y z ∧
      separatedDerivative p q r x y z = expandedClosed p q r x y z := by
  have hscaled : ∀ (n : ℕ) (a b t : ℝ),
      iterDeriv n (fun s => a * factor s * b) t =
        a * (Real.exp t * (t + n)) * b := by
    intro n
    induction n with
    | zero =>
        intro a b t
        simp only [iterDeriv, Function.iterate_zero_apply, factor,
          Nat.cast_zero, add_zero]
        rw [mul_comm t (Real.exp t)]
    | succ n ih =>
        intro a b t
        simp only [iterDeriv, Function.iterate_succ_apply']
        have hiter :
            (deriv^[n]) (fun s => a * factor s * b) =
              fun s => a * (Real.exp s * (s + (n : ℝ))) * b := by
          funext s
          exact ih a b s
        rw [hiter]
        have hd :=
          (((Real.hasDerivAt_exp t).mul
              ((hasDerivAt_id t).add_const (n : ℝ))).const_mul a).mul_const b
        have hderiv := hd.deriv
        change
          deriv (fun s : ℝ => a * (Real.exp s * (s + (n : ℝ))) * b) t =
            a * (Real.exp t * (t + (n : ℝ)) + Real.exp t * 1) * b
          at hderiv
        calc
          deriv (fun s : ℝ => a * (Real.exp s * (s + (n : ℝ))) * b) t =
              a * (Real.exp t * (t + (n : ℝ)) + Real.exp t * 1) * b := hderiv
          _ = a * (Real.exp t * (t + (Nat.succ n : ℕ))) * b := by
            rw [Nat.cast_succ]
            ring
  have hfactor (n : ℕ) (t : ℝ) :
      iterDeriv n factor t = Real.exp t * (t + n) := by
    simpa using hscaled n 1 1 t
  constructor
  · change
      iterDeriv r
        (fun c => iterDeriv q
          (fun b => iterDeriv p
            (fun a => factor a * factor b * factor c) x) y) z =
        Real.exp x * (x + p) *
          (Real.exp y * (y + q)) *
          (Real.exp z * (z + r))
    have hx (b c : ℝ) :
        iterDeriv p (fun a => factor a * factor b * factor c) x =
          Real.exp x * (x + p) * factor b * factor c := by
      simpa [mul_assoc] using
        hscaled p 1 (factor b * factor c) x
    simp_rw [hx]
    have hy (c : ℝ) :
        iterDeriv q
            (fun b => Real.exp x * (x + p) * factor b * factor c) y =
          Real.exp x * (x + p) *
            (Real.exp y * (y + q)) * factor c := by
      exact hscaled q (Real.exp x * (x + p)) (factor c) y
    simp_rw [hy]
    simpa using
      hscaled r
        (Real.exp x * (x + p) * (Real.exp y * (y + q))) 1 z
  · change
      iterDeriv p factor x * iterDeriv q factor y * iterDeriv r factor z =
        Real.exp x * (x + p) *
          (Real.exp y * (y + q)) *
          (Real.exp z * (z + r))
    rw [hfactor p x, hfactor q y, hfactor r z]

theorem gap1 :
    ∀ p q r x y z,
      mixedOrder p q r u x y z =
        mixedOrder p q r separated x y z := by
  intro p q r x y z
  have hu : u = separated := by
    funext a b c
    simp [u, separated, Real.exp_add] <;> ring
  rw [hu]

theorem gap2 :
    ∀ p q r x y z,
      mixedOrder p q r separated x y z =
        separatedDerivative p q r x y z := by
  intro p q r x y z
  have h := separated_calculus p q r x y z
  exact h.1.trans h.2.symm

theorem gap3 :
    ∀ p q r x y z,
      mixedOrder p q r u x y z =
        separatedDerivative p q r x y z := by
  intro p q r x y z
  exact (gap1 p q r x y z).trans (gap2 p q r x y z)

theorem gap4 :
    ∀ p q r x y z,
      mixedOrder p q r u x y z = expandedClosed p q r x y z := by
  intro p q r x y z
  exact (gap3 p q r x y z).trans (separated_calculus p q r x y z).2

theorem gap5 :
    ∀ x p y q z r, expandedClosed p q r x y z =
      closedForm p q r x y z := by
  intro x p y q z r
  simp only [expandedClosed, closedForm, Real.exp_add]
  ring

theorem gap6 :
    ∀ p q r x y z,
      mixedOrder p q r u x y z = closedForm p q r x y z := by
  intro p q r x y z
  exact (gap4 p q r x y z).trans (gap5 x p y q z r)

end

end ProofGap.Exercise3265
