import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise3275

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun t => f (x + t * dx) (y + t * dy)) 0

def phase (a b : ℝ) (x y : ℝ) : ℝ :=
  a * x + b * y

def exponential (a b : ℝ) (x y : ℝ) : ℝ :=
  Real.exp (phase a b x y)

private theorem hasDerivAt_phase_line
    (a b x y dx dy t : ℝ) :
    HasDerivAt
      (fun s : ℝ => phase a b (x + s * dx) (y + s * dy))
      (a * dx + b * dy) t := by
  unfold phase
  simpa only [zero_add, one_mul] using
    (((hasDerivAt_const t x).add
          ((hasDerivAt_id t).mul_const dx)).const_mul a).add
      (((hasDerivAt_const t y).add
          ((hasDerivAt_id t).mul_const dy)).const_mul b)

private theorem hasDerivAt_exponential_line
    (a b x y dx dy t : ℝ) :
    HasDerivAt
      (fun s : ℝ => exponential a b (x + s * dx) (y + s * dy))
      (exponential a b (x + t * dx) (y + t * dy) *
        (a * dx + b * dy)) t := by
  simpa only [exponential] using
    (Real.hasDerivAt_exp
      (phase a b (x + t * dx) (y + t * dy))).comp t
        (hasDerivAt_phase_line a b x y dx dy t)

private theorem iterDeriv_exponential_line
    (a b x y dx dy : ℝ) (n : ℕ) :
    iterDeriv n
        (fun t : ℝ => exponential a b (x + t * dx) (y + t * dy)) =
      fun t : ℝ =>
        exponential a b (x + t * dx) (y + t * dy) *
          (a * dx + b * dy) ^ n := by
  induction n with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      unfold iterDeriv
      rw [Function.iterate_succ_apply']
      change
        deriv
            (iterDeriv n
              (fun t : ℝ =>
                exponential a b (x + t * dx) (y + t * dy))) =
          _
      rw [ih]
      funext t
      have h :=
        (hasDerivAt_exponential_line a b x y dx dy t).mul_const
          ((a * dx + b * dy) ^ n)
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h.deriv

theorem gap1 (a b x y dx dy : ℝ) :
    nthDifferential 2 (phase a b) x y dx dy = 0 := by
  unfold nthDifferential
  change
    deriv
        (deriv
          (fun t : ℝ => phase a b (x + t * dx) (y + t * dy)))
        0 =
      0
  have hderiv :
      deriv (fun t : ℝ => phase a b (x + t * dx) (y + t * dy)) =
        fun _ : ℝ => a * dx + b * dy := by
    funext t
    exact (hasDerivAt_phase_line a b x y dx dy t).deriv
  rw [hderiv]
  exact (hasDerivAt_const (0 : ℝ) (a * dx + b * dy)).deriv

theorem gap2 (u : ℝ → ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x y, u x y = exponential a b x y)
    (n : ℕ) (x y dx dy : ℝ) :
    nthDifferential n u x y dx dy =
      nthDifferential n (exponential a b) x y dx dy := by
  have hfun :
      (fun t : ℝ => u (x + t * dx) (y + t * dy)) =
        fun t : ℝ => exponential a b (x + t * dx) (y + t * dy) := by
    funext t
    exact hu _ _
  unfold nthDifferential
  rw [hfun]

theorem gap3 (a b : ℝ) (n : ℕ) (x y dx dy : ℝ) :
    nthDifferential n (exponential a b) x y dx dy =
      exponential a b x y * (a * dx + b * dy) ^ n := by
  unfold nthDifferential
  rw [iterDeriv_exponential_line a b x y dx dy n]
  simp

theorem gap4 (a b : ℝ) (n : ℕ) (x y dx dy : ℝ) :
    exponential a b x y *
        (nthDifferential 1 (phase a b) x y dx dy) ^ n =
      exponential a b x y * (a * dx + b * dy) ^ n := by
  have hfirst :
      nthDifferential 1 (phase a b) x y dx dy = a * dx + b * dy := by
    unfold nthDifferential
    change
      deriv (fun t : ℝ => phase a b (x + t * dx) (y + t * dy)) 0 =
        a * dx + b * dy
    exact (hasDerivAt_phase_line a b x y dx dy 0).deriv
  rw [hfirst]

theorem gap5 (u : ℝ → ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x y, u x y = exponential a b x y)
    (n : ℕ) (x y dx dy : ℝ) :
    nthDifferential n u x y dx dy =
      exponential a b x y * (a * dx + b * dy) ^ n := by
  calc
    nthDifferential n u x y dx dy =
        nthDifferential n (exponential a b) x y dx dy :=
      gap2 u a b hu n x y dx dy
    _ = exponential a b x y * (a * dx + b * dy) ^ n :=
      gap3 a b n x y dx dy

end

end ProofGap.Exercise3275
