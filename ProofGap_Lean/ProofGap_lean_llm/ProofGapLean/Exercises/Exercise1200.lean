import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1200

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (a b x : ℝ) : ℝ :=
  Real.sin (a * x) ^ 2 * Real.cos (b * x)

def expanded (a b x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.cos (b * x) -
    (1 / 4 : ℝ) * Real.cos ((2 * a + b) * x) -
    (1 / 4 : ℝ) * Real.cos ((2 * a - b) * x)

private theorem iterDeriv_expanded_formula (a b : ℝ) (n : ℕ) :
    iterDeriv n (expanded a b) =
      fun x =>
        (1 / 2 : ℝ) * b ^ n *
            Real.cos (b * x + (n : ℝ) / 2 * Real.pi) -
          (1 / 4 : ℝ) * (2 * a + b) ^ n *
            Real.cos ((2 * a + b) * x + (n : ℝ) / 2 * Real.pi) -
          (1 / 4 : ℝ) * (2 * a - b) ^ n *
            Real.cos ((2 * a - b) * x + (n : ℝ) / 2 * Real.pi) := by
  induction n with
  | zero =>
      funext x
      simp [iterDeriv, expanded]
  | succ n ih =>
      rw [show iterDeriv (Nat.succ n) (expanded a b) =
          deriv (iterDeriv n (expanded a b)) by
            simp [iterDeriv, Function.iterate_succ_apply']]
      rw [ih]
      funext x
      let phase : ℝ := (n : ℝ) / 2 * Real.pi
      let nextPhase : ℝ := (Nat.succ n : ℝ) / 2 * Real.pi
      have hphase : nextPhase = phase + Real.pi / 2 := by
        dsimp [phase, nextPhase]
        rw [Nat.cast_succ]
        ring
      have hterm (c k : ℝ) :
          HasDerivAt
            (fun t : ℝ => c * k ^ n * Real.cos (k * t + phase))
            (c * k ^ (Nat.succ n) * Real.cos (k * x + nextPhase)) x := by
        have hinner :
            HasDerivAt (fun t : ℝ => k * t + phase) k x := by
          simpa only [mul_one] using
            (((hasDerivAt_id x).const_mul k).add_const phase)
        have hraw :
            HasDerivAt
              (fun t : ℝ => (c * k ^ n) * Real.cos (k * t + phase))
              ((c * k ^ n) * (-Real.sin (k * x + phase) * k)) x :=
          hinner.cos.const_mul (c * k ^ n)
        have hcos :
            Real.cos (k * x + nextPhase) =
              -Real.sin (k * x + phase) := by
          rw [hphase, ← add_assoc, Real.cos_add,
            Real.cos_pi_div_two, Real.sin_pi_div_two]
          ring
        have hderiv :
            c * k ^ (Nat.succ n) * Real.cos (k * x + nextPhase) =
              (c * k ^ n) * (-Real.sin (k * x + phase) * k) := by
          rw [hcos, pow_succ]
          ring
        rw [hderiv]
        exact hraw
      exact
        (((hterm (1 / 2 : ℝ) b).sub
          (hterm (1 / 4 : ℝ) (2 * a + b))).sub
          (hterm (1 / 4 : ℝ) (2 * a - b))).deriv

theorem gap1 (a b x : ℝ) :
    y a b x =
      (1 / 2 : ℝ) * Real.cos (b * x) *
        (1 - Real.cos (2 * a * x)) := by
  unfold y
  have harg : 2 * a * x = 2 * (a * x) := by ring
  rw [harg, Real.cos_two_mul']
  have hid :
      1 - (Real.cos (a * x) ^ 2 - Real.sin (a * x) ^ 2) =
        2 * Real.sin (a * x) ^ 2 := by
    calc
      1 - (Real.cos (a * x) ^ 2 - Real.sin (a * x) ^ 2) =
          (Real.sin (a * x) ^ 2 + Real.cos (a * x) ^ 2) -
            (Real.cos (a * x) ^ 2 - Real.sin (a * x) ^ 2) := by
              rw [Real.sin_sq_add_cos_sq]
      _ = 2 * Real.sin (a * x) ^ 2 := by ring
  rw [hid]
  ring

theorem gap2 (a b x : ℝ) :
    (1 / 2 : ℝ) * Real.cos (b * x) *
        (1 - Real.cos (2 * a * x)) =
      expanded a b x := by
  unfold expanded
  have hplus : (2 * a + b) * x = 2 * a * x + b * x := by ring
  have hminus : (2 * a - b) * x = 2 * a * x - b * x := by ring
  rw [hplus, hminus, Real.cos_add, Real.cos_sub]
  ring

theorem gap3 (a b x : ℝ) :
    y a b x = expanded a b x := by
  calc
    y a b x =
        (1 / 2 : ℝ) * Real.cos (b * x) *
          (1 - Real.cos (2 * a * x)) := gap1 a b x
    _ = expanded a b x := gap2 a b x

theorem gap4 (a b : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a b) x =
      (1 / 2 : ℝ) * b ^ n *
          Real.cos (b * x + (n : ℝ) / 2 * Real.pi) -
        (1 / 4 : ℝ) * (2 * a + b) ^ n *
          Real.cos ((2 * a + b) * x + (n : ℝ) / 2 * Real.pi) -
        (1 / 4 : ℝ) * (2 * a - b) ^ n *
          Real.cos ((2 * a - b) * x + (n : ℝ) / 2 * Real.pi) := by
  have hfun : y a b = expanded a b := by
    funext t
    exact gap3 a b t
  rw [hfun]
  exact congrFun (iterDeriv_expanded_formula a b n) x

end

end ProofGap.Exercise1200
