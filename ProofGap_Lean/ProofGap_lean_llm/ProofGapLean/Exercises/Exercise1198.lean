import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1198

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (a b x : ℝ) : ℝ :=
  Real.cos (a * x) * Real.cos (b * x)

private theorem hasDerivAt_scaled_cos
    (A c d x : ℝ) :
    HasDerivAt (fun z : ℝ => A * Real.cos (c * z + d))
      (A * c * Real.cos (c * x + d + Real.pi / 2)) x := by
  have hlin : HasDerivAt (fun z : ℝ => c * z + d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).add_const d
  convert (((Real.hasDerivAt_cos (c * x + d)).comp x hlin).const_mul A) using 1
  rw [Real.cos_add_pi_div_two]
  ring

private theorem iterDeriv_two_scaled_cos
    (A c d B e q : ℝ) (n : ℕ) :
    iterDeriv n
        (fun z : ℝ =>
          A * Real.cos (c * z + d) + B * Real.cos (e * z + q)) =
      fun z : ℝ =>
        A * c ^ n *
            Real.cos (c * z + (d + (n : ℝ) / 2 * Real.pi)) +
          B * e ^ n *
            Real.cos (e * z + (q + (n : ℝ) / 2 * Real.pi)) := by
  induction n with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      rw [iterDeriv, Function.iterate_succ_apply']
      change deriv
          (iterDeriv n
            (fun z : ℝ =>
              A * Real.cos (c * z + d) + B * Real.cos (e * z + q))) = _
      rw [ih]
      funext x
      have h :=
        ((hasDerivAt_scaled_cos
            (A * c ^ n) c (d + (n : ℝ) / 2 * Real.pi) x).add
          (hasDerivAt_scaled_cos
            (B * e ^ n) e (q + (n : ℝ) / 2 * Real.pi) x)).deriv
      have hphase :
          (n.succ : ℝ) / 2 * Real.pi =
            (n : ℝ) / 2 * Real.pi + Real.pi / 2 := by
        rw [Nat.cast_succ]
        ring
      simpa only [pow_succ, hphase, mul_assoc, add_assoc] using h

theorem gap1 (a b x : ℝ) :
    y a b x =
      (1 / 2 : ℝ) * Real.cos ((a - b) * x) +
        (1 / 2 : ℝ) * Real.cos ((a + b) * x) := by
  have hsub : (a - b) * x = a * x - b * x := by ring
  have hadd : (a + b) * x = a * x + b * x := by ring
  simp only [y, hsub, hadd, Real.cos_sub, Real.cos_add]
  ring

theorem gap2 (a b : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a b) x =
      (a - b) ^ n / 2 *
          Real.cos ((a - b) * x + (n : ℝ) / 2 * Real.pi) +
        (1 / 2 : ℝ) * (a + b) ^ n *
          Real.cos ((a + b) * x + (n : ℝ) / 2 * Real.pi) := by
  have hy :
      y a b = fun z : ℝ =>
        (1 / 2 : ℝ) * Real.cos ((a - b) * z) +
          (1 / 2 : ℝ) * Real.cos ((a + b) * z) := by
    funext z
    exact gap1 a b z
  rw [hy]
  have h := congrFun
    (iterDeriv_two_scaled_cos
      (1 / 2 : ℝ) (a - b) 0 (1 / 2 : ℝ) (a + b) 0 n) x
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end

end ProofGap.Exercise1198
