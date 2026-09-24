import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1167

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ :=
  Real.sin x * Real.sin (2 * x) * Real.sin (3 * x)

private theorem nthDeriv_trig_sum (n : ℕ) :
    nthDeriv n
        (fun x : ℝ =>
          (1 / 4 : ℝ) * Real.sin (4 * x) -
            (1 / 4 : ℝ) * Real.sin (6 * x) +
            (1 / 4 : ℝ) * Real.sin (2 * x)) =
      (fun x : ℝ =>
        (1 / 4 : ℝ) * 4 ^ n *
            Real.sin (4 * x + (n : ℝ) / 2 * Real.pi) -
          (1 / 4 : ℝ) * 6 ^ n *
            Real.sin (6 * x + (n : ℝ) / 2 * Real.pi) +
          (1 / 4 : ℝ) * 2 ^ n *
            Real.sin (2 * x + (n : ℝ) / 2 * Real.pi)) := by
  induction n with
  | zero =>
      funext x
      simp [nthDeriv]
  | succ n ih =>
      change
        deriv
            (nthDeriv n
              (fun x : ℝ =>
                (1 / 4 : ℝ) * Real.sin (4 * x) -
                  (1 / 4 : ℝ) * Real.sin (6 * x) +
                  (1 / 4 : ℝ) * Real.sin (2 * x))) = _
      rw [ih]
      funext x
      have hlin (a : ℝ) :
          HasDerivAt
            (fun z : ℝ => a * z + (n : ℝ) / 2 * Real.pi) a x := by
        convert
          (((hasDerivAt_const x a).mul (hasDerivAt_id x)).add
            (hasDerivAt_const x ((n : ℝ) / 2 * Real.pi))) using 1 <;> ring
      have hsin (a : ℝ) :
          HasDerivAt
            (fun z : ℝ => Real.sin (a * z + (n : ℝ) / 2 * Real.pi))
            (Real.cos (a * x + (n : ℝ) / 2 * Real.pi) * a) x := by
        exact (Real.hasDerivAt_sin _).comp x (hlin a)
      have hd :
          HasDerivAt
            (fun z : ℝ =>
              (1 / 4 : ℝ) * 4 ^ n *
                  Real.sin (4 * z + (n : ℝ) / 2 * Real.pi) -
                (1 / 4 : ℝ) * 6 ^ n *
                  Real.sin (6 * z + (n : ℝ) / 2 * Real.pi) +
                (1 / 4 : ℝ) * 2 ^ n *
                  Real.sin (2 * z + (n : ℝ) / 2 * Real.pi))
            ((1 / 4 : ℝ) * 4 ^ n *
                  (Real.cos (4 * x + (n : ℝ) / 2 * Real.pi) * 4) -
                (1 / 4 : ℝ) * 6 ^ n *
                  (Real.cos (6 * x + (n : ℝ) / 2 * Real.pi) * 6) +
                (1 / 4 : ℝ) * 2 ^ n *
                  (Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) * 2)) x := by
        convert
          (((hasDerivAt_const x ((1 / 4 : ℝ) * 4 ^ n)).mul (hsin 4)).sub
              ((hasDerivAt_const x ((1 / 4 : ℝ) * 6 ^ n)).mul (hsin 6))).add
            ((hasDerivAt_const x ((1 / 4 : ℝ) * 2 ^ n)).mul (hsin 2)) using 1 <;>
          ring
      rw [hd.deriv]
      have hphase (a : ℝ) :
          a * x + (Nat.succ n : ℝ) / 2 * Real.pi =
            (a * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
        simp only [Nat.cast_succ]
        ring
      rw [hphase 4, hphase 6, hphase 2]
      simp only [Real.sin_add_pi_div_two, pow_succ]
      ring

theorem gap1 (x : ℝ) :
    y x =
      (1 / 4 : ℝ) * Real.sin (4 * x) -
        (1 / 4 : ℝ) * Real.sin (6 * x) +
        (1 / 4 : ℝ) * Real.sin (2 * x) := by
  unfold y
  have h13 :
      Real.cos (2 * x) - Real.cos (4 * x) =
        2 * (Real.sin x * Real.sin (3 * x)) := by
    calc
      Real.cos (2 * x) - Real.cos (4 * x) =
          Real.cos (3 * x - x) - Real.cos (3 * x + x) := by
            congr 1 <;> ring
      _ = 2 * (Real.sin x * Real.sin (3 * x)) := by
        rw [Real.cos_sub, Real.cos_add]
        ring
  have hprod :
      Real.sin x * Real.sin (3 * x) =
        (Real.cos (2 * x) - Real.cos (4 * x)) / 2 := by
    linarith [h13]
  have h22 :
      Real.sin (4 * x) =
        2 * Real.sin (2 * x) * Real.cos (2 * x) := by
    calc
      Real.sin (4 * x) = Real.sin (2 * x + 2 * x) := by
        congr 1 <;> ring
      _ = 2 * Real.sin (2 * x) * Real.cos (2 * x) := by
        rw [Real.sin_add]
        ring
  have h24 :
      Real.sin (6 * x) - Real.sin (2 * x) =
        2 * Real.sin (2 * x) * Real.cos (4 * x) := by
    calc
      Real.sin (6 * x) - Real.sin (2 * x) =
          Real.sin (4 * x + 2 * x) - Real.sin (4 * x - 2 * x) := by
            congr 1 <;> ring
      _ = 2 * Real.sin (2 * x) * Real.cos (4 * x) := by
        rw [Real.sin_add, Real.sin_sub]
        ring
  calc
    Real.sin x * Real.sin (2 * x) * Real.sin (3 * x) =
        Real.sin (2 * x) * (Real.sin x * Real.sin (3 * x)) := by ring
    _ = (1 / 2 : ℝ) * Real.sin (2 * x) *
          (Real.cos (2 * x) - Real.cos (4 * x)) := by
      rw [hprod]
      ring
    _ = (1 / 4 : ℝ) * Real.sin (4 * x) -
          (1 / 4 : ℝ) * (Real.sin (6 * x) - Real.sin (2 * x)) := by
      rw [h22, h24]
      ring
    _ = (1 / 4 : ℝ) * Real.sin (4 * x) -
          (1 / 4 : ℝ) * Real.sin (6 * x) +
          (1 / 4 : ℝ) * Real.sin (2 * x) := by ring

theorem gap2 (x : ℝ) :
    nthDeriv 10 y x =
      (1 / 4 : ℝ) * 4 ^ 10 *
          Real.sin (4 * x + (10 / 2 : ℝ) * Real.pi) -
        (1 / 4 : ℝ) * 6 ^ 10 *
          Real.sin (6 * x + (10 / 2 : ℝ) * Real.pi) +
        (1 / 4 : ℝ) * 2 ^ 10 *
          Real.sin (2 * x + (10 / 2 : ℝ) * Real.pi) := by
  have hy :
      y = (fun z : ℝ =>
        (1 / 4 : ℝ) * Real.sin (4 * z) -
          (1 / 4 : ℝ) * Real.sin (6 * z) +
          (1 / 4 : ℝ) * Real.sin (2 * z)) := by
    funext z
    exact gap1 z
  rw [hy]
  simpa using congrFun (nthDeriv_trig_sum 10) x

theorem gap3 (x : ℝ) :
    nthDeriv 10 y x =
      -(2 : ℝ) ^ 18 * Real.sin (4 * x) +
        2 ^ 8 * 3 ^ 10 * Real.sin (6 * x) -
        2 ^ 8 * Real.sin (2 * x) := by
  have hshift (t : ℝ) :
      Real.sin (t + (10 / 2 : ℝ) * Real.pi) = -Real.sin t := by
    have hfive :
        (10 / 2 : ℝ) * Real.pi =
          Real.pi + Real.pi + Real.pi + Real.pi + Real.pi := by
      ring
    rw [hfive]
    simp [Real.sin_add, Real.cos_add]
  rw [gap2 x, hshift, hshift, hshift]
  norm_num <;> ring

end

end ProofGap.Exercise1167
