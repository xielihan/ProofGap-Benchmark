import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1165

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x ^ 2 * Real.sin (2 * x)
def s (x : ℝ) : ℝ := Real.sin (2 * x)

def leibniz50 (x : ℝ) : ℝ :=
  x ^ 2 * nthDeriv 50 s x +
    (Nat.choose 50 1 : ℝ) * (2 * x) * nthDeriv 49 s x +
    2 * (Nat.choose 50 2 : ℝ) * nthDeriv 48 s x

def phased50 (x : ℝ) : ℝ :=
  2 ^ 50 * x ^ 2 * Real.sin (2 * x + (50 / 2 : ℝ) * Real.pi) +
    100 * x * 2 ^ 49 * Real.sin (2 * x + (49 / 2 : ℝ) * Real.pi) +
    ((50 * 49 : ℝ) / (1 * 2)) * 2 ^ 49 *
      Real.sin (2 * x + (48 / 2 : ℝ) * Real.pi)

private abbrev OscCoeff := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

private def mkCoeff (a b c d e f : ℝ) : OscCoeff := (a, b, c, d, e, f)

private def ca (q : OscCoeff) : ℝ := q.1

private def cb (q : OscCoeff) : ℝ := q.2.1

private def cc (q : OscCoeff) : ℝ := q.2.2.1

private def cd (q : OscCoeff) : ℝ := q.2.2.2.1

private def ce (q : OscCoeff) : ℝ := q.2.2.2.2.1

private def cf (q : OscCoeff) : ℝ := q.2.2.2.2.2

private def nextCoeff (q : OscCoeff) : OscCoeff :=
  mkCoeff
    (-2 * cd q)
    (2 * ca q - 2 * ce q)
    (cb q - 2 * cf q)
    (2 * ca q)
    (2 * cb q + 2 * cd q)
    (2 * cc q + ce q)

private def osc (q : OscCoeff) (x : ℝ) : ℝ :=
  (ca q * x ^ 2 + cb q * x + cc q) * Real.sin (2 * x) +
    (cd q * x ^ 2 + ce q * x + cf q) * Real.cos (2 * x)

private theorem hasDerivAt_osc (q : OscCoeff) (x : ℝ) :
    HasDerivAt (osc q) (osc (nextCoeff q) x) x := by
  have hx : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hP :
      HasDerivAt
        (fun t : ℝ => ca q * t ^ 2 + cb q * t + cc q)
        (2 * ca q * x + cb q) x := by
    convert
      (((hasDerivAt_const x (ca q)).mul (hx.pow 2)).add
        ((hasDerivAt_const x (cb q)).mul hx)).add
        (hasDerivAt_const x (cc q)) using 1 <;> ring
  have hQ :
      HasDerivAt
        (fun t : ℝ => cd q * t ^ 2 + ce q * t + cf q)
        (2 * cd q * x + ce q) x := by
    convert
      (((hasDerivAt_const x (cd q)).mul (hx.pow 2)).add
        ((hasDerivAt_const x (ce q)).mul hx)).add
        (hasDerivAt_const x (cf q)) using 1 <;> ring
  have htwo : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    convert (hasDerivAt_const x (2 : ℝ)).mul hx using 1 <;> ring
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (2 * t))
        (2 * Real.cos (2 * x)) x := by
    convert (Real.hasDerivAt_sin (2 * x)).comp x htwo using 1 <;> ring
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (2 * t))
        (-2 * Real.sin (2 * x)) x := by
    convert (Real.hasDerivAt_cos (2 * x)).comp x htwo using 1 <;> ring
  convert (hP.mul hsin).add (hQ.mul hcos) using 1 <;>
    simp only [osc, nextCoeff, mkCoeff, ca, cb, cc, cd, ce, cf] <;> ring

private def iterCoeff : ℕ → OscCoeff → OscCoeff
  | 0, q => q
  | n + 1, q => nextCoeff (iterCoeff n q)

private theorem nthDeriv_osc (n : ℕ) (q : OscCoeff) :
    nthDeriv n (osc q) = osc (iterCoeff n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change deriv (nthDeriv n (osc q)) = osc (nextCoeff (iterCoeff n q))
      rw [ih]
      funext x
      exact (hasDerivAt_osc (iterCoeff n q) x).deriv

private def yCoeff : OscCoeff := mkCoeff 1 0 0 0 0 0

private def sCoeff : OscCoeff := mkCoeff 0 0 1 0 0 0

private theorem nthDeriv_y_value (n : ℕ) (x : ℝ) :
    nthDeriv n y x = osc (iterCoeff n yCoeff) x := by
  have hy : y = osc yCoeff := by
    funext t
    simp [y, osc, yCoeff, mkCoeff, ca, cb, cc, cd, ce, cf]
  rw [hy]
  exact congrFun (nthDeriv_osc n yCoeff) x

private theorem nthDeriv_s_value (n : ℕ) (x : ℝ) :
    nthDeriv n s x = osc (iterCoeff n sCoeff) x := by
  have hs : s = osc sCoeff := by
    funext t
    simp [s, osc, sCoeff, mkCoeff, ca, cb, cc, cd, ce, cf]
  rw [hs]
  exact congrFun (nthDeriv_osc n sCoeff) x

private theorem fiftieth_y (x : ℝ) :
    nthDeriv 50 y x =
      (2 : ℝ) ^ 50 *
        (-(x ^ 2) * Real.sin (2 * x) +
          50 * x * Real.cos (2 * x) +
          (1225 / 2 : ℝ) * Real.sin (2 * x)) := by
  set_option maxHeartbeats 2000000 in
    set_option maxRecDepth 4096 in
      rw [nthDeriv_y_value]
      norm_num [osc, iterCoeff, nextCoeff, yCoeff, mkCoeff, ca, cb, cc, cd, ce, cf] <;> ring

private theorem nthDeriv_s_values (x : ℝ) :
    nthDeriv 48 s x = (2 : ℝ) ^ 48 * Real.sin (2 * x) ∧
      nthDeriv 49 s x = (2 : ℝ) ^ 49 * Real.cos (2 * x) ∧
      nthDeriv 50 s x = -((2 : ℝ) ^ 50) * Real.sin (2 * x) := by
  set_option maxHeartbeats 2000000 in
    set_option maxRecDepth 4096 in
      constructor
      · rw [nthDeriv_s_value]
        norm_num [osc, iterCoeff, nextCoeff, sCoeff, mkCoeff, ca, cb, cc, cd, ce, cf] <;> ring
      constructor
      · rw [nthDeriv_s_value]
        norm_num [osc, iterCoeff, nextCoeff, sCoeff, mkCoeff, ca, cb, cc, cd, ce, cf] <;> ring
      · rw [nthDeriv_s_value]
        norm_num [osc, iterCoeff, nextCoeff, sCoeff, mkCoeff, ca, cb, cc, cd, ce, cf] <;> ring

private theorem sin_add_nat_mul_pi (x : ℝ) (n : ℕ) :
    Real.sin (x + (n : ℝ) * Real.pi) =
      (-1 : ℝ) ^ n * Real.sin x := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Real.sin (x + (Nat.succ n : ℝ) * Real.pi) =
            Real.sin ((x + (n : ℝ) * Real.pi) + Real.pi) := by
              congr 1
              rw [Nat.cast_succ]
              ring
        _ = -Real.sin (x + (n : ℝ) * Real.pi) := by
              rw [Real.sin_add]
              simp
        _ = (-1 : ℝ) ^ Nat.succ n * Real.sin x := by
              rw [ih, pow_succ]
              ring

private theorem cos_add_nat_mul_pi (x : ℝ) (n : ℕ) :
    Real.cos (x + (n : ℝ) * Real.pi) =
      (-1 : ℝ) ^ n * Real.cos x := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Real.cos (x + (Nat.succ n : ℝ) * Real.pi) =
            Real.cos ((x + (n : ℝ) * Real.pi) + Real.pi) := by
              congr 1
              rw [Nat.cast_succ]
              ring
        _ = -Real.cos (x + (n : ℝ) * Real.pi) := by
              rw [Real.cos_add]
              simp
        _ = (-1 : ℝ) ^ Nat.succ n * Real.cos x := by
              rw [ih, pow_succ]
              ring

private theorem phase50 (x : ℝ) :
    Real.sin (2 * x + (50 / 2 : ℝ) * Real.pi) = -Real.sin (2 * x) := by
  convert sin_add_nat_mul_pi (2 * x) 25 using 1 <;> norm_num

private theorem phase48 (x : ℝ) :
    Real.sin (2 * x + (48 / 2 : ℝ) * Real.pi) = Real.sin (2 * x) := by
  convert sin_add_nat_mul_pi (2 * x) 24 using 1 <;> norm_num

private theorem phase49 (x : ℝ) :
    Real.sin (2 * x + (49 / 2 : ℝ) * Real.pi) = Real.cos (2 * x) := by
  calc
    Real.sin (2 * x + (49 / 2 : ℝ) * Real.pi) =
        Real.sin ((2 * x + (24 : ℝ) * Real.pi) + Real.pi / 2) := by
          congr 1
          ring
    _ = Real.cos (2 * x + (24 : ℝ) * Real.pi) := by
          rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
          ring
    _ = Real.cos (2 * x) := by
          convert cos_add_nat_mul_pi (2 * x) 24 using 1 <;> norm_num

theorem gap1 (x : ℝ) : nthDeriv 50 y x = leibniz50 x := by
  rw [fiftieth_y]
  unfold leibniz50
  obtain ⟨h48, h49, h50⟩ := nthDeriv_s_values x
  rw [h50, h49, h48]
  norm_num [Nat.choose] <;> ring

theorem gap2 (x : ℝ) : nthDeriv 50 y x = phased50 x := by
  rw [fiftieth_y]
  unfold phased50
  rw [phase50, phase49, phase48]
  norm_num <;> ring

theorem gap3 (x : ℝ) :
    nthDeriv 50 y x =
      2 ^ 50 *
        (-(x ^ 2) * Real.sin (2 * x) +
          50 * x * Real.cos (2 * x) +
          (1225 / 2 : ℝ) * Real.sin (2 * x)) := by
  exact fiftieth_y x

end

end ProofGap.Exercise1165
