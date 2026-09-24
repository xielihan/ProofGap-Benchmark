import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1190

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ := 1 / (x ^ 2 - 3 * x + 2)

def closed (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) *
    (1 / (x - 2) ^ (n + 1) - 1 / (x - 1) ^ (n + 1))

private theorem hasDerivAt_one_div_pow_sub
    (n : ℕ) (c x : ℝ) (hx : x - c ≠ 0) :
    HasDerivAt (fun z : ℝ => 1 / (z - c) ^ n)
      (-(n : ℝ) / (x - c) ^ (n + 1)) x := by
  cases n with
  | zero =>
      convert hasDerivAt_const (x := x) (c := (1 : ℝ)) using 1 <;>
        (try funext z) <;> simp
  | succ n =>
      have hsub := (hasDerivAt_id x).sub_const c
      have h := (hsub.pow (n + 1)).inv (pow_ne_zero (n + 1) hx)
      convert h using 1
      all_goals
        first
        | funext z
          simp
        | simp [pow_succ]
          field_simp [hx]
          ring

private theorem hasDerivAt_closed
    (n : ℕ) (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    HasDerivAt (closed n) (closed (n + 1) x) x := by
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hx2' : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have h2 := hasDerivAt_one_div_pow_sub (n + 1) 2 x hx2'
  have h1 := hasDerivAt_one_div_pow_sub (n + 1) 1 x hx1'
  unfold closed
  convert (h2.sub h1).const_mul
    ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ)) using 1
  simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  ring

theorem gap1 (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    y x = 1 / ((x - 2) * (x - 1)) := by
  unfold y
  congr 1
  ring

theorem gap2 (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    1 / ((x - 2) * (x - 1)) = 1 / (x - 2) - 1 / (x - 1) := by
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hx2' : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  field_simp [hx1', hx2']
  ring

theorem gap3 (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    y x = 1 / (x - 2) - 1 / (x - 1) := by
  calc
    y x = 1 / ((x - 2) * (x - 1)) := gap1 x hx1 hx2
    _ = 1 / (x - 2) - 1 / (x - 1) := gap2 x hx1 hx2

theorem gap4 (n : ℕ) (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    iterDeriv n y x = closed n x := by
  induction n generalizing x with
  | zero =>
      change y x = closed 0 x
      rw [gap3 x hx1 hx2]
      simp [closed]
  | succ n ih =>
      have heq :
          iterDeriv n y =ᶠ[nhds x] closed n := by
        filter_upwards [eventually_ne_nhds hx1,
          eventually_ne_nhds hx2] with z hz1 hz2
        exact ih z hz1 hz2
      have hsucc :
          iterDeriv (n + 1) y = deriv (iterDeriv n y) := by
        simp [iterDeriv, Function.iterate_succ_apply']
      rw [hsucc]
      calc
        deriv (iterDeriv n y) x = deriv (closed n) x := heq.deriv_eq
        _ = closed (n + 1) x :=
          (hasDerivAt_closed n x hx1 hx2).deriv

end

end ProofGap.Exercise1190
