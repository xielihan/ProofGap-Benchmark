import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1219_2

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (x : ℝ) : ℝ := x / Real.sqrt (1 - x)

def oddDoubleFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * oddDoubleFactorial n

def nthFormula (n : ℕ) (x : ℝ) : ℝ :=
  (oddDoubleFactorial (n - 1) : ℝ) / 2 ^ n /
      Real.sqrt (1 - x) ^ (2 * n - 1) +
    (oddDoubleFactorial n : ℝ) / 2 ^ n /
      Real.sqrt (1 - x) ^ (2 * n + 1)

def zeroValue (n : ℕ) : ℝ :=
  (n : ℝ) * oddDoubleFactorial (n - 1) / 2 ^ (n - 1)

private theorem hasDerivAt_sqrt_one_sub (x : ℝ) (hx : x < 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y))
      (-(Real.sqrt (1 - x))⁻¹ / 2) x := by
  have hne : 1 - x ≠ 0 := by linarith
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  convert (Real.hasDerivAt_sqrt hne).comp x hinner using 1 <;> ring

private theorem hasDerivAt_inv_sqrt_pow (k : ℕ) (x : ℝ) (hx : x < 1) :
    HasDerivAt
      (fun y : ℝ => 1 / Real.sqrt (1 - y) ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) / 2 /
        Real.sqrt (1 - x) ^ (k + 3)) x := by
  have hsne : Real.sqrt (1 - x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sub_pos.2 hx))
  have hs := hasDerivAt_sqrt_one_sub x hx
  have hi :
      HasDerivAt
        (fun y : ℝ => (Real.sqrt (1 - y))⁻¹)
        (1 / 2 / Real.sqrt (1 - x) ^ 3) x := by
    convert hs.inv hsne using 1 <;>
      field_simp [hsne] <;> ring
  have hp := hi.pow (k + 1)
  convert hp using 1
  · funext y
    simp [one_div, inv_pow]
  · rw [pow_add]
    simp only [one_div, inv_pow]
    field_simp [hsne]
    ring_nf
    have hk : 1 + k - 1 = k := by omega
    rw [hk]

private theorem hasDerivAt_nthFormula
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x < 1) :
    HasDerivAt (nthFormula n) (nthFormula (n + 1) x) x := by
  rcases n with _ | n
  · omega
  have hp₁ : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hp₂ : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  have hq₁ : 2 * (n + 1 + 1) - 1 = 2 * n + 3 := by omega
  have hq₂ : 2 * (n + 1 + 1) + 1 = 2 * n + 5 := by omega
  have hsub : n + 1 + 1 - 1 = n + 1 := by omega
  have h₁ := hasDerivAt_inv_sqrt_pow (2 * n) x hx
  have h₂ := hasDerivAt_inv_sqrt_pow (2 * n + 2) x hx
  have hder :=
    ((hasDerivAt_const x
        ((oddDoubleFactorial n : ℝ) / 2 ^ (n + 1))).mul h₁).add
      ((hasDerivAt_const x
        ((oddDoubleFactorial (n + 1) : ℝ) / 2 ^ (n + 1))).mul h₂)
  convert hder using 1
  · funext y
    simp [nthFormula, hp₁, hp₂, div_eq_mul_inv]
  · simp [nthFormula, oddDoubleFactorial, hp₂, hq₁, hq₂, hsub,
      div_eq_mul_inv]
    field_simp [pow_succ]
    ring

theorem gap1 (x : ℝ) (hx : x < 1) :
    f x = -Real.sqrt (1 - x) + 1 / Real.sqrt (1 - x) := by
  have hs : Real.sqrt (1 - x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sub_pos.2 hx))
  have hs_sq : Real.sqrt (1 - x) ^ 2 = 1 - x :=
    Real.sq_sqrt (sub_nonneg.2 (le_of_lt hx))
  unfold f
  field_simp
  nlinarith

theorem gap2 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : x < 1) :
    iterDeriv n f x = nthFormula n x := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hs := hasDerivAt_sqrt_one_sub x hx
        have hi := hasDerivAt_inv_sqrt_pow 0 x hx
        have hder :
            HasDerivAt
              (fun y : ℝ =>
                -Real.sqrt (1 - y) + 1 / Real.sqrt (1 - y))
              (nthFormula 1 x) x := by
          convert hs.neg.add hi using 1
          · funext y
            simp [one_div]
          · simp [nthFormula, oddDoubleFactorial, one_div]
            ring
        have heq :
            f =ᶠ[nhds x]
              (fun y : ℝ =>
                -Real.sqrt (1 - y) + 1 / Real.sqrt (1 - y)) := by
          filter_upwards [Iio_mem_nhds hx] with y hy
          exact gap1 y hy
        have hf : HasDerivAt f (nthFormula 1 x) x :=
          hder.congr_of_eventuallyEq heq
        calc
          iterDeriv 1 f x = deriv f x := by simp [iterDeriv]
          _ = nthFormula 1 x := hf.deriv
      · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
        have heq : iterDeriv n f =ᶠ[nhds x] nthFormula n := by
          filter_upwards [Iio_mem_nhds hx] with y hy
          exact ih y hn' hy
        have hd :
            HasDerivAt (iterDeriv n f) (nthFormula (n + 1) x) x :=
          (hasDerivAt_nthFormula n hn' x hx).congr_of_eventuallyEq heq
        simpa [iterDeriv, Function.iterate_succ_apply'] using hd.deriv

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    iterDeriv n f 0 =
      (oddDoubleFactorial (n - 1) : ℝ) / 2 ^ n +
        oddDoubleFactorial n / 2 ^ n := by
  simpa [nthFormula] using gap2 n 0 hn (by norm_num : (0 : ℝ) < 1)

theorem gap4 (n : ℕ) (hn : 1 ≤ n) :
    (oddDoubleFactorial (n - 1) : ℝ) / 2 ^ n +
        oddDoubleFactorial n / 2 ^ n =
      zeroValue n := by
  rcases n with _ | n
  · omega
  · simp [oddDoubleFactorial, zeroValue, pow_succ] <;> ring

theorem gap5 (n : ℕ) (hn : 1 ≤ n) :
    iterDeriv n f 0 = zeroValue n := by
  exact (gap3 n hn).trans (gap4 n hn)

end

end ProofGap.Exercise1219_2
