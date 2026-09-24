import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1219_1

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (x : ℝ) : ℝ := 1 / ((1 - 2 * x) * (1 + x))

def nthFormula (n : ℕ) (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) *
    (((-1 : ℝ) ^ n * (Nat.factorial n : ℝ)) / (1 + x) ^ (n + 1) +
      (2 : ℝ) ^ (n + 1) * (Nat.factorial n : ℝ) / (1 - 2 * x) ^ (n + 1))

private theorem nthFormula_hasDerivAt
    (n : ℕ) (x : ℝ) (hp : 1 + x ≠ 0) (hm : 1 - 2 * x ≠ 0) :
    HasDerivAt (nthFormula n) (nthFormula (n + 1) x) x := by
  have hpbase : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using
      (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hmbase : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
    simpa using
      (hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x))
  have hfirst :
      HasDerivAt
        (fun y : ℝ =>
          (((-1 : ℝ) ^ n) * (Nat.factorial n : ℝ)) /
            (1 + y) ^ (n + 1))
        (((-1 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 1) : ℝ) /
          (1 + x) ^ (n + 2)) x := by
    convert
      (hasDerivAt_const x
        (((-1 : ℝ) ^ n) * (Nat.factorial n : ℝ))).div
        (hpbase.pow (n + 1)) (pow_ne_zero (n + 1) hp)
      using 1
    simp only [zero_mul, zero_sub, mul_one, Nat.add_sub_cancel]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hp]
    simp [pow_succ, pow_mul] <;> ring
  have hsecond :
      HasDerivAt
        (fun y : ℝ =>
          ((2 : ℝ) ^ (n + 1) * (Nat.factorial n : ℝ)) /
            (1 - 2 * y) ^ (n + 1))
        ((2 : ℝ) ^ (n + 2) * (Nat.factorial (n + 1) : ℝ) /
          (1 - 2 * x) ^ (n + 2)) x := by
    convert
      (hasDerivAt_const x
        (((2 : ℝ) ^ (n + 1)) * (Nat.factorial n : ℝ))).div
        (hmbase.pow (n + 1)) (pow_ne_zero (n + 1) hm)
      using 1
    simp only [zero_mul, zero_sub, Nat.add_sub_cancel]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hm]
    simp [pow_succ, pow_mul] <;> ring
  change
    HasDerivAt (fun y : ℝ => nthFormula n y) (nthFormula (n + 1) x) x
  simpa [nthFormula, Nat.add_assoc] using
    (hasDerivAt_const x (1 / 3 : ℝ)).mul (hfirst.add hsecond)

theorem gap1 (x : ℝ) (hp : 1 + x ≠ 0) (hm : 1 - 2 * x ≠ 0) :
    f x = (1 / 3 : ℝ) * (1 / (1 + x) + 2 / (1 - 2 * x)) := by
  unfold f
  field_simp [hp, hm] <;> ring

theorem gap2 (n : ℕ) (x : ℝ) (hp : 1 + x ≠ 0) (hm : 1 - 2 * x ≠ 0) :
    iterDeriv n f x = nthFormula n x := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv, nthFormula] using gap1 x hp hm
  | succ n ih =>
      have hp_eventually : ∀ᶠ y : ℝ in nhds x, 1 + y ≠ 0 :=
        (show ContinuousAt (fun y : ℝ => 1 + y) x from
          continuousAt_const.add continuousAt_id).eventually_ne hp
      have hm_eventually : ∀ᶠ y : ℝ in nhds x, 1 - 2 * y ≠ 0 :=
        (show ContinuousAt (fun y : ℝ => 1 - 2 * y) x from
          continuousAt_const.sub
            ((continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ)) x).mul
              continuousAt_id)).eventually_ne hm
      have hev : iterDeriv n f =ᶠ[nhds x] nthFormula n :=
        (hp_eventually.and hm_eventually).mono (by
          intro y hy
          exact ih y hy.1 hy.2)
      calc
        iterDeriv (Nat.succ n) f x = deriv (iterDeriv n f) x := by
          simp [iterDeriv, Function.iterate_succ_apply']
        _ = deriv (nthFormula n) x := hev.deriv_eq
        _ = nthFormula (Nat.succ n) x := by
          simpa [Nat.succ_eq_add_one] using
            (nthFormula_hasDerivAt n x hp hm).deriv

theorem gap3 (n : ℕ) :
    iterDeriv n f 0 =
      (Nat.factorial n : ℝ) / 3 * ((-1 : ℝ) ^ n + 2 ^ (n + 1)) := by
  rw [gap2 n 0 (by norm_num) (by norm_num)]
  simp [nthFormula] <;> ring

end

end ProofGap.Exercise1219_1
