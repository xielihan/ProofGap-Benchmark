import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise850

noncomputable section

def y (p q : ℕ) (x : ℝ) : ℝ :=
  x ^ p * (1 - x) ^ q / (1 + x)

/-- Source: `proof_gap/exercise_850/1.txt`; interpret the power parameters as
natural exponents and restore the source exercise's condition `x ≠ -1`. -/
private theorem hasDerivAt_nat_power
    {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    ∀ n : ℕ, HasDerivAt (fun z => (f z) ^ n)
      ((n : ℝ) * (f x) ^ (n - 1) * f') x := by
  intro n
  induction n with
  | zero =>
      simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ)))
  | succ n ih =>
      cases n with
      | zero => simpa using hf
      | succ n =>
          convert HasDerivAt.mul ih hf using 1 <;> simp [pow_succ] <;> ring

theorem gap1 (p q : ℕ) (x : ℝ) (hx : x ≠ -1) :
    HasDerivAt (y p q)
      ((((p : ℝ) * x ^ (p - 1) * (1 - x) ^ q -
          (q : ℝ) * x ^ p * (1 - x) ^ (q - 1)) * (1 + x) -
        x ^ p * (1 - x) ^ q) / (1 + x) ^ 2) x := by
  unfold y
  have hne : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  have hid : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const (x := x) (c := (1 : ℝ))
  have hbase : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    convert HasDerivAt.sub hone hid using 1 <;> ring
  have hnum :
      HasDerivAt (fun z : ℝ => z ^ p * (1 - z) ^ q)
        ((p : ℝ) * x ^ (p - 1) * (1 - x) ^ q -
          (q : ℝ) * x ^ p * (1 - x) ^ (q - 1)) x := by
    convert HasDerivAt.mul
      (hasDerivAt_nat_power hid p) (hasDerivAt_nat_power hbase q) using 1 <;>
      ring
  have hden : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
    convert HasDerivAt.add hone hid using 1 <;> ring
  convert HasDerivAt.div hnum hden hne using 1 <;> ring

/-- Source: `proof_gap/exercise_850/2.txt`; positivity of the natural
exponents is needed for the displayed common-factor extraction. -/
theorem gap2 (p q : ℕ) (x : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hx : x ≠ -1) :
    HasDerivAt (y p q)
      (x ^ (p - 1) * (1 - x) ^ (q - 1) / (1 + x) ^ 2 *
        ((p : ℝ) - ((q : ℝ) + 1) * x -
          ((p : ℝ) + (q : ℝ) - 1) * x ^ 2)) x := by
  have hxp : x ^ p = x ^ (p - 1) * x := by
    calc
      x ^ p = x ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp]
      _ = x ^ (p - 1) * x := by rw [pow_succ]
  have hxq : (1 - x) ^ q = (1 - x) ^ (q - 1) * (1 - x) := by
    calc
      (1 - x) ^ q = (1 - x) ^ (q - 1 + 1) := by
        rw [Nat.sub_add_cancel hq]
      _ = (1 - x) ^ (q - 1) * (1 - x) := by rw [pow_succ]
  convert gap1 p q x hx using 1
  rw [hxp, hxq]
  ring

end

end ProofGap.Exercise850
