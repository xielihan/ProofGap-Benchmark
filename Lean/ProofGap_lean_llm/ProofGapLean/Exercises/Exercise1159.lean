import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1159

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x ^ 2 / (1 - x)

private theorem hasDerivAt_const_div_one_sub_pow
    (c : ℝ) (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt (fun z : ℝ => c / (1 - z) ^ (n + 1))
      (c * (n + 1) / (1 - x) ^ (n + 2)) x := by
  have hne : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hden : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    simpa [id] using
      (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hpow : HasDerivAt (fun z : ℝ => (1 - z) ^ (n + 1))
      (-(n + 1) * (1 - x) ^ n) x := by
    convert hden.pow (n + 1) using 1 <;>
      simp [Nat.cast_add, Nat.cast_one] <;> ring
  convert (hasDerivAt_const x c).div hpow
      (pow_ne_zero (n + 1) hne) using 1
  field_simp [hne, pow_add] <;> ring

theorem gap1 (x : ℝ) (hx : x ≠ 1) :
    y x = (x ^ 2 - 1 + 1) / (1 - x) := by
  unfold y
  ring

theorem gap2 (x : ℝ) (hx : x ≠ 1) :
    (x ^ 2 - 1 + 1) / (1 - x) = -(x + 1) + 1 / (1 - x) := by
  have hne : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp [hne]
  ring

theorem gap3 (x : ℝ) (hx : x ≠ 1) :
    y x = -(x + 1) + 1 / (1 - x) := by
  calc
    y x = (x ^ 2 - 1 + 1) / (1 - x) := gap1 x hx
    _ = -(x + 1) + 1 / (1 - x) := gap2 x hx

theorem gap4 (x : ℝ) (hx : x ≠ 1) :
    deriv y x = -1 + 1 / (1 - x) ^ 2 := by
  have hne : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hnum : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 2
  have hden : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    simpa [id] using
      (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hy : HasDerivAt y
      ((2 * x * (1 - x) - x ^ 2 * (-1)) / (1 - x) ^ 2) x := by
    simpa [y] using hnum.div hden hne
  calc
    deriv y x = (2 * x * (1 - x) - x ^ 2 * (-1)) / (1 - x) ^ 2 := hy.deriv
    _ = -1 + 1 / (1 - x) ^ 2 := by
      field_simp [hne]
      ring

theorem gap5 (x : ℝ) (hx : x ≠ 1) :
    nthDeriv 2 y x = 2 / (1 - x) ^ 3 := by
  have heq : deriv y =ᶠ[nhds x]
      (fun z : ℝ => -1 + 1 / (1 - z) ^ 2) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    exact gap4 z hz
  have hf : HasDerivAt (fun z : ℝ => -1 + 1 / (1 - z) ^ 2)
      (2 / (1 - x) ^ 3) x := by
    convert (hasDerivAt_const x (-1 : ℝ)).add
      (hasDerivAt_const_div_one_sub_pow 1 1 x hx) using 1 <;> norm_num
  change deriv (deriv y) x = 2 / (1 - x) ^ 3
  calc
    deriv (deriv y) x = deriv (fun z : ℝ => -1 + 1 / (1 - z) ^ 2) x :=
      heq.deriv_eq
    _ = 2 / (1 - x) ^ 3 := hf.deriv

theorem gap6 (x : ℝ) (hx : x ≠ 1) :
    nthDeriv 3 y x = (2 * 3) / (1 - x) ^ 4 := by
  have heq : nthDeriv 2 y =ᶠ[nhds x]
      (fun z : ℝ => 2 / (1 - z) ^ 3) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    exact gap5 z hz
  change deriv (nthDeriv 2 y) x = (2 * 3) / (1 - x) ^ 4
  calc
    deriv (nthDeriv 2 y) x = deriv (fun z : ℝ => 2 / (1 - z) ^ 3) x :=
      heq.deriv_eq
    _ = (2 * 3) / (1 - x) ^ 4 := by
      have h := (hasDerivAt_const_div_one_sub_pow 2 2 x hx).deriv
      norm_num at h ⊢
      exact h

theorem gap7 (x : ℝ) (hx : x ≠ 1) :
    nthDeriv 8 y x =
      ((Nat.factorial 8 : ℕ) : ℝ) / (1 - x) ^ 9 := by
  have step (n : ℕ)
      (hn : ∀ z : ℝ, z ≠ 1 →
        nthDeriv n y z =
          ((Nat.factorial n : ℕ) : ℝ) / (1 - z) ^ (n + 1)) :
      ∀ z : ℝ, z ≠ 1 →
        nthDeriv (n + 1) y z =
          ((Nat.factorial (n + 1) : ℕ) : ℝ) / (1 - z) ^ (n + 1 + 1) := by
    intro z hz
    have heq : nthDeriv n y =ᶠ[nhds z]
        (fun w : ℝ =>
          ((Nat.factorial n : ℕ) : ℝ) / (1 - w) ^ (n + 1)) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact hn w hw
    change deriv (nthDeriv n y) z =
      ((Nat.factorial (n + 1) : ℕ) : ℝ) / (1 - z) ^ (n + 1 + 1)
    calc
      deriv (nthDeriv n y) z =
          deriv (fun w : ℝ =>
            ((Nat.factorial n : ℕ) : ℝ) / (1 - w) ^ (n + 1)) z :=
        heq.deriv_eq
      _ = ((Nat.factorial n : ℕ) : ℝ) * (n + 1) /
          (1 - z) ^ (n + 2) :=
        (hasDerivAt_const_div_one_sub_pow
          ((Nat.factorial n : ℕ) : ℝ) n z hz).deriv
      _ = ((Nat.factorial (n + 1) : ℕ) : ℝ) /
          (1 - z) ^ (n + 1 + 1) := by
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
  have h2 : ∀ z : ℝ, z ≠ 1 →
      nthDeriv 2 y z =
        ((Nat.factorial 2 : ℕ) : ℝ) / (1 - z) ^ (2 + 1) := by
    intro z hz
    norm_num
    exact gap5 z hz
  have h3 := step 2 h2
  have h4 := step 3 h3
  have h5 := step 4 h4
  have h6 := step 5 h5
  have h7 := step 6 h6
  have h8 := step 7 h7
  simpa using h8 x hx

end

end ProofGap.Exercise1159
