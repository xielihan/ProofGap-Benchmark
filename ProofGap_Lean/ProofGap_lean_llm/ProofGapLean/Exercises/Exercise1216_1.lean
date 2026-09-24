import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import ProofGapLean.Exercises.Exercise1216_3
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1216_1

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def t (x : ℝ) : ℂ := (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)
def f (p : ℕ) (x : ℝ) : ℝ := Real.sin x ^ (2 * p + 1)

def complexBinomial (p : ℕ) (x : ℝ) : ℂ :=
  1 / (2 * Complex.I) ^ (2 * p + 1) *
    ∑ k ∈ Finset.range (2 * p + 2),
      (Nat.choose (2 * p + 1) k : ℂ) * t x ^ (2 * p + 1 - k) *
        (-1 : ℂ) ^ k * star (t x) ^ k

def sineExpansion (p : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1),
    ((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p + 1) k : ℝ) /
        2 ^ (2 * p)) * Real.sin ((2 * p + 1 - 2 * k : ℕ) * x)

def derivativeExpansion (p n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1),
    ((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p + 1) k : ℝ) /
        2 ^ (2 * p)) *
      (2 * p + 1 - 2 * k : ℝ) ^ n *
      Real.sin ((2 * p + 1 - 2 * k : ℕ) * x + (n : ℝ) / 2 * Real.pi)

private theorem star_t (x : ℝ) : star (t x) = t (-x) := by
  apply Complex.ext <;>
    simp [t, Real.cos_neg, Real.sin_neg]

private theorem cos_odd_pi_div_two_sub (q : ℕ) (z : ℝ) :
    Real.cos (((2 * q + 1 : ℕ) : ℝ) * (Real.pi / 2) - z) =
      (-1 : ℝ) ^ q * Real.sin z := by
  induction q with
  | zero =>
      norm_num
      exact Real.cos_pi_div_two_sub z
  | succ q ih =>
      have harg :
          (((2 * (q + 1) + 1 : ℕ) : ℝ) * (Real.pi / 2) - z) =
            (((2 * q + 1 : ℕ) : ℝ) * (Real.pi / 2) - z) + Real.pi := by
        push_cast
        ring
      rw [harg, Real.cos_add_pi, ih, pow_succ]
      ring

private theorem sine_mode_from_shift (p k : ℕ) (x : ℝ)
    (hk : k < p + 1) :
    Real.cos (((2 * p + 1 - 2 * k : ℕ) : ℝ) *
        (Real.pi / 2 - x)) =
      (-1 : ℝ) ^ (p + k) *
        Real.sin (((2 * p + 1 - 2 * k : ℕ) : ℝ) * x) := by
  have hkp : k ≤ p := by omega
  have hfreq : 2 * p + 1 - 2 * k = 2 * (p - k) + 1 := by
    omega
  have hsign : (-1 : ℝ) ^ (p - k) = (-1 : ℝ) ^ (p + k) := by
    rw [show p + k = (p - k) + 2 * k by omega, pow_add, pow_mul]
    norm_num
  rw [hfreq]
  have hdistrib :
      (((2 * (p - k) + 1 : ℕ) : ℝ) * (Real.pi / 2 - x)) =
      ((2 * (p - k) + 1 : ℕ) : ℝ) * (Real.pi / 2) -
        ((2 * (p - k) + 1 : ℕ) : ℝ) * x := by
    ring
  rw [hdistrib]
  rw [cos_odd_pi_div_two_sub, hsign]

private theorem hasDerivAt_sinMode (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        a ^ n * Real.sin (a * y + (n : ℝ) / 2 * Real.pi))
      (a ^ (n + 1) *
        Real.sin (a * x + ((n + 1 : ℕ) : ℝ) / 2 * Real.pi)) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * y + (n : ℝ) / 2 * Real.pi) a x := by
    convert ((hasDerivAt_id x).const_mul a).add_const
      ((n : ℝ) / 2 * Real.pi) using 1 <;> ring
  have h := hinner.sin.const_mul (a ^ n)
  convert h using 1
  rw [show a * x + ((n + 1 : ℕ) : ℝ) / 2 * Real.pi =
      (a * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 by
        norm_num [Nat.cast_add]
        ring]
  rw [Real.sin_add_pi_div_two]
  ring

private theorem deriv_derivativeExpansion (p n : ℕ) (x : ℝ) :
    deriv (derivativeExpansion p n) x =
      derivativeExpansion p (n + 1) x := by
  unfold derivativeExpansion
  have hs : ∀ k ∈ Finset.range (p + 1),
      HasDerivAt
        (fun y : ℝ =>
          ((-1 : ℝ) ^ (p + k) *
              (Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p + 1 - 2 * k : ℝ) ^ n *
            Real.sin (((2 * p + 1 - 2 * k : ℕ) : ℝ) * y +
              (n : ℝ) / 2 * Real.pi))
        (((-1 : ℝ) ^ (p + k) *
              (Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p + 1 - 2 * k : ℝ) ^ (n + 1) *
            Real.sin (((2 * p + 1 - 2 * k : ℕ) : ℝ) * x +
              ((n + 1 : ℕ) : ℝ) / 2 * Real.pi)) x := by
    intro k hk
    have hle : 2 * k ≤ 2 * p + 1 := by
      have hk' : k ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      omega
    have hcast :
        ((2 * p + 1 - 2 * k : ℕ) : ℝ) =
          (2 * p + 1 - 2 * k : ℝ) := by
      rw [Nat.cast_sub hle]
      norm_num
    simpa [hcast, mul_assoc] using
      (hasDerivAt_sinMode (2 * p + 1 - 2 * k : ℝ) n x).const_mul
        ((-1 : ℝ) ^ (p + k) *
          (Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p))
  have h := HasDerivAt.sum hs
  have hfun :
      (fun y : ℝ =>
        ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ (p + k) *
              (Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p + 1 - 2 * k : ℝ) ^ n *
            Real.sin (((2 * p + 1 - 2 * k : ℕ) : ℝ) * y +
              (n : ℝ) / 2 * Real.pi)) =
        ∑ k ∈ Finset.range (p + 1), fun y : ℝ =>
          ((-1 : ℝ) ^ (p + k) *
              (Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p + 1 - 2 * k : ℝ) ^ n *
            Real.sin (((2 * p + 1 - 2 * k : ℕ) : ℝ) * y +
              (n : ℝ) / 2 * Real.pi) := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun]
  exact h.deriv

theorem gap1 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    (Real.sin x : ℂ) = 1 / (2 * Complex.I) * (t x - star (t x)) := by
  have hI : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  have hdiff :
      t x - star (t x) = 2 * Complex.I * (Real.sin x : ℂ) := by
    rw [star_t]
    apply Complex.ext <;>
      simp [t, Real.cos_neg, Real.sin_neg] <;>
      ring
  rw [hdiff]
  field_simp [hI]

theorem gap2 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    (Real.sin x : ℂ) ^ (2 * p + 1) = complexBinomial p x := by
  calc
    (Real.sin x : ℂ) ^ (2 * p + 1) =
        (1 / (2 * Complex.I) * (t x - star (t x))) ^ (2 * p + 1) := by
      rw [gap1 p x hp]
    _ = 1 / (2 * Complex.I) ^ (2 * p + 1) *
        (t x - star (t x)) ^ (2 * p + 1) := by
      rw [mul_pow, one_div_pow]
    _ = complexBinomial p x := by
      unfold complexBinomial
      congr 1
      rw [sub_eq_add_neg, add_comm, add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      rw [neg_pow]
      ring

theorem gap3 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    complexBinomial p x =
      1 / (2 * Complex.I) ^ (2 * p + 1) *
        ∑ k ∈ Finset.range (2 * p + 2),
          (Nat.choose (2 * p + 1) k : ℂ) * (-1 : ℂ) ^ k *
            ((Real.cos ((((2 * p + 1 : ℕ) : ℝ) - 2 * (k : ℝ)) * x) : ℂ) +
              Complex.I *
                (Real.sin ((((2 * p + 1 : ℕ) : ℝ) - 2 * (k : ℝ)) * x) : ℂ)) := by
  have ht : ∀ y : ℝ,
      t y = Complex.exp ((y : ℂ) * Complex.I) := by
    intro y
    rw [Complex.exp_ofReal_mul_I]
    unfold t
    ring
  unfold complexBinomial
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ 2 * p + 1 := by
    have hk' := Finset.mem_range.mp hk
    omega
  have hphase :
      t x ^ (2 * p + 1 - k) * star (t x) ^ k =
        (Real.cos ((((2 * p + 1 : ℕ) : ℝ) - 2 * (k : ℝ)) * x) : ℂ) +
          Complex.I *
            (Real.sin ((((2 * p + 1 : ℕ) : ℝ) - 2 * (k : ℝ)) * x) : ℂ) := by
    rw [star_t, ht x, ht (-x), ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    have harg :
        ((2 * p + 1 - k : ℕ) : ℂ) * ((x : ℂ) * Complex.I) +
            (k : ℂ) * (((-x : ℝ) : ℂ) * Complex.I) =
          (((((2 * p + 1 : ℕ) : ℝ) - 2 * (k : ℝ)) * x : ℝ) : ℂ) *
            Complex.I := by
      rw [Nat.cast_sub hkN]
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I]
    ring
  calc
    (Nat.choose (2 * p + 1) k : ℂ) * t x ^ (2 * p + 1 - k) *
          (-1 : ℂ) ^ k * star (t x) ^ k =
        (Nat.choose (2 * p + 1) k : ℂ) * (-1 : ℂ) ^ k *
          (t x ^ (2 * p + 1 - k) * star (t x) ^ k) := by ring
    _ = _ := by rw [hphase]

theorem gap4 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    f p x = sineExpansion p x := by
  have hcos :=
    ProofGap.Exercise1216_3.gap2 p 0 (Real.pi / 2 - x) hp
  have hbase :
      Real.sin x ^ (2 * p + 1) =
        ∑ k ∈ Finset.range (p + 1),
          ((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            Real.cos (((2 * p + 1 - 2 * k : ℕ) : ℝ) *
              (Real.pi / 2 - x)) := by
    simpa [ProofGap.Exercise1216_3.iterDeriv,
      ProofGap.Exercise1216_3.f,
      ProofGap.Exercise1216_3.derivativeExpansion,
      Real.cos_pi_div_two_sub] using hcos
  unfold f sineExpansion
  rw [hbase]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sine_mode_from_shift p k x (Finset.mem_range.mp hk)]
  ring

theorem gap5 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    iterDeriv n (f p) x = derivativeExpansion p n x := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv, derivativeExpansion, sineExpansion] using
        gap4 p x hp
  | succ n ih =>
      change (deriv^[n + 1]) (f p) x = derivativeExpansion p (n + 1) x
      rw [Function.iterate_succ_apply']
      have hfun : (deriv^[n]) (f p) = derivativeExpansion p n := by
        funext y
        simpa [iterDeriv] using ih y
      rw [hfun]
      exact deriv_derivativeExpansion p n x

end

end ProofGap.Exercise1216_1
