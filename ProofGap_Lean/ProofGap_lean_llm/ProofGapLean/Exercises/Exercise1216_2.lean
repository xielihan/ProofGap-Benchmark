import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1216_2

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (p : ℕ) (x : ℝ) : ℝ := Real.cos x ^ (2 * p)

def derivativeExpansion (p n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range p,
    (2 * (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
      (2 * p - 2 * k : ℝ) ^ n *
      Real.cos ((2 * p - 2 * k : ℕ) * x + (n : ℝ) / 2 * Real.pi)

private theorem cos_even_pow_full_sum (p : ℕ) (x : ℝ) :
    (2 : ℝ) ^ (2 * p) * Real.cos x ^ (2 * p) =
      ∑ k ∈ Finset.range (2 * p + 1),
        (Nat.choose (2 * p) k : ℝ) *
          Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x)) := by
  let z : ℂ := (x : ℂ) * Complex.I
  have heuler : Complex.exp (-z) + Complex.exp z =
      ((2 * Real.cos x : ℝ) : ℂ) := by
    dsimp [z]
    rw [show -((x : ℂ) * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  have hterm (k : ℕ) (hk : k ≤ 2 * p) :
      ((Complex.exp (-z) ^ k * Complex.exp z ^ (2 * p - k) *
          (Nat.choose (2 * p) k : ℂ)).re) =
        (Nat.choose (2 * p) k : ℝ) *
          Real.cos ((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x) := by
    have hexp : Complex.exp (-z) ^ k * Complex.exp z ^ (2 * p - k) =
        Complex.exp ((((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x : ℝ) : ℂ) *
          Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      dsimp [z]
      rw [Nat.cast_sub hk]
      push_cast
      ring
    rw [hexp]
    rw [Complex.mul_re]
    norm_num
    rw [Complex.exp_re]
    simp
    ring
  have hbin : (((2 * Real.cos x : ℝ) : ℂ) ^ (2 * p)) =
      ∑ k ∈ Finset.range (2 * p + 1),
        Complex.exp (-z) ^ k * Complex.exp z ^ (2 * p - k) *
          (Nat.choose (2 * p) k : ℂ) := by
    rw [← heuler]
    exact add_pow (Complex.exp (-z)) (Complex.exp z) (2 * p)
  have hrealpow : ((((2 * Real.cos x : ℝ) : ℂ) ^ (2 * p)).re) =
      (2 * Real.cos x) ^ (2 * p) := by
    norm_cast
  calc
    (2 : ℝ) ^ (2 * p) * Real.cos x ^ (2 * p) =
        (2 * Real.cos x) ^ (2 * p) := by rw [mul_pow]
    _ = ((((2 * Real.cos x : ℝ) : ℂ) ^ (2 * p)).re) := hrealpow.symm
    _ = (∑ k ∈ Finset.range (2 * p + 1),
        Complex.exp (-z) ^ k * Complex.exp z ^ (2 * p - k) *
          (Nat.choose (2 * p) k : ℂ)).re := congrArg Complex.re hbin
    _ = ∑ k ∈ Finset.range (2 * p + 1),
        ((Complex.exp (-z) ^ k * Complex.exp z ^ (2 * p - k) *
          (Nat.choose (2 * p) k : ℂ)).re) := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

private theorem cos_even_pow_half_sum (p : ℕ) (x : ℝ) :
    (2 : ℝ) ^ (2 * p) * Real.cos x ^ (2 * p) =
      (Nat.choose (2 * p) p : ℝ) +
        2 * ∑ k ∈ Finset.range p,
          (Nat.choose (2 * p) k : ℝ) *
            Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x)) := by
  classical
  let g : ℕ → ℝ := fun k =>
    (Nat.choose (2 * p) k : ℝ) *
      Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x))
  have hsym (k : ℕ) (hk : k ≤ 2 * p) : g (2 * p - k) = g k := by
    have hangle :
        (((2 * p : ℕ) : ℝ) - 2 * ((2 * p - k : ℕ) : ℝ)) * x =
          -((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x) := by
      rw [Nat.cast_sub hk]
      push_cast
      ring
    dsimp [g]
    rw [Nat.choose_symm hk, hangle, Real.cos_neg]
  have hreflect :
      (∑ j ∈ Finset.Ico 0 p, g (2 * p - j)) =
        ∑ j ∈ Finset.Ico (p + 1) (2 * p + 1), g j := by
    have hb : p + p + 1 - p = p + 1 := by omega
    simpa [two_mul, hb] using
      (Finset.sum_Ico_reflect g 0 (m := p) (n := 2 * p) (by omega))
  have hupper :
      (∑ j ∈ Finset.Ico (p + 1) (2 * p + 1), g j) =
        ∑ j ∈ Finset.range p, g j := by
    calc
      (∑ j ∈ Finset.Ico (p + 1) (2 * p + 1), g j) =
          ∑ j ∈ Finset.Ico 0 p, g (2 * p - j) := hreflect.symm
      _ = ∑ j ∈ Finset.range p, g j := by
        rw [Nat.Ico_zero_eq_range]
        apply Finset.sum_congr rfl
        intro j hj
        exact hsym j (by
          have hj' := Finset.mem_range.mp hj
          omega)
  change (2 : ℝ) ^ (2 * p) * Real.cos x ^ (2 * p) =
    (Nat.choose (2 * p) p : ℝ) + 2 * ∑ k ∈ Finset.range p, g k
  calc
    (2 : ℝ) ^ (2 * p) * Real.cos x ^ (2 * p) =
        ∑ k ∈ Finset.range (2 * p + 1), g k := cos_even_pow_full_sum p x
    _ = (∑ k ∈ Finset.range (p + 1), g k) +
        ∑ k ∈ Finset.Ico (p + 1) (2 * p + 1), g k :=
      (Finset.sum_range_add_sum_Ico g (by omega)).symm
    _ = ((∑ k ∈ Finset.range p, g k) + g p) +
        ∑ k ∈ Finset.range p, g k := by rw [Finset.sum_range_succ, hupper]
    _ = (Nat.choose (2 * p) p : ℝ) +
        2 * ∑ k ∈ Finset.range p, g k := by
      dsimp [g]
      norm_num
      ring

private theorem cos_even_pow_expansion (p : ℕ) (x : ℝ) :
    Real.cos x ^ (2 * p) =
      (Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p) +
        ∑ k ∈ Finset.range p,
          (2 * (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
            Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x)) := by
  have h := cos_even_pow_half_sum p x
  have htwo : (2 : ℝ) ^ (2 * p) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    Real.cos x ^ (2 * p) =
        ((Nat.choose (2 * p) p : ℝ) +
          2 * ∑ k ∈ Finset.range p,
            (Nat.choose (2 * p) k : ℝ) *
              Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x))) /
            2 ^ (2 * p) := by
      apply (eq_div_iff htwo).2
      nlinarith [h]
    _ = (Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p) +
        (2 * ∑ k ∈ Finset.range p,
          (Nat.choose (2 * p) k : ℝ) *
            Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * x))) /
          2 ^ (2 * p) := by rw [add_div]
    _ = _ := by
      congr 1
      rw [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

private theorem iteratedDeriv_cos_phase (n : ℕ) (y : ℝ) :
    iteratedDeriv n Real.cos y =
      Real.cos (y + (n : ℝ) / 2 * Real.pi) := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' n
  · subst n
    calc
      iteratedDeriv (2 * q) Real.cos y =
          (-1 : ℝ) ^ q * Real.cos y :=
        congrFun (Real.iteratedDeriv_even_cos q) y
      _ = Real.cos (y + (q : ℝ) * Real.pi) :=
        (Real.cos_add_nat_mul_pi y q).symm
      _ = Real.cos (y + ((2 * q : ℕ) : ℝ) / 2 * Real.pi) := by
        congr 1
        push_cast
        ring
  · subst n
    calc
      iteratedDeriv (2 * q + 1) Real.cos y =
          (-1 : ℝ) ^ (q + 1) * Real.sin y :=
        congrFun (Real.iteratedDeriv_odd_cos q) y
      _ = (-1 : ℝ) ^ q * (-Real.sin y) := by
        rw [pow_succ]
        ring
      _ = (-1 : ℝ) ^ q * Real.cos (y + Real.pi / 2) := by
        rw [Real.cos_add_pi_div_two]
      _ = Real.cos ((y + Real.pi / 2) + (q : ℝ) * Real.pi) :=
        (Real.cos_add_nat_mul_pi (y + Real.pi / 2) q).symm
      _ = Real.cos (y + ((2 * q + 1 : ℕ) : ℝ) / 2 * Real.pi) := by
        congr 1
        push_cast
        ring

private theorem iteratedDeriv_cos_mul_phase (n : ℕ) (a x : ℝ) :
    iteratedDeriv n (fun t : ℝ => Real.cos (a * t)) x =
      a ^ n * Real.cos (a * x + (n : ℝ) / 2 * Real.pi) := by
  rw [congrFun (iteratedDeriv_comp_const_mul (n := n)
    (Real.contDiff_cos : ContDiff ℝ n Real.cos) a) x]
  rw [iteratedDeriv_cos_phase]

theorem gap1 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    iterDeriv n (f p) x =
      iterDeriv n (fun t : ℝ => Real.cos t ^ (2 * p)) x := by
  rfl

theorem gap2 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    iterDeriv n (fun t : ℝ => Real.cos t ^ (2 * p)) x =
      derivativeExpansion p n x := by
  classical
  unfold iterDeriv derivativeExpansion
  rw [← iteratedDeriv_eq_iterate]
  have hfun :
      (fun t : ℝ => Real.cos t ^ (2 * p)) =
        fun t : ℝ =>
          (Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p) +
            ∑ k ∈ Finset.range p,
              (2 * (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
                Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * t)) := by
    funext t
    exact cos_even_pow_expansion p t
  rw [hfun]
  rw [iteratedDeriv_const_add (by omega)
    ((Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p))]
  have hsumfun :
      (fun t : ℝ => ∑ k ∈ Finset.range p,
        (2 * (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
          Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * t))) =
        ∑ k ∈ Finset.range p, fun t : ℝ =>
          (2 * (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
            Real.cos (((((2 * p : ℕ) : ℝ) - 2 * (k : ℝ)) * t)) := by
    funext t
    simp
  rw [hsumfun]
  rw [iteratedDeriv_sum (by
    intro k hk
    fun_prop)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_cos_mul_phase]
  have hle : 2 * k ≤ 2 * p := by
    have hkp := Finset.mem_range.mp hk
    omega
  have hcast : (((2 * p - 2 * k : ℕ) : ℝ)) =
      ((2 * p : ℕ) : ℝ) - 2 * (k : ℝ) := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hcast]
  push_cast
  ring

theorem gap3 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    iterDeriv n (f p) x = derivativeExpansion p n x := by
  calc
    iterDeriv n (f p) x =
        iterDeriv n (fun t : ℝ => Real.cos t ^ (2 * p)) x := gap1 p n x hp
    _ = derivativeExpansion p n x := gap2 p n x hp hn

end

end ProofGap.Exercise1216_2
