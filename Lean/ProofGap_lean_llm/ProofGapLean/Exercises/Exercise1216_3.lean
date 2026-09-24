import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1216_3

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (p : ℕ) (x : ℝ) : ℝ := Real.cos x ^ (2 * p + 1)

def derivativeExpansion (p n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1),
    ((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
      (2 * p + 1 - 2 * k : ℝ) ^ n *
      Real.cos ((2 * p + 1 - 2 * k : ℕ) * x + (n : ℝ) / 2 * Real.pi)

private theorem sum_range_reflect {α : Type*} [AddCommMonoid α]
    (g : ℕ → α) (p : ℕ) :
    (∑ k ∈ Finset.range (p + 1), g (p - k)) =
      ∑ k ∈ Finset.range (p + 1), g k := by
  classical
  refine Finset.sum_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro a ha b hb hab
    change p - a = p - b at hab
    simp only [Finset.mem_range] at ha hb
    omega
  · intro b hb
    refine ⟨p - b, ?_, ?_⟩
    · simp only [Finset.mem_range] at hb ⊢
      omega
    · change p - (p - b) = b
      simp only [Finset.mem_range] at hb
      omega
  · intro k hk
    rfl

private theorem cos_pow_odd_expansion (p : ℕ) (x : ℝ) :
    Real.cos x ^ (2 * p + 1) =
      ∑ k ∈ Finset.range (p + 1),
        ((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
          Real.cos ((2 * p + 1 - 2 * k : ℕ) * x) := by
  classical
  let N : ℕ := 2 * p + 1
  let u : ℂ := (x : ℂ) * Complex.I
  let A : ℕ → ℂ := fun k =>
    (Nat.choose N k : ℂ) * Complex.exp u ^ k *
      Complex.exp (-u) ^ (N - k)
  let freq : ℕ → ℝ := fun k => ((N : ℝ) - 2 * (k : ℝ)) * x
  have hEuler (y : ℝ) :
      Complex.exp ((y : ℂ) * Complex.I) +
          Complex.exp (-((y : ℂ) * Complex.I)) =
        2 * (Real.cos y : ℂ) := by
    rw [Complex.exp_mul_I]
    rw [show -((y : ℂ) * Complex.I) = ((-y : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [Complex.exp_mul_I]
    simp
    ring
  have hAneg (k : ℕ) (hk : k ≤ p) :
      A k = (Nat.choose N k : ℂ) *
        Complex.exp (-((freq k : ℂ) * Complex.I)) := by
    have hkN : k ≤ N := by
      dsimp [N]
      omega
    have hexp :
        (k : ℂ) * u + (N - k : ℕ) * (-u) =
          -((freq k : ℂ) * Complex.I) := by
      dsimp [u, freq]
      rw [Nat.cast_sub hkN]
      push_cast
      ring
    simp only [A]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    calc
      (Nat.choose N k : ℂ) * Complex.exp ((k : ℂ) * u) *
          Complex.exp ((N - k : ℕ) * (-u)) =
        (Nat.choose N k : ℂ) *
          (Complex.exp ((k : ℂ) * u) *
            Complex.exp ((N - k : ℕ) * (-u))) := by ring
      _ = (Nat.choose N k : ℂ) *
          Complex.exp ((k : ℂ) * u + (N - k : ℕ) * (-u)) := by
            rw [← Complex.exp_add]
      _ = (Nat.choose N k : ℂ) *
          Complex.exp (-((freq k : ℂ) * Complex.I)) := by rw [hexp]
  have hApos (k : ℕ) (hk : k ≤ p) :
      A (N - k) = (Nat.choose N k : ℂ) *
        Complex.exp ((freq k : ℂ) * Complex.I) := by
    have hkN : k ≤ N := by
      dsimp [N]
      omega
    have hsub : N - (N - k) = k := by
      omega
    have hexp :
        (N - k : ℕ) * u + (N - (N - k) : ℕ) * (-u) =
          (freq k : ℂ) * Complex.I := by
      dsimp [u, freq]
      rw [Nat.cast_sub hkN, hsub]
      push_cast
      ring
    simp only [A]
    rw [Nat.choose_symm hkN]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    calc
      (Nat.choose N k : ℂ) * Complex.exp ((N - k : ℕ) * u) *
          Complex.exp ((N - (N - k) : ℕ) * (-u)) =
        (Nat.choose N k : ℂ) *
          (Complex.exp ((N - k : ℕ) * u) *
            Complex.exp ((N - (N - k) : ℕ) * (-u))) := by ring
      _ = (Nat.choose N k : ℂ) *
          Complex.exp ((N - k : ℕ) * u +
            (N - (N - k) : ℕ) * (-u)) := by
            rw [← Complex.exp_add]
      _ = (Nat.choose N k : ℂ) *
          Complex.exp ((freq k : ℂ) * Complex.I) := by rw [hexp]
  have hpair (k : ℕ) (hk : k < p + 1) :
      A k + A (N - k) =
        2 * (Nat.choose N k : ℂ) * (Real.cos (freq k) : ℂ) := by
    have hkp : k ≤ p := by omega
    rw [hAneg k hkp, hApos k hkp]
    calc
      (Nat.choose N k : ℂ) *
            Complex.exp (-((freq k : ℂ) * Complex.I)) +
          (Nat.choose N k : ℂ) *
            Complex.exp ((freq k : ℂ) * Complex.I) =
        (Nat.choose N k : ℂ) *
          (Complex.exp ((freq k : ℂ) * Complex.I) +
            Complex.exp (-((freq k : ℂ) * Complex.I))) := by ring
      _ = (Nat.choose N k : ℂ) *
          (2 * (Real.cos (freq k) : ℂ)) := by rw [hEuler]
      _ = 2 * (Nat.choose N k : ℂ) *
          (Real.cos (freq k) : ℂ) := by ring
  have hsplit :
      (∑ k ∈ Finset.range (N + 1), A k) =
        ∑ k ∈ Finset.range (p + 1), (A k + A (N - k)) := by
    have hN : N + 1 = (p + 1) + (p + 1) := by
      dsimp [N]
      omega
    rw [hN, Finset.sum_range_add, Finset.sum_add_distrib]
    congr 1
    calc
      (∑ j ∈ Finset.range (p + 1), A (p + 1 + j)) =
          ∑ j ∈ Finset.range (p + 1), A (N - (p - j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            simp only [Finset.mem_range] at hj
            dsimp [N]
            omega
      _ = ∑ j ∈ Finset.range (p + 1), A (N - j) := by
            simpa using sum_range_reflect (fun j => A (N - j)) p
  have hcos :
      (Real.cos x : ℂ) =
        (Complex.exp u + Complex.exp (-u)) / 2 := by
    have h := hEuler x
    dsimp [u]
    rw [h]
    ring
  have hbinom :
      ((Complex.exp u + Complex.exp (-u)) / 2) ^ N =
        (1 / (2 : ℂ) ^ N) * ∑ k ∈ Finset.range (N + 1), A k := by
    rw [div_pow, add_pow]
    have hsum :
        (∑ k ∈ Finset.range (N + 1),
          Complex.exp u ^ k * Complex.exp (-u) ^ (N - k) *
            (Nat.choose N k : ℂ)) =
          ∑ k ∈ Finset.range (N + 1), A k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [A]
      ring
    rw [hsum]
    ring
  have hc :
      (Real.cos x : ℂ) ^ N =
        ∑ k ∈ Finset.range (p + 1),
          ((((Nat.choose N k : ℝ) / 2 ^ (2 * p)) *
            Real.cos ((N - 2 * k : ℕ) * x) : ℝ) : ℂ) := by
    rw [hcos, hbinom, hsplit, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hpair k (Finset.mem_range.mp hk)]
    have hle : 2 * k ≤ N := by
      dsimp [N]
      have hk' : k ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      omega
    have hfreq :
        freq k = ((N - 2 * k : ℕ) : ℝ) * x := by
      dsimp [freq]
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hfreq]
    dsimp [N]
    norm_num [pow_succ]
    ring
  have hc' :
      ((Real.cos x ^ N : ℝ) : ℂ) =
        ((∑ k ∈ Finset.range (p + 1),
          ((Nat.choose N k : ℝ) / 2 ^ (2 * p)) *
            Real.cos ((N - 2 * k : ℕ) * x) : ℝ) : ℂ) := by
    calc
      ((Real.cos x ^ N : ℝ) : ℂ) = (Real.cos x : ℂ) ^ N := by norm_cast
      _ = ∑ k ∈ Finset.range (p + 1),
          ((((Nat.choose N k : ℝ) / 2 ^ (2 * p)) *
            Real.cos ((N - 2 * k : ℕ) * x) : ℝ) : ℂ) := hc
      _ = ((∑ k ∈ Finset.range (p + 1),
          ((Nat.choose N k : ℝ) / 2 ^ (2 * p)) *
            Real.cos ((N - 2 * k : ℕ) * x) : ℝ) : ℂ) := by norm_cast
  have hreal := Complex.ofReal_injective hc'
  dsimp [N] at hreal
  simpa using hreal

private theorem hasDerivAt_cosMode (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => a ^ n * Real.cos (a * y + (n : ℝ) / 2 * Real.pi))
      (a ^ (n + 1) * Real.cos (a * x + ((n + 1 : ℕ) : ℝ) / 2 * Real.pi)) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * y + (n : ℝ) / 2 * Real.pi) a x := by
    convert ((hasDerivAt_id x).const_mul a).add_const ((n : ℝ) / 2 * Real.pi) using 1 <;> ring
  have h := hinner.cos.const_mul (a ^ n)
  convert h using 1
  rw [show a * x + ((n + 1 : ℕ) : ℝ) / 2 * Real.pi =
      (a * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 by
        norm_num [Nat.cast_add]
        ring]
  rw [Real.cos_add_pi_div_two]
  ring

private theorem deriv_derivativeExpansion (p n : ℕ) (x : ℝ) :
    deriv (derivativeExpansion p n) x = derivativeExpansion p (n + 1) x := by
  unfold derivativeExpansion
  have hs : ∀ k ∈ Finset.range (p + 1),
      HasDerivAt
        (fun y : ℝ =>
          ((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p + 1 - 2 * k : ℝ) ^ n *
            Real.cos ((2 * p + 1 - 2 * k : ℕ) * y +
              (n : ℝ) / 2 * Real.pi))
        (((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
          (2 * p + 1 - 2 * k : ℝ) ^ (n + 1) *
          Real.cos ((2 * p + 1 - 2 * k : ℕ) * x +
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
      (hasDerivAt_cosMode
        ((2 * p + 1 - 2 * k : ℕ) : ℝ) n x).const_mul
          ((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p))
  have h := HasDerivAt.sum hs
  have hfun :
      (fun y : ℝ =>
        ∑ k ∈ Finset.range (p + 1),
          ((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p + 1 - 2 * k : ℝ) ^ n *
            Real.cos ((2 * p + 1 - 2 * k : ℕ) * y +
              (n : ℝ) / 2 * Real.pi)) =
        ∑ k ∈ Finset.range (p + 1), fun y : ℝ =>
          ((Nat.choose (2 * p + 1) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p + 1 - 2 * k : ℝ) ^ n *
            Real.cos ((2 * p + 1 - 2 * k : ℕ) * y +
              (n : ℝ) / 2 * Real.pi) := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun]
  exact h.deriv

theorem gap1 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    iterDeriv n (f p) x =
      iterDeriv n (fun t : ℝ => Real.cos t ^ (2 * p + 1)) x := by
  rfl

theorem gap2 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    iterDeriv n (fun t : ℝ => Real.cos t ^ (2 * p + 1)) x =
      derivativeExpansion p n x := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv, derivativeExpansion] using cos_pow_odd_expansion p x
  | succ n ih =>
      change (deriv^[n + 1]) (fun t : ℝ => Real.cos t ^ (2 * p + 1)) x =
        derivativeExpansion p (n + 1) x
      rw [Function.iterate_succ_apply']
      have hfun :
          (deriv^[n]) (fun t : ℝ => Real.cos t ^ (2 * p + 1)) =
            derivativeExpansion p n := by
        funext y
        simpa [iterDeriv] using ih y
      rw [hfun]
      exact deriv_derivativeExpansion p n x

theorem gap3 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    iterDeriv n (f p) x = derivativeExpansion p n x := by
  rw [gap1 p n x hp]
  exact gap2 p n x hp

end

end ProofGap.Exercise1216_3
