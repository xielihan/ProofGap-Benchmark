import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1222_1

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def f (x : ℝ) : ℝ := Real.arctan x ^ 2

def fullLeibnizSum (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * k + 1),
    (Nat.choose (2 * k) i : ℝ) *
      iterDeriv i Real.arctan 0 * iterDeriv (2 * k - i) Real.arctan 0

def oddLeibnizSum (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    (Nat.choose (2 * k) (2 * i + 1) : ℝ) *
      iterDeriv (2 * i + 1) Real.arctan 0 *
      iterDeriv (2 * k - 2 * i - 1) Real.arctan 0

def factorialSum (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    (Nat.choose (2 * k) (2 * i + 1) : ℝ) *
      (-1 : ℝ) ^ i * (Nat.factorial (2 * i) : ℝ) *
      (-1 : ℝ) ^ (k - i - 1) * (Nat.factorial (2 * k - 2 * i - 2) : ℝ)

def reciprocalSum (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    1 / ((2 * i + 1 : ℕ) : ℝ) / ((2 * k - 2 * i - 1 : ℕ) : ℝ)

def oddHarmonic (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, 1 / ((2 * i + 1 : ℕ) : ℝ)

def closedForm (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k - 1) * 2 * (Nat.factorial (2 * k - 1) : ℝ) * oddHarmonic k

private theorem iterDeriv_arctan_even_zero (r : ℕ) :
    iterDeriv (2 * r) Real.arctan 0 = 0 := by
  have hfun :
      (fun x : ℝ => Real.arctan (-x)) = -Real.arctan := by
    funext x
    simp
  have h := congrArg (fun g : ℝ → ℝ => iteratedDeriv (2 * r) g 0) hfun
  change iteratedDeriv (2 * r) (fun x : ℝ => Real.arctan (-x)) 0 =
    iteratedDeriv (2 * r) (fun x : ℝ => -Real.arctan x) 0 at h
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at h
  simp only [neg_zero, smul_eq_mul, pow_mul] at h
  norm_num at h
  have hz : iteratedDeriv (2 * r) Real.arctan 0 = 0 := by
    linarith
  simpa only [iterDeriv, ← iteratedDeriv_eq_iterate] using hz

private theorem iteratedDeriv_one_add_sq_zero (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => 1 + x ^ 2) 0 =
      if n = 0 then 1 else if n = 2 then 2 else 0 := by
  have h := iteratedDeriv_fun_add (n := n) (x := (0 : ℝ))
    (f := fun _ : ℝ => 1) (g := fun x : ℝ => x ^ 2)
    contDiffAt_const (contDiffAt_id.pow 2)
  rw [h]
  rcases n with _ | _ | _ | n <;>
    norm_num [iteratedDeriv_const, iteratedDeriv_pow,
      Nat.descFactorial_eq_zero_iff_lt] <;> omega

private theorem iterDeriv_arctan_recurrence (n : ℕ) (hn : 1 ≤ n) :
    iterDeriv (n + 1) Real.arctan 0 =
      -(n : ℝ) * (n - 1 : ℕ) *
        iterDeriv (n - 1) Real.arctan 0 := by
  have hp : ContDiffAt ℝ n (fun x : ℝ => 1 + x ^ 2) 0 := by
    fun_prop
  have hq : ContDiffAt ℝ n (deriv Real.arctan) 0 := by
    rw [Real.deriv_arctan]
    exact contDiffAt_const.div
      (contDiffAt_const.add (contDiffAt_id.pow 2)) (by norm_num)
  have h := iteratedDeriv_fun_mul hp hq
  have hone :
      (fun x : ℝ => (1 + x ^ 2) * deriv Real.arctan x) =
        fun _ : ℝ => 1 := by
    funext x
    rw [Real.deriv_arctan]
    field_simp
  rw [hone] at h
  simp only [iteratedDeriv_const, if_neg (by omega : n ≠ 0)] at h
  let T : ℕ → ℝ := fun i =>
    (Nat.choose n i : ℝ) *
      iteratedDeriv i (fun x : ℝ => 1 + x ^ 2) 0 *
      iteratedDeriv (n - i) (deriv Real.arctan) 0
  change 0 = ∑ i ∈ Finset.range (n + 1), T i at h
  by_cases hn1 : n = 1
  · subst n
    simpa using iterDeriv_arctan_even_zero 1
  · have hn2 : 2 ≤ n := by omega
    have hzero : 0 ∈ Finset.range (n + 1) := by simp
    have htwo : 2 ∈ (Finset.range (n + 1)).erase 0 := by
      simp
      omega
    have hrest :
        ∑ i ∈ ((Finset.range (n + 1)).erase 0).erase 2, T i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi0 : i ≠ 0 := by
        simp only [Finset.mem_erase] at hi
        exact hi.2.1
      have hi2 : i ≠ 2 := by
        simp only [Finset.mem_erase] at hi
        exact hi.1
      simp [T, iteratedDeriv_one_add_sq_zero, hi0, hi2]
    have hs0 :=
      Finset.sum_erase_add (Finset.range (n + 1)) T hzero
    have hs2 :=
      Finset.sum_erase_add ((Finset.range (n + 1)).erase 0) T htwo
    have hsum :
        ∑ i ∈ Finset.range (n + 1), T i = T 0 + T 2 := by
      rw [hrest, zero_add] at hs2
      linarith
    rw [hsum] at h
    norm_num [T, iteratedDeriv_one_add_sq_zero,
      Nat.choose_two_right] at h
    have hderivInv :
        (fun x : ℝ => (1 + x ^ 2)⁻¹) = deriv Real.arctan := by
      rw [Real.deriv_arctan]
      funext x
      simp [one_div]
    rw [hderivInv] at h
    have hlead :
        iteratedDeriv n (deriv Real.arctan) 0 =
          iteratedDeriv (n + 1) Real.arctan 0 := by
      rw [iteratedDeriv_succ']
    have hprev :
        iteratedDeriv (n - 2) (deriv Real.arctan) 0 =
          iteratedDeriv (n - 1) Real.arctan 0 := by
      rw [← show n - 2 + 1 = n - 1 by omega]
      rw [iteratedDeriv_succ']
    have hcoeff :
        ((n * (n - 1) / 2 : ℕ) : ℝ) * 2 =
          (n : ℝ) * (n - 1 : ℕ) := by
      rw [← Nat.choose_two_right, Nat.cast_choose_two]
      rw [Nat.cast_sub hn]
      ring
    rw [hlead, hprev, hcoeff] at h
    simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
    push_cast at h ⊢
    ring_nf at h ⊢
    linarith

private theorem iterDeriv_arctan_odd_zero (i : ℕ) :
    iterDeriv (2 * i + 1) Real.arctan 0 =
      (-1 : ℝ) ^ i * (Nat.factorial (2 * i) : ℝ) := by
  induction i with
  | zero =>
      have h := congrFun Real.deriv_arctan 0
      norm_num at h
      simpa [iterDeriv] using h
  | succ i ih =>
      have hr := iterDeriv_arctan_recurrence (2 * i + 2) (by omega)
      have hnext : 2 * (i + 1) + 1 = (2 * i + 2) + 1 := by omega
      have hprev : (2 * i + 2) - 1 = 2 * i + 1 := by omega
      rw [← hnext, hprev, ih] at hr
      rw [hr]
      rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega,
        Nat.factorial_succ,
        show 2 * i + 1 = 2 * i + 1 by rfl,
        Nat.factorial_succ]
      push_cast
      rw [pow_succ]
      ring

private theorem sum_range_reflect {α : Type*} [AddCommMonoid α]
    (g : ℕ → α) (p : ℕ) :
    (∑ i ∈ Finset.range (p + 1), g (p - i)) =
      ∑ i ∈ Finset.range (p + 1), g i := by
  classical
  refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
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
  · intro i hi
    rfl

theorem gap1 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k - 1) f 0 =
      iterDeriv (2 * k - 1) (fun x : ℝ => Real.arctan x * Real.arctan x) 0 := by
  have hfun : f =
      fun x : ℝ => Real.arctan x * Real.arctan x := by
    funext x
    simp [f, pow_two]
  rw [hfun]

theorem gap2 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k - 1) (fun x : ℝ => Real.arctan x * Real.arctan x) 0 = 0 := by
  let g : ℝ → ℝ := fun x => Real.arctan x * Real.arctan x
  have heven : (fun x : ℝ => g (-x)) = g := by
    funext x
    simp [g]
  have h := congrArg
    (fun q : ℝ → ℝ => iteratedDeriv (2 * k - 1) q 0) heven
  change iteratedDeriv (2 * k - 1) (fun x : ℝ => g (-x)) 0 =
    iteratedDeriv (2 * k - 1) g 0 at h
  rw [iteratedDeriv_comp_neg] at h
  have hodd : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  rw [hodd] at h
  simp only [neg_zero, smul_eq_mul, pow_add, pow_mul] at h
  norm_num at h
  have hz' : iteratedDeriv (2 * (k - 1) + 1) g 0 = 0 := by
    linarith
  have hz : iteratedDeriv (2 * k - 1) g 0 = 0 := by
    rw [hodd]
    exact hz'
  simpa only [g, iterDeriv, ← iteratedDeriv_eq_iterate] using hz

theorem gap3 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k - 1) f 0 = 0 := by
  rw [gap1 k hk]
  exact gap2 k hk

theorem gap4 (k : ℕ) :
    iterDeriv (2 * k) f 0 =
      iterDeriv (2 * k) (fun x : ℝ => Real.arctan x * Real.arctan x) 0 := by
  have hfun : f =
      fun x : ℝ => Real.arctan x * Real.arctan x := by
    funext x
    simp [f, pow_two]
  rw [hfun]

theorem gap5 (k : ℕ) :
    iterDeriv (2 * k) (fun x : ℝ => Real.arctan x * Real.arctan x) 0 =
      fullLeibnizSum k := by
  have hs : ContDiffAt ℝ (2 * k) Real.arctan 0 :=
    Real.contDiff_arctan.contDiffAt.of_le le_top
  have h := iteratedDeriv_fun_mul hs hs
  simpa only [iteratedDeriv_eq_iterate, iterDeriv, fullLeibnizSum,
    mul_assoc] using h

theorem gap6 (k : ℕ) :
    iterDeriv (2 * k) f 0 = fullLeibnizSum k := by
  rw [gap4 k, gap5 k]

theorem gap7 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 = oddLeibnizSum k := by
  classical
  rw [gap6]
  unfold fullLeibnizSum oddLeibnizSum
  let T : ℕ → ℝ := fun i =>
    (Nat.choose (2 * k) i : ℝ) *
      iterDeriv i Real.arctan 0 *
      iterDeriv (2 * k - i) Real.arctan 0
  change (∑ i ∈ Finset.range (2 * k + 1), T i) =
    ∑ i ∈ Finset.range k, T (2 * i + 1)
  have hfilter :
      (∑ i ∈ Finset.range (2 * k + 1), T i) =
        ∑ i ∈ (Finset.range (2 * k + 1)).filter
          (fun i => i % 2 = 1), T i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hodd
    · rfl
    · have hmod : i % 2 = 0 := by omega
      have heven : i = 2 * (i / 2) := by omega
      rw [heven]
      simp [T, iterDeriv_arctan_even_zero]
  rw [hfilter]
  symm
  refine Finset.sum_bij (fun i _ => 2 * i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · omega
  · intro a ha b hb hab
    have ha' : a < k := Finset.mem_range.mp ha
    have hb' : b < k := Finset.mem_range.mp hb
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨b / 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).2
      omega
    · change 2 * (b / 2) + 1 = b
      omega
  · intro i hi
    rfl

theorem gap8 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 = factorialSum k := by
  rw [gap7 k hk]
  unfold oddLeibnizSum factorialSum
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hindex :
      2 * k - 2 * i - 1 = 2 * (k - i - 1) + 1 := by
    omega
  have hfactorial : 2 * (k - i - 1) = 2 * k - 2 * i - 2 := by
    omega
  rw [iterDeriv_arctan_odd_zero i, hindex,
    iterDeriv_arctan_odd_zero (k - i - 1), hfactorial]
  ring

theorem gap9 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 =
      (-1 : ℝ) ^ (k - 1) *
        ∑ i ∈ Finset.range k,
          (Nat.factorial (2 * k) : ℝ) /
              ((Nat.factorial (2 * i + 1) : ℝ) *
                (Nat.factorial (2 * k - 2 * i - 1) : ℝ)) *
            (Nat.factorial (2 * i) : ℝ) *
            (Nat.factorial (2 * k - 2 * i - 2) : ℝ) := by
  rw [gap8 k hk]
  unfold factorialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hle : 2 * i + 1 ≤ 2 * k := by omega
  have hsub : 2 * k - (2 * i + 1) = 2 * k - 2 * i - 1 := by
    omega
  have hchoose :
      (Nat.factorial (2 * k) : ℝ) /
          ((Nat.factorial (2 * i + 1) : ℝ) *
            (Nat.factorial (2 * k - 2 * i - 1) : ℝ)) =
        (Nat.choose (2 * k) (2 * i + 1) : ℝ) := by
    apply (div_eq_iff ?_).2
    · have hnat :=
        Nat.choose_mul_factorial_mul_factorial hle
      rw [hsub] at hnat
      rw [← mul_assoc]
      exact_mod_cast hnat.symm
    · positivity
  have hsign :
      (-1 : ℝ) ^ i * (-1 : ℝ) ^ (k - i - 1) =
        (-1 : ℝ) ^ (k - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hchoose]
  rw [← hsign]
  ring

theorem gap10 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 =
      (-1 : ℝ) ^ (k - 1) * (Nat.factorial (2 * k) : ℝ) * reciprocalSum k := by
  rw [gap9 k hk]
  unfold reciprocalSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hsecond :
      2 * k - 2 * i - 1 = (2 * k - 2 * i - 2) + 1 := by
    omega
  rw [Nat.factorial_succ, hsecond, Nat.factorial_succ]
  push_cast
  field_simp

theorem gap11 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 =
      (-1 : ℝ) ^ (k - 1) * (Nat.factorial (2 * k) : ℝ) *
        ∑ i ∈ Finset.range k,
          1 / (2 * k : ℝ) *
            (1 / (2 * i + 1 : ℝ) + 1 / (2 * k - 2 * i - 1 : ℕ)) := by
  rw [gap10 k hk]
  congr 1
  unfold reciprocalSum
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hle : 2 * i + 1 ≤ 2 * k := by omega
  have hsub :
      2 * k - 2 * i - 1 = 2 * k - (2 * i + 1) := by
    omega
  rw [hsub, Nat.cast_sub hle]
  push_cast
  have hkpos : (0 : ℝ) < 2 * k := by positivity
  have hipos : (0 : ℝ) < 2 * i + 1 := by positivity
  have hrestpos : (0 : ℝ) < 2 * k - (2 * i + 1) := by
    exact_mod_cast (by omega : 0 < 2 * k - (2 * i + 1))
  field_simp [ne_of_gt hkpos, ne_of_gt hipos, ne_of_gt hrestpos]
  ring

theorem gap12 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 =
      (-1 : ℝ) ^ (k - 1) * 2 * (Nat.factorial (2 * k - 1) : ℝ) *
        ∑ i ∈ Finset.range k, 1 / ((2 * (k - i) - 1 : ℕ) : ℝ) := by
  rw [gap11 k hk]
  let L : ℝ :=
    ∑ i ∈ Finset.range k, 1 / ((2 * i + 1 : ℕ) : ℝ)
  let R : ℝ :=
    ∑ i ∈ Finset.range k,
      1 / ((2 * k - 2 * i - 1 : ℕ) : ℝ)
  have hkform : k = (k - 1) + 1 := by omega
  have hreflect : R = L := by
    have href := sum_range_reflect
      (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ)) (k - 1)
    rw [← hkform] at href
    unfold R L
    calc
      (∑ i ∈ Finset.range k,
          1 / ((2 * k - 2 * i - 1 : ℕ) : ℝ)) =
          ∑ i ∈ Finset.range k,
            1 / ((2 * (k - 1 - i) + 1 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 3
        simp only [Finset.mem_range] at hi
        omega
      _ = ∑ i ∈ Finset.range k,
          1 / ((2 * i + 1 : ℕ) : ℝ) := href
  have hinner :
      (∑ i ∈ Finset.range k,
          1 / (2 * k : ℝ) *
            (1 / (2 * i + 1 : ℝ) +
              1 / (2 * k - 2 * i - 1 : ℕ))) =
        1 / (2 * k : ℝ) * (2 * R) := by
    calc
      (∑ i ∈ Finset.range k,
          1 / (2 * k : ℝ) *
            (1 / (2 * i + 1 : ℝ) +
              1 / (2 * k - 2 * i - 1 : ℕ))) =
          1 / (2 * k : ℝ) *
            ∑ i ∈ Finset.range k,
              (1 / (2 * i + 1 : ℝ) +
                1 / (2 * k - 2 * i - 1 : ℕ)) := by
        rw [Finset.mul_sum]
      _ = 1 / (2 * k : ℝ) * (L + R) := by
        rw [Finset.sum_add_distrib]
        simp [L, R]
      _ = 1 / (2 * k : ℝ) * (2 * R) := by
        rw [← hreflect]
        ring
  rw [hinner]
  have htarget :
      R = ∑ i ∈ Finset.range k,
        1 / ((2 * (k - i) - 1 : ℕ) : ℝ) := by
    unfold R
    apply Finset.sum_congr rfl
    intro i hi
    congr 3
    simp only [Finset.mem_range] at hi
    omega
  rw [htarget]
  rw [show 2 * k = (2 * k - 1) + 1 by omega,
    Nat.factorial_succ]
  push_cast
  have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    push_cast
    ring
  rw [hcast]
  have hkne : (2 * (k : ℝ)) ≠ 0 := by positivity
  field_simp [hkne]
  ring

theorem gap13 (k : ℕ) (hk : 1 ≤ k) :
    iterDeriv (2 * k) f 0 = closedForm k := by
  rw [gap12 k hk]
  unfold closedForm oddHarmonic
  congr 1
  have hkform : k = (k - 1) + 1 := by omega
  have href := sum_range_reflect
    (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ)) (k - 1)
  rw [← hkform] at href
  calc
    (∑ i ∈ Finset.range k,
        1 / ((2 * (k - i) - 1 : ℕ) : ℝ)) =
        ∑ i ∈ Finset.range k,
          1 / ((2 * (k - 1 - i) + 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      simp only [Finset.mem_range] at hi
      omega
    _ = ∑ i ∈ Finset.range k,
        1 / ((2 * i + 1 : ℕ) : ℝ) := href

end

end ProofGap.Exercise1222_1
