import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2891

noncomputable section

open scoped BigOperators

def sec (x : ℝ) : ℝ :=
  1 / Real.cos x

def bernoulliMagnitude (n : ℕ) : ℝ :=
  |(((bernoulli (2 * n) : ℚ) : ℝ))|

def A (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * n) * ((2 : ℝ) ^ (2 * n) - 1) *
    bernoulliMagnitude n / (Nat.factorial (2 * n) : ℝ)

def tangentMaclaurinTerm (x : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n Real.tan 0 / (Nat.factorial n : ℝ) * x ^ n

def tangentSeriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  A (k + 1) * x ^ (2 * k + 1)

def ξ (x : ℝ) : ℝ :=
  1 - Real.cos x

private theorem hasDerivAt_sec_sq (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun y => sec y ^ 2) (2 * sec x ^ 2 * Real.tan x) x := by
  have h := ((Real.hasDerivAt_cos x).pow 2).inv (pow_ne_zero 2 hx)
  have heq : (fun y => sec y ^ 2) =ᶠ[nhds x] (Real.cos ^ 2)⁻¹ :=
    Filter.Eventually.of_forall fun y => by
      simp [sec, one_div]
  have h' := h.congr_of_eventuallyEq heq
  convert h' using 1
  simp only [Pi.pow_apply]
  unfold sec
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx]
  ring

private theorem iteratedDeriv_two_tan (x : ℝ) (hx : Real.cos x ≠ 0) :
    iteratedDeriv 2 Real.tan x = 2 * sec x ^ 2 * Real.tan x := by
  calc
    iteratedDeriv 2 Real.tan x = deriv (iteratedDeriv 1 Real.tan) x := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv (deriv Real.tan) x := by
      rw [show iteratedDeriv 1 Real.tan = deriv Real.tan by
        rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero]]
    _ = 2 * sec x ^ 2 * Real.tan x := by
      rw [show deriv Real.tan = fun y => (Real.cos y ^ 2)⁻¹ by
        funext y
        simpa [one_div] using Real.deriv_tan y]
      have hderiv := (((Real.hasDerivAt_cos x).pow 2).inv (pow_ne_zero 2 hx)).deriv
      change deriv ((Real.cos ^ 2)⁻¹) x = _
      rw [hderiv]
      simp only [Pi.pow_apply]
      unfold sec
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hx]
      ring

private theorem iteratedDeriv_three_tan (x : ℝ) (hx : Real.cos x ≠ 0) :
    iteratedDeriv 3 Real.tan x =
      2 * sec x ^ 4 + 4 * sec x ^ 2 * Real.tan x ^ 2 := by
  calc
    iteratedDeriv 3 Real.tan x = deriv (iteratedDeriv 2 Real.tan) x := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv (fun y => 2 * sec y ^ 2 * Real.tan y) x := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hx] with y hy
      exact iteratedDeriv_two_tan y hy
    _ = 2 * sec x ^ 4 + 4 * sec x ^ 2 * Real.tan x ^ 2 := by
      have h := (hasDerivAt_sec_sq x hx).const_mul 2 |>.mul
        (Real.hasDerivAt_tan hx)
      convert h.deriv using 1 <;> simp [sec, one_div] <;> ring

private theorem iteratedDeriv_four_tan (x : ℝ) (hx : Real.cos x ≠ 0) :
    iteratedDeriv 4 Real.tan x =
      8 * sec x ^ 4 * Real.tan x +
      8 * sec x ^ 2 * Real.tan x ^ 3 +
      8 * sec x ^ 4 * Real.tan x := by
  calc
    iteratedDeriv 4 Real.tan x = deriv (iteratedDeriv 3 Real.tan) x := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv
        (fun y => 2 * sec y ^ 4 + 4 * sec y ^ 2 * Real.tan y ^ 2) x := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hx] with y hy
      exact iteratedDeriv_three_tan y hy
    _ = 8 * sec x ^ 4 * Real.tan x +
        8 * sec x ^ 2 * Real.tan x ^ 3 +
        8 * sec x ^ 4 * Real.tan x := by
      have hq := hasDerivAt_sec_sq x hx
      have ht := Real.hasDerivAt_tan hx
      have h := (hq.pow 2).const_mul 2 |>.add
        ((hq.mul (ht.pow 2)).const_mul 4)
      rw [show
        (fun y => 2 * sec y ^ 4 + 4 * sec y ^ 2 * Real.tan y ^ 2) =
          (fun y => 2 * (sec y ^ 2) ^ 2 +
            4 * (sec y ^ 2 * Real.tan y ^ 2)) by
        funext y
        ring]
      convert h.deriv using 1 <;> simp [sec, one_div] <;> ring

private theorem iteratedDeriv_five_tan (x : ℝ) (hx : Real.cos x ≠ 0) :
    iteratedDeriv 5 Real.tan x =
      32 * sec x ^ 4 * Real.tan x ^ 2 + 8 * sec x ^ 6 +
      16 * sec x ^ 2 * Real.tan x ^ 4 +
      24 * sec x ^ 4 * Real.tan x ^ 2 +
      32 * sec x ^ 4 * Real.tan x ^ 2 + 8 * sec x ^ 6 := by
  calc
    iteratedDeriv 5 Real.tan x = deriv (iteratedDeriv 4 Real.tan) x := by
      rw [show (5 : ℕ) = 4 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv
        (fun y =>
          8 * sec y ^ 4 * Real.tan y +
          8 * sec y ^ 2 * Real.tan y ^ 3 +
          8 * sec y ^ 4 * Real.tan y) x := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hx] with y hy
      exact iteratedDeriv_four_tan y hy
    _ = 32 * sec x ^ 4 * Real.tan x ^ 2 + 8 * sec x ^ 6 +
        16 * sec x ^ 2 * Real.tan x ^ 4 +
        24 * sec x ^ 4 * Real.tan x ^ 2 +
        32 * sec x ^ 4 * Real.tan x ^ 2 + 8 * sec x ^ 6 := by
      have hq := hasDerivAt_sec_sq x hx
      have ht := Real.hasDerivAt_tan hx
      have hterm := ((hq.pow 2).mul ht).const_mul 8
      have hmiddle := (hq.mul (ht.pow 3)).const_mul 8
      have h := hterm.add hmiddle |>.add hterm
      rw [show
        (fun y =>
          8 * sec y ^ 4 * Real.tan y +
          8 * sec y ^ 2 * Real.tan y ^ 3 +
          8 * sec y ^ 4 * Real.tan y) =
          (fun y =>
            8 * ((sec y ^ 2) ^ 2 * Real.tan y) +
            8 * (sec y ^ 2 * Real.tan y ^ 3) +
            8 * ((sec y ^ 2) ^ 2 * Real.tan y)) by
        funext y
        ring]
      convert h.deriv using 1 <;> simp [sec, one_div] <;> ring

private theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  norm_num [Finset.sum_range_succ, h5, Nat.choose]

private theorem bernoulli_abs_eq_signed (n : ℕ) (hn : n ≠ 0) :
    |((bernoulli (2 * n) : ℚ) : ℝ)| =
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℚ) : ℝ) := by
  have hz := hasSum_zeta_nat hn
  have hzpos : 0 < ∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n) :=
    hz.summable.tsum_pos (fun m => by positivity) 1 (by simp)
  rw [hz.tsum_eq] at hzpos
  have hfac :
      0 < (2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ) := by
    positivity
  have hprod :
      0 < ((-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℚ) : ℝ)) *
        ((2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) /
          (Nat.factorial (2 * n) : ℝ)) := by
    convert hzpos using 1 <;> ring
  have hsign :
      0 < (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℚ) : ℝ) :=
    pos_of_mul_pos_left hprod hfac.le
  calc
    |((bernoulli (2 * n) : ℚ) : ℝ)| =
        |(-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℚ) : ℝ)| := by simp
    _ = (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℚ) : ℝ) :=
      abs_of_pos hsign

private theorem A_eq_signed (n : ℕ) (hn : n ≠ 0) :
    A n = (-1 : ℝ) ^ (n + 1) *
      (2 : ℝ) ^ (2 * n) * ((2 : ℝ) ^ (2 * n) - 1) *
      ((bernoulli (2 * n) : ℚ) : ℝ) /
      (Nat.factorial (2 * n) : ℝ) := by
  unfold A bernoulliMagnitude
  rw [bernoulli_abs_eq_signed n hn]
  ring

private theorem bernoulliFun_eq_sum (N : ℕ) (x : ℝ) :
    bernoulliFun N x =
      ∑ i ∈ Finset.range (N + 1),
        (Nat.choose N i : ℝ) * ((bernoulli i : ℚ) : ℝ) * x ^ (N - i) := by
  simp [bernoulliFun, Polynomial.bernoulli]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem scaled_bernoulli_quarter_half (n : ℕ) :
    (4 : ℝ) ^ (2 * n + 2) * bernoulliFun (2 * n + 2) (1 / 4) =
      (2 : ℝ) ^ (2 * n + 2) * bernoulliFun (2 * n + 2) (1 / 2) := by
  let N := 2 * n + 2
  have hmul := bernoulliFun_mul N two_ne_zero (1 / 4 : ℝ)
  have href := bernoulliFun_eval_one_sub (k := N) (x := (1 / 4 : ℝ))
  have hEven : Even N := by
    refine ⟨n + 1, ?_⟩
    dsimp [N]
    omega
  have hsign : (-1 : ℝ) ^ N = 1 := hEven.neg_one_pow
  norm_num [Finset.sum_range_succ] at hmul href
  rw [hsign, one_mul] at href
  have hb : bernoulliFun N (1 / 2) =
      (2 : ℝ) ^ N * bernoulliFun N (1 / 4) := by
    rw [href] at hmul
    nlinarith
  change (4 : ℝ) ^ N * bernoulliFun N (1 / 4) =
    (2 : ℝ) ^ N * bernoulliFun N (1 / 2)
  rw [hb]
  rw [show (4 : ℝ) ^ N = (2 : ℝ) ^ N * (2 : ℝ) ^ N by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]]
  ring

private theorem scale_bernoulliFun (N : ℕ) (a : ℝ) (ha : a ≠ 0) :
    a ^ N * bernoulliFun N (1 / a) =
      ∑ i ∈ Finset.range (N + 1),
        (Nat.choose N i : ℝ) * ((bernoulli i : ℚ) : ℝ) * a ^ i := by
  rw [bernoulliFun_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i ≤ N := by
    simpa [Finset.mem_range] using hi
  have hpow : a ^ N * (1 / a) ^ (N - i) = a ^ i := by
    calc
      a ^ N * (1 / a) ^ (N - i) =
          (a ^ (N - i) * a ^ i) * (1 / a) ^ (N - i) := by
        rw [← pow_add, Nat.sub_add_cancel hiN]
      _ = (a ^ (N - i) * a ^ i) * (a⁻¹) ^ (N - i) := by
        rw [one_div]
      _ = (a ^ (N - i) * (a⁻¹) ^ (N - i)) * a ^ i := by ring
      _ = a ^ i := by
        rw [← mul_pow, mul_inv_cancel₀ ha, one_pow, one_mul]
  calc
    _ = (Nat.choose N i : ℝ) * ((bernoulli i : ℚ) : ℝ) *
          (a ^ N * (1 / a) ^ (N - i)) := by ring
    _ = (Nat.choose N i : ℝ) * ((bernoulli i : ℚ) : ℝ) * a ^ i := by
      rw [hpow]

private theorem full_weighted_bernoulli_sum (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 2 + 1),
        (Nat.choose (2 * n + 2) i : ℝ) *
          ((4 : ℝ) ^ i - (2 : ℝ) ^ i) *
          ((bernoulli i : ℚ) : ℝ) = 0 := by
  have h := scaled_bernoulli_quarter_half n
  rw [scale_bernoulliFun (2 * n + 2) 4 (by norm_num),
    scale_bernoulliFun (2 * n + 2) 2 (by norm_num)] at h
  rw [← sub_eq_zero] at h
  rw [← Finset.sum_sub_distrib] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def weightedBernoulli (N i : ℕ) : ℝ :=
  (Nat.choose N i : ℝ) * ((4 : ℝ) ^ i - (2 : ℝ) ^ i) *
    ((bernoulli i : ℚ) : ℝ)

private theorem full_eq_neg_add_even_sum (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n + 2 + 1),
        weightedBernoulli (2 * n + 2) i) =
      -(2 * n + 2 : ℕ) +
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 2) (2 * k + 2) : ℝ) *
            (2 : ℝ) ^ (2 * k + 2) *
            ((2 : ℝ) ^ (2 * k + 2) - 1) *
            ((bernoulli (2 * k + 2) : ℚ) : ℝ) := by
  let N := 2 * n + 2
  let s : Finset ℕ :=
    insert 1 (Finset.image (fun k => 2 * k + 2) (Finset.range (n + 1)))
  have hs : s ⊆ Finset.range (N + 1) := by
    intro i hi
    simp only [s, Finset.mem_insert, Finset.mem_image] at hi
    rcases hi with rfl | ⟨k, hk, rfl⟩
    · simp [N]
    · simp only [Finset.mem_range] at hk ⊢
      dsimp [N]
      omega
  have hzero : ∀ i ∈ Finset.range (N + 1), i ∉ s →
      weightedBernoulli N i = 0 := by
    intro i hi hnot
    have hiN : i ≤ N := by simpa [Finset.mem_range] using hi
    by_cases hi0 : i = 0
    · subst i
      simp [weightedBernoulli]
    by_cases hi1 : i = 1
    · subst i
      exact False.elim (hnot (by simp [s]))
    rcases i.even_or_odd with heven | hodd
    · obtain ⟨q, hq⟩ := heven
      exfalso
      apply hnot
      simp only [s, Finset.mem_insert, Finset.mem_image]
      right
      refine ⟨q - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]
        dsimp [N] at hiN
        omega
      · omega
    · unfold weightedBernoulli
      rw [bernoulli_eq_zero_of_odd hodd (by omega)]
      simp
  have hrestricted := (Finset.sum_subset hs hzero).symm
  change (∑ i ∈ Finset.range (N + 1), weightedBernoulli N i) = _
  rw [hrestricted]
  have hnotone :
      1 ∉ Finset.image (fun k => 2 * k + 2) (Finset.range (n + 1)) := by
    simp only [Finset.mem_image, not_exists]
    intro k hk
    omega
  rw [Finset.sum_insert hnotone]
  rw [Finset.sum_image (by
    intro a ha b hb hab
    dsimp at hab
    omega)]
  dsimp [N]
  congr 1
  · norm_num [weightedBernoulli]
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    unfold weightedBernoulli
    rw [show (4 : ℝ) ^ (2 * k + 2) =
        (2 : ℝ) ^ (2 * k + 2) * (2 : ℝ) ^ (2 * k + 2) by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]]
    ring

private theorem raw_tangent_coefficient_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n + 2) (2 * k + 2) : ℝ) *
          (2 : ℝ) ^ (2 * k + 2) *
          ((2 : ℝ) ^ (2 * k + 2) - 1) *
          ((bernoulli (2 * k + 2) : ℚ) : ℝ)) =
      (2 * n + 2 : ℕ) := by
  have hzero :
      (∑ i ∈ Finset.range (2 * n + 2 + 1),
          weightedBernoulli (2 * n + 2) i) = 0 := by
    simpa [weightedBernoulli] using full_weighted_bernoulli_sum n
  rw [full_eq_neg_add_even_sum n] at hzero
  push_cast at hzero ⊢
  linarith

private theorem tangent_cosine_term (n k : ℕ) (hk : k ≤ n) :
    A (k + 1) *
        ((-1 : ℝ) ^ (n - k) / (Nat.factorial (2 * (n - k)) : ℝ)) =
      ((-1 : ℝ) ^ n / (Nat.factorial (2 * n + 2) : ℝ)) *
        ((Nat.choose (2 * n + 2) (2 * k + 2) : ℝ) *
          (2 : ℝ) ^ (2 * k + 2) *
          ((2 : ℝ) ^ (2 * k + 2) - 1) *
          ((bernoulli (2 * k + 2) : ℚ) : ℝ)) := by
  rw [A_eq_signed (k + 1) (by omega)]
  have hK : 2 * k + 2 ≤ 2 * n + 2 := by omega
  have hsub : 2 * n + 2 - (2 * k + 2) = 2 * (n - k) := by omega
  have hchoose :
      (Nat.choose (2 * n + 2) (2 * k + 2) : ℝ) *
          (Nat.factorial (2 * k + 2) : ℝ) *
          (Nat.factorial (2 * (n - k)) : ℝ) =
        (Nat.factorial (2 * n + 2) : ℝ) := by
    rw [← hsub]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hK
  have hsign :
      (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ n := by
    calc
      (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n - k) =
          (-1 : ℝ) ^ (k + (n - k)) := (pow_add _ _ _).symm
      _ = (-1 : ℝ) ^ n := by rw [Nat.add_sub_of_le hk]
  field_simp
  rw [← hsign, ← hchoose]
  simp only [Nat.mul_add, Nat.mul_one]
  ring

private theorem tangent_cosine_coefficient (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        A (k + 1) *
          ((-1 : ℝ) ^ (n - k) /
            (Nat.factorial (2 * (n - k)) : ℝ))) =
      (-1 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        A (k + 1) *
          ((-1 : ℝ) ^ (n - k) /
            (Nat.factorial (2 * (n - k)) : ℝ))) =
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ n / (Nat.factorial (2 * n + 2) : ℝ)) *
          ((Nat.choose (2 * n + 2) (2 * k + 2) : ℝ) *
            (2 : ℝ) ^ (2 * k + 2) *
            ((2 : ℝ) ^ (2 * k + 2) - 1) *
            ((bernoulli (2 * k + 2) : ℚ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact tangent_cosine_term n k (by
          simpa [Finset.mem_range] using hk)
    _ = ((-1 : ℝ) ^ n / (Nat.factorial (2 * n + 2) : ℝ)) *
        (∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 2) (2 * k + 2) : ℝ) *
            (2 : ℝ) ^ (2 * k + 2) *
            ((2 : ℝ) ^ (2 * k + 2) - 1) *
            ((bernoulli (2 * k + 2) : ℚ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = ((-1 : ℝ) ^ n / (Nat.factorial (2 * n + 2) : ℝ)) *
        (2 * n + 2 : ℕ) := by
      rw [raw_tangent_coefficient_sum]
    _ = (-1 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ) := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
      push_cast
      field_simp

private theorem A_eq_zeta_sum (n : ℕ) (hn : n ≠ 0) :
    A n =
      2 * ((2 : ℝ) ^ (2 * n) - 1) *
        (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n)) /
        Real.pi ^ (2 * n) := by
  rw [A_eq_signed n hn, (hasSum_zeta_nat hn).tsum_eq]
  have hpow : (2 : ℝ) ^ (2 * n) =
      2 * (2 : ℝ) ^ (2 * n - 1) := by
    calc
      (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ ((2 * n - 1) + 1) := by
        congr 1
        omega
      _ = 2 * (2 : ℝ) ^ (2 * n - 1) := by rw [pow_succ]; ring
  rw [hpow]
  field_simp [Real.pi_ne_zero]

private theorem zeta_sum_le_pi_sq_div_six (n : ℕ) (hn : n ≠ 0) :
    (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n)) ≤ Real.pi ^ 2 / 6 := by
  have hle : ∀ m : ℕ,
      1 / (m : ℝ) ^ (2 * n) ≤ 1 / (m : ℝ) ^ 2 := by
    intro m
    by_cases hm : m = 0
    · subst m
      have htwo : 2 * n ≠ 0 := by omega
      simp [htwo]
    have hmone : (1 : ℝ) ≤ m := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
    have hp : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ (2 * n) :=
      pow_le_pow_right₀ hmone (by omega)
    exact one_div_le_one_div_of_le (by positivity) hp
  have h := (hasSum_zeta_nat hn).summable.tsum_le_tsum hle
    hasSum_zeta_two.summable
  exact h.trans_eq hasSum_zeta_two.tsum_eq

private theorem A_le_geometric_coefficient (k : ℕ) :
    A (k + 1) ≤ 8 * (4 / Real.pi ^ 2) ^ k := by
  rw [A_eq_zeta_sum (k + 1) (by omega)]
  let z := ∑' m : ℕ, 1 / (m : ℝ) ^ (2 * (k + 1))
  have hz0 : 0 ≤ z := tsum_nonneg fun m => by positivity
  have hzle : z ≤ Real.pi ^ 2 / 6 :=
    zeta_sum_le_pi_sq_div_six (k + 1) (by omega)
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * (k + 1)) := one_le_pow₀ (by norm_num)
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  calc
    2 * ((2 : ℝ) ^ (2 * (k + 1)) - 1) * z /
          Real.pi ^ (2 * (k + 1)) ≤
        2 * (2 : ℝ) ^ (2 * (k + 1)) * (Real.pi ^ 2 / 6) /
          Real.pi ^ (2 * (k + 1)) := by
      gcongr
      linarith
    _ ≤ 2 * (2 : ℝ) ^ (2 * (k + 1)) * Real.pi ^ 2 /
          Real.pi ^ (2 * (k + 1)) := by
      gcongr
      nlinarith
    _ = 8 * (4 / Real.pi ^ 2) ^ k := by
      rw [div_pow]
      field_simp [Real.pi_ne_zero]
      rw [show (2 : ℝ) ^ (2 * (k + 1)) = 4 ^ (k + 1) by
        rw [mul_add, pow_add, pow_mul]
        norm_num
        rw [pow_succ]]
      rw [pow_succ]
      ring

private theorem A_nonneg (n : ℕ) : 0 ≤ A n := by
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * n) := one_le_pow₀ (by norm_num)
  unfold A bernoulliMagnitude
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg (pow_nonneg (by norm_num) _) (sub_nonneg.mpr hp))
      (abs_nonneg _)
  · positivity

private theorem tangent_geometric_ratio_lt_one (x : ℝ)
    (hx : |x| < Real.pi / 2) :
    ‖(4 / Real.pi ^ 2) * |x| ^ 2‖ < 1 := by
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hsquare : 4 * |x| ^ 2 < Real.pi ^ 2 := by
    nlinarith [abs_nonneg x, Real.pi_pos]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [show (4 / Real.pi ^ 2) * |x| ^ 2 =
      (4 * |x| ^ 2) / Real.pi ^ 2 by ring]
  exact (div_lt_one hpi2).2 hsquare

private theorem norm_tangentSeriesTerm_le (x : ℝ) (k : ℕ) :
    ‖tangentSeriesTerm x k‖ ≤
      8 * |x| * (((4 : ℝ) / Real.pi ^ 2) * |x| ^ 2) ^ k := by
  unfold tangentSeriesTerm
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (A_nonneg (k + 1))]
  calc
    A (k + 1) * |x| ^ (2 * k + 1) ≤
        (8 * (4 / Real.pi ^ 2) ^ k) * |x| ^ (2 * k + 1) :=
      mul_le_mul_of_nonneg_right (A_le_geometric_coefficient k)
        (by positivity)
    _ = 8 * |x| * ((4 / Real.pi ^ 2) * |x| ^ 2) ^ k := by
      have hxpow : |x| ^ (2 * k + 1) = |x| * (|x| ^ 2) ^ k := by
        calc
          |x| ^ (2 * k + 1) = |x| ^ (2 * k) * |x| := by rw [pow_succ]
          _ = (|x| ^ 2) ^ k * |x| := by rw [pow_mul]
          _ = |x| * (|x| ^ 2) ^ k := by ring
      rw [hxpow, mul_pow]
      ring

private theorem tangentSeriesTerm_summable (x : ℝ)
    (hx : |x| < Real.pi / 2) : Summable (tangentSeriesTerm x) := by
  have hg : Summable
      (fun k : ℕ => (((4 : ℝ) / Real.pi ^ 2) * |x| ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one (tangent_geometric_ratio_lt_one x hx)
  exact Summable.of_norm_bounded (hg.mul_left (8 * |x|))
    (norm_tangentSeriesTerm_le x)

private theorem norm_tangentSeriesTerm_summable (x : ℝ)
    (hx : |x| < Real.pi / 2) :
    Summable (fun k => ‖tangentSeriesTerm x k‖) := by
  have hg : Summable
      (fun k : ℕ => (((4 : ℝ) / Real.pi ^ 2) * |x| ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one (tangent_geometric_ratio_lt_one x hx)
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (norm_tangentSeriesTerm_le x) (hg.mul_left (8 * |x|))

private def cosineSeriesTerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * x ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)

private theorem norm_cosineSeriesTerm_summable (x : ℝ) :
    Summable (fun j : ℕ => ‖cosineSeriesTerm x j‖) := by
  have h := (Real.summable_pow_div_factorial |x|).comp_injective
    (i := fun j : ℕ => 2 * j) (by
      intro a b hab
      dsimp at hab
      omega)
  convert h using 1
  funext j
  simp [cosineSeriesTerm, Real.norm_eq_abs]

private theorem tangent_cosine_cauchy_term (x : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        tangentSeriesTerm x k *
          ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k)) /
            (Nat.factorial (2 * (n - k)) : ℝ))) =
      (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
        (Nat.factorial (2 * n + 1) : ℝ) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        tangentSeriesTerm x k *
          ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k)) /
            (Nat.factorial (2 * (n - k)) : ℝ))) =
      ∑ k ∈ Finset.range (n + 1),
        (A (k + 1) *
          ((-1 : ℝ) ^ (n - k) /
            (Nat.factorial (2 * (n - k)) : ℝ))) *
          x ^ (2 * n + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := by simpa [Finset.mem_range] using hk
        unfold tangentSeriesTerm
        have hpow : x ^ (2 * k + 1) * x ^ (2 * (n - k)) =
            x ^ (2 * n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        calc
          A (k + 1) * x ^ (2 * k + 1) *
              ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k)) /
                (Nat.factorial (2 * (n - k)) : ℝ)) =
            (A (k + 1) *
              ((-1 : ℝ) ^ (n - k) /
                (Nat.factorial (2 * (n - k)) : ℝ))) *
              (x ^ (2 * k + 1) * x ^ (2 * (n - k))) := by ring
          _ = (A (k + 1) *
              ((-1 : ℝ) ^ (n - k) /
                (Nat.factorial (2 * (n - k)) : ℝ))) *
              x ^ (2 * n + 1) := by rw [hpow]
    _ = (∑ k ∈ Finset.range (n + 1),
        A (k + 1) *
          ((-1 : ℝ) ^ (n - k) /
            (Nat.factorial (2 * (n - k)) : ℝ))) *
          x ^ (2 * n + 1) := by
      rw [Finset.sum_mul]
    _ = (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
        (Nat.factorial (2 * n + 1) : ℝ) := by
      rw [tangent_cosine_coefficient]
      ring

private theorem real_cauchy_product {f g : ℕ → ℝ}
    (hf : Summable f) (hg : Summable g)
    (hfg : Summable (fun p : ℕ × ℕ => f p.1 * g p.2)) :
    ((∑' k, f k) * ∑' j, g j) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) :=
  hf.tsum_mul_tsum_eq_tsum_sum_range hg hfg

set_option maxHeartbeats 1000000 in
private theorem tan_eq_tangentSeries (x : ℝ)
    (hx : |x| < Real.pi / 2) :
    Real.tan x = ∑' k, tangentSeriesTerm x k := by
  have hfNorm : Summable (fun k => ‖tangentSeriesTerm x k‖) :=
    norm_tangentSeriesTerm_summable x hx
  have hgNorm : Summable (fun j => ‖cosineSeriesTerm x j‖) :=
    norm_cosineSeriesTerm_summable x
  have hf : Summable (tangentSeriesTerm x) := Summable.of_norm hfNorm
  have hg : Summable (cosineSeriesTerm x) := Summable.of_norm hgNorm
  have hpairNorm : Summable (fun p : ℕ × ℕ =>
      ‖tangentSeriesTerm x p.1‖ * ‖cosineSeriesTerm x p.2‖) :=
    Summable.mul_of_nonneg hfNorm hgNorm (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)
  have hpair : Summable (fun p : ℕ × ℕ =>
      tangentSeriesTerm x p.1 * cosineSeriesTerm x p.2) :=
    Summable.of_norm (by simpa [norm_mul] using hpairNorm)
  have hcauchy :
      ((∑' k, tangentSeriesTerm x k) *
          ∑' j, cosineSeriesTerm x j) =
        ∑' n, ∑ k ∈ Finset.range (n + 1),
          tangentSeriesTerm x k * cosineSeriesTerm x (n - k) :=
    real_cauchy_product hf hg hpair
  have hcosSeries : (∑' j, cosineSeriesTerm x j) = Real.cos x := by
    simpa [cosineSeriesTerm] using (Real.hasSum_cos x).tsum_eq
  have hproduct : (∑' k, tangentSeriesTerm x k) * Real.cos x = Real.sin x := by
    rw [← hcosSeries]
    rw [hcauchy]
    rw [tsum_congr (fun n => by
      simpa [cosineSeriesTerm, mul_div_assoc] using
        tangent_cosine_cauchy_term x n)]
    simpa [mul_div_assoc] using (Real.hasSum_sin x).tsum_eq
  have hcos : Real.cos x ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  rw [Real.tan_eq_sin_div_cos, div_eq_iff hcos]
  exact hproduct.symm

private theorem iteratedDeriv_even_tan_zero (n : ℕ) :
    iteratedDeriv (2 * n) Real.tan 0 = 0 := by
  have h := iteratedDeriv_comp_neg (2 * n) Real.tan (0 : ℝ)
  have h' : -iteratedDeriv (2 * n) Real.tan 0 =
      iteratedDeriv (2 * n) Real.tan 0 := by
    simpa [Real.tan_neg, iteratedDeriv_neg] using h
  linarith

private theorem iteratedDeriv_tan_mul_cos (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1),
        (Nat.choose N i : ℝ) * iteratedDeriv i Real.tan 0 *
          iteratedDeriv (N - i) Real.cos 0) =
      iteratedDeriv N Real.sin 0 := by
  have hlocal : (fun y : ℝ => Real.tan y * Real.cos y) =ᶠ[nhds 0]
      Real.sin := by
    filter_upwards [Real.continuous_cos.continuousAt.eventually_ne
      (by norm_num : Real.cos 0 ≠ 0)] with y hy
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hEq := hlocal.iteratedDeriv_eq N
  rw [iteratedDeriv_fun_mul
    (Real.contDiffAt_tan.mpr (by norm_num)) Real.contDiff_cos.contDiffAt] at hEq
  simpa using hEq

private theorem odd_tan_derivative_convolution (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
          iteratedDeriv (2 * k + 1) Real.tan 0 *
          (-1 : ℝ) ^ (n - k)) = (-1 : ℝ) ^ n := by
  let N := 2 * n + 1
  let s : Finset ℕ :=
    Finset.image (fun k => 2 * k + 1) (Finset.range (n + 1))
  have hs : s ⊆ Finset.range (N + 1) := by
    intro i hi
    simp only [s, Finset.mem_image] at hi
    rcases hi with ⟨k, hk, rfl⟩
    simp only [Finset.mem_range] at hk ⊢
    dsimp [N]
    omega
  have hzero : ∀ i ∈ Finset.range (N + 1), i ∉ s →
      (Nat.choose N i : ℝ) * iteratedDeriv i Real.tan 0 *
        iteratedDeriv (N - i) Real.cos 0 = 0 := by
    intro i hi hnot
    have hiN : i ≤ N := by simpa [Finset.mem_range] using hi
    rcases i.even_or_odd with heven | hodd
    · obtain ⟨q, hq⟩ := heven
      have hiq : i = 2 * q := by omega
      rw [hiq, iteratedDeriv_even_tan_zero]
      ring
    · obtain ⟨q, hq⟩ := hodd
      exfalso
      apply hnot
      simp only [s, Finset.mem_image]
      refine ⟨q, ?_, ?_⟩
      · simp only [Finset.mem_range]
        dsimp [N] at hiN
        omega
      · omega
  have hrestricted := (Finset.sum_subset hs hzero).symm
  have hbase := iteratedDeriv_tan_mul_cos N
  rw [hrestricted] at hbase
  rw [Finset.sum_image (by
    intro a ha b hb hab
    dsimp at hab
    omega)] at hbase
  dsimp [N] at hbase
  have hleft :
      (∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
            iteratedDeriv (2 * k + 1) Real.tan 0 *
            iteratedDeriv ((2 * n + 1) - (2 * k + 1)) Real.cos 0) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
            iteratedDeriv (2 * k + 1) Real.tan 0 *
            (-1 : ℝ) ^ (n - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by simpa [Finset.mem_range] using hk
    rw [show (2 * n + 1) - (2 * k + 1) = 2 * (n - k) by omega]
    rw [congrFun (Real.iteratedDeriv_even_cos (n - k)) 0]
    simp
  rw [hleft] at hbase
  rw [congrFun (Real.iteratedDeriv_odd_sin n) 0] at hbase
  simpa using hbase

private theorem target_odd_derivative_convolution (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
          ((Nat.factorial (2 * k + 1) : ℝ) * A (k + 1)) *
          (-1 : ℝ) ^ (n - k)) = (-1 : ℝ) ^ n := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
          ((Nat.factorial (2 * k + 1) : ℝ) * A (k + 1)) *
          (-1 : ℝ) ^ (n - k)) =
      (Nat.factorial (2 * n + 1) : ℝ) *
        (∑ k ∈ Finset.range (n + 1),
          A (k + 1) *
            ((-1 : ℝ) ^ (n - k) /
              (Nat.factorial (2 * (n - k)) : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := by simpa [Finset.mem_range] using hk
        have hK : 2 * k + 1 ≤ 2 * n + 1 := by omega
        have hsub : (2 * n + 1) - (2 * k + 1) = 2 * (n - k) := by omega
        have hchoose :
            (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
                (Nat.factorial (2 * k + 1) : ℝ) *
                (Nat.factorial (2 * (n - k)) : ℝ) =
              (Nat.factorial (2 * n + 1) : ℝ) := by
          rw [← hsub]
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hK
        rw [← hchoose]
        field_simp
    _ = (Nat.factorial (2 * n + 1) : ℝ) *
        ((-1 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)) := by
      rw [tangent_cosine_coefficient]
    _ = (-1 : ℝ) ^ n := by
      field_simp

private theorem iteratedDeriv_odd_tan_zero (n : ℕ) :
    iteratedDeriv (2 * n + 1) Real.tan 0 =
      (Nat.factorial (2 * n + 1) : ℝ) * A (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hactual := odd_tan_derivative_convolution n
      have htarget := target_odd_derivative_convolution n
      have hprevious :
          (∑ k ∈ Finset.range n,
              (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
                iteratedDeriv (2 * k + 1) Real.tan 0 *
                (-1 : ℝ) ^ (n - k)) =
            ∑ k ∈ Finset.range n,
              (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
                ((Nat.factorial (2 * k + 1) : ℝ) * A (k + 1)) *
                (-1 : ℝ) ^ (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (by simpa [Finset.mem_range] using hk)]
      rw [Finset.sum_range_succ, hprevious] at hactual
      rw [Finset.sum_range_succ] at htarget
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        pow_zero, mul_one] at hactual htarget
      linarith

private theorem tangentMaclaurinTerm_even (x : ℝ) (k : ℕ) :
    tangentMaclaurinTerm x (2 * k) = 0 := by
  unfold tangentMaclaurinTerm
  rw [iteratedDeriv_even_tan_zero]
  simp

private theorem tangentMaclaurinTerm_odd (x : ℝ) (k : ℕ) :
    tangentMaclaurinTerm x (2 * k + 1) = tangentSeriesTerm x k := by
  unfold tangentMaclaurinTerm tangentSeriesTerm
  rw [iteratedDeriv_odd_tan_zero]
  have hfact : (Nat.factorial (2 * k + 1) : ℝ) ≠ 0 := by positivity
  field_simp

private theorem tangentMaclaurin_tsum_eq_tangentSeries (x : ℝ)
    (hx : |x| < Real.pi / 2) :
    (∑' n, tangentMaclaurinTerm x n) = ∑' k, tangentSeriesTerm x k := by
  have he : Summable (fun k => tangentMaclaurinTerm x (2 * k)) := by
    simpa only [tangentMaclaurinTerm_even] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have ho : Summable (fun k => tangentMaclaurinTerm x (2 * k + 1)) := by
    exact (tangentSeriesTerm_summable x hx).congr
      (fun k => (tangentMaclaurinTerm_odd x k).symm)
  have hsplit := tsum_even_add_odd he ho
  rw [← hsplit]
  rw [tsum_congr (tangentMaclaurinTerm_even x)]
  rw [tsum_congr (tangentMaclaurinTerm_odd x)]
  simp

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    f 0 = 0 := by
  rw [hf]
  exact Real.tan_zero

theorem gap2 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    ∀ x, Real.cos x ≠ 0 → deriv f x = sec x ^ 2 := by
  have hfun : f = Real.tan := funext hf
  subst f
  intro x hx
  simpa [sec, one_div] using Real.deriv_tan x

theorem gap3 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    deriv f 0 = 1 := by
  have hfun : f = Real.tan := funext hf
  subst f
  simpa using Real.deriv_tan 0

theorem gap4 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    ∀ x, Real.cos x ≠ 0 →
      iteratedDeriv 2 f x = 2 * sec x ^ 2 * Real.tan x := by
  have hfun : f = Real.tan := funext hf
  subst f
  exact iteratedDeriv_two_tan

theorem gap5 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    iteratedDeriv 2 f 0 = 0 := by
  have hfun : f = Real.tan := funext hf
  subst f
  simpa [sec] using iteratedDeriv_two_tan 0 (by norm_num)

theorem gap6 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    ∀ x, Real.cos x ≠ 0 →
      iteratedDeriv 3 f x =
        2 * sec x ^ 4 + 4 * sec x ^ 2 * Real.tan x ^ 2 := by
  have hfun : f = Real.tan := funext hf
  subst f
  exact iteratedDeriv_three_tan

theorem gap7 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    ∀ x, Real.cos x ≠ 0 →
      iteratedDeriv 4 f x =
        8 * sec x ^ 4 * Real.tan x +
        8 * sec x ^ 2 * Real.tan x ^ 3 +
        8 * sec x ^ 4 * Real.tan x := by
  have hfun : f = Real.tan := funext hf
  subst f
  exact iteratedDeriv_four_tan

theorem gap8 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    iteratedDeriv 4 f 0 = 0 := by
  have hfun : f = Real.tan := funext hf
  subst f
  simpa [sec] using iteratedDeriv_four_tan 0 (by norm_num)

theorem gap9 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    ∀ x, Real.cos x ≠ 0 →
      iteratedDeriv 5 f x =
        32 * sec x ^ 4 * Real.tan x ^ 2 + 8 * sec x ^ 6 +
        16 * sec x ^ 2 * Real.tan x ^ 4 +
        24 * sec x ^ 4 * Real.tan x ^ 2 +
        32 * sec x ^ 4 * Real.tan x ^ 2 + 8 * sec x ^ 6 := by
  have hfun : f = Real.tan := funext hf
  subst f
  exact iteratedDeriv_five_tan

theorem gap10 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    iteratedDeriv 5 f 0 = 16 := by
  have hfun : f = Real.tan := funext hf
  subst f
  have h := iteratedDeriv_five_tan 0 (by norm_num)
  norm_num [sec] at h ⊢
  exact h

theorem gap11 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    ∀ x, |x| < Real.pi / 2 →
      f x = ∑' n, tangentMaclaurinTerm x n := by
  intro x hx
  rw [hf]
  exact (tan_eq_tangentSeries x hx).trans
    (tangentMaclaurin_tsum_eq_tangentSeries x hx).symm

theorem gap12 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      (∑' n, tangentMaclaurinTerm x n) =
        ∑' k, tangentSeriesTerm x k := by
  intro x hx
  exact tangentMaclaurin_tsum_eq_tangentSeries x hx

theorem gap13 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan x) :
    ∀ x, |x| < Real.pi / 2 →
      f x = ∑' k, tangentSeriesTerm x k := by
  intro x hx
  rw [hf]
  exact tan_eq_tangentSeries x hx

theorem gap14 :
    ∀ x : ℝ, |x| < Real.pi / 2 → |ξ x| < 1 := by
  intro x hx
  have hcpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
  have hcle : Real.cos x ≤ 1 := Real.cos_le_one x
  rw [abs_of_nonneg]
  · unfold ξ
    linarith
  · unfold ξ
    linarith

theorem gap15 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tan x = Real.sin x / Real.cos x := by
  intro x hx
  exact Real.tan_eq_sin_div_cos x

theorem gap16 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.sin x / Real.cos x = Real.sin x * (1 / (1 - ξ x)) := by
  intro x hx
  simp [ξ, div_eq_mul_inv]

theorem gap17 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tan x = Real.sin x * (1 / (1 - ξ x)) := by
  intro x hx
  rw [Real.tan_eq_sin_div_cos]
  simp [ξ, div_eq_mul_inv]

theorem gap18 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tan x = ∑' k, tangentSeriesTerm x k := by
  intro x hx
  exact tan_eq_tangentSeries x hx

theorem gap19 :
    A 1 = 1 := by
  norm_num [A, bernoulliMagnitude, Nat.factorial]

theorem gap20 :
    A 2 = 1 / 3 := by
  unfold A bernoulliMagnitude
  rw [show bernoulli 4 = -1 / 30 by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]]
  norm_num [Nat.factorial]

theorem gap21 :
    A 3 =
      1 / (Nat.factorial 5 : ℝ) -
      1 / ((Nat.factorial 3 : ℝ) * (Nat.factorial 2 : ℝ)) -
      1 / (Nat.factorial 4 : ℝ) +
      1 / ((Nat.factorial 2 : ℝ) * (Nat.factorial 2 : ℝ)) := by
  unfold A bernoulliMagnitude
  rw [show bernoulli 6 = 1 / 42 by exact bernoulli_six]
  norm_num [Nat.factorial]

theorem gap22 :
    1 / (Nat.factorial 5 : ℝ) -
        1 / ((Nat.factorial 3 : ℝ) * (Nat.factorial 2 : ℝ)) -
        1 / (Nat.factorial 4 : ℝ) +
        1 / ((Nat.factorial 2 : ℝ) * (Nat.factorial 2 : ℝ)) =
      2 / 15 := by
  norm_num [Nat.factorial]

theorem gap23 :
    A 3 = 2 / 15 := by
  exact gap21.trans gap22

theorem gap24 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tan x = ∑' k, tangentSeriesTerm x k := by
  intro x hx
  exact tan_eq_tangentSeries x hx

end

end ProofGap.Exercise2891
