import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ProofGapLean.Exercises.Exercise3028

namespace ProofGap.Exercise2890

noncomputable section

open scoped BigOperators

def φ (x : ℝ) : ℝ :=
  Real.arcsin x ^ 2

def coefficient (n : ℕ) : ℝ :=
  if n % 2 = 0 ∧ 2 ≤ n then
    let k := (n - 2) / 2
    (2 : ℝ) ^ (2 * k + 1) * (Nat.factorial k : ℝ) ^ 2 /
      (Nat.factorial (2 * k + 2) : ℝ)
  else
    0

def powerSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  coefficient n * x ^ n

def firstDerivativeTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  (n : ℝ) * coefficient n * x ^ k

def secondDerivativeTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 2
  (n : ℝ) * (n - 1 : ℝ) * coefficient n * x ^ k

def shiftedFirstDerivativeTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 2
  (n : ℝ) * coefficient n * x ^ n

def combinedResidualTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 2
  ((n + 2 : ℝ) * (n + 1 : ℝ) * coefficient (n + 2) -
    (n : ℝ) ^ 2 * coefficient n) * x ^ n

def evenSeriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k + 1) * (Nat.factorial k : ℝ) ^ 2 /
      (Nat.factorial (2 * k + 2) : ℝ) *
    x ^ (2 * k + 2)

def dividedEvenSeriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k + 1) * (Nat.factorial k : ℝ) ^ 2 /
      (Nat.factorial (2 * k + 2) : ℝ) *
    x ^ (2 * k)

private theorem source_term_eq (x : ℝ) (k : ℕ) :
    ProofGap.Exercise3028.term x (k + 1) =
      2 * evenSeriesTerm x k := by
  rw [ProofGap.Exercise3028.term, evenSeriesTerm, mul_pow]
  simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]
  ring

private theorem even_tsum_eq (x : ℝ) (hx : |x| ≤ 1) :
    (∑' k, evenSeriesTerm x k) = φ x := by
  have hsource :=
    ProofGap.Exercise3028.gap18 x (show x ∈ Set.Icc (-1 : ℝ) 1 by
      exact abs_le.mp hx)
  have heq :
      (∑' k, ProofGap.Exercise3028.term x (k + 1)) =
        2 * ∑' k, evenSeriesTerm x k := by
    rw [← tsum_mul_left]
    apply tsum_congr
    exact source_term_eq x
  rw [heq] at hsource
  rw [φ]
  linarith

private theorem coefficient_odd (k : ℕ) : coefficient (2 * k + 1) = 0 := by
  rw [coefficient]
  split_ifs with h
  · omega
  · rfl

private theorem coefficient_even (k : ℕ) : coefficient (2 * k + 2) =
      (2 : ℝ) ^ (2 * k + 1) * (Nat.factorial k : ℝ) ^ 2 /
        (Nat.factorial (2 * k + 2) : ℝ) := by
  rw [coefficient]
  rw [if_pos ⟨by omega, by omega⟩]
  simp only [show (2 * k + 2 - 2) / 2 = k by omega]

private theorem evenSeries_summable (x : ℝ) (hx : |x| ≤ 1) :
    Summable (evenSeriesTerm x) := by
  have hxdom : x ∈ ProofGap.Exercise3028.convergenceDomain := by
    rw [ProofGap.Exercise3028.gap4]
    exact abs_le.mp hx
  have hsource :
      Summable (fun k => ProofGap.Exercise3028.term x (k + 1)) :=
    hxdom
  exact (hsource.mul_left (1 / 2 : ℝ)).congr fun k => by
    rw [source_term_eq]
    ring

private theorem powerSeries_hasSum (x : ℝ) (hx : |x| ≤ 1) :
    HasSum (powerSeriesTerm x) (φ x) := by
  have heven := evenSeries_summable x hx
  let p : ℕ → ℝ := fun k => powerSeriesTerm x (2 * k)
  have htail :
      HasSum (fun k => p (k + 1))
        (∑' k, evenSeriesTerm x k) := by
    apply heven.hasSum.congr_fun
    intro k
    change powerSeriesTerm x (2 * (k + 1)) = evenSeriesTerm x k
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      powerSeriesTerm, coefficient_even, evenSeriesTerm]
  have hevenIndices :
      HasSum (fun k => powerSeriesTerm x (2 * k))
        (∑' k, evenSeriesTerm x k) := by
    have h := htail.zero_add
    have hp : p = fun k => powerSeriesTerm x (2 * k) := rfl
    rw [hp] at h
    have hzero : powerSeriesTerm x (2 * 0) = 0 := by
      norm_num [powerSeriesTerm, coefficient]
    simpa only [hzero, zero_add] using h
  have hoddIndices :
      HasSum (fun k => powerSeriesTerm x (2 * k + 1)) 0 := by
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).congr_fun
    intro k
    simp only [powerSeriesTerm, coefficient_odd, zero_mul]
  have hall :=
    hevenIndices.even_add_odd hoddIndices
  rw [even_tsum_eq x hx] at hall
  simpa using hall

private theorem local_gap2 :
    ∀ x : ℝ, |x| < 1 →
      deriv φ x = 2 * Real.arcsin x / Real.sqrt (1 - x ^ 2) := by
  intro x hx
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have ha :=
    Real.hasDerivAt_arcsin (ne_of_gt hxI.1) (ne_of_lt hxI.2)
  have h := (ha.pow 2).deriv
  simpa [φ, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

private theorem local_gap9 :
    ∀ x : ℝ, |x| < 1 →
      Real.sqrt (1 - x ^ 2) * deriv φ x = 2 * Real.arcsin x := by
  intro x hx
  have hq : 0 < 1 - x ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).2 hx)
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  rw [local_gap2 x hx]
  field_simp [hs]

private theorem local_gap10 :
    ∀ x : ℝ, |x| < 1 →
      Real.sqrt (1 - x ^ 2) * iteratedDeriv 2 φ x -
          x * deriv φ x / Real.sqrt (1 - x ^ 2) =
        2 / Real.sqrt (1 - x ^ 2) := by
  intro x hx
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hq : 0 < 1 - x ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).2 hx)
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hqder : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hsder :
      HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hqder using 1 <;>
      field_simp [hs] <;> ring
  have hquot :
      HasDerivAt (fun y : ℝ => 2 / Real.sqrt (1 - y ^ 2))
        (2 * x / Real.sqrt (1 - x ^ 2) ^ 3) x := by
    convert (hasDerivAt_const x (2 : ℝ)).div hsder hs using 1 <;>
      field_simp [hs] <;> ring
  have ha :=
    Real.hasDerivAt_arcsin (ne_of_gt hxI.1) (ne_of_lt hxI.2)
  have heq :
      deriv φ =ᶠ[nhds x]
        (fun y : ℝ => 2 / Real.sqrt (1 - y ^ 2) * Real.arcsin y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy
    rw [local_gap2 y (abs_lt.mpr hy)]
    ring
  have hsecond :
      iteratedDeriv 2 φ x =
        (2 * x / Real.sqrt (1 - x ^ 2) ^ 3) * Real.arcsin x +
          (2 / Real.sqrt (1 - x ^ 2)) *
            (1 / Real.sqrt (1 - x ^ 2)) := by
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ,
      iteratedDeriv_one]
    rw [heq.deriv_eq]
    exact (hquot.mul ha).deriv
  rw [hsecond, local_gap2 x hx]
  field_simp [hs]
  ring

private theorem local_gap11 :
    ∀ x : ℝ, |x| < 1 →
      (1 - x ^ 2) * iteratedDeriv 2 φ x - x * deriv φ x = 2 := by
  intro x hx
  have hq : 0 < 1 - x ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).2 hx)
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hq.le
  have h := local_gap10 x hx
  field_simp [hs] at h
  rw [hs2] at h
  linarith

private def sourceFirstTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) ^ 2 /
      (Nat.factorial (2 * (k + 1)) : ℝ) *
    (4 * ((k + 1 : ℕ) : ℝ)) * (2 * x) ^ (2 * k + 1)

private theorem sourceFirstTerm_eq (x : ℝ) (k : ℕ) :
    sourceFirstTerm x k = 2 * firstDerivativeTerm x (2 * k + 1) := by
  rw [sourceFirstTerm, firstDerivativeTerm]
  simp only [coefficient_even, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_pow]
  ring

private def sourceFirstRatio (x : ℝ) (k : ℕ) : ℝ :=
  (2 * ((k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ)) * x ^ 2

private theorem sourceFirstTerm_succ (x : ℝ) (k : ℕ) :
    sourceFirstTerm x (k + 1) =
      sourceFirstTerm x k * sourceFirstRatio x k := by
  rw [sourceFirstTerm, sourceFirstTerm, sourceFirstRatio]
  rw [Nat.factorial_succ]
  rw [show 2 * (k + 1 + 1) = (2 * (k + 1) + 1) + 1 by omega,
    Nat.factorial_succ]
  rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
    Nat.factorial_succ]
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (((2 * (k + 1) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h3 : (((2 * (k + 1) + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * (k + 1)) : ℝ) ≠ 0 := by positivity
  field_simp [hk, h2, h3, hf]
  push_cast
  ring

private theorem sourceFirstRatio_tendsto (x : ℝ) :
    Filter.Tendsto (sourceFirstRatio x) Filter.atTop (nhds (x ^ 2)) := by
  have hrat :
      Filter.Tendsto
        (fun k : ℕ =>
          (2 * ((k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ)))
        Filter.atTop (nhds 1) := by
    convert tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 2 3 2 (d := 2) (by norm_num) using 1
    · funext k
      push_cast
      ring
    · norm_num
  convert hrat.mul_const (x ^ 2) using 1 <;>
    simp [sourceFirstRatio]

private theorem sourceFirstTerm_summable (x : ℝ) (hx : |x| < 1) :
    Summable (sourceFirstTerm x) := by
  have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  obtain ⟨r, hxr, hr⟩ := exists_between hx2
  have hnorm :
      Filter.Tendsto (fun k : ℕ => ‖sourceFirstRatio x k‖)
        Filter.atTop (nhds (x ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] using
      (sourceFirstRatio_tendsto x).norm
  have hev := hnorm.eventually_le_const hxr
  apply summable_of_ratio_norm_eventually_le hr
  filter_upwards [hev] with k hk
  rw [sourceFirstTerm_succ, norm_mul, mul_comm r]
  exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)

private theorem firstDerivative_tsum_eq_source (x : ℝ) (hx : |x| < 1) :
    (∑' k, firstDerivativeTerm x k) =
      (1 / 2 : ℝ) * ∑' k, sourceFirstTerm x k := by
  have hsource := sourceFirstTerm_summable x hx
  have hodd :
      HasSum (fun k => firstDerivativeTerm x (2 * k + 1))
        ((1 / 2 : ℝ) * ∑' k, sourceFirstTerm x k) := by
    apply (hsource.hasSum.mul_left (1 / 2 : ℝ)).congr_fun
    intro k
    rw [sourceFirstTerm_eq]
    ring
  have heven :
      HasSum (fun k => firstDerivativeTerm x (2 * k)) 0 := by
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).congr_fun
    intro k
    rw [firstDerivativeTerm]
    simp only [show 2 * k + 1 = 2 * k + 1 by rfl, coefficient_odd,
      mul_zero, zero_mul]
  simpa only [zero_add] using (heven.even_add_odd hodd).tsum_eq

private theorem local_gap3 :
    ∀ x : ℝ, |x| < 1 →
      2 * Real.arcsin x / Real.sqrt (1 - x ^ 2) =
        ∑' k, firstDerivativeTerm x k := by
  intro x hx
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hseries := ProofGap.Exercise3028.gap6 x hxI
  have hvalue := ProofGap.Exercise3028.gap13 x hxI
  have hsource :
      (∑' k, sourceFirstTerm x k) =
        ∑' n : ℕ,
          (((n : ℕ).factorial : ℝ) ^ 2 /
            ((2 * (n + 1)).factorial : ℝ)) *
            (4 * ((n + 1 : ℕ) : ℝ)) * (2 * x) ^ (2 * n + 1) := by
    apply tsum_congr
    intro k
    rfl
  rw [← hsource] at hseries
  rw [hvalue] at hseries
  rw [firstDerivative_tsum_eq_source x hx]
  calc
    2 * Real.arcsin x / Real.sqrt (1 - x ^ 2) =
        (1 / 2 : ℝ) *
          (4 * Real.arcsin x / Real.sqrt (1 - x ^ 2)) := by ring
    _ = (1 / 2 : ℝ) * ∑' k, sourceFirstTerm x k := by rw [hseries]

private def sourceSecondTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) ^ 2 /
      (Nat.factorial (2 * (k + 1)) : ℝ) *
    (8 * ((k + 1 : ℕ) : ℝ) *
      (2 * ((k + 1 : ℕ) : ℝ) - 1)) *
    (2 * x) ^ (2 * k)

private theorem sourceSecondTerm_eq (x : ℝ) (k : ℕ) :
    sourceSecondTerm x k = 2 * secondDerivativeTerm x (2 * k) := by
  rw [sourceSecondTerm, secondDerivativeTerm]
  simp only [coefficient_even, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_pow]
  ring

private def sourceSecondRatio (x : ℝ) (k : ℕ) : ℝ :=
  (2 * ((k + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) * x ^ 2

private theorem sourceSecondTerm_succ (x : ℝ) (k : ℕ) :
    sourceSecondTerm x (k + 1) =
      sourceSecondTerm x k * sourceSecondRatio x k := by
  rw [sourceSecondTerm, sourceSecondTerm, sourceSecondRatio]
  rw [Nat.factorial_succ]
  rw [show 2 * (k + 1 + 1) = (2 * (k + 1) + 1) + 1 by omega,
    Nat.factorial_succ]
  rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
    Nat.factorial_succ]
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h1 : (((2 * k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h2 : (((2 * (k + 1) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h3 : (((2 * (k + 1) + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * (k + 1)) : ℝ) ≠ 0 := by positivity
  field_simp [hk, h1, h2, h3, hf]
  push_cast
  ring

private theorem sourceSecondRatio_tendsto (x : ℝ) :
    Filter.Tendsto (sourceSecondRatio x) Filter.atTop (nhds (x ^ 2)) := by
  have hrat :
      Filter.Tendsto
        (fun k : ℕ =>
          (2 * ((k + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 1) := by
    convert tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 2 1 2 (d := 2) (by norm_num) using 1
    · funext k
      push_cast
      ring
    · norm_num
  convert hrat.mul_const (x ^ 2) using 1 <;> simp

private theorem sourceSecondTerm_summable (x : ℝ) (hx : |x| < 1) :
    Summable (sourceSecondTerm x) := by
  have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  obtain ⟨r, hxr, hr⟩ := exists_between hx2
  have hnorm :
      Filter.Tendsto (fun k : ℕ => ‖sourceSecondRatio x k‖)
        Filter.atTop (nhds (x ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] using
      (sourceSecondRatio_tendsto x).norm
  have hev := hnorm.eventually_le_const hxr
  apply summable_of_ratio_norm_eventually_le hr
  filter_upwards [hev] with k hk
  rw [sourceSecondTerm_succ, norm_mul, mul_comm r]
  exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)

private theorem secondDerivative_tsum_eq_source (x : ℝ) (hx : |x| < 1) :
    (∑' k, secondDerivativeTerm x k) =
      (1 / 2 : ℝ) * ∑' k, sourceSecondTerm x k := by
  have hsource := sourceSecondTerm_summable x hx
  have heven :
      HasSum (fun k => secondDerivativeTerm x (2 * k))
        ((1 / 2 : ℝ) * ∑' k, sourceSecondTerm x k) := by
    apply (hsource.hasSum.mul_left (1 / 2 : ℝ)).congr_fun
    intro k
    rw [sourceSecondTerm_eq]
    ring
  have hodd :
      HasSum (fun k => secondDerivativeTerm x (2 * k + 1)) 0 := by
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).congr_fun
    intro k
    rw [secondDerivativeTerm]
    have hindex : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by omega
    rw [hindex, coefficient_odd]
    ring
  simpa only [add_zero] using (heven.even_add_odd hodd).tsum_eq

private theorem secondDerivative_tsum_eq_iterated (x : ℝ) (hx : |x| < 1) :
    (∑' k, secondDerivativeTerm x k) = iteratedDeriv 2 φ x := by
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hseries := ProofGap.Exercise3028.gap7 x hxI
  have hsource :
      (∑' k, sourceSecondTerm x k) =
        ∑' n : ℕ,
          (((n : ℕ).factorial : ℝ) ^ 2 /
            ((2 * (n + 1)).factorial : ℝ)) *
            (8 * ((n + 1 : ℕ) : ℝ) *
              (2 * ((n + 1 : ℕ) : ℝ) - 1)) *
            (2 * x) ^ (2 * n) := by
    apply tsum_congr
    intro k
    rfl
  rw [← hsource] at hseries
  have heq :
      deriv ProofGap.Exercise3028.f =ᶠ[nhds x]
        (fun y => 2 * deriv φ y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy
    rw [ProofGap.Exercise3028.gap13 y hy, local_gap2 y (abs_lt.mpr hy)]
    ring
  have hderiv := heq.deriv_eq
  rw [deriv_const_mul_field'] at hderiv
  rw [secondDerivative_tsum_eq_source x hx]
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ,
    iteratedDeriv_one]
  rw [hseries] at hderiv
  have hderiv' :
      (∑' k, sourceSecondTerm x k) = 2 * deriv (deriv φ) x := by
    simpa using hderiv
  calc
    (1 / 2 : ℝ) * ∑' k, sourceSecondTerm x k =
        (1 / 2 : ℝ) * (2 * deriv (deriv φ) x) := by rw [hderiv']
    _ = deriv (deriv φ) x := by ring

private theorem local_gap12 :
    ∀ x : ℝ, |x| < 1 →
      (1 - x ^ 2) * (∑' k, secondDerivativeTerm x k) -
        (∑' k, shiftedFirstDerivativeTerm x k) = 2 := by
  intro x hx
  have hfirst := firstDerivative_tsum_eq_source x hx
  have hsfirst := sourceFirstTerm_summable x hx
  have hfirstSummable : Summable (firstDerivativeTerm x) := by
    have heven :
        Summable (fun k => firstDerivativeTerm x (2 * k)) := by
      simpa [firstDerivativeTerm, coefficient_odd] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    have hodd :
        Summable (fun k => firstDerivativeTerm x (2 * k + 1)) := by
      exact (hsfirst.mul_left (1 / 2 : ℝ)).congr fun k => by
        rw [sourceFirstTerm_eq]
        ring
    exact heven.even_add_odd hodd
  have htail : Summable (fun k => firstDerivativeTerm x (k + 1)) :=
    hfirstSummable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hshift :
      (∑' k, shiftedFirstDerivativeTerm x k) =
        x * ∑' k, firstDerivativeTerm x k := by
    have hterms :
        (∑' k, shiftedFirstDerivativeTerm x k) =
          ∑' k, x * firstDerivativeTerm x (k + 1) := by
      apply tsum_congr
      intro k
      rw [shiftedFirstDerivativeTerm, firstDerivativeTerm]
      have hpow : x ^ (k + 2) = x * x ^ (k + 1) := by
        rw [show k + 2 = 1 + (k + 1) by omega, pow_add]
        simp
      rw [hpow]
      push_cast
      ring
    rw [hterms, htail.tsum_mul_left]
    have hdrop := hfirstSummable.sum_add_tsum_nat_add 1
    simpa [firstDerivativeTerm, coefficient] using congrArg (fun y => x * y) hdrop
  rw [secondDerivative_tsum_eq_iterated x hx, hshift,
    ← local_gap3 x hx, ← local_gap2 x hx]
  exact local_gap11 x hx

private theorem secondDerivative_summable (x : ℝ) (hx : |x| < 1) :
    Summable (secondDerivativeTerm x) := by
  have hsource := sourceSecondTerm_summable x hx
  have heven :
      Summable (fun k => secondDerivativeTerm x (2 * k)) :=
    (hsource.mul_left (1 / 2 : ℝ)).congr fun k => by
      rw [sourceSecondTerm_eq]
      ring
  have hodd :
      Summable (fun k => secondDerivativeTerm x (2 * k + 1)) := by
    simpa only [secondDerivativeTerm,
      show ∀ k : ℕ, 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega,
      coefficient_odd, mul_zero, zero_mul] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  exact heven.even_add_odd hodd

private theorem shiftedFirstDerivative_summable (x : ℝ) (hx : |x| < 1) :
    Summable (shiftedFirstDerivativeTerm x) := by
  have hfirst : Summable (firstDerivativeTerm x) := by
    have hsource := sourceFirstTerm_summable x hx
    have heven :
        Summable (fun k => firstDerivativeTerm x (2 * k)) := by
      simpa [firstDerivativeTerm, coefficient_odd] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    have hodd :
        Summable (fun k => firstDerivativeTerm x (2 * k + 1)) :=
      (hsource.mul_left (1 / 2 : ℝ)).congr fun k => by
        rw [sourceFirstTerm_eq]
        ring
    exact heven.even_add_odd hodd
  have htail : Summable (fun k => firstDerivativeTerm x (k + 1)) :=
    hfirst.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  exact (htail.mul_left x).congr fun k => by
    rw [shiftedFirstDerivativeTerm, firstDerivativeTerm]
    have hpow : x ^ (k + 2) = x * x ^ (k + 1) := by
      rw [show k + 2 = 1 + (k + 1) by omega, pow_add]
      simp
    rw [hpow]
    push_cast
    ring

private theorem local_gap13 :
    ∀ x : ℝ, |x| < 1 →
      (∑' k, secondDerivativeTerm x k) -
      (∑' k,
          let n : ℕ := k + 2
          (n : ℝ) ^ 2 * coefficient n * x ^ n) = 2 := by
  intro x hx
  let Q : ℕ → ℝ := fun k =>
    let n : ℕ := k + 2
    (n : ℝ) ^ 2 * coefficient n * x ^ n
  have hs2 := secondDerivative_summable x hx
  have hshift := shiftedFirstDerivative_summable x hx
  have hQ :
      (∑' k, Q k) =
        x ^ 2 * (∑' k, secondDerivativeTerm x k) +
          ∑' k, shiftedFirstDerivativeTerm x k := by
    rw [← hs2.tsum_mul_left (x ^ 2)]
    rw [← (hs2.mul_left (x ^ 2)).tsum_add hshift]
    apply tsum_congr
    intro k
    simp only [Q, secondDerivativeTerm, shiftedFirstDerivativeTerm]
    have hpow : x ^ (k + 2) = x ^ 2 * x ^ k := by
      rw [show k + 2 = 2 + k by omega, pow_add]
    rw [hpow]
    push_cast
    ring
  change (∑' k, secondDerivativeTerm x k) - ∑' k, Q k = 2
  rw [hQ]
  have h := local_gap12 x hx
  ring_nf at h ⊢
  linarith

private theorem coefficient_of_mod_ne (n : ℕ) (hn : n % 2 ≠ 0) :
    coefficient n = 0 := by
  rw [coefficient, if_neg]
  intro h
  exact hn h.1

private theorem coefficient_recurrence (n : ℕ) (hn : 2 ≤ n) :
    coefficient (n + 2) =
      ((n : ℝ) ^ 2 / ((n + 2 : ℝ) * (n + 1 : ℝ))) *
        coefficient n := by
  by_cases heven : n % 2 = 0
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 := by
      refine ⟨(n - 2) / 2, ?_⟩
      omega
    subst n
    rw [show 2 * k + 2 + 2 = 2 * (k + 1) + 2 by omega]
    rw [coefficient_even (k + 1), coefficient_even k]
    rw [Nat.factorial_succ]
    rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega,
      Nat.factorial_succ]
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega,
      Nat.factorial_succ]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
      pow_add]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (((2 * k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    have h3 : (((2 * k + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
    have h4 : (((2 * k + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hf : (Nat.factorial (2 * k + 2) : ℝ) ≠ 0 := by positivity
    field_simp [hk1, h2, h3, h4, hf]
    push_cast
    ring
  · have heven2 : (n + 2) % 2 ≠ 0 := by omega
    rw [coefficient_of_mod_ne n heven,
      coefficient_of_mod_ne (n + 2) heven2, mul_zero]

private theorem combinedResidualTerm_zero (x : ℝ) (k : ℕ) :
    combinedResidualTerm x k = 0 := by
  rw [combinedResidualTerm]
  rw [coefficient_recurrence (k + 2) (by omega)]
  have h1 : ((k : ℝ) + 3) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 4) ≠ 0 := by positivity
  push_cast
  field_simp [h1, h2]
  ring

private theorem evenSeriesTerm_eq_mul_divided (x : ℝ) (k : ℕ) :
    evenSeriesTerm x k = x ^ 2 * dividedEvenSeriesTerm x k := by
  rw [evenSeriesTerm, dividedEvenSeriesTerm]
  rw [show x ^ (2 * k + 2) = x ^ 2 * x ^ (2 * k) by
    rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add]]
  ring

private theorem divided_tsum_eq (x : ℝ) (hx0 : x ≠ 0) (hx : |x| ≤ 1) :
    (Real.arcsin x / x) ^ 2 =
      ∑' k, dividedEvenSeriesTerm x k := by
  have hdiv : Summable (dividedEvenSeriesTerm x) := by
    have h :=
      (evenSeries_summable x hx).mul_left (x ^ 2)⁻¹
    refine h.congr (fun k => ?_)
    rw [evenSeriesTerm_eq_mul_divided]
    field_simp
  have hsum :
      (∑' k, evenSeriesTerm x k) =
        x ^ 2 * ∑' k, dividedEvenSeriesTerm x k := by
    rw [← hdiv.tsum_mul_left (x ^ 2)]
    exact tsum_congr (evenSeriesTerm_eq_mul_divided x)
  have hphi :
      φ x = x ^ 2 * ∑' k, dividedEvenSeriesTerm x k := by
    calc
      φ x = ∑' k, evenSeriesTerm x k := (even_tsum_eq x hx).symm
      _ = x ^ 2 * ∑' k, dividedEvenSeriesTerm x k := hsum
  rw [φ] at hphi
  field_simp [hx0]
  nlinarith

theorem gap1 :
    ∀ x : ℝ, |x| ≤ 1 → φ x = ∑' n, powerSeriesTerm x n := by
  intro x hx
  exact (powerSeries_hasSum x hx).tsum_eq.symm

theorem gap2 :
    ∀ x : ℝ, |x| < 1 →
      deriv φ x = 2 * Real.arcsin x / Real.sqrt (1 - x ^ 2) := by
  exact local_gap2

theorem gap3 :
    ∀ x : ℝ, |x| < 1 →
      2 * Real.arcsin x / Real.sqrt (1 - x ^ 2) =
        ∑' k, firstDerivativeTerm x k := by
  exact local_gap3

theorem gap4 :
    ∀ x : ℝ, |x| < 1 →
      deriv φ x = ∑' k, firstDerivativeTerm x k := by
  intro x hx
  rw [local_gap2 x hx, local_gap3 x hx]

theorem gap5 :
    φ 0 = 0 := by
  norm_num [φ]

theorem gap6 :
    deriv φ 0 = 0 := by
  rw [local_gap2 0 (by norm_num)]
  norm_num

theorem gap7 :
    coefficient 0 = 0 := by
  norm_num [coefficient]

theorem gap8 :
    coefficient 1 = 0 := by
  norm_num [coefficient]

theorem gap9 :
    ∀ x : ℝ, |x| < 1 →
      Real.sqrt (1 - x ^ 2) * deriv φ x = 2 * Real.arcsin x := by
  exact local_gap9

theorem gap10 :
    ∀ x : ℝ, |x| < 1 →
      Real.sqrt (1 - x ^ 2) * iteratedDeriv 2 φ x -
          x * deriv φ x / Real.sqrt (1 - x ^ 2) =
        2 / Real.sqrt (1 - x ^ 2) := by
  exact local_gap10

theorem gap11 :
    ∀ x : ℝ, |x| < 1 →
      (1 - x ^ 2) * iteratedDeriv 2 φ x - x * deriv φ x = 2 := by
  exact local_gap11

theorem gap12 :
    ∀ x : ℝ, |x| < 1 →
      (1 - x ^ 2) * (∑' k, secondDerivativeTerm x k) -
        (∑' k, shiftedFirstDerivativeTerm x k) = 2 := by
  exact local_gap12

theorem gap13 :
    ∀ x : ℝ, |x| < 1 →
      (∑' k, secondDerivativeTerm x k) -
      (∑' k,
          let n : ℕ := k + 2
          (n : ℝ) ^ 2 * coefficient n * x ^ n) = 2 := by
  exact local_gap13

theorem gap14 :
    ∀ x : ℝ, |x| < 1 →
      2 * coefficient 2 + 6 * coefficient 3 * x +
        (∑' k, combinedResidualTerm x k) = 2 := by
  intro x hx
  norm_num [coefficient, combinedResidualTerm_zero]

theorem gap15 :
    coefficient 2 = 1 := by
  norm_num [coefficient]

theorem gap16 :
    coefficient 3 = 0 := by
  norm_num [coefficient]

theorem gap17 :
    ∀ n : ℕ, 2 ≤ n →
      coefficient (n + 2) =
        ((n : ℝ) ^ 2 / ((n + 2 : ℝ) * (n + 1 : ℝ))) *
          coefficient n := by
  exact coefficient_recurrence

theorem gap18 :
    ∀ k : ℕ, coefficient (2 * k + 1) = 0 := by
  exact coefficient_odd

theorem gap19 :
    ∀ k : ℕ, coefficient (2 * k + 2) =
      (2 : ℝ) ^ (2 * k + 1) * (Nat.factorial k : ℝ) ^ 2 /
        (Nat.factorial (2 * k + 2) : ℝ) := by
  exact coefficient_even

theorem gap20 :
    ∀ x : ℝ, |x| ≤ 1 → φ x = ∑' k, evenSeriesTerm x k := by
  intro x hx
  exact (even_tsum_eq x hx).symm

theorem gap21 :
    ∀ x : ℝ, x ≠ 0 → |x| < 1 →
      (Real.arcsin x / x) ^ 2 =
        ∑' k, dividedEvenSeriesTerm x k := by
  intro x hx0 hx
  exact divided_tsum_eq x hx0 hx.le

theorem gap22 :
    ∀ x : ℝ, x ≠ 0 → |x| ≤ 1 →
      (Real.arcsin x / x) ^ 2 =
        ∑' k, dividedEvenSeriesTerm x k := by
  exact divided_tsum_eq

end

end ProofGap.Exercise2890
