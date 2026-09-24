import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise3028
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace ProofGap.Exercise3029

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ)

def term (x : ℝ) (n : ℕ) : ℝ := coefficient n * x ^ n

def seriesFunction (x : ℝ) : ℝ := ∑' n : ℕ, term x n

def convergenceDomain : Set ℝ := {x | Summable (term x)}

def powerSeriesRadius : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r → Summable (term x)}

def asinSquare (t : ℝ) : ℝ := 2 * Real.arcsin t ^ 2

def F (t : ℝ) : ℝ := seriesFunction (4 * t ^ 2)

def derivativeSeries (t : ℝ) : ℝ :=
  ∑' n : ℕ,
    (((n : ℕ).factorial : ℝ) ^ 2 / ((2 * (n + 1)).factorial : ℝ)) *
      (4 * ((n + 1 : ℕ) : ℝ)) * (2 * t) ^ (2 * n + 1)

def g (t : ℝ) : ℝ :=
  ∑' n : ℕ,
    (-1 : ℝ) ^ n *
      (((n : ℕ).factorial : ℝ) ^ 2 / ((2 * (n + 1)).factorial : ℝ)) *
      ((n + 1 : ℕ) : ℝ) * (2 * t) ^ (2 * n + 1)

def G (t : ℝ) : ℝ := seriesFunction (-4 * t ^ 2)

def positiveClosedForm (x : ℝ) : ℝ :=
  4 / (4 - x) +
    4 * Real.sqrt x / ((4 - x) * Real.sqrt (4 - x)) *
      Real.arcsin (Real.sqrt x / 2)

def negativeClosedForm (x : ℝ) : ℝ :=
  4 / (4 - x) -
    4 * Real.sqrt |x| / ((4 - x) * Real.sqrt (4 - x)) *
      Real.log ((Real.sqrt |x| + Real.sqrt (4 - x)) / 2)

private def ratioModel (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) ^ 2) /
    ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1))

private theorem ratioModel_tendsto :
    Tendsto ratioModel atTop (𝓝 (1 / 4 : ℝ)) := by
  have h₁ :=
    tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 1 2 1 (d := 2) (by norm_num)
  have h₂ :=
    tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 1 1 1 (d := 2) (by norm_num)
  have h := h₁.mul h₂
  convert h using 1
  · funext n
    unfold ratioModel
    push_cast
    field_simp
    ring
  · norm_num

private theorem coefficient_pos (n : ℕ) :
    0 < coefficient n := by
  unfold coefficient
  positivity

private theorem coefficient_ne_zero (n : ℕ) :
    coefficient n ≠ 0 :=
  (coefficient_pos n).ne'

private theorem coefficient_ratio_eq (n : ℕ) :
    coefficient (n + 1) / coefficient n = ratioModel n := by
  unfold coefficient ratioModel
  rw [Nat.factorial_succ]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

private theorem ratioModel_pos (n : ℕ) :
    0 < ratioModel n := by
  unfold ratioModel
  positivity

private theorem term_ratio_eq (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    term x (n + 1) / term x n = ratioModel n * x := by
  calc
    term x (n + 1) / term x n =
        (coefficient (n + 1) / coefficient n) * x := by
      unfold term
      rw [pow_succ]
      field_simp [coefficient_ne_zero n, hx]
    _ = ratioModel n * x := by rw [coefficient_ratio_eq]

private theorem term_norm_ratio_eq (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    ‖term x (n + 1)‖ / ‖term x n‖ =
      ratioModel n * |x| := by
  rw [← norm_div, term_ratio_eq x hx n, Real.norm_eq_abs,
    abs_mul, abs_of_pos (ratioModel_pos n)]

private theorem term_norm_ratio_tendsto (x : ℝ) (hx : x ≠ 0) :
    Tendsto
      (fun n : ℕ => ‖term x (n + 1)‖ / ‖term x n‖)
      atTop (𝓝 (|x| / 4)) := by
  have h := ratioModel_tendsto.mul_const |x|
  convert h using 1
  · funext n
    exact term_norm_ratio_eq x hx n
  · ring

private theorem boundary_ratio_eq
    (x : ℝ) (hx : |x| = 4) (n : ℕ) :
    |term x (n + 1) / term x n| =
      (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  rw [term_ratio_eq x hx0, abs_mul,
    abs_of_pos (ratioModel_pos n), hx]
  unfold ratioModel
  field_simp
  push_cast
  ring

private theorem boundary_ratio_gt (n : ℕ) :
    1 < (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) := by
  apply (lt_div_iff₀ (by positivity)).2
  linarith

private theorem boundary_abs_ratio_gt
    (x : ℝ) (hx : |x| = 4) (n : ℕ) :
    1 < |term x (n + 1) / term x n| := by
  rw [boundary_ratio_eq x hx n]
  exact boundary_ratio_gt n

private theorem boundary_abs_term_lt
    (x : ℝ) (hx : |x| = 4) (n : ℕ) :
    |term x n| < |term x (n + 1)| := by
  have hterm : term x n ≠ 0 := by
    unfold term
    exact mul_ne_zero (coefficient_ne_zero n)
      (pow_ne_zero n (abs_ne_zero.mp (by simpa [hx])))
  have hratio := boundary_abs_ratio_gt x hx n
  rw [abs_div, div_eq_mul_inv] at hratio
  have habs : 0 < |term x n| := abs_pos.mpr hterm
  have hratio' :
      1 < |term x (n + 1)| / |term x n| := by
    simpa [div_eq_mul_inv] using hratio
  have hmul := (lt_div_iff₀ habs).mp hratio'
  simpa using hmul

private theorem abs_term_ge_one_of_boundary
    (x : ℝ) (hx : |x| = 4) :
    ∀ n : ℕ, 1 ≤ |term x n| := by
  intro n
  induction n with
  | zero =>
      norm_num [term, coefficient]
  | succ n ih =>
      exact ih.trans (boundary_abs_term_lt x hx n).le

private theorem term_not_summable_of_boundary
    (x : ℝ) (hx : |x| = 4) :
    ¬Summable (term x) := by
  intro hsum
  have htend :
      Tendsto (fun n : ℕ => |term x n|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using
      hsum.tendsto_atTop_zero.norm
  have hev : ∀ᶠ n : ℕ in atTop, |term x n| < (1 / 2 : ℝ) :=
    (tendsto_order.1 htend).2 _ (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsmall := hN N le_rfl
  linarith [abs_term_ge_one_of_boundary x hx N]

private theorem term_summable_iff (x : ℝ) :
    Summable (term x) ↔ |x| < 4 := by
  by_cases hx0 : x = 0
  · subst x
    constructor
    · intro
      norm_num
    · intro
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      unfold term
      rw [zero_pow hn, mul_zero]
  constructor
  · intro hsum
    by_contra hlt
    have hge : 4 ≤ |x| := le_of_not_gt hlt
    rcases hge.eq_or_lt with heq | hgt
    · exact term_not_summable_of_boundary x heq.symm hsum
    · have hlim : 1 < |x| / 4 := by linarith
      exact
        (not_summable_of_ratio_test_tendsto_gt_one
          hlim (term_norm_ratio_tendsto x hx0)) hsum
  · intro hlt
    have hlim : |x| / 4 < 1 := by linarith
    apply summable_of_ratio_test_tendsto_lt_one
      (f := term x) hlim
    · apply Eventually.of_forall
      intro n
      unfold term
      exact mul_ne_zero (coefficient_ne_zero n)
        (pow_ne_zero n hx0)
    · exact term_norm_ratio_tendsto x hx0

theorem gap1 :
    Tendsto (fun n : ℕ => coefficient (n + 1) / coefficient n)
        atTop (𝓝 (1 / 4)) ∧
      Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ) ^ 2) /
            ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1)))
        atTop (𝓝 (1 / 4)) := by
  constructor
  · convert ratioModel_tendsto using 1
    funext n
    exact coefficient_ratio_eq n
  · exact ratioModel_tendsto

theorem gap2 :
    Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ 2) /
          ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1)))
      atTop (𝓝 (1 / 4)) := by
  exact ratioModel_tendsto

theorem gap3 :
    Tendsto (fun n : ℕ => coefficient (n + 1) / coefficient n)
      atTop (𝓝 (1 / 4)) := by
  convert ratioModel_tendsto using 1
  funext n
  exact coefficient_ratio_eq n

theorem gap4 : powerSeriesRadius = 4 := by
  have hset :
      {r : ℝ | 0 ≤ r ∧
        ∀ x : ℝ, |x| < r → Summable (term x)} =
        Set.Icc (0 : ℝ) 4 := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hr0, hr⟩
      refine ⟨hr0, ?_⟩
      by_contra hle
      have hr4 : 4 < r := lt_of_not_ge hle
      let x : ℝ := (r + 4) / 2
      have hxpos : 0 < x := by
        dsimp [x]
        linarith
      have hxr : |x| < r := by
        rw [abs_of_pos hxpos]
        dsimp [x]
        linarith
      have hx4 := (term_summable_iff x).mp (hr x hxr)
      rw [abs_of_pos hxpos] at hx4
      dsimp [x] at hx4
      linarith
    · rintro ⟨hr0, hr4⟩
      refine ⟨hr0, ?_⟩
      intro x hx
      exact (term_summable_iff x).mpr (lt_of_lt_of_le hx hr4)
  unfold powerSeriesRadius
  rw [hset]
  norm_num

theorem gap5 (x : ℝ) (hx : |x| = 4) (n : ℕ) :
    |term x (n + 1) / term x n| =
      (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) := by
  exact boundary_ratio_eq x hx n

theorem gap6 (x : ℝ) (hx : |x| = 4) (n : ℕ) :
    1 < (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) := by
  exact boundary_ratio_gt n

theorem gap7 (x : ℝ) (hx : |x| = 4) (n : ℕ) :
    1 < |term x (n + 1) / term x n| := by
  exact boundary_abs_ratio_gt x hx n

theorem gap8 (x : ℝ) (hx : |x| = 4) (n : ℕ) :
    |term x n| < |term x (n + 1)| := by
  exact boundary_abs_term_lt x hx n

theorem gap9 (x : ℝ) (hx : |x| = 4) :
    ¬Summable (term x) := by
  exact term_not_summable_of_boundary x hx

theorem gap10 : convergenceDomain = Set.Ioo (-4) 4 := by
  ext x
  simp only [convergenceDomain, Set.mem_setOf_eq, Set.mem_Ioo]
  rw [term_summable_iff, abs_lt]

private def derivativeTerm (t : ℝ) (n : ℕ) : ℝ :=
  (((n : ℕ).factorial : ℝ) ^ 2 /
      ((2 * (n + 1)).factorial : ℝ)) *
    (4 * ((n + 1 : ℕ) : ℝ)) * (2 * t) ^ (2 * n + 1)

private def alternatingTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n *
    (((n : ℕ).factorial : ℝ) ^ 2 /
      ((2 * (n + 1)).factorial : ℝ)) *
    ((n + 1 : ℕ) : ℝ) * (2 * t) ^ (2 * n + 1)

private theorem derivativeTerm_scaled_eq (t : ℝ) (n : ℕ) :
    t / 4 * derivativeTerm t n =
      term (4 * t ^ 2) (n + 1) -
        t ^ 2 * term (4 * t ^ 2) n := by
  unfold derivativeTerm term coefficient
  rw [Nat.factorial_succ]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  have hp : (t * 2) ^ (2 * n) = (t ^ 2 * 4) ^ n := by
    rw [pow_mul]
    congr 1
    ring
  rw [show 2 * n + 1 = 2 * n + 1 by omega, pow_add, hp]
  ring

private theorem alternatingTerm_scaled_eq (t : ℝ) (n : ℕ) :
    t * alternatingTerm t n =
      -term (-4 * t ^ 2) (n + 1) -
        t ^ 2 * term (-4 * t ^ 2) n := by
  unfold alternatingTerm term coefficient
  rw [Nat.factorial_succ]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  have hp : (t * 2) ^ (2 * n) = (t ^ 2 * 4) ^ n := by
    rw [pow_mul]
    congr 1
    ring
  rw [show 2 * n + 1 = 2 * n + 1 by omega, pow_add, hp]
  rw [neg_pow (t ^ 2 * 4) (n + 1), neg_pow (t ^ 2 * 4) n,
    pow_succ (-1 : ℝ) n, pow_succ (t ^ 2 * 4) n]
  ring

private theorem abs_t_lt_one_of_positive_substitution
    {x t : ℝ} (hx4 : x < 4) (ht : x = (2 * t) ^ 2) :
    |t| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one t).mp
  rw [ht] at hx4
  nlinarith [sq_nonneg t]

private theorem abs_t_lt_one_of_negative_substitution
    {x t : ℝ} (hx4 : -4 < x) (ht : x = -(2 * t) ^ 2) :
    |t| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one t).mp
  rw [ht] at hx4
  nlinarith [sq_nonneg t]

private theorem derivativeSeries_eq_deriv_asinSquare (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    derivativeSeries t = deriv asinSquare t := by
  calc
    derivativeSeries t = deriv ProofGap.Exercise3028.f t := by
      simpa [derivativeSeries] using
        (ProofGap.Exercise3028.gap6 t ht).symm
    _ = deriv asinSquare t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
      simpa [asinSquare] using
        (ProofGap.Exercise3028.gap17 y ⟨hy.1.le, hy.2.le⟩)

private theorem hasDerivAt_asinSquare (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt asinSquare
      (4 * Real.arcsin t / Real.sqrt (1 - t ^ 2)) t := by
  have hasin :=
    Real.hasDerivAt_arcsin (ne_of_gt ht.1) (ne_of_lt ht.2)
  unfold asinSquare
  convert (hasin.pow 2).const_mul 2 using 1
  ring

private def alternatingDerivTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n *
    (((n : ℕ).factorial : ℝ) ^ 2 /
      ((2 * (n + 1)).factorial : ℝ)) *
    (2 * ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) *
    (2 * t) ^ (2 * n)

private def alternatingDerivMajorant (t : ℝ) (n : ℕ) : ℝ :=
  (((n : ℕ).factorial : ℝ) ^ 2 /
      ((2 * (n + 1)).factorial : ℝ)) *
    (2 * ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) *
    (2 * t) ^ (2 * n)

private theorem hasDerivAt_alternatingTerm (t : ℝ) (n : ℕ) :
    HasDerivAt (fun y => alternatingTerm y n)
      (alternatingDerivTerm t n) t := by
  have hpow : 2 * n + 1 - 1 = 2 * n := by omega
  unfold alternatingTerm alternatingDerivTerm
  convert (((hasDerivAt_id t).const_mul 2).pow (2 * n + 1)).const_mul
    (((-1 : ℝ) ^ n *
      (((n : ℕ).factorial : ℝ) ^ 2 /
        ((2 * (n + 1)).factorial : ℝ)) *
      ((n + 1 : ℕ) : ℝ))) using 1 <;>
    simp [id_eq, hpow] <;> push_cast <;> ring

private theorem alternatingDerivMajorant_nonneg
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ alternatingDerivMajorant t n := by
  unfold alternatingDerivMajorant
  rw [show 2 * n = n * 2 by omega, pow_mul]
  positivity

private theorem alternatingDerivMajorant_ne_zero
    (t : ℝ) (ht : t ≠ 0) (n : ℕ) :
    alternatingDerivMajorant t n ≠ 0 := by
  unfold alternatingDerivMajorant
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply div_ne_zero <;> positivity
    · positivity
  · exact pow_ne_zero _ (mul_ne_zero (by norm_num) ht)

private theorem alternatingDerivMajorant_ratio_eq
    (t : ℝ) (ht : t ≠ 0) (n : ℕ) :
    alternatingDerivMajorant t (n + 1) /
        alternatingDerivMajorant t n =
      (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) * t ^ 2 := by
  unfold alternatingDerivMajorant
  rw [Nat.factorial_succ]
  rw [show 2 * (n + 1 + 1) = (2 * (n + 1) + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  push_cast
  have hfac : (((n.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpow : (2 * t) ^ (2 * n) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) ht)
  field_simp [hfac, hpow, ht]
  ring

private theorem alternatingDerivMajorant_ratio_tendsto (t : ℝ)
    (ht : t ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        alternatingDerivMajorant t (n + 1) /
          alternatingDerivMajorant t n)
      atTop (𝓝 (t ^ 2)) := by
  have hlin :=
    tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 2 1 2 (d := 2) (by norm_num)
  have h := hlin.mul_const (t ^ 2)
  convert h using 1
  · funext n
    rw [alternatingDerivMajorant_ratio_eq t ht n]
    ring
  · norm_num

private theorem summable_alternatingDerivMajorant
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Summable (alternatingDerivMajorant t) := by
  apply summable_of_ratio_test_tendsto_lt_one
      (show t ^ 2 < 1 by nlinarith)
  · exact Filter.Eventually.of_forall fun n =>
      alternatingDerivMajorant_ne_zero t ht0.ne' n
  · convert alternatingDerivMajorant_ratio_tendsto t ht0.ne' using 1
    funext n
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (alternatingDerivMajorant_nonneg t ht0.le (n + 1)),
      abs_of_nonneg (alternatingDerivMajorant_nonneg t ht0.le n)]

private theorem norm_alternatingDerivTerm_le
    (r y : ℝ) (hr : 0 < r) (hy : y ∈ Set.Ioo (-r) r) (n : ℕ) :
    ‖alternatingDerivTerm y n‖ ≤ alternatingDerivMajorant r n := by
  have hay : |y| ≤ r := (abs_lt.mpr hy).le
  have hbase : |2 * y| ≤ 2 * r := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  unfold alternatingDerivTerm alternatingDerivMajorant
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
    abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤
        2 * ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1))]
  norm_num only [one_mul]
  gcongr

private theorem summable_alternatingDerivTerm_interior (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    Summable (alternatingDerivTerm t) := by
  have htAbs : |t| < 1 := abs_lt.mpr ht
  obtain ⟨r, htr, hr1⟩ := exists_between htAbs
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) htr
  exact (summable_alternatingDerivMajorant r hr0 hr1).of_norm_bounded
    (fun n =>
      norm_alternatingDerivTerm_le r t hr0 (abs_lt.mp htr) n)

private theorem hasDerivAt_g_interior (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt g (∑' n : ℕ, alternatingDerivTerm t n) t := by
  have htAbs : |t| < 1 := abs_lt.mpr ht
  obtain ⟨r, htr, hr1⟩ := exists_between htAbs
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) htr
  have htrIoo : t ∈ Set.Ioo (-r) r := abs_lt.mp htr
  have h0Ioo : (0 : ℝ) ∈ Set.Ioo (-r) r := by simpa using hr0
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_alternatingDerivMajorant r hr0 hr1)
    isOpen_Ioo isPreconnected_Ioo
    (fun n y hy => hasDerivAt_alternatingTerm y n)
    (fun n y hy => norm_alternatingDerivTerm_le r y hr0 hy n)
    h0Ioo (by simp [alternatingTerm]) htrIoo
  change HasDerivAt (fun z => ∑' n : ℕ, alternatingTerm z n)
    (∑' n : ℕ, alternatingDerivTerm t n) t
  exact h

private theorem summable_alternatingTerm_interior (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    Summable (alternatingTerm t) := by
  by_cases ht0 : t = 0
  · subst t
    have hz : alternatingTerm 0 = fun _ => 0 := by
      funext n
      unfold alternatingTerm
      rw [show 2 * n + 1 = 2 * n + 1 by omega, pow_add]
      norm_num
    rw [hz]
    exact summable_zero
  have hyabs : |-4 * t ^ 2| < 4 := by
    have hsq : t ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr ht.2)
        (by linarith [ht.1] : 0 < 1 + t)]
    rw [abs_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg t))]
    nlinarith
  have hsum : Summable (term (-4 * t ^ 2)) :=
    (term_summable_iff _).mpr hyabs
  have hshift :
      Summable (fun n : ℕ => term (-4 * t ^ 2) (n + 1)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff 1).mpr hsum
  have hright :
      Summable (fun n : ℕ =>
        -term (-4 * t ^ 2) (n + 1) -
          t ^ 2 * term (-4 * t ^ 2) n) :=
    hshift.neg.sub (hsum.mul_left (t ^ 2))
  have htmul :
      Summable (fun n : ℕ => t * alternatingTerm t n) :=
    hright.congr fun n => (alternatingTerm_scaled_eq t n).symm
  simpa [mul_assoc, ht0] using htmul.mul_left t⁻¹

private theorem alternating_ode_term_identity (t : ℝ) (n : ℕ) :
    (1 + t ^ 2) * alternatingDerivTerm t n +
        t * alternatingTerm t n =
      alternatingDerivTerm t n - alternatingDerivTerm t (n + 1) := by
  unfold alternatingDerivTerm alternatingTerm
  rw [Nat.factorial_succ]
  rw [show 2 * (n + 1 + 1) = (2 * (n + 1) + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  push_cast
  have hfac : (((n.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hfac]
  rw [pow_succ (-1 : ℝ) n]
  ring

private theorem alternating_tsum_ode_identity (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 + t ^ 2) * (∑' n : ℕ, alternatingDerivTerm t n) +
        t * (∑' n : ℕ, alternatingTerm t n) = 1 := by
  have hsd := summable_alternatingDerivTerm_interior t ht
  have hsq := summable_alternatingTerm_interior t ht
  have hsdShift :
      Summable (fun n : ℕ => alternatingDerivTerm t (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsd
  calc
    (1 + t ^ 2) * (∑' n : ℕ, alternatingDerivTerm t n) +
          t * (∑' n : ℕ, alternatingTerm t n) =
        ∑' n : ℕ,
          ((1 + t ^ 2) * alternatingDerivTerm t n +
            t * alternatingTerm t n) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact (((hsd.mul_left (1 + t ^ 2)).hasSum.add
        (hsq.mul_left t).hasSum).tsum_eq).symm
    _ = ∑' n : ℕ,
        (alternatingDerivTerm t n -
          alternatingDerivTerm t (n + 1)) := by
      apply tsum_congr
      exact alternating_ode_term_identity t
    _ = (∑' n : ℕ, alternatingDerivTerm t n) -
        ∑' n : ℕ, alternatingDerivTerm t (n + 1) := by
      exact (hsd.hasSum.sub hsdShift.hasSum).tsum_eq
    _ = alternatingDerivTerm t 0 := by
      have h := hsd.sum_add_tsum_nat_add 1
      simpa using sub_eq_iff_eq_add.mpr h.symm
    _ = 1 := by norm_num [alternatingDerivTerm]

private theorem normalized_g_ode_interior (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.sqrt (1 + t ^ 2) * deriv g t +
        t / Real.sqrt (1 + t ^ 2) * g t =
      1 / Real.sqrt (1 + t ^ 2) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hs : Real.sqrt (1 + t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hs2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt hpos.le
  have hode : (1 + t ^ 2) * deriv g t + t * g t = 1 := by
    rw [(hasDerivAt_g_interior t ht).deriv]
    unfold g
    exact alternating_tsum_ode_identity t ht
  field_simp [hs]
  rw [hs2]
  nlinarith

private def negativeFirstIntegral (t : ℝ) : ℝ :=
  Real.sqrt (1 + t ^ 2) * g t - Real.arsinh t

private theorem hasDerivAt_negativeFirstIntegral (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt negativeFirstIntegral 0 t := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hs : Real.sqrt (1 + t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2) using 1 <;>
      simp <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
        (t / Real.sqrt (1 + t ^ 2)) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp t hinner using 1 <;>
      field_simp [hs] <;> ring
  have hg := hasDerivAt_g_interior t ht
  have harsinh := Real.hasDerivAt_arsinh t
  unfold negativeFirstIntegral
  convert (hsqrt.mul hg).sub harsinh using 1
  rw [← hg.deriv, inv_eq_one_div]
  have hnorm := normalized_g_ode_interior t ht
  linarith

private theorem negativeFirstIntegral_eq_zero (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    negativeFirstIntegral t = 0 := by
  have hdiff :
      DifferentiableOn ℝ negativeFirstIntegral (Set.Ioo (-1 : ℝ) 1) := by
    intro y hy
    exact (hasDerivAt_negativeFirstIntegral y hy).differentiableAt
      |>.differentiableWithinAt
  have hder :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1, deriv negativeFirstIntegral y = 0 := by
    intro y hy
    exact (hasDerivAt_negativeFirstIntegral y hy).deriv
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    hdiff hder ht (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
  have hzero : negativeFirstIntegral 0 = 0 := by
    unfold negativeFirstIntegral g
    simp [alternatingTerm, pow_succ]
  linarith

private theorem g_closed_form_interior (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    g t =
      Real.log (t + Real.sqrt (1 + t ^ 2)) /
        Real.sqrt (1 + t ^ 2) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hs : Real.sqrt (1 + t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have h := negativeFirstIntegral_eq_zero t ht
  unfold negativeFirstIntegral at h
  rw [Real.arsinh] at h
  exact (eq_div_iff hs).2 (by linarith)

private theorem g_zero : g 0 = 0 := by
  unfold g
  have hz :
      (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (((n : ℕ).factorial : ℝ) ^ 2 /
            ((2 * (n + 1)).factorial : ℝ)) *
          ((n + 1 : ℕ) : ℝ) * (2 * 0) ^ (2 * n + 1)) =
        fun _ => 0 := by
    funext n
    rw [show 2 * n + 1 = 2 * n + 1 by omega, pow_add]
    norm_num
  rw [hz, tsum_zero]

theorem gap11 (x t : ℝ) (hx0 : 0 ≤ x) (hx4 : x < 4)
    (ht : x = (2 * t) ^ 2) :
    (1 - t ^ 2) * F t - 1 =
      t / 4 * derivativeSeries t := by
  have habst := abs_t_lt_one_of_positive_substitution hx4 ht
  have hyabs : |4 * t ^ 2| < 4 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg t))]
    nlinarith [(sq_lt_one_iff_abs_lt_one t).mpr habst]
  have hsum : Summable (term (4 * t ^ 2)) :=
    (term_summable_iff _).mpr hyabs
  have hshift :
      Summable (fun n : ℕ => term (4 * t ^ 2) (n + 1)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff 1).mpr hsum
  have hsplit := hsum.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  have hrhs :
      t / 4 * derivativeSeries t =
        ∑' n : ℕ, t / 4 * derivativeTerm t n := by
    unfold derivativeSeries derivativeTerm
    rw [tsum_mul_left]
  rw [hrhs]
  unfold F seriesFunction
  have hscaled :
      (fun n : ℕ => t / 4 * derivativeTerm t n) =
        fun n : ℕ =>
          term (4 * t ^ 2) (n + 1) -
            t ^ 2 * term (4 * t ^ 2) n := by
    funext n
    exact derivativeTerm_scaled_eq t n
  change
    (1 - t ^ 2) * (∑' n : ℕ, term (4 * t ^ 2) n) - 1 =
      ∑' n : ℕ, t / 4 * derivativeTerm t n
  rw [hscaled, hshift.tsum_sub (hsum.mul_left (t ^ 2))]
  rw [tsum_mul_left]
  have hzero : term (4 * t ^ 2) 0 = 1 := by
    norm_num [term, coefficient]
  rw [hzero] at hsplit
  linarith

theorem gap12 (x t : ℝ) (hx0 : 0 ≤ x) (hx4 : x < 4)
    (ht : x = (2 * t) ^ 2) :
    (1 - t ^ 2) * F t - 1 =
      t / 4 * deriv asinSquare t := by
  rw [gap11 x t hx0 hx4 ht]
  rw [derivativeSeries_eq_deriv_asinSquare t
    ⟨by
      have habst := abs_t_lt_one_of_positive_substitution hx4 ht
      exact (abs_lt.mp habst).1,
    by
      have habst := abs_t_lt_one_of_positive_substitution hx4 ht
      exact (abs_lt.mp habst).2⟩]

theorem gap13 (x t : ℝ) (hx0 : 0 ≤ x) (hx4 : x < 4)
    (ht : x = (2 * t) ^ 2) (htRange : t ∈ Set.Ico (0 : ℝ) 1) :
    t / 4 * deriv asinSquare t =
      t / Real.sqrt (1 - t ^ 2) * Real.arcsin t := by
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [htRange.1], htRange.2⟩
  rw [(hasDerivAt_asinSquare t htIoo).deriv]
  ring

theorem gap14 (x t : ℝ) (hx0 : 0 ≤ x) (hx4 : x < 4)
    (ht : x = (2 * t) ^ 2) (htRange : t ∈ Set.Ico (0 : ℝ) 1) :
    (1 - t ^ 2) * F t - 1 =
      t / Real.sqrt (1 - t ^ 2) * Real.arcsin t := by
  calc
    (1 - t ^ 2) * F t - 1 =
        t / 4 * deriv asinSquare t := gap12 x t hx0 hx4 ht
    _ = t / Real.sqrt (1 - t ^ 2) * Real.arcsin t :=
      gap13 x t hx0 hx4 ht htRange

theorem gap15 (x t : ℝ) (hx0 : 0 ≤ x) (hx4 : x < 4)
    (ht : x = (2 * t) ^ 2) (htRange : t ∈ Set.Ico (0 : ℝ) 1) :
    F t =
      1 / (1 - t ^ 2) *
        (1 + t / Real.sqrt (1 - t ^ 2) * Real.arcsin t) := by
  have hq : 0 < 1 - t ^ 2 := by
    nlinarith [htRange.1, htRange.2]
  have h := gap14 x t hx0 hx4 ht htRange
  field_simp [hq.ne'] at h ⊢
  nlinarith

theorem gap16 (x : ℝ) (hx0 : 0 ≤ x) (hx4 : x < 4) :
    seriesFunction x = positiveClosedForm x := by
  let t : ℝ := Real.sqrt x / 2
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht1 : t < 1 := by
    dsimp [t]
    nlinarith [Real.sqrt_nonneg x, hsx]
  have hsub : x = (2 * t) ^ 2 := by
    dsimp [t]
    nlinarith
  have hF := gap15 x t hx0 hx4 hsub ⟨ht0, ht1⟩
  have harg : 1 - t ^ 2 = (4 - x) / 4 := by
    dsimp [t]
    nlinarith
  have h4x : 0 < 4 - x := sub_pos.mpr hx4
  have hsqrt :
      Real.sqrt (1 - t ^ 2) = Real.sqrt (4 - x) / 2 := by
    rw [harg, Real.sqrt_div h4x.le]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hFt : F t = seriesFunction x := by
    unfold F
    congr 2
    dsimp [t]
    nlinarith
  rw [hFt] at hF
  unfold positiveClosedForm
  rw [hF, hsqrt, harg]
  dsimp [t]
  have hsqrt4x : Real.sqrt (4 - x) ≠ 0 :=
    (Real.sqrt_pos.2 h4x).ne'
  field_simp [h4x.ne', hsqrt4x]

theorem gap17 (x t : ℝ) (hx4 : -4 < x) (hx0 : x < 0)
    (ht : x = -(2 * t) ^ 2) :
    1 - (1 + t ^ 2) * G t = t * g t := by
  have habst := abs_t_lt_one_of_negative_substitution hx4 ht
  have hyabs : |-4 * t ^ 2| < 4 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg t)]
    norm_num
    nlinarith [(sq_lt_one_iff_abs_lt_one t).mpr habst]
  have hsum : Summable (term (-4 * t ^ 2)) :=
    (term_summable_iff _).mpr hyabs
  have hshift :
      Summable (fun n : ℕ => term (-4 * t ^ 2) (n + 1)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff 1).mpr hsum
  have hsplit := hsum.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  have hrhs :
      t * g t =
        ∑' n : ℕ, t * alternatingTerm t n := by
    unfold g alternatingTerm
    rw [tsum_mul_left]
  rw [hrhs]
  unfold G seriesFunction
  have hscaled :
      (fun n : ℕ => t * alternatingTerm t n) =
        fun n : ℕ =>
          -term (-4 * t ^ 2) (n + 1) -
            t ^ 2 * term (-4 * t ^ 2) n := by
    funext n
    exact alternatingTerm_scaled_eq t n
  change
    1 - (1 + t ^ 2) * (∑' n : ℕ, term (-4 * t ^ 2) n) =
      ∑' n : ℕ, t * alternatingTerm t n
  rw [hscaled,
    hshift.neg.tsum_sub (hsum.mul_left (t ^ 2))]
  rw [tsum_neg, tsum_mul_left]
  have hzero : term (-4 * t ^ 2) 0 = 1 := by
    norm_num [term, coefficient]
  rw [hzero] at hsplit
  linarith

theorem gap18 (x t : ℝ) (hx4 : -4 < x) (hx0 : x < 0)
    (ht : x = -(2 * t) ^ 2) :
    (1 + t ^ 2) * deriv g t + t * g t = 1 := by
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) 1 :=
    abs_lt.mp (abs_t_lt_one_of_negative_substitution hx4 ht)
  rw [(hasDerivAt_g_interior t htIoo).deriv]
  unfold g
  exact alternating_tsum_ode_identity t htIoo

theorem gap19 (x t : ℝ) (hx4 : -4 < x) (hx0 : x < 0)
    (ht : x = -(2 * t) ^ 2) :
    Real.sqrt (1 + t ^ 2) * deriv g t +
        t / Real.sqrt (1 + t ^ 2) * g t =
      1 / Real.sqrt (1 + t ^ 2) := by
  exact normalized_g_ode_interior t
    (abs_lt.mp (abs_t_lt_one_of_negative_substitution hx4 ht))

theorem gap20 :
    ∃ C : ℝ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      Real.sqrt (1 + t ^ 2) * g t =
        Real.log (t + Real.sqrt (1 + t ^ 2)) + C := by
  refine ⟨0, ?_⟩
  intro t ht
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hs : Real.sqrt (1 + t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  rw [g_closed_form_interior t ht]
  field_simp [hs]
  ring

theorem gap21 : g 0 = 0 := by
  exact g_zero

theorem gap22 (C : ℝ)
    (hC : ∀ t : ℝ,
      Real.sqrt (1 + t ^ 2) * g t =
        Real.log (t + Real.sqrt (1 + t ^ 2)) + C) :
    C = 0 := by
  have h := hC 0
  rw [g_zero] at h
  norm_num at h
  simpa [show Real.sqrt (1 : ℝ) = 1 by simpa using Real.sqrt_one] using h.symm

theorem gap23 (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    g t =
      Real.log (t + Real.sqrt (1 + t ^ 2)) /
        Real.sqrt (1 + t ^ 2) := by
  exact g_closed_form_interior t ht

theorem gap24 (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    G t = 1 / (1 + t ^ 2) * (1 - t * g t) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  by_cases ht0 : t = 0
  · subst t
    have hG0 : G 0 = 1 := by
      unfold G seriesFunction
      norm_num only [neg_zero, zero_pow, mul_zero]
      rw [tsum_eq_single 0]
      · norm_num [term, coefficient]
      · intro n hn
        simp [term, hn]
    rw [hG0, g_zero]
    norm_num
  have hx4 : -4 < -4 * t ^ 2 := by
    have hsq : t ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr ht.2)
        (by linarith [ht.1] : 0 < 1 + t)]
    nlinarith
  have hx0 : -4 * t ^ 2 < 0 := by
    nlinarith [sq_pos_of_ne_zero ht0]
  have h := gap17 (-4 * t ^ 2) t hx4 hx0 (by ring)
  field_simp [hpos.ne']
  nlinarith

private theorem G_closed_form_interior (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    G t = 1 / (1 + t ^ 2) * (1 - t * g t) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  by_cases ht0 : t = 0
  · subst t
    have hG0 : G 0 = 1 := by
      unfold G seriesFunction
      norm_num only [neg_zero, zero_pow, mul_zero]
      rw [tsum_eq_single 0]
      · norm_num [term, coefficient]
      · intro n hn
        simp [term, hn]
    rw [hG0, g_zero]
    norm_num
  have hx4 : -4 < -4 * t ^ 2 := by
    have hsq : t ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr ht.2)
        (by linarith [ht.1] : 0 < 1 + t)]
    nlinarith
  have hx0 : -4 * t ^ 2 < 0 := by
    nlinarith [sq_pos_of_ne_zero ht0]
  have h := gap17 (-4 * t ^ 2) t hx4 hx0 (by ring)
  field_simp [hpos.ne']
  nlinarith

theorem gap25 (x : ℝ) (hx4 : -4 < x) (hx0 : x < 0) :
    seriesFunction x = negativeClosedForm x := by
  let t : ℝ := Real.sqrt |x| / 2
  have habsx : |x| = -x := abs_of_neg hx0
  have hsx : Real.sqrt |x| ^ 2 = |x| :=
    Real.sq_sqrt (abs_nonneg x)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht1 : t < 1 := by
    dsimp [t]
    nlinarith [Real.sqrt_nonneg |x|, hsx]
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have hsub : x = -(2 * t) ^ 2 := by
    dsimp [t]
    nlinarith [hsx]
  have hGt : G t = seriesFunction x := by
    unfold G
    congr 2
    nlinarith
  have hG := G_closed_form_interior t htIoo
  have hg := g_closed_form_interior t htIoo
  rw [hGt, hg] at hG
  have harg : 1 + t ^ 2 = (4 - x) / 4 := by
    dsimp [t]
    nlinarith [hsx]
  have h4x : 0 < 4 - x := by linarith
  have hsqrt :
      Real.sqrt (1 + t ^ 2) = Real.sqrt (4 - x) / 2 := by
    rw [harg, Real.sqrt_div h4x.le]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  unfold negativeClosedForm
  rw [hG, hsqrt, harg]
  dsimp [t]
  have hsqrt4x : Real.sqrt (4 - x) ≠ 0 :=
    (Real.sqrt_pos.2 h4x).ne'
  field_simp [h4x.ne', hsqrt4x]

end

end ProofGap.Exercise3029
