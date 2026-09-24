import ProofGapLean.Prelude.Analysis
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

namespace ProofGap.Exercise2893

noncomputable section

open scoped BigOperators

def cot (x : ℝ) : ℝ :=
  Real.cos x / Real.sin x

def ξ (x : ℝ) : ℝ :=
  1 - Real.sin x / x

def g (x : ℝ) : ℝ :=
  x * (cot x - 1 / x)

def bernoulliMagnitude (n : ℕ) : ℝ :=
  |(((bernoulli (2 * n) : ℚ) : ℝ))|

def P (n : ℕ) : ℝ :=
  -(2 : ℝ) ^ (2 * n) * bernoulliMagnitude n /
    (Nat.factorial (2 * n) : ℝ)

def cosineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def xiSeriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  (-1 : ℝ) ^ (n + 1) * x ^ (2 * n) /
    (Nat.factorial (2 * n + 1) : ℝ)

def gSeriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  P n * x ^ (2 * n)

def cotTailTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  P n * x ^ (2 * n - 1)

private theorem sin_div_pos_of_ne_zero_of_abs_lt_pi
    {x : ℝ} (hx : x ≠ 0) (hpi : |x| < Real.pi) :
    0 < Real.sin x / x := by
  have hb := abs_lt.mp hpi
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · exact div_pos_of_neg_of_neg
      (Real.sin_neg_of_neg_of_neg_pi_lt hxneg hb.1) hxneg
  · exact div_pos (Real.sin_pos_of_pos_of_lt_pi hxpos hb.2) hxpos

private theorem xi_abs_lt_one
    (x : ℝ) (hx : x ≠ 0) (hpi : |x| < Real.pi) :
    |ξ x| < 1 := by
  have hsincpos := sin_div_pos_of_ne_zero_of_abs_lt_pi hx hpi
  have hsincle : Real.sin x / x ≤ 1 := by
    rw [← Real.sinc_of_ne_zero hx]
    exact Real.sinc_le_one x
  unfold ξ
  rw [abs_of_nonneg (sub_nonneg.mpr hsincle)]
  linarith

private theorem cosineTerm_hasSum (x : ℝ) :
    HasSum (cosineTerm x) (Real.cos x) := by
  simpa [cosineTerm] using Real.hasSum_cos x

private theorem sincSeriesTerm_hasSum (x : ℝ) (hx : x ≠ 0) :
    HasSum
      (fun n : ℕ =>
        (-1 : ℝ) ^ n * x ^ (2 * n) /
          (Nat.factorial (2 * n + 1) : ℝ))
      (Real.sin x / x) := by
  have hfun :
      (fun n : ℕ =>
        ((-1 : ℝ) ^ n * x ^ (2 * n + 1) /
          (Nat.factorial (2 * n + 1) : ℝ)) / x) =
      fun n : ℕ =>
        (-1 : ℝ) ^ n * x ^ (2 * n) /
          (Nat.factorial (2 * n + 1) : ℝ) := by
    funext n
    rw [pow_succ]
    field_simp
  simpa only [hfun] using (Real.hasSum_sin x).div_const x

private theorem bernoulli_even_abs (n : ℕ) (hn : n ≠ 0) :
    |(((bernoulli (2 * n) : ℚ) : ℝ))| =
      (-1 : ℝ) ^ (n + 1) * (((bernoulli (2 * n) : ℚ) : ℝ)) := by
  have hz := hasSum_zeta_nat hn
  have hpos :
      0 <
        (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) *
          Real.pi ^ (2 * n) *
            (((bernoulli (2 * n) : ℚ) : ℝ)) /
              (Nat.factorial (2 * n) : ℝ) := by
    rw [← hz.tsum_eq]
    exact hz.summable.tsum_pos (fun k => by positivity) 1 (by norm_num)
  have hfactor :
      0 <
        (2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) /
          (Nat.factorial (2 * n) : ℝ) := by
    positivity
  have hsigned :
      0 < (-1 : ℝ) ^ (n + 1) *
        (((bernoulli (2 * n) : ℚ) : ℝ)) := by
    have hprod :
        0 <
          ((2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) /
            (Nat.factorial (2 * n) : ℝ)) *
              ((-1 : ℝ) ^ (n + 1) *
                (((bernoulli (2 * n) : ℚ) : ℝ))) := by
      have heq :
          (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) *
                Real.pi ^ (2 * n) *
                  (((bernoulli (2 * n) : ℚ) : ℝ)) /
                    (Nat.factorial (2 * n) : ℝ) =
            ((2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) /
              (Nat.factorial (2 * n) : ℝ)) *
                ((-1 : ℝ) ^ (n + 1) *
                  (((bernoulli (2 * n) : ℚ) : ℝ))) := by
        ring
      rwa [heq] at hpos
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hfactor.le) h.1)
  calc
    |(((bernoulli (2 * n) : ℚ) : ℝ))| =
        |(-1 : ℝ) ^ (n + 1) *
          (((bernoulli (2 * n) : ℚ) : ℝ))| := by
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ = _ := abs_of_pos hsigned

private theorem P_eq_bernoulli_coefficient (n : ℕ) (hn : n ≠ 0) :
    P n =
      (-1 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) *
        (((bernoulli (2 * n) : ℚ) : ℝ)) /
          (Nat.factorial (2 * n) : ℝ) := by
  rw [P, bernoulliMagnitude, bernoulli_even_abs n hn]
  rw [pow_succ]
  ring

private def cotPartialTerm (x : ℝ) (m : ℕ) : ℝ :=
  2 * x /
    (x ^ 2 - (Real.pi * (m + 1 : ℝ)) ^ 2)

private theorem cotPartialTerm_scale
    (x : ℝ) (hpi : |x| < Real.pi) (m : ℕ) :
    2 * (x / Real.pi) /
        ((x / Real.pi) ^ 2 - (m + 1 : ℝ) ^ 2) =
      Real.pi * cotPartialTerm x m := by
  have hmone : (1 : ℝ) ≤ (m + 1 : ℝ) := by norm_num
  have hbound : |x| < Real.pi * (m + 1 : ℝ) := by
    nlinarith [Real.pi_pos]
  have hden :
      x ^ 2 - (Real.pi * (m + 1 : ℝ)) ^ 2 ≠ 0 := by
    have hp : 0 < Real.pi * (m + 1 : ℝ) := by
      nlinarith [Real.pi_pos]
    have hsq : x ^ 2 < (Real.pi * (m + 1 : ℝ)) ^ 2 := by
      nlinarith [sq_abs x, abs_nonneg x]
    linarith
  have hscaleDen :
      (x / Real.pi) ^ 2 - (m + 1 : ℝ) ^ 2 =
        (x ^ 2 - (Real.pi * (m + 1 : ℝ)) ^ 2) /
          Real.pi ^ 2 := by
    field_simp [Real.pi_ne_zero]
  rw [hscaleDen]
  unfold cotPartialTerm
  field_simp [Real.pi_ne_zero, hden]

private theorem cotTerm_re_eq_pi_mul_cotPartialTerm
    (x : ℝ) (hpi : |x| < Real.pi)
    (hzmem : (((x / Real.pi : ℝ) : ℂ)) ∈ Complex.integerComplement)
    (m : ℕ) :
    (cotTerm (((x / Real.pi : ℝ) : ℂ)) m).re =
      Real.pi * cotPartialTerm x m := by
  let z : ℂ := ((x / Real.pi : ℝ) : ℂ)
  have hplus : z + (m + 1 : ℂ) ≠ 0 := by
    simpa [z] using
      Complex.integerComplement_add_ne_zero hzmem ((m + 1 : ℕ) : ℤ)
  have hminus : z - (m + 1 : ℂ) ≠ 0 := by
    simpa [z, sub_eq_add_neg] using
      Complex.integerComplement_add_ne_zero hzmem (-((m + 1 : ℕ) : ℤ))
  have hterm :
      1 / (z - (m + 1 : ℂ)) + 1 / (z + (m + 1 : ℂ)) =
        ((Real.pi * cotPartialTerm x m : ℝ) : ℂ) := by
    calc
      1 / (z - (m + 1 : ℂ)) + 1 / (z + (m + 1 : ℂ)) =
          2 * z / (z ^ 2 - (m + 1 : ℂ) ^ 2) := by
        rw [show z ^ 2 - (m + 1 : ℂ) ^ 2 =
          (z - (m + 1 : ℂ)) * (z + (m + 1 : ℂ)) by ring]
        field_simp [hplus, hminus]
        ring
      _ = ((Real.pi * cotPartialTerm x m : ℝ) : ℂ) := by
        simpa [z] using congrArg (fun r : ℝ => (r : ℂ))
          (cotPartialTerm_scale x hpi m)
  simpa only [cotTerm, Complex.ofReal_re] using congrArg Complex.re hterm

private theorem tsum_cotTerm_re_eq_pi_mul_partial
    (x : ℝ) (hpi : |x| < Real.pi)
    (hzmem : (((x / Real.pi : ℝ) : ℂ)) ∈ Complex.integerComplement) :
    (∑' m : ℕ, (cotTerm (((x / Real.pi : ℝ) : ℂ)) m).re) =
      ∑' m : ℕ, Real.pi * cotPartialTerm x m := by
  exact tsum_congr
    (fun m => cotTerm_re_eq_pi_mul_cotPartialTerm x hpi hzmem m)

private theorem cot_sub_inv_eq_tsum_partial
    (x : ℝ) (hx : x ≠ 0) (hpi : |x| < Real.pi) :
    cot x - 1 / x = ∑' m : ℕ, cotPartialTerm x m := by
  let z : ℂ := ((x / Real.pi : ℝ) : ℂ)
  have hzmem : z ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hnre : (n : ℝ) = x / Real.pi := by
      simpa [z] using congrArg Complex.re hn
    have hnabs : |(n : ℝ)| < 1 := by
      rw [hnre, abs_div, abs_of_pos Real.pi_pos]
      exact (div_lt_one Real.pi_pos).2 hpi
    have hn0 : n = 0 := by
      apply Int.abs_lt_one_iff.mp
      exact_mod_cast hnabs
    subst n
    norm_num at hnre
    exact hx ((div_eq_zero_iff.mp hnre.symm).resolve_right Real.pi_ne_zero)
  have hc := cot_series_rep' hzmem
  have hs := summable_cotTerm hzmem
  have hcre := congrArg Complex.re hc
  rw [Complex.re_tsum hs] at hcre
  have hleft :
      (Real.pi * Complex.cot (Real.pi * z) - 1 / z).re =
        Real.pi * (cot x - 1 / x) := by
    have hcomplex :
        (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z =
          ((Real.pi * (cot x - 1 / x) : ℝ) : ℂ) := by
      dsimp [z]
      rw [show (Real.pi : ℂ) * ((x / Real.pi : ℝ) : ℂ) = (x : ℂ) by
        push_cast
        field_simp [Real.pi_ne_zero]]
      unfold Complex.cot cot
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      field_simp [Real.pi_ne_zero]
    simpa using congrArg Complex.re hcomplex
  rw [hleft] at hcre
  apply mul_left_cancel₀ Real.pi_ne_zero
  rw [hcre, ← tsum_mul_left]
  exact tsum_cotTerm_re_eq_pi_mul_partial x hpi hzmem

private def cotDoubleTerm (x : ℝ) (m k : ℕ) : ℝ :=
  (-2 * x /
      (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2)) *
    (x ^ 2 /
      (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2)) ^ k

private theorem cotDoubleTerm_hasSum_partial
    (x : ℝ) (hpi : |x| < Real.pi) (m : ℕ) :
    HasSum (cotDoubleTerm x m) (cotPartialTerm x m) := by
  let d : ℝ := Real.pi ^ 2 * (m + 1 : ℝ) ^ 2
  let q : ℝ := x ^ 2 / d
  have hmone : (1 : ℝ) ≤ (m + 1 : ℝ) := by norm_num
  have hbound : |x| < Real.pi * (m + 1 : ℝ) := by
    nlinarith [Real.pi_pos]
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hsq : x ^ 2 < d := by
    dsimp [d]
    nlinarith [sq_abs x, abs_nonneg x]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    exact (div_lt_one hdpos).2 hsq
  have hqabs : |q| < 1 := by
    rw [abs_of_nonneg hq0]
    exact hq1
  have hg :=
    (hasSum_geometric_of_abs_lt_one hqabs).mul_left (-2 * x / d)
  have hg' :
      HasSum (cotDoubleTerm x m) (-2 * x / d * (1 - q)⁻¹) := by
    apply hg.congr
    intro k
    simp [cotDoubleTerm, d, q]
  convert hg' using 1
  dsimp [d, q]
  unfold cotPartialTerm
  have hden :
      x ^ 2 - Real.pi ^ 2 * (m + 1 : ℝ) ^ 2 ≠ 0 := by
    linarith
  have hden' :
      Real.pi ^ 2 * (m + 1 : ℝ) ^ 2 - x ^ 2 ≠ 0 := by
    linarith
  field_simp [hden, hden']
  ring

private theorem cotDoubleTerm_norm_formula (x : ℝ) (m k : ℕ) :
    ‖cotDoubleTerm x m k‖ =
      (2 * |x| /
          (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2)) *
        (x ^ 2 /
          (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2)) ^ k := by
  simp [cotDoubleTerm, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

private theorem cotDoubleTerm_norm_le (x : ℝ) (m k : ℕ) :
    ‖cotDoubleTerm x m k‖ ≤
      ((2 * |x| / Real.pi ^ 2) *
        (1 / (m + 1 : ℝ) ^ 2)) *
        (x ^ 2 / Real.pi ^ 2) ^ k := by
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hm : (1 : ℝ) ≤ (m + 1 : ℝ) := by norm_num
  have hm2 : (1 : ℝ) ≤ (m + 1 : ℝ) ^ 2 := by nlinarith
  have hden :
      Real.pi ^ 2 ≤ Real.pi ^ 2 * (m + 1 : ℝ) ^ 2 := by
    nlinarith
  have hratio :
      x ^ 2 / (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2) ≤
        x ^ 2 / Real.pi ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg x) hpi2 hden
  rw [cotDoubleTerm_norm_formula]
  calc
    (2 * |x| / (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2)) *
          (x ^ 2 / (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2)) ^ k =
        ((2 * |x| / Real.pi ^ 2) *
          (1 / (m + 1 : ℝ) ^ 2)) *
          (x ^ 2 / (Real.pi ^ 2 * (m + 1 : ℝ) ^ 2)) ^ k := by
      field_simp [Real.pi_ne_zero]
    _ ≤ ((2 * |x| / Real.pi ^ 2) *
          (1 / (m + 1 : ℝ) ^ 2)) *
          (x ^ 2 / Real.pi ^ 2) ^ k := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (by positivity) hratio k
      · positivity

private theorem summable_cotDoubleTerm
    (x : ℝ) (hpi : |x| < Real.pi) :
    Summable (fun p : ℕ × ℕ => cotDoubleTerm x p.1 p.2) := by
  have hpSeries :
      Summable (fun m : ℕ => (1 : ℝ) / (m + 1 : ℝ) ^ 2) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg] using
      (summable_pow_div_add (1 : ℝ) 2 1 Nat.one_lt_two)
  have houter :
      Summable (fun m : ℕ =>
        (2 * |x| / Real.pi ^ 2) *
          (1 / (m + 1 : ℝ) ^ 2)) := by
    exact hpSeries.mul_left _
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hsq : x ^ 2 < Real.pi ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x]
  have hq0 : 0 ≤ x ^ 2 / Real.pi ^ 2 := by positivity
  have hq1 : x ^ 2 / Real.pi ^ 2 < 1 :=
    (div_lt_one hpi2).2 hsq
  have hqnorm : ‖x ^ 2 / Real.pi ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom :
      Summable (fun k : ℕ => (x ^ 2 / Real.pi ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hmajor :
      Summable (fun p : ℕ × ℕ =>
        ((2 * |x| / Real.pi ^ 2) *
          (1 / (p.1 + 1 : ℝ) ^ 2)) *
          (x ^ 2 / Real.pi ^ 2) ^ p.2) :=
    houter.mul_of_nonneg hgeom (by intro m; positivity) (by intro k; positivity)
  have hnorm :
      Summable (fun p : ℕ × ℕ => ‖cotDoubleTerm x p.1 p.2‖) :=
    Summable.of_nonneg_of_le
      (fun p => norm_nonneg _)
      (fun p => cotDoubleTerm_norm_le x p.1 p.2)
      hmajor
  exact hnorm.of_norm

private theorem one_div_shift_hasSum_zeta (n : ℕ) (hn : n ≠ 0) :
    HasSum
      (fun m : ℕ => 1 / (m + 1 : ℝ) ^ (2 * n))
      ((-1 : ℝ) ^ (n + 1) *
        ((2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) *
          (bernoulli (2 * n) : ℝ) /
            (Nat.factorial (2 * n) : ℝ))) := by
  have hz := hasSum_zeta_nat hn
  convert (hasSum_nat_add_iff' 1).2 hz using 1 <;>
    simp [hn]
  ring

private theorem cotDoubleTerm_eq_zetaTerm (x : ℝ) (m k : ℕ) :
    cotDoubleTerm x m k =
      (-2 * x ^ (2 * (k + 1) - 1) /
        Real.pi ^ (2 * (k + 1))) *
        (1 / (m + 1 : ℝ) ^ (2 * (k + 1))) := by
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    show 2 * (k + 1) = 2 * k + 2 by omega]
  unfold cotDoubleTerm
  simp only [div_pow, mul_pow]
  field_simp [Real.pi_ne_zero]
  simp only [pow_add, pow_mul, pow_one, pow_two]
  ring

private theorem cotDoubleTerm_hasSum_tail (x : ℝ) (k : ℕ) :
    HasSum (fun m : ℕ => cotDoubleTerm x m k) (cotTailTerm x k) := by
  have hn : k + 1 ≠ 0 := by omega
  have hs :=
    (one_div_shift_hasSum_zeta (k + 1) hn).mul_left
      (-2 * x ^ (2 * (k + 1) - 1) /
        Real.pi ^ (2 * (k + 1)))
  convert hs using 1
  · funext m
    exact cotDoubleTerm_eq_zetaTerm x m k
  · dsimp [cotTailTerm]
    rw [P_eq_bernoulli_coefficient (k + 1) hn]
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega]
    field_simp [Real.pi_ne_zero]
    simp only [pow_succ]
    ring

private theorem cot_sub_inv_eq_tsum_tail
    (x : ℝ) (hx : x ≠ 0) (hpi : |x| < Real.pi) :
    cot x - 1 / x = ∑' k : ℕ, cotTailTerm x k := by
  rw [cot_sub_inv_eq_tsum_partial x hx hpi]
  calc
    (∑' m : ℕ, cotPartialTerm x m) =
        ∑' m : ℕ, ∑' k : ℕ, cotDoubleTerm x m k := by
      apply tsum_congr
      intro m
      exact (cotDoubleTerm_hasSum_partial x hpi m).tsum_eq.symm
    _ = ∑' k : ℕ, ∑' m : ℕ, cotDoubleTerm x m k := by
      exact (summable_cotDoubleTerm x hpi).tsum_comm.symm
    _ = ∑' k : ℕ, cotTailTerm x k := by
      apply tsum_congr
      intro k
      exact (cotDoubleTerm_hasSum_tail x k).tsum_eq

private theorem gSeriesTerm_eq_mul_cotTailTerm (x : ℝ) (k : ℕ) :
    gSeriesTerm x k = x * cotTailTerm x k := by
  dsimp [gSeriesTerm, cotTailTerm]
  have hpow :
      x ^ (2 * (k + 1)) = x * x ^ (2 * (k + 1) - 1) := by
    calc
      x ^ (2 * (k + 1)) =
          x ^ ((2 * (k + 1) - 1) + 1) := by
        congr 1
      _ = x ^ (2 * (k + 1) - 1) * x := pow_succ _ _
      _ = x * x ^ (2 * (k + 1) - 1) := mul_comm _ _
  rw [hpow]
  ring

private theorem g_eq_tsum_gSeries
    (x : ℝ) (hx : x ≠ 0) (hpi : |x| < Real.pi) :
    g x = ∑' k : ℕ, gSeriesTerm x k := by
  calc
    g x = x * (∑' k : ℕ, cotTailTerm x k) := by
      unfold g
      rw [cot_sub_inv_eq_tsum_tail x hx hpi]
    _ = ∑' k : ℕ, x * cotTailTerm x k := tsum_mul_left.symm
    _ = ∑' k : ℕ, gSeriesTerm x k :=
      tsum_congr (fun k => (gSeriesTerm_eq_mul_cotTailTerm x k).symm)

theorem gap1 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      cot x - 1 / x = Real.cos x / Real.sin x - 1 / x := by
  intro x hx hpi
  rfl

theorem gap2 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      cot x - 1 / x =
        (1 / x) *
          ((∑' n, cosineTerm x n) * (∑' m : ℕ, ξ x ^ m) - 1) := by
  intro x hx hpi
  have hsinc := (sin_div_pos_of_ne_zero_of_abs_lt_pi hx hpi).ne'
  rw [(cosineTerm_hasSum x).tsum_eq,
    tsum_geometric_of_abs_lt_one (xi_abs_lt_one x hx hpi)]
  unfold cot ξ
  rw [show 1 - (1 - Real.sin x / x) = Real.sin x / x by ring]
  field_simp

theorem gap3 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      cot x - 1 / x =
        (1 / x) * (∑' k, gSeriesTerm x k) := by
  intro x hx hpi
  rw [← g_eq_tsum_gSeries x hx hpi]
  unfold g
  field_simp

theorem gap4 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      cot x - 1 / x = ∑' k, cotTailTerm x k := by
  intro x hx hpi
  exact cot_sub_inv_eq_tsum_tail x hx hpi

theorem gap5 :
    ∀ x : ℝ, x ≠ 0 → g x = x * cot x - 1 := by
  intro x hx
  unfold g
  field_simp

theorem gap6 :
    ∀ x : ℝ, x ≠ 0 →
      x * cot x - 1 = Real.cos x / (Real.sin x / x) - 1 := by
  intro x hx
  unfold cot
  field_simp

theorem gap7 :
    ∀ x : ℝ, x ≠ 0 →
      g x = Real.cos x / (Real.sin x / x) - 1 := by
  intro x hx
  rw [gap5 x hx, gap6 x hx]

theorem gap8 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi → |ξ x| < 1 := by
  intro x hx hpi
  exact xi_abs_lt_one x hx hpi

theorem gap9 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      g x = Real.cos x * (∑' m : ℕ, ξ x ^ m) - 1 := by
  intro x hx hpi
  have hsinc := (sin_div_pos_of_ne_zero_of_abs_lt_pi hx hpi).ne'
  rw [gap7 x hx, tsum_geometric_of_abs_lt_one (xi_abs_lt_one x hx hpi)]
  unfold ξ
  rw [show 1 - (1 - Real.sin x / x) = Real.sin x / x by ring]
  field_simp

theorem gap10 :
    ∀ x : ℝ, x ≠ 0 →
      ξ x = ∑' k, xiSeriesTerm x k := by
  intro x hx
  have htail :
      HasSum
        (fun k : ℕ =>
          (-1 : ℝ) ^ (k + 1) * x ^ (2 * (k + 1)) /
            (Nat.factorial (2 * (k + 1) + 1) : ℝ))
        (Real.sin x / x - 1) := by
    simpa using
      ((hasSum_nat_add_iff' 1).2 (sincSeriesTerm_hasSum x hx))
  have hneg := htail.neg
  have hseries : HasSum (xiSeriesTerm x) (ξ x) := by
    convert hneg using 1
    · funext k
      simp only [xiSeriesTerm]
      rw [pow_succ]
      ring
    · unfold ξ
      ring
  exact hseries.tsum_eq.symm

theorem gap11 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      g x = ∑' k, gSeriesTerm x k := by
  intro x hx hpi
  exact g_eq_tsum_gSeries x hx hpi

theorem gap12 :
    P 1 = -(1 / 3 : ℝ) := by
  norm_num [P, bernoulliMagnitude]

theorem gap13 :
    P 2 = -(1 / 45 : ℝ) := by
  norm_num [P, bernoulliMagnitude, bernoulli]

theorem gap14 :
    P 3 = -(2 / 945 : ℝ) := by
  have h5 : bernoulli' 5 = 0 :=
    bernoulli'_eq_zero_of_odd (by exact ⟨2, by omega⟩) (by omega)
  have hc2 : Nat.choose 6 2 = 15 := by decide
  have hc4 : Nat.choose 6 4 = 15 := by decide
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, h5, hc2, hc4]
  norm_num [P, bernoulliMagnitude, bernoulli, h6]

theorem gap15 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      cot x - 1 / x = ∑' k, cotTailTerm x k := by
  intro x hx hpi
  exact cot_sub_inv_eq_tsum_tail x hx hpi

end

end ProofGap.Exercise2893
