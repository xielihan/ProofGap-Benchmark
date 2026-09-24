import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2932_6

noncomputable section

open scoped BigOperators Interval

def sinhc (x : ℝ) : ℝ :=
  Real.sinh x / x

def sinhcTerm (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * n) / (Nat.factorial (2 * n + 1) : ℝ)

def integratedTerm (n : ℕ) : ℝ :=
  1 /
    (((2 * n + 1 : ℕ) : ℝ) *
      (Nat.factorial (2 * n + 1) : ℝ))

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, sinhc x

def partialIntegral : ℝ :=
  ∑ n ∈ Finset.range 3, integratedTerm n

def remainder : ℝ :=
  targetIntegral - partialIntegral

def remainderBound : ℝ :=
  (1 / (7 * (Nat.factorial 7 : ℝ))) *
    ∑' n : ℕ, (1 / 7 ^ 2 : ℝ) ^ n

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem sinhcTerm_hasSum (x : ℝ) (hx : x ≠ 0) :
    HasSum (fun n => sinhcTerm n x) (sinhc x) := by
  have h := (Real.hasSum_sinh x).div_const x
  have heq :
      (fun n : ℕ =>
        (x ^ (2 * n + 1) /
          (Nat.factorial (2 * n + 1) : ℝ)) / x) =
        fun n : ℕ => sinhcTerm n x := by
    funext n
    unfold sinhcTerm
    field_simp
    rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ]
    ring
  rw [← heq]
  simpa [sinhc] using h

private theorem integral_sinhcTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..1, sinhcTerm n x) = integratedTerm n := by
  have hfun :
      (fun x : ℝ => sinhcTerm n x) =
        fun x : ℝ =>
          (1 / (Nat.factorial (2 * n + 1) : ℝ)) * x ^ (2 * n) := by
    funext x
    unfold sinhcTerm
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp [integratedTerm]

private theorem norm_sinhcTerm_le
    (t : ℝ) (n : ℕ) (ht : t ∈ Set.uIcc 0 1) :
    ‖sinhcTerm n t‖ ≤
      1 / (Nat.factorial (2 * n + 1) : ℝ) := by
  have habs : |t| ≤ 1 := by
    have hdist := Real.dist_left_le_of_mem_uIcc ht
    simpa [Real.dist_eq] using hdist
  rw [Real.norm_eq_abs]
  simp only [sinhcTerm, abs_div, abs_pow]
  have hfact :
      0 ≤ (Nat.factorial (2 * n + 1) : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hfact]
  have hp : |t| ^ (2 * n) ≤ 1 := by
    simpa using pow_le_one₀ (abs_nonneg t) habs
  exact div_le_div_of_nonneg_right hp (Nat.cast_nonneg _)

private theorem two_mul_add_injective (c : ℕ) :
    Function.Injective (fun n : ℕ => 2 * n + c) := by
  intro a b hab
  have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
  exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hmul

private theorem summable_odd_inv_factorial :
    Summable (fun n : ℕ =>
      1 / (Nat.factorial (2 * n + 1) : ℝ)) := by
  simpa [Function.comp_def] using
    (Real.summable_pow_div_factorial 1).comp_injective
      (two_mul_add_injective 1)

private theorem sinhcIntegral_hasSum :
    HasSum
      (fun n : ℕ => ∫ x in (0 : ℝ)..1, sinhcTerm n x)
      targetIntegral := by
  unfold targetIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => 1 / (Nat.factorial (2 * n + 1) : ℝ))
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold sinhcTerm
    fun_prop
  · intro n
    filter_upwards with t ht
    exact norm_sinhcTerm_le t n (Set.uIoc_subset_uIcc ht)
  · filter_upwards with t ht
    exact summable_odd_inv_factorial
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    apply sinhcTerm_hasSum t
    simp only [Set.mem_uIoc] at ht
    rcases ht with ht | ht
    · exact ne_of_gt ht.1
    · exfalso
      linarith [ht.1, ht.2]

private theorem integratedTerm_hasSum :
    HasSum integratedTerm targetIntegral := by
  apply sinhcIntegral_hasSum.congr_fun
  intro n
  exact (integral_sinhcTerm n).symm

private theorem summable_integratedTerm :
    Summable integratedTerm :=
  integratedTerm_hasSum.summable

private theorem integratedTerm_pos (n : ℕ) :
    0 < integratedTerm n := by
  unfold integratedTerm
  positivity

private theorem remainder_eq_tail :
    remainder = ∑' n : ℕ, integratedTerm (n + 3) := by
  rw [remainder, partialIntegral, ← integratedTerm_hasSum.tsum_eq]
  have hsplit := summable_integratedTerm.sum_add_tsum_nat_add 3
  linarith

private theorem integratedTerm_step (m : ℕ) (hm : 3 ≤ m) :
    integratedTerm (m + 1) ≤ integratedTerm m / 49 := by
  have hfactor :
      (49 : ℝ) * (2 * (m : ℝ) + 1) ≤
        (2 * (m : ℝ) + 3) *
          (2 * (m : ℝ) + 3) *
          (2 * (m : ℝ) + 2) := by
    have hm' : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h9 : (9 : ℝ) ≤ 2 * (m : ℝ) + 3 := by linarith
    have h8 : (8 : ℝ) ≤ 2 * (m : ℝ) + 2 := by linarith
    have hprod :
        (72 : ℝ) ≤
          (2 * (m : ℝ) + 3) * (2 * (m : ℝ) + 2) := by
      convert mul_le_mul h9 h8 (by norm_num) (by positivity) using 1 <;>
        norm_num
    have hlin :
        2 * (m : ℝ) + 1 ≤ 2 * (m : ℝ) + 3 := by linarith
    have hnonneg : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by positivity
    calc
      (49 : ℝ) * (2 * (m : ℝ) + 1) ≤
          ((2 * (m : ℝ) + 3) * (2 * (m : ℝ) + 2)) *
            (2 * (m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hnonneg
      _ ≤
          ((2 * (m : ℝ) + 3) * (2 * (m : ℝ) + 2)) *
            (2 * (m : ℝ) + 3) :=
        mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = _ := by ring
  unfold integratedTerm
  rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hfact :
      (0 : ℝ) ≤ (Nat.factorial (2 * m + 1) : ℝ) := Nat.cast_nonneg _
  have hden :
      (49 : ℝ) *
          ((2 * (m : ℝ) + 1) *
            (Nat.factorial (2 * m + 1) : ℝ)) ≤
        (2 * (m : ℝ) + 1 + 2) *
          ((2 * (m : ℝ) + 2 + 1) *
            ((2 * (m : ℝ) + 1 + 1) *
              (Nat.factorial (2 * m + 1) : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_right hfactor hfact
    nlinarith [hmul]
  have hrewrite :
      (1 /
        ((2 * (m : ℝ) + 1) *
          (Nat.factorial (2 * m + 1) : ℝ))) / 49 =
        1 /
          ((49 : ℝ) *
            ((2 * (m : ℝ) + 1) *
              (Nat.factorial (2 * m + 1) : ℝ))) := by
    have hd :
        (2 * (m : ℝ) + 1) *
          (Nat.factorial (2 * m + 1) : ℝ) ≠ 0 := by
      positivity
    field_simp [hd]
  rw [hrewrite]
  exact one_div_le_one_div_of_le (by positivity) hden

private theorem tail_term_le_majorant (n : ℕ) :
    integratedTerm (n + 3) ≤
      integratedTerm 3 * (1 / 49 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      calc
        integratedTerm (n + 1 + 3) =
            integratedTerm ((n + 3) + 1) := by rfl
        _ ≤ integratedTerm (n + 3) / 49 :=
          integratedTerm_step (n + 3) (by omega)
        _ ≤
            (integratedTerm 3 * (1 / 49 : ℝ) ^ n) / 49 := by
          exact div_le_div_of_nonneg_right ih (by norm_num)
        _ = integratedTerm 3 * (1 / 49 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          ring

private theorem majorant_summable :
    Summable (fun n : ℕ =>
      integratedTerm 3 * (1 / 49 : ℝ) ^ n) := by
  exact
    (summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] : ‖(1 / 49 : ℝ)‖ < 1)).mul_left _

private theorem tail_summable :
    Summable (fun n : ℕ => integratedTerm (n + 3)) :=
  (summable_nat_add_iff 3).2 summable_integratedTerm

theorem gap1 :
    targetIntegral =
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, sinhcTerm n x := by
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x hx
  exact (sinhcTerm_hasSum x (by
    simp only [Set.mem_uIoc] at hx
    rcases hx with hx | hx
    · exact ne_of_gt hx.1
    · exfalso
      linarith [hx.1, hx.2])).tsum_eq.symm

theorem gap2 :
    (∫ x in (0 : ℝ)..1, ∑' n : ℕ, sinhcTerm n x) =
      ∑' n : ℕ, integratedTerm n := by
  exact gap1.symm.trans integratedTerm_hasSum.tsum_eq.symm

theorem gap3 :
    targetIntegral = ∑' n : ℕ, integratedTerm n := by
  exact gap1.trans gap2

theorem gap4 :
    0 < remainder := by
  rw [remainder_eq_tail]
  have hsplit := tail_summable.sum_add_tsum_nat_add 1
  have hrest :
      0 ≤ ∑' n : ℕ, integratedTerm (n + 1 + 3) :=
    tsum_nonneg (fun n => (integratedTerm_pos _).le)
  calc
    0 < integratedTerm 3 + ∑' n : ℕ, integratedTerm (n + 1 + 3) :=
      add_pos_of_pos_of_nonneg (integratedTerm_pos 3) hrest
    _ = ∑' n : ℕ, integratedTerm (n + 3) := by
      simpa using hsplit

theorem gap5 :
    remainder < remainderBound := by
  rw [remainder_eq_tail]
  have hstrict :
      integratedTerm (1 + 3) <
        integratedTerm 3 * (1 / 49 : ℝ) ^ 1 := by
    norm_num [integratedTerm, Nat.factorial]
  have hsumlt :
      (∑' n : ℕ, integratedTerm (n + 3)) <
        ∑' n : ℕ, integratedTerm 3 * (1 / 49 : ℝ) ^ n :=
    tail_summable.tsum_lt_tsum tail_term_le_majorant hstrict
      majorant_summable
  calc
    (∑' n : ℕ, integratedTerm (n + 3)) <
        ∑' n : ℕ, integratedTerm 3 * (1 / 49 : ℝ) ^ n :=
      hsumlt
    _ = remainderBound := by
      rw [remainderBound, tsum_mul_left]
      norm_num [integratedTerm, Nat.factorial]

theorem gap6 :
    remainderBound =
      (1 / (7 * (Nat.factorial 7 : ℝ))) *
        (1 / (1 - (1 / 7 ^ 2 : ℝ))) := by
  unfold remainderBound
  rw [tsum_geometric_of_norm_lt_one
    (by norm_num [Real.norm_eq_abs] :
      ‖(1 / 7 ^ 2 : ℝ)‖ < 1)]
  simp only [one_div]

theorem gap7 :
    (1 / (7 * (Nat.factorial 7 : ℝ))) *
        (1 / (1 - (1 / 7 ^ 2 : ℝ))) <
      (1 / 10 ^ 3 : ℝ) := by
  norm_num [Nat.factorial]

theorem gap8 :
    (0 : ℝ) < 1 / 10 ^ 3 := by
  norm_num

theorem gap9 :
    (1 : ℝ) = 10000 / 10000 := by
  norm_num

theorem gap10 :
    Approx (1 / (3 * (Nat.factorial 3 : ℝ)))
      (556 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  norm_num [Approx, Nat.factorial, abs_lt]

theorem gap11 :
    Approx (1 / (5 * (Nat.factorial 5 : ℝ)))
      (17 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  norm_num [Approx, Nat.factorial, abs_lt]

theorem gap12 :
    Approx targetIntegral (1057 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have hpos := gap4
  have hbound := gap5
  rw [gap6] at hbound
  norm_num [Nat.factorial] at hbound
  have heq : targetIntegral = partialIntegral + remainder := by
    unfold remainder
    ring
  rw [Approx, abs_lt, heq]
  norm_num [partialIntegral, integratedTerm, Finset.sum_range_succ,
    Nat.factorial]
  constructor <;> linarith

end

end ProofGap.Exercise2932_6
