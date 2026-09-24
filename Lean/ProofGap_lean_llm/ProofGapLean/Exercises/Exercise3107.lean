import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

namespace ProofGap.Exercise3107

noncomputable section

open Filter
open scoped BigOperators Topology

def normalizedProduct (t : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 + (i : ℝ) * t)

def normalizedSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 + (i : ℝ) * t)

def geometricMean (t : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (normalizedProduct t n) (1 / (n : ℝ))

def arithmeticMean (t : ℝ) (n : ℕ) : ℝ :=
  normalizedSum t n / n

def normalizedRatio (t : ℝ) (n : ℕ) : ℝ :=
  geometricMean t n / arithmeticMean t n

def rawProduct (a b : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (a + (i : ℝ) * b)

def rawSum (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (a + (i : ℝ) * b)

def rawRatio (a b : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (rawProduct a b n) (1 / (n : ℝ)) /
    (rawSum a b n / n)

def sumRemainder (t : ℝ) (n : ℕ) : ℝ :=
  normalizedSum t n - (t / 2) * (n : ℝ) ^ 2

def logRemainder (t : ℝ) (n : ℕ) : ℝ :=
  Real.log (geometricMean t n) - (Real.log (n * t) - 1)

private theorem normalizedSum_eq (t : ℝ) (n : ℕ) :
    normalizedSum t n =
      (n : ℝ) + (t / 2) * (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp [normalizedSum]
  | succ n ih =>
      rw [normalizedSum, Finset.sum_range_succ, ← normalizedSum, ih]
      push_cast
      ring

private theorem normalizedProduct_succ (t : ℝ) (n : ℕ) :
    normalizedProduct t (n + 1) =
      normalizedProduct t n * (1 + (n : ℝ) * t) := by
  rw [normalizedProduct, Finset.prod_range_succ, ← normalizedProduct]

private theorem normalizedProduct_pos (t : ℝ) (ht : 0 < t) (n : ℕ) :
    0 < normalizedProduct t n := by
  apply Finset.prod_pos
  intro i hi
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  positivity

private theorem normalizedSum_succ (t : ℝ) (n : ℕ) :
    normalizedSum t (n + 1) =
      normalizedSum t n + (1 + (n : ℝ) * t) := by
  rw [normalizedSum, Finset.sum_range_succ, ← normalizedSum]

private theorem rawProduct_eq (a b : ℝ) (ha : a ≠ 0) (n : ℕ) :
    rawProduct a b n = a ^ n * normalizedProduct (b / a) n := by
  induction n with
  | zero => simp [rawProduct, normalizedProduct]
  | succ n ih =>
      rw [rawProduct, Finset.prod_range_succ, ← rawProduct, ih]
      rw [normalizedProduct_succ]
      have hfactor : a + (n : ℝ) * b = a * (1 + (n : ℝ) * (b / a)) := by
        field_simp
      rw [hfactor, pow_succ]
      ring

private theorem rawSum_eq (a b : ℝ) (ha : a ≠ 0) (n : ℕ) :
    rawSum a b n = a * normalizedSum (b / a) n := by
  induction n with
  | zero => simp [rawSum, normalizedSum]
  | succ n ih =>
      rw [rawSum, Finset.sum_range_succ, ← rawSum, ih]
      rw [normalizedSum_succ]
      have hfactor : a + (n : ℝ) * b = a * (1 + (n : ℝ) * (b / a)) := by
        field_simp
      rw [hfactor]
      ring

private theorem log_sum_integral_bounds (t : ℝ) (ht : 0 < t) (n : ℕ) :
    let S := ∑ i ∈ Finset.range n, Real.log (1 + (i : ℝ) * t)
    let I := ∫ x : ℝ in 0..(n : ℝ), Real.log (1 + x * t)
    S ≤ I ∧ I ≤ S + Real.log (1 + (n : ℝ) * t) ∧
      I =
        (1 / t) *
          ((1 + t * (n : ℝ)) * Real.log (1 + t * (n : ℝ)) -
            (1 + t * (n : ℝ)) + 1) := by
  dsimp only
  have hmono :
      MonotoneOn (fun x : ℝ => Real.log (1 + x * t))
        (Set.Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    apply Real.strictMonoOn_log.monotoneOn
    · exact (show 0 < 1 + x * t by
        have hx0 : 0 ≤ x := hx.1
        positivity)
    · exact (show 0 < 1 + y * t by
        have hy0 : 0 ≤ y := hy.1
        positivity)
    · simpa [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_right hxy ht.le) 1
  have hleft :
      (∑ i ∈ Finset.range n, Real.log (1 + (i : ℝ) * t)) ≤
        ∫ x : ℝ in 0..(n : ℝ), Real.log (1 + x * t) := by
    simpa using hmono.sum_le_integral
  have hright0 :
      (∫ x : ℝ in 0..(n : ℝ), Real.log (1 + x * t)) ≤
        ∑ i ∈ Finset.range n, Real.log (1 + ((i + 1 : ℕ) : ℝ) * t) := by
    simpa using hmono.integral_le_sum
  have hshift :
      (∑ i ∈ Finset.range n, Real.log (1 + ((i + 1 : ℕ) : ℝ) * t)) =
        (∑ i ∈ Finset.range n, Real.log (1 + (i : ℝ) * t)) +
          Real.log (1 + (n : ℝ) * t) := by
    have hfirst :=
      Finset.sum_range_succ'
        (f := fun i : ℕ => Real.log (1 + (i : ℝ) * t)) n
    have hlast :=
      Finset.sum_range_succ
        (f := fun i : ℕ => Real.log (1 + (i : ℝ) * t)) n
    rw [hlast] at hfirst
    simpa [add_comm] using hfirst.symm
  have hright := hright0.trans_eq hshift
  have hint :
      (∫ x : ℝ in 0..(n : ℝ), Real.log (1 + x * t)) =
        (1 / t) *
          ((1 + t * (n : ℝ)) * Real.log (1 + t * (n : ℝ)) -
            (1 + t * (n : ℝ)) + 1) := by
    calc
      (∫ x : ℝ in 0..(n : ℝ), Real.log (1 + x * t)) =
          ∫ x : ℝ in 0..(n : ℝ), Real.log (t * x + 1) := by
            congr 1
            funext x
            congr 1
            ring
      _ = t⁻¹ • ∫ y : ℝ in t * 0 + 1..t * (n : ℝ) + 1, Real.log y := by
            exact intervalIntegral.integral_comp_mul_add Real.log ht.ne' 1
      _ = _ := by
            rw [integral_log]
            simp only [smul_eq_mul, mul_zero, zero_add, Real.log_one, mul_zero]
            simp only [one_div]
            ring
  exact ⟨hleft, hright, hint⟩

/-- Exercise 3107, gap 1. -/
theorem gap1 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : t = b / a) :
    0 < t := by
  rw [ht]
  exact div_pos hb ha

/-- Exercise 3107, gap 2; the means require a positive sample count. -/
theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ n : ℕ, 1 ≤ n →
      rawRatio a b n = normalizedRatio (b / a) n := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hprodpos : 0 < normalizedProduct (b / a) n := by
    apply Finset.prod_pos
    intro i hi
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    positivity
  have hrpow :
      Real.rpow (a ^ n * normalizedProduct (b / a) n) (1 / (n : ℝ)) =
        a * Real.rpow (normalizedProduct (b / a) n) (1 / (n : ℝ)) := by
    have ha_rpow :
        Real.rpow (a ^ n) (1 / (n : ℝ)) = a := by
      rw [← Real.rpow_natCast]
      calc
        Real.rpow (Real.rpow a (n : ℝ)) (1 / (n : ℝ)) =
            Real.rpow a ((n : ℝ) * (1 / (n : ℝ))) := by
          exact (Real.rpow_mul ha.le (n : ℝ) (1 / (n : ℝ))).symm
        _ = a := by
          rw [show (n : ℝ) * (1 / (n : ℝ)) = 1 by field_simp]
          exact Real.rpow_one a
    calc
      Real.rpow (a ^ n * normalizedProduct (b / a) n) (1 / (n : ℝ)) =
          Real.rpow (a ^ n) (1 / (n : ℝ)) *
            Real.rpow (normalizedProduct (b / a) n) (1 / (n : ℝ)) :=
        Real.mul_rpow (pow_nonneg ha.le n) hprodpos.le
      _ = _ := by rw [ha_rpow]
  rw [rawRatio, normalizedRatio, geometricMean, arithmeticMean,
    rawProduct_eq a b ha.ne', rawSum_eq a b ha.ne', hrpow]
  field_simp

/-- Exercise 3107, gap 3; formalize the scalar big-O as a sequence estimate. -/
theorem gap3 (t : ℝ) :
    sumRemainder t =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  have h :=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left
      (1 - t / 2)
  convert h using 1
  funext n
  rw [sumRemainder, normalizedSum_eq]
  ring

/-- Exercise 3107, gap 4; the logarithmic mean identity starts at `n=1`. -/
theorem gap4 (t : ℝ) (ht : 0 < t) :
    ∀ n : ℕ, 1 ≤ n →
      Real.log (geometricMean t n) =
        (1 / (n : ℝ)) *
          ∑ i ∈ Finset.range n, Real.log (1 + (i : ℝ) * t) := by
  intro n hn
  rw [geometricMean]
  calc
    Real.log
        (Real.rpow (normalizedProduct t n) (1 / (n : ℝ))) =
        (1 / (n : ℝ)) * Real.log (normalizedProduct t n) :=
      Real.log_rpow (normalizedProduct_pos t ht n) (1 / (n : ℝ))
    _ = _ := by
      rw [normalizedProduct]
      rw [Real.log_prod (fun i hi => by
        exact ne_of_gt (by
          have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
          positivity))]

private theorem logRemainder_bound (t : ℝ) (ht : 0 < t) (m : ℕ)
    (hm : 2 ≤ m) :
    |logRemainder t m| ≤
      ((1 + Real.log (1 + t) / Real.log 2) +
          (1 + Real.log (1 + t) / Real.log 2) / t +
          1 / (t * Real.log 2)) *
        (Real.log m / (m : ℝ)) := by
  have hm1 : 1 ≤ m := by omega
  have hm0n : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0n
  have hmpos : 0 < (m : ℝ) := by positivity
  have hm_two : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hm_two)
  have hlog2_le : Real.log 2 ≤ Real.log (m : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 2) hmpos hm_two
  have ht1 : 1 ≤ 1 + t := by linarith
  have hlogt1 : 0 ≤ Real.log (1 + t) := Real.log_nonneg ht1
  let C : ℝ := 1 + Real.log (1 + t) / Real.log 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC_log :
      Real.log (1 + t) + Real.log (m : ℝ) ≤
        C * Real.log (m : ℝ) := by
    have hratio : 0 ≤ Real.log (1 + t) / Real.log 2 := by positivity
    have hmul :=
      mul_le_mul_of_nonneg_left hlog2_le hratio
    dsimp [C]
    have heq :
        Real.log (1 + t) / Real.log 2 * Real.log 2 =
          Real.log (1 + t) := by field_simp
    calc
      Real.log (1 + t) + Real.log (m : ℝ) =
          (Real.log (1 + t) / Real.log 2) * Real.log 2 +
            Real.log (m : ℝ) := by rw [heq]
      _ ≤ (Real.log (1 + t) / Real.log 2) * Real.log (m : ℝ) +
            Real.log (m : ℝ) := by
        simpa [add_comm] using add_le_add_right hmul (Real.log (m : ℝ))
      _ = _ := by ring
  have hu_pos : 0 < 1 + t * (m : ℝ) := by positivity
  have hv_pos : 0 < t * (m : ℝ) := mul_pos ht hmpos
  have hlogu_nonneg : 0 ≤ Real.log (1 + t * (m : ℝ)) := by
    apply Real.log_nonneg
    linarith
  have hlogu :
      Real.log (1 + t * (m : ℝ)) ≤ C * Real.log (m : ℝ) := by
    have huv :
        1 + t * (m : ℝ) ≤ (1 + t) * (m : ℝ) := by
      nlinarith
    have hlog_le :=
      Real.strictMonoOn_log.monotoneOn hu_pos
        (mul_pos (by linarith) hmpos) huv
    rw [Real.log_mul (by linarith : 1 + t ≠ 0) hm0] at hlog_le
    exact hlog_le.trans hC_log
  let S : ℝ :=
    ∑ i ∈ Finset.range m, Real.log (1 + (i : ℝ) * t)
  let I : ℝ :=
    ∫ x : ℝ in 0..(m : ℝ), Real.log (1 + x * t)
  have hb := log_sum_integral_bounds t ht m
  have hSI : S ≤ I := by simpa [S, I] using hb.1
  have hIS :
      I ≤ S + Real.log (1 + (m : ℝ) * t) := by
    simpa [S, I] using hb.2.1
  have hI :
      I =
        (1 / t) *
          ((1 + t * (m : ℝ)) * Real.log (1 + t * (m : ℝ)) -
            (1 + t * (m : ℝ)) + 1) := by
    simpa [I] using hb.2.2
  have hdiff_nonneg :
      0 ≤ Real.log (1 + t * (m : ℝ)) -
        Real.log (t * (m : ℝ)) := by
    have hle :
        Real.log (t * (m : ℝ)) ≤
          Real.log (1 + t * (m : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn hv_pos hu_pos (by linarith)
    linarith
  have hdiff_le :
      Real.log (1 + t * (m : ℝ)) -
          Real.log (t * (m : ℝ)) ≤
        1 / (t * (m : ℝ)) := by
    rw [← Real.log_div hu_pos.ne' hv_pos.ne']
    have hlog :=
      Real.log_le_sub_one_of_pos (div_pos hu_pos hv_pos)
    calc
      Real.log ((1 + t * (m : ℝ)) / (t * (m : ℝ))) ≤
          (1 + t * (m : ℝ)) / (t * (m : ℝ)) - 1 := hlog
      _ = 1 / (t * (m : ℝ)) := by
        field_simp
        ring
  let Q : ℝ :=
    Real.log (1 + t * (m : ℝ)) / (t * (m : ℝ)) +
      (Real.log (1 + t * (m : ℝ)) - Real.log (t * (m : ℝ)))
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hQ_le :
      Q ≤
        Real.log (1 + t * (m : ℝ)) / (t * (m : ℝ)) +
          1 / (t * (m : ℝ)) := by
    dsimp [Q]
    linarith
  have hR :
      logRemainder t m = (S - I) / (m : ℝ) + Q := by
    rw [logRemainder, gap4 t ht m hm1]
    rw [hI]
    dsimp [S, Q]
    field_simp
    ring
  have hErr_nonneg : 0 ≤ I - S := sub_nonneg.mpr hSI
  have hErr_le :
      I - S ≤ Real.log (1 + t * (m : ℝ)) := by
    have := sub_le_iff_le_add.mpr hIS
    simpa [add_comm, mul_comm] using this
  have hErr_div :
      (I - S) / (m : ℝ) ≤
        C * Real.log (m : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right (hErr_le.trans hlogu) hmpos.le
  have hlog_div :
      Real.log (1 + t * (m : ℝ)) / (t * (m : ℝ)) ≤
        (C / t) * (Real.log (m : ℝ) / (m : ℝ)) := by
    calc
      Real.log (1 + t * (m : ℝ)) / (t * (m : ℝ)) ≤
          (C * Real.log (m : ℝ)) / (t * (m : ℝ)) :=
        div_le_div_of_nonneg_right hlogu (mul_pos ht hmpos).le
      _ = _ := by field_simp
  have hone_div :
      1 / (t * (m : ℝ)) ≤
        (1 / (t * Real.log 2)) *
          (Real.log (m : ℝ) / (m : ℝ)) := by
    have hbase :
        1 ≤ Real.log (m : ℝ) / Real.log 2 := by
      exact (le_div_iff₀ hlog2).2 (by simpa using hlog2_le)
    calc
      1 / (t * (m : ℝ)) ≤
          (Real.log (m : ℝ) / Real.log 2) / (t * (m : ℝ)) :=
        div_le_div_of_nonneg_right hbase (mul_pos ht hmpos).le
      _ = _ := by field_simp
  rw [hR]
  calc
    |(S - I) / (m : ℝ) + Q| ≤
        |(S - I) / (m : ℝ)| + |Q| := abs_add_le _ _
    _ = (I - S) / (m : ℝ) + Q := by
      rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hSI) hmpos.le), abs_of_nonneg hQ_nonneg]
      ring
    _ ≤ C * Real.log (m : ℝ) / (m : ℝ) +
        ((C / t) * (Real.log (m : ℝ) / (m : ℝ)) +
          (1 / (t * Real.log 2)) *
            (Real.log (m : ℝ) / (m : ℝ))) := by
      linarith
    _ = _ := by
      dsimp [C]
      ring

/-- Exercise 3107, gap 5; state the asymptotic remainder at function level. -/
theorem gap5 (t : ℝ) (ht : 0 < t) :
    (fun n : ℕ => logRemainder t (n + 1))
      =O[atTop]
        (fun n : ℕ =>
          Real.log (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine
    ⟨(1 + Real.log (1 + t) / Real.log 2) +
        (1 + Real.log (1 + t) / Real.log 2) / t +
        1 / (t * Real.log 2), ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hm : 2 ≤ n + 1 := by omega
  have hbound := logRemainder_bound t ht (n + 1) hm
  have hdenpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  simp only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
  have hquotpos :
      0 < Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) := by
    have hlogpos' : 0 < Real.log ((n : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hlogpos
    have hdenpos' : 0 < (n : ℝ) + 1 := by positivity
    exact div_pos hlogpos' hdenpos'
  rw [abs_of_pos hquotpos]
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

private theorem geometricMean_eq_exp_logRemainder (t : ℝ) (ht : 0 < t)
    (n : ℕ) (hn : 1 ≤ n) :
    geometricMean t n =
      ((n : ℝ) * t / Real.exp 1) * Real.exp (logRemainder t n) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hgm :
      0 < geometricMean t n := by
    rw [geometricMean]
    exact Real.rpow_pos_of_pos (normalizedProduct_pos t ht n) _
  have hnt : 0 < (n : ℝ) * t := mul_pos hnpos ht
  rw [logRemainder, Real.exp_sub, Real.exp_sub,
    Real.exp_log hgm, Real.exp_log hnt]
  field_simp [hnt.ne', Real.exp_ne_zero]

/--
Exercise 3107, gap 6; replace the exponentiated big-O
placeholder by a remainder function.
-/
theorem gap6 (t : ℝ) (ht : 0 < t) :
    ∃ E : ℕ → ℝ,
      (fun n : ℕ => E (n + 1))
        =O[atTop]
          (fun n : ℕ =>
            Real.log (n + 1) / ((n + 1 : ℕ) : ℝ)) ∧
      ∀ n : ℕ, 1 ≤ n →
        geometricMean t n =
          ((n : ℝ) * t / Real.exp 1) * Real.exp (E n) := by
  refine ⟨logRemainder t, gap5 t ht, ?_⟩
  intro n hn
  exact geometricMean_eq_exp_logRemainder t ht n hn

/--
Exercise 3107, gap 7; expose both numerator and
arithmetic-mean remainder functions.
-/
theorem gap7 (t : ℝ) (ht : 0 < t) :
    ∃ E R : ℕ → ℝ,
      (fun n : ℕ => E (n + 1))
        =O[atTop]
          (fun n : ℕ =>
            Real.log (n + 1) / ((n + 1 : ℕ) : ℝ)) ∧
      R =O[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ n : ℕ, 1 ≤ n →
        normalizedRatio t n =
          (((n : ℝ) * t / Real.exp 1) * Real.exp (E n)) /
            ((t / 2) * n + R n) := by
  refine
    ⟨logRemainder t, (fun _ : ℕ => 1 - t / 2),
      gap5 t ht, ?_, ?_⟩
  · exact
      (by
        simpa only [mul_one] using
          (Asymptotics.isBigO_refl
            (fun _ : ℕ => (1 : ℝ)) atTop).const_mul_left (1 - t / 2))
  · intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hmean :
        arithmeticMean t n = (t / 2) * (n : ℝ) + (1 - t / 2) := by
      rw [arithmeticMean, normalizedSum_eq]
      field_simp
      ring
    rw [normalizedRatio, geometricMean_eq_exp_logRemainder t ht n hn, hmean]

private def denominatorError (t : ℝ) (n : ℕ) : ℝ :=
  (2 * (1 - t / 2)) / (t * (n : ℝ))

private theorem normalizedRatio_eq_exp (t : ℝ) (ht : 0 < t)
    (n : ℕ) (hn : 1 ≤ n) :
    normalizedRatio t n =
      (2 / Real.exp 1) *
        (Real.exp (logRemainder t n) / (1 + denominatorError t n)) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hmean :
      arithmeticMean t n = (t / 2) * (n : ℝ) + (1 - t / 2) := by
    rw [arithmeticMean, normalizedSum_eq]
    field_simp
    ring
  have hgm := geometricMean_eq_exp_logRemainder t ht n hn
  have hden :
      0 < 1 + denominatorError t n := by
    have hmeanpos : 0 < arithmeticMean t n := by
      rw [arithmeticMean]
      apply div_pos
      · apply Finset.sum_pos
        · intro i hi
          have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
          positivity
        · simpa using (show n ≠ 0 by omega)
      · exact hnpos
    rw [hmean] at hmeanpos
    have hfactor :
        (t / 2) * (n : ℝ) * (1 + denominatorError t n) =
          (t / 2) * (n : ℝ) + (1 - t / 2) := by
      rw [denominatorError]
      field_simp
    have htn : 0 < (t / 2) * (n : ℝ) := by positivity
    nlinarith [hfactor]
  rw [normalizedRatio, hgm, hmean, denominatorError]
  field_simp [Real.exp_ne_zero, hden.ne', ht.ne', hn0]

/--
Exercise 3107, gap 8; normalize the bounded denominator
remainder to `O(1/n)`.
-/
theorem gap8 (t : ℝ) (ht : 0 < t) :
    ∃ E D : ℕ → ℝ,
      (fun n : ℕ => E (n + 1))
        =O[atTop]
          (fun n : ℕ =>
            Real.log (n + 1) / ((n + 1 : ℕ) : ℝ)) ∧
      (fun n : ℕ => D (n + 1))
        =O[atTop] (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) ∧
      ∀ n : ℕ, 1 ≤ n →
        normalizedRatio t n =
          (2 / Real.exp 1) * (Real.exp (E n) / (1 + D n)) := by
  refine ⟨logRemainder t, denominatorError t, gap5 t ht, ?_, ?_⟩
  · have h :=
      (Asymptotics.isBigO_refl
        (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop).const_mul_left
        (2 * (1 - t / 2) / t)
    convert h using 1
    funext n
    rw [denominatorError]
    field_simp
  · intro n hn
    exact normalizedRatio_eq_exp t ht n hn

private theorem log_div_nat_succ_tendsto_zero :
    Tendsto
      (fun n : ℕ => Real.log (n + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have harg :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have h :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  simpa only [Function.comp_apply, id_eq, Nat.cast_add, Nat.cast_one] using h

/-- Exercise 3107, gap 9. -/
theorem gap9 (t : ℝ) (ht : 0 < t) :
    Tendsto (normalizedRatio t) atTop (𝓝 (2 / Real.exp 1)) := by
  have hEshift :
      Tendsto (fun n : ℕ => logRemainder t (n + 1)) atTop (𝓝 0) :=
    (gap5 t ht).trans_tendsto log_div_nat_succ_tendsto_zero
  have hE :
      Tendsto (logRemainder t) atTop (𝓝 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp hEshift
  have hExp :
      Tendsto (fun n : ℕ => Real.exp (logRemainder t n))
        atTop (𝓝 1) := by
    have h :=
      Real.continuous_exp.continuousAt.tendsto.comp hE
    simpa using h
  have hD :
      Tendsto (denominatorError t) atTop (𝓝 0) := by
    have hinv :
        Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hc :
        Tendsto (fun _ : ℕ => 2 * (1 - t / 2) / t) atTop
          (𝓝 (2 * (1 - t / 2) / t)) :=
      tendsto_const_nhds
    have hmul := hc.mul hinv
    convert hmul using 1
    · funext n
      rw [denominatorError]
      field_simp
    · ring
  have hDen :
      Tendsto (fun n : ℕ => 1 + denominatorError t n)
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hD
  have hQuot :
      Tendsto
        (fun n : ℕ =>
          Real.exp (logRemainder t n) / (1 + denominatorError t n))
        atTop (𝓝 1) := by
    simpa using hExp.div hDen (by norm_num)
  have hmain :
      Tendsto
        (fun n : ℕ =>
          (2 / Real.exp 1) *
            (Real.exp (logRemainder t n) / (1 + denominatorError t n)))
        atTop (𝓝 (2 / Real.exp 1)) := by
    have hc :
        Tendsto (fun _ : ℕ => 2 / Real.exp 1) atTop
          (𝓝 (2 / Real.exp 1)) :=
      tendsto_const_nhds
    simpa using hc.mul hQuot
  apply hmain.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (normalizedRatio_eq_exp t ht n hn).symm

/-- Exercise 3107, gap 10; restore the positive parameter premises. -/
theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (rawRatio a b) atTop (𝓝 (2 / Real.exp 1)) := by
  have ht : 0 < b / a := div_pos hb ha
  have hmain := gap9 (b / a) ht
  apply hmain.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (gap2 a b ha hb n hn).symm

end

end ProofGap.Exercise3107
