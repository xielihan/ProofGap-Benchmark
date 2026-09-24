import ProofGapLean.Prelude.Full

/-!
# Exercise 43

Semantic formalization of `proof_gap/exercise_43/{1,...,30}.txt`.
The source defines an “infinite limit” through eventual growth of absolute
values, so that is represented by convergence of `|x n|` to `atTop`.
-/

namespace ProofGap.Exercise43

noncomputable section

def log10 (x : ℝ) : ℝ :=
  Real.log x / Real.log 10

def seq1 (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n : ℝ)

def seq2 (n : ℕ) : ℝ :=
  Real.rpow 2 (Real.sqrt (n : ℝ))

def seq3 (n : ℕ) : ℝ :=
  log10 (log10 (n : ℝ))

def M1 (E : ℝ) : ℕ :=
  Nat.floor E

def M2 (E : ℝ) : ℕ :=
  Nat.floor ((Real.log E / Real.log 2) ^ 2)

def M3 (E : ℝ) : ℕ :=
  Nat.floor (Real.rpow 10 (Real.rpow 10 E))

def tower10 (E : ℕ) : ℕ :=
  10 ^ (10 ^ E)

def HasGrowthCutoff (u : ℕ → ℝ) : Prop :=
  ∃ N : ℝ → ℕ, ∀ (n : ℕ) (E : ℝ),
    0 < E → N E < n → E < |u n|

def DivergesInAbs (u : ℕ → ℝ) : Prop :=
  Tendsto (fun n => |u n|) atTop atTop

def S1Abs : Prop :=
  ∀ n : ℕ, |seq1 n| = (n : ℝ)

def S1Growth : Prop :=
  ∀ (n : ℕ) (E : ℝ), 0 < E →
    E < (n : ℝ) → E < |seq1 n|

def S2Abs : Prop :=
  ∀ n : ℕ, |seq2 n| = seq2 n

def S2Transfer : Prop :=
  ∀ (n : ℕ) (E : ℝ), 0 < E →
    E < seq2 n → E < |seq2 n|

def S2Index : Prop :=
  ∀ (n : ℕ) (E : ℝ), 0 < E →
    (n : ℝ) > (Real.log E / Real.log 2) ^ 2 →
    E < seq2 n

def S2FromIndex : Prop :=
  ∀ (n : ℕ) (E : ℝ), 0 < E →
    (n : ℝ) > (Real.log E / Real.log 2) ^ 2 →
    E < |seq2 n|

def LogFirstPositive : Prop :=
  ∀ n : ℕ, 10 < n → 1 < log10 (n : ℝ)

def LogSecondPositive : Prop :=
  ∀ n : ℕ, 10 < n → 0 < log10 (log10 (n : ℝ))

def S3Transfer : Prop :=
  ∀ (n : ℕ) (E : ℝ), 0 < E →
    E < seq3 n → E < |seq3 n|

def S3Index : Prop :=
  ∀ (n : ℕ) (E : ℝ), 0 < E →
    (n : ℝ) > Real.rpow 10 (Real.rpow 10 E) →
    E < seq3 n

def S3FromIndex : Prop :=
  ∀ (n : ℕ) (E : ℝ), 0 < E →
    (n : ℝ) > Real.rpow 10 (Real.rpow 10 E) →
    E < |seq3 n|

private theorem divergesInAbs_of_hasGrowthCutoff {u : ℕ → ℝ}
    (h : HasGrowthCutoff u) : DivergesInAbs u := by
  unfold HasGrowthCutoff at h
  unfold DivergesInAbs
  rw [Filter.tendsto_atTop]
  intro E
  obtain ⟨N, hN⟩ := h
  filter_upwards [Filter.eventually_ge_atTop (N (max E 1) + 1)] with n hn
  have hE : 0 < max E 1 :=
    zero_lt_one.trans_le (le_max_right E 1)
  exact (le_max_left E 1).trans
    (hN n (max E 1) hE (lt_of_lt_of_le (Nat.lt_succ_self _) hn)).le

private theorem logTen_div_logTwo_bounds :
    (83 : ℝ) / 25 < Real.log 10 / Real.log 2 ∧
      Real.log 10 / Real.log 2 < (133 : ℝ) / 40 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlo :
      Real.log ((2 : ℝ) ^ 83) < Real.log ((10 : ℝ) ^ 25) :=
    Real.log_lt_log (by positivity) (by norm_num)
  have hhi :
      Real.log ((10 : ℝ) ^ 40) < Real.log ((2 : ℝ) ^ 133) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlo hhi
  norm_num at hlo hhi
  constructor
  · apply (lt_div_iff₀ hlog2).2
    nlinarith
  · apply (div_lt_iff₀ hlog2).2
    nlinarith

private theorem logTen_div_logTwo_sq_bounds :
    (6889 : ℝ) / 625 < (Real.log 10 / Real.log 2) ^ 2 ∧
      (Real.log 10 / Real.log 2) ^ 2 < (17689 : ℝ) / 1600 := by
  obtain ⟨hlo, hhi⟩ := logTen_div_logTwo_bounds
  have hbase : 0 < Real.log 10 / Real.log 2 := by
    positivity
  constructor <;> nlinarith [sq_nonneg (Real.log 10 / Real.log 2)]

private theorem M3_nat (E : ℕ) :
    M3 (E : ℝ) = tower10 E := by
  unfold M3 tower10
  have hinner :
      Real.rpow 10 (E : ℝ) = (((10 : ℕ) ^ E : ℕ) : ℝ) := by
    rw [show Real.rpow 10 (E : ℝ) = (10 : ℝ) ^ E from
      Real.rpow_natCast 10 E]
    norm_cast
  have houter :
      Real.rpow 10 ((((10 : ℕ) ^ E : ℕ) : ℝ)) =
        (((10 : ℕ) ^ ((10 : ℕ) ^ E) : ℕ) : ℝ) := by
    rw [show Real.rpow 10 ((((10 : ℕ) ^ E : ℕ) : ℝ)) =
      (10 : ℝ) ^ ((10 : ℕ) ^ E) from
        Real.rpow_natCast 10 ((10 : ℕ) ^ E)]
    norm_cast
  rw [hinner, houter]
  rw [Nat.floor_natCast]

/-- Source: `proof_gap/exercise_43/1.txt`. -/
theorem gap1 : S1Abs := by
  intro n
  simp [seq1, abs_mul, abs_pow]

/-- Source: `proof_gap/exercise_43/2.txt`. -/
theorem gap2 (h1 : S1Abs) : S1Growth := by
  intro n E hE hn
  rw [h1 n]
  exact hn

/-- Source: `proof_gap/exercise_43/3.txt`. -/
theorem gap3 (h2 : S1Growth) : S1Growth := by
  exact h2

/-- Source: `proof_gap/exercise_43/4.txt`. -/
theorem gap4 (h3 : S1Growth) : HasGrowthCutoff seq1 := by
  refine ⟨M1, ?_⟩
  intro n E hE hn
  apply h3 n E hE
  unfold M1 at hn
  have hsuc : Nat.floor E + 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hcast : ((Nat.floor E : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hsuc
  exact (Nat.lt_floor_add_one E).trans_le hcast

/-- Source: `proof_gap/exercise_43/5.txt`. -/
theorem gap5 (h4 : HasGrowthCutoff seq1) : DivergesInAbs seq1 := by
  exact divergesInAbs_of_hasGrowthCutoff h4

/-- Source: `proof_gap/exercise_43/6.txt`. -/
theorem gap6 : S2Abs := by
  intro n
  rw [abs_of_pos]
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- Source: `proof_gap/exercise_43/7.txt`. -/
theorem gap7 (h6 : S2Abs) : S2Transfer := by
  intro n E hE hn
  rw [h6 n]
  exact hn

/-- Source: `proof_gap/exercise_43/8.txt`. -/
theorem gap8 (h7 : S2Transfer) : S2Index := by
  intro n E hE hn
  change (n : ℝ) > (Real.logb 2 E) ^ 2 at hn
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hindex : Real.logb 2 E < Real.sqrt (n : ℝ) := by
    nlinarith [sq_nonneg (Real.logb 2 E)]
  unfold seq2
  calc
    E = Real.rpow 2 (Real.logb 2 E) :=
      (Real.rpow_logb (by norm_num) (by norm_num) hE).symm
    _ < Real.rpow 2 (Real.sqrt (n : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hindex

/-- Source: `proof_gap/exercise_43/9.txt`. -/
theorem gap9 (h7 : S2Transfer) (h8 : S2Index) : S2FromIndex := by
  intro n E hE hn
  exact h7 n E hE (h8 n E hE hn)

/-- Source: `proof_gap/exercise_43/10.txt`. -/
theorem gap10 (h9 : S2FromIndex) : HasGrowthCutoff seq2 := by
  refine ⟨M2, ?_⟩
  intro n E hE hn
  apply h9 n E hE
  unfold M2 at hn
  have hsuc :
      Nat.floor ((Real.log E / Real.log 2) ^ 2) + 1 ≤ n :=
    Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor ((Real.log E / Real.log 2) ^ 2) : ℕ) : ℝ) + 1 ≤
        (n : ℝ) := by
    exact_mod_cast hsuc
  exact (Nat.lt_floor_add_one _).trans_le hcast

/-- Source: `proof_gap/exercise_43/11.txt`. -/
theorem gap11 (h10 : HasGrowthCutoff seq2) : DivergesInAbs seq2 := by
  exact divergesInAbs_of_hasGrowthCutoff h10

/-- Source: `proof_gap/exercise_43/12.txt`. -/
theorem gap12 : LogFirstPositive := by
  intro n hn
  unfold log10
  have hlog10 : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  apply (one_lt_div hlog10).2
  apply Real.log_lt_log (by norm_num)
  exact_mod_cast hn

/-- Source: `proof_gap/exercise_43/13.txt`. -/
theorem gap13 (h12 : LogFirstPositive) : LogSecondPositive := by
  intro n hn
  unfold log10
  exact div_pos (Real.log_pos (h12 n hn))
    (Real.log_pos (by norm_num))

/-- Source: `proof_gap/exercise_43/14.txt`. -/
theorem gap14 (h13 : LogSecondPositive) : S3Transfer := by
  intro n E hE hn
  rw [abs_of_pos (hE.trans hn)]
  exact hn

/-- Source: `proof_gap/exercise_43/15.txt`. -/
theorem gap15 (h14 : S3Transfer) : S3Index := by
  intro n E hE hn
  change E < Real.logb 10 (Real.logb 10 (n : ℝ))
  have htower : 0 < Real.rpow 10 (Real.rpow 10 E) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hfirst :
      Real.rpow 10 E < Real.logb 10 (n : ℝ) := by
    have hlog :=
      Real.logb_lt_logb (b := 10) (by norm_num) htower hn
    simpa [Real.logb_rpow (by norm_num : (0 : ℝ) < 10)
      (by norm_num : (10 : ℝ) ≠ 1)] using hlog
  have hsecond :=
    Real.logb_lt_logb (b := 10) (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) E) hfirst
  simpa [Real.logb_rpow (by norm_num : (0 : ℝ) < 10)
    (by norm_num : (10 : ℝ) ≠ 1)] using hsecond

/-- Source: `proof_gap/exercise_43/16.txt`. -/
theorem gap16 (h14 : S3Transfer) (h15 : S3Index) : S3FromIndex := by
  intro n E hE hn
  exact h14 n E hE (h15 n E hE hn)

/-- Source: `proof_gap/exercise_43/17.txt`. -/
theorem gap17 (h16 : S3FromIndex) : HasGrowthCutoff seq3 := by
  refine ⟨M3, ?_⟩
  intro n E hE hn
  apply h16 n E hE
  unfold M3 at hn
  have hsuc :
      Nat.floor (Real.rpow 10 (Real.rpow 10 E)) + 1 ≤ n :=
    Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor (Real.rpow 10 (Real.rpow 10 E)) : ℕ) : ℝ) + 1 ≤
        (n : ℝ) := by
    exact_mod_cast hsuc
  exact (Nat.lt_floor_add_one _).trans_le hcast

/-- Source: `proof_gap/exercise_43/18.txt`. -/
theorem gap18 (h17 : HasGrowthCutoff seq3) : DivergesInAbs seq3 := by
  exact divergesInAbs_of_hasGrowthCutoff h17

/-- Source: `proof_gap/exercise_43/19.txt`; uses the cutoff for sequence (1). -/
theorem gap19 : M1 10 = 10 := by
  norm_num [M1]

/-- Source: `proof_gap/exercise_43/20.txt`; uses the cutoff for sequence (1). -/
theorem gap20 : M1 100 = 100 := by
  norm_num [M1]

/-- Source: `proof_gap/exercise_43/21.txt`; uses the cutoff for sequence (1). -/
theorem gap21 : M1 1000 = 1000 := by
  norm_num [M1]

/-- Source: `proof_gap/exercise_43/22.txt`; uses the cutoff for sequence (1). -/
theorem gap22 : M1 10000 = 10000 := by
  norm_num [M1]

/-- Source: `proof_gap/exercise_43/23.txt`; uses the cutoff for sequence (2). -/
theorem gap23 : M2 10 = 11 := by
  unfold M2
  apply (Nat.floor_eq_iff (sq_nonneg _)).2
  obtain ⟨hlo, hhi⟩ := logTen_div_logTwo_sq_bounds
  constructor <;> norm_num <;> nlinarith

/-- Source: `proof_gap/exercise_43/24.txt`; uses the cutoff for sequence (2). -/
theorem gap24 : M2 100 = 44 := by
  unfold M2
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
  norm_num
  have heq :
      (2 * Real.log 10 / Real.log 2) ^ 2 =
        4 * (Real.log 10 / Real.log 2) ^ 2 := by ring
  rw [heq]
  apply (Nat.floor_eq_iff (by positivity)).2
  obtain ⟨hlo, hhi⟩ := logTen_div_logTwo_sq_bounds
  constructor <;> norm_num <;> nlinarith

/-- Source: `proof_gap/exercise_43/25.txt`; uses the cutoff for sequence (2). -/
theorem gap25 : M2 1000 = 99 := by
  unfold M2
  rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
  norm_num
  have heq :
      (3 * Real.log 10 / Real.log 2) ^ 2 =
        9 * (Real.log 10 / Real.log 2) ^ 2 := by ring
  rw [heq]
  apply (Nat.floor_eq_iff (by positivity)).2
  obtain ⟨hlo, hhi⟩ := logTen_div_logTwo_sq_bounds
  constructor <;> norm_num <;> nlinarith

/-- Source: `proof_gap/exercise_43/26.txt`; uses the cutoff for sequence (2). -/
theorem gap26 : M2 10000 = 176 := by
  unfold M2
  rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow]
  norm_num
  have heq :
      (4 * Real.log 10 / Real.log 2) ^ 2 =
        16 * (Real.log 10 / Real.log 2) ^ 2 := by ring
  rw [heq]
  apply (Nat.floor_eq_iff (by positivity)).2
  obtain ⟨hlo, hhi⟩ := logTen_div_logTwo_sq_bounds
  constructor <;> norm_num <;> nlinarith

/-- Source: `proof_gap/exercise_43/27.txt`; uses the cutoff for sequence (3). -/
theorem gap27 : M3 10 = tower10 10 := by
  exact M3_nat 10

/-- Source: `proof_gap/exercise_43/28.txt`; uses the cutoff for sequence (3). -/
theorem gap28 : M3 100 = tower10 100 := by
  exact M3_nat 100

/-- Source: `proof_gap/exercise_43/29.txt`; uses the cutoff for sequence (3). -/
theorem gap29 : M3 1000 = tower10 1000 := by
  exact M3_nat 1000

/-- Source: `proof_gap/exercise_43/30.txt`; uses the cutoff for sequence (3). -/
theorem gap30 : M3 10000 = tower10 10000 := by
  exact M3_nat 10000

end

end ProofGap.Exercise43
