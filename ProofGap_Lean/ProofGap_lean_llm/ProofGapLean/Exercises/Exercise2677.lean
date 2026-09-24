import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.Asymptotics

namespace ProofGap.Exercise2677

noncomputable section

open Filter
open scoped BigOperators

def z (p : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Real.rpow n p

def logArgument (p : ℝ) (n : ℕ) : ℝ :=
  1 + z p n

def logTerm (p : ℝ) (n : ℕ) : ℝ :=
  Real.log (logArgument p n)

def comparison (q : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n q

def truncatedExpansion (p : ℝ) (m n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m,
    (-1 : ℝ) ^ (j + 1) / j * z p n ^ j

def evenMagnitudePart (p : ℝ) (m n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m with Even j,
    (1 / (j : ℝ)) * comparison (j * p) n

def ConditionallySummable (p : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => logTerm p (n + 2)) ∧
    ¬ Summable (fun n : ℕ => |logTerm p (n + 2)|)

private theorem abs_z (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |z p n| = comparison p n := by
  unfold z comparison
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow]
  congr 1
  exact abs_of_pos
    (Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)) p)

private theorem abs_z_pow (p : ℝ) (n m : ℕ) (hn : 1 ≤ n) :
    |z p n| ^ m = comparison ((m : ℝ) * p) n := by
  rw [abs_z p n hn]
  unfold comparison
  rw [div_pow, one_pow, ← Real.rpow_natCast]
  congr 1
  calc
    Real.rpow (Real.rpow (n : ℝ) p) (m : ℝ) =
        Real.rpow (n : ℝ) (p * (m : ℝ)) :=
      (Real.rpow_mul (by positivity) p (m : ℝ)).symm
    _ = Real.rpow (n : ℝ) ((m : ℝ) * p) := by rw [mul_comm]

private theorem tendsto_z_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => z p (n + 2)) atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hmag : Tendsto (fun n : ℕ =>
      (Real.rpow ((n : ℝ) + 2) p)⁻¹) atTop (nhds 0) :=
    ((tendsto_rpow_atTop hp).comp hbase).inv_tendsto_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply hmag.congr'
  filter_upwards with n
  rw [Real.norm_eq_abs, abs_z p (n + 2) (by omega)]
  simp only [comparison, one_div, Nat.cast_add, Nat.cast_ofNat]

private theorem summable_comparison_shift (q : ℝ) (hq : 1 < q) :
    Summable (fun n : ℕ => comparison q (n + 2)) := by
  have hs := (Real.summable_one_div_nat_add_rpow 2 q).2 hq
  apply hs.congr
  intro n
  unfold comparison
  rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 2)]
  norm_num [Nat.cast_add]

private theorem not_summable_abs_z_shift (p : ℝ) (hp : p ≤ 1) :
    ¬ Summable (fun n : ℕ => |z p (n + 2)|) := by
  intro hs
  have hs' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ p) := by
    apply hs.congr
    intro n
    rw [abs_z p (n + 2) (by omega)]
    unfold comparison
    rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 2)]
    norm_num [Nat.cast_add]
  have := (Real.summable_one_div_nat_add_rpow 2 p).1 hs'
  linarith

private theorem seriesConverges_z_shift (p : ℝ) (hp : 0 < p) :
    ProofGap.SeriesConverges (fun n : ℕ => z p (n + 2)) := by
  let a : ℕ → ℝ := fun n => (Real.rpow ((n : ℝ) + 2) p)⁻¹
  have ha : Antitone a := by
    intro m n hmn
    unfold a
    apply inv_anti₀ (Real.rpow_pos_of_pos (by positivity) p)
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast (by simpa [Nat.add_comm] using add_le_add_right hmn 2)
    · exact hp.le
  have ha0 : Tendsto a atTop (nhds 0) := by
    unfold a
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact ((tendsto_rpow_atTop hp).comp hbase).inv_tendsto_atTop
  rcases ha.tendsto_alternating_series_of_tendsto_zero ha0 with ⟨s, hs⟩
  unfold ProofGap.SeriesConverges
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
  rw [tendsto_map'_iff]
  apply hs.congr'
  filter_upwards with N
  apply Finset.sum_congr rfl
  intro n hn
  unfold a z
  rw [show (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n by
    rw [pow_add]; norm_num]
  simp only [Nat.cast_add, Nat.cast_ofNat, one_div]
  ring

private theorem ofReal_truncatedExpansion (p : ℝ) (m n : ℕ) :
    (truncatedExpansion p m n : ℂ) =
      Complex.logTaylor (m + 1) (z p n : ℂ) := by
  unfold truncatedExpansion Complex.logTaylor
  have hset : Finset.range (m + 1) =
      insert 0 (Finset.Icc 1 m) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_add, pow_one, pow_zero, div_zero, zero_add]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

private theorem log_remainder_isBigO (p : ℝ) (hp : 0 < p) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        logTerm p (n + 2) - truncatedExpansion p m (n + 2))
      (fun n : ℕ => comparison ((m + 1 : ℝ) * p) (n + 2)) := by
  have hz0 := tendsto_z_zero p hp
  have hcomplex := (Complex.log_sub_logTaylor_isBigO m).comp_tendsto hz0.ofReal
  apply Asymptotics.IsBigO.of_norm_norm
  refine hcomplex.norm_norm.congr' ?_ ?_
  · filter_upwards [hz0.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2))]
      with n hn
    have hn' : |z p (n + 2)| < 1 / 2 := by
      simpa [Real.dist_eq] using hn
    have harg : 0 < 1 + z p (n + 2) := by linarith [neg_abs_le (z p (n + 2))]
    have hlog : (Real.log (1 + z p (n + 2)) : ℂ) =
        Complex.log (1 + (z p (n + 2) : ℂ)) := by
      rw [Complex.ofReal_log harg.le, Complex.ofReal_add, Complex.ofReal_one]
    simp only [Function.comp_apply]
    rw [← hlog, ← ofReal_truncatedExpansion]
    simp only [logTerm, logArgument]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  · filter_upwards with n
    simp only [Function.comp_apply]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_z_pow p (n + 2) (m + 1) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Real.norm_eq_abs, abs_of_pos]
    unfold comparison
    exact one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

private theorem truncatedExpansion_two (p : ℝ) (n : ℕ) :
    truncatedExpansion p 2 n = z p n - z p n ^ 2 / 2 := by
  unfold truncatedExpansion
  norm_num [Finset.sum_Icc_succ_top]
  ring

theorem gap1 :
    ∀ p : ℝ, 0 < p →
      Asymptotics.IsBigO atTop
        (fun n : ℕ =>
          logTerm p (n + 2) -
            (z p (n + 2) - z p (n + 2) ^ 2 / 2))
        (fun n : ℕ => comparison (3 * p) (n + 2)) := by
  intro p hp
  refine (log_remainder_isBigO p hp 2).congr ?_ ?_
  · intro n
    rw [truncatedExpansion_two]
  · intro n
    congr 2
    norm_num

theorem gap2 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => |z p (n + 2)|) := by
  intro p hp
  have hs := summable_comparison_shift p hp
  apply hs.congr
  intro n
  exact (abs_z p (n + 2) (by omega)).symm

theorem gap3 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => comparison (2 * p) (n + 2)) := by
  intro p hp
  exact summable_comparison_shift (2 * p) (by linarith)

theorem gap4 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => comparison (3 * p) (n + 2)) := by
  intro p hp
  exact summable_comparison_shift (3 * p) (by linarith)

theorem gap5 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => |logTerm p (n + 2)|) := by
  intro p hp
  have hz := Summable.of_abs (gap2 p hp)
  have hlog := Real.summable_log_one_add_of_summable hz
  apply hlog.abs.congr
  intro n
  rfl

theorem gap6 :
    ∀ p : ℝ, 1 / 2 < p → p ≤ 1 →
      (ProofGap.SeriesConverges (fun n : ℕ => z p (n + 2)) ∧
        ¬ Summable (fun n : ℕ => |z p (n + 2)|)) := by
  intro p hp hp1
  exact ⟨seriesConverges_z_shift p (by linarith), not_summable_abs_z_shift p hp1⟩

theorem gap7 :
    ∀ p : ℝ, 1 / 2 < p → p ≤ 1 →
      Summable (fun n : ℕ => comparison (2 * p) (n + 2)) := by
  intro p hp hp1
  exact summable_comparison_shift (2 * p) (by linarith)

theorem gap8 :
    ∀ p : ℝ, 1 / 2 < p → p ≤ 1 →
      Summable (fun n : ℕ => comparison (3 * p) (n + 2)) := by
  intro p hp hp1
  exact summable_comparison_shift (3 * p) (by linarith)

private theorem seriesConverges_of_summable {a : ℕ → ℝ} (ha : Summable a) :
    ProofGap.SeriesConverges a := by
  unfold ProofGap.SeriesConverges
  refine ⟨∑' n, a n, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
  rw [tendsto_map'_iff]
  exact (Summable.hasSum_iff_tendsto_nat ha).1 ha.hasSum

private theorem seriesConverges_add {a b : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) (hb : ProofGap.SeriesConverges b) :
    ProofGap.SeriesConverges (fun n => a n + b n) := by
  unfold ProofGap.SeriesConverges at ha hb ⊢
  rcases ha with ⟨sa, ha⟩
  rcases hb with ⟨sb, hb⟩
  exact ⟨sa + sb, ha.add hb⟩

private theorem seriesConverges_congr {a b : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) (h : ∀ n, a n = b n) :
    ProofGap.SeriesConverges b := by
  unfold ProofGap.SeriesConverges at ha ⊢
  rcases ha with ⟨s, ha⟩
  refine ⟨s, ha.congr' ?_⟩
  filter_upwards with u
  apply Finset.sum_congr rfl
  intro n hn
  exact h n

theorem gap9 :
    ∀ p : ℝ, 1 / 2 < p → p ≤ 1 → ConditionallySummable p := by
  intro p hp hp1
  have hrem : Summable (fun n : ℕ =>
      logTerm p (n + 2) - (z p (n + 2) - z p (n + 2) ^ 2 / 2)) :=
    summable_of_isBigO_nat (gap8 p hp hp1) (gap1 p (by linarith))
  have hzsq : Summable (fun n : ℕ => z p (n + 2) ^ 2) := by
    apply (gap7 p hp hp1).congr
    intro n
    simpa [sq_abs] using (abs_z_pow p (n + 2) 2 (by omega)).symm
  have hz2 : Summable (fun n : ℕ => z p (n + 2) ^ 2 / 2) := hzsq.div_const 2
  have hcorr : Summable (fun n : ℕ => logTerm p (n + 2) - z p (n + 2)) := by
    apply (hrem.sub hz2).congr
    intro n
    ring
  constructor
  · apply seriesConverges_congr
      (seriesConverges_add (gap6 p hp hp1).1 (seriesConverges_of_summable hcorr))
    intro n
    ring
  · intro habs
    have hlog : Summable (fun n : ℕ => logTerm p (n + 2)) := habs.of_abs
    have hzsum : Summable (fun n : ℕ => z p (n + 2)) := by
      apply (hlog.sub hcorr).congr
      intro n
      ring
    exact (gap6 p hp hp1).2 hzsum.abs

theorem gap10 :
    ∀ p : ℝ, p ≤ 0 →
      ∃ n : ℕ, 2 ≤ n ∧ logArgument p n ≤ 0 := by
  intro p hp
  refine ⟨3, by norm_num, ?_⟩
  have hr : Real.rpow 3 p ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hp
  have hrpos : 0 < Real.rpow 3 p := Real.rpow_pos_of_pos (by norm_num) p
  have hinv : 1 ≤ 1 / Real.rpow 3 p := (le_div_iff₀ hrpos).2 (by simpa using hr)
  unfold logArgument z
  rw [show (-1 : ℝ) ^ 3 = -1 by norm_num]
  rw [neg_div]
  linarith

theorem gap11 :
    ∀ p : ℝ, p ≤ 0 →
      ¬ (∀ n : ℕ, 2 ≤ n → 0 < logArgument p n) := by
  intro p hp hall
  rcases gap10 p hp with ⟨n, hn, hnonpos⟩
  exact (not_lt_of_ge hnonpos) (hall n hn)

theorem gap12 :
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ m : ℕ,
      (m : ℝ) * p ≤ 1 → 1 < (m + 1 : ℝ) * p →
        Asymptotics.IsBigO atTop
          (fun n : ℕ =>
            logTerm p (n + 2) - truncatedExpansion p m (n + 2))
          (fun n : ℕ => comparison ((m + 1 : ℝ) * p) (n + 2)) := by
  intro p hp hp12 m hm hm1
  exact log_remainder_isBigO p hp m

theorem gap13 :
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ m : ℕ,
      (m : ℝ) * p ≤ 1 → 1 < (m + 1 : ℝ) * p →
        ¬ Summable (fun n : ℕ => evenMagnitudePart p m (n + 2)) := by
  intro p hp hp12 m hm hm1 hs
  have hm2 : 2 ≤ m := by
    by_contra h
    have hmle : m ≤ 1 := by omega
    interval_cases m <;> norm_num at hm1 <;> nlinarith
  have hle (n : ℕ) :
      (1 / 2 : ℝ) * comparison (2 * p) (n + 2) ≤ evenMagnitudePart p m (n + 2) := by
    unfold evenMagnitudePart
    have hmem : 2 ∈ (Finset.Icc 1 m).filter Even := by
      simp [hm2]
    have hsingle := Finset.single_le_sum
      (s := (Finset.Icc 1 m).filter Even)
      (f := fun j : ℕ => (1 / (j : ℝ)) * comparison (j * p) (n + 2))
      (fun j hj => by
        have hjIcc := (Finset.mem_filter.mp hj).1
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjIcc).1
        exact mul_nonneg (one_div_nonneg.mpr (by exact_mod_cast Nat.zero_le j))
          (le_of_lt (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)))) hmem
    simpa using hsingle
  have hhalf : Summable (fun n : ℕ =>
      (1 / 2 : ℝ) * comparison (2 * p) (n + 2)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by norm_num) (le_of_lt (one_div_pos.mpr
        (Real.rpow_pos_of_pos (by positivity) _)))) hle hs
  have hcomp : Summable (fun n : ℕ => comparison (2 * p) (n + 2)) := by
    have h := hhalf.mul_left 2
    apply h.congr
    intro n
    ring
  have hstandard : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (2 * p)) := by
    apply hcomp.congr
    intro n
    unfold comparison
    rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 2)]
    norm_num [Nat.cast_add]
  have hpseries := (Real.summable_one_div_nat_add_rpow 2 (2 * p)).1 hstandard
  linarith

private theorem seriesConverges_neg {a : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) :
    ProofGap.SeriesConverges (fun n => -a n) := by
  unfold ProofGap.SeriesConverges at ha ⊢
  rcases ha with ⟨s, ha⟩
  exact ⟨-s, ha.neg⟩

private theorem seriesConverges_sub {a b : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) (hb : ProofGap.SeriesConverges b) :
    ProofGap.SeriesConverges (fun n => a n - b n) := by
  simpa [sub_eq_add_neg] using seriesConverges_add ha (seriesConverges_neg hb)

private theorem seriesConverges_const_mul (c : ℝ) {a : ℕ → ℝ}
    (ha : ProofGap.SeriesConverges a) :
    ProofGap.SeriesConverges (fun n => c * a n) := by
  unfold ProofGap.SeriesConverges at ha ⊢
  rcases ha with ⟨s, ha⟩
  exact ⟨c * s, ha.mul_left c⟩

private theorem seriesConverges_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ → ℝ)
    (ha : ∀ i ∈ s, ProofGap.SeriesConverges (a i)) :
    ProofGap.SeriesConverges (fun n => ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold ProofGap.SeriesConverges
      refine ⟨0, ?_⟩
      simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact seriesConverges_add (ha i (Finset.mem_insert_self i s))
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

private theorem summable_of_nonneg_seriesConverges {a : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (ha : ProofGap.SeriesConverges a) : Summable a := by
  unfold ProofGap.SeriesConverges at ha
  rcases ha with ⟨s, ha⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range] at ha
  rw [tendsto_map'_iff] at ha
  exact ((hasSum_iff_tendsto_nat_of_nonneg ha0 s).2 ha).summable

private theorem z_pow_odd (p : ℝ) (n j : ℕ) (hn : 1 ≤ n) (hj : Odd j) :
    z p n ^ j = z ((j : ℝ) * p) n := by
  unfold z
  rw [div_pow]
  have hnum : ((-1 : ℝ) ^ n) ^ j = (-1 : ℝ) ^ n := by
    by_cases he : Even n
    · simp [he.neg_one_pow]
    · have ho : Odd n := Nat.not_even_iff_odd.mp he
      simp [ho.neg_one_pow, hj.neg_one_pow]
  rw [hnum]
  congr 1
  rw [← Real.rpow_natCast]
  calc
    Real.rpow (Real.rpow (n : ℝ) p) (j : ℝ) =
        Real.rpow (n : ℝ) (p * (j : ℝ)) :=
      (Real.rpow_mul (by positivity) p (j : ℝ)).symm
    _ = Real.rpow (n : ℝ) ((j : ℝ) * p) := by rw [mul_comm]

private def oddExpansion (p : ℝ) (m n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m,
    if Even j then 0 else (1 / (j : ℝ)) * z ((j : ℝ) * p) n

private theorem truncated_add_even_eq_odd (p : ℝ) (m n : ℕ) (hn : 1 ≤ n) :
    truncatedExpansion p m n + evenMagnitudePart p m n = oddExpansion p m n := by
  unfold truncatedExpansion evenMagnitudePart oddExpansion
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : Even j
  · have hzpow : z p n ^ j = comparison ((j : ℝ) * p) n := by
      rw [← he.pow_abs, abs_z_pow p n j hn]
    rw [if_pos he, if_pos he, (he.add_one).neg_one_pow, hzpow]
    ring
  · have ho : Odd j := Nat.not_even_iff_odd.mp he
    rw [if_neg he, if_neg he, (ho.add_one).neg_one_pow, z_pow_odd p n j hn ho]
    ring

private theorem seriesConverges_oddExpansion (p : ℝ) (hp : 0 < p) (m : ℕ) :
    ProofGap.SeriesConverges (fun n : ℕ => oddExpansion p m (n + 2)) := by
  unfold oddExpansion
  apply seriesConverges_finset_sum (Finset.Icc 1 m)
  intro j hj
  by_cases he : Even j
  · simp [he, ProofGap.SeriesConverges]
  · have ho : Odd j := Nat.not_even_iff_odd.mp he
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjp : 0 < (j : ℝ) * p := mul_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hj1)) hp
    simpa [he] using seriesConverges_const_mul (1 / (j : ℝ))
      (seriesConverges_z_shift ((j : ℝ) * p) hjp)

private theorem not_seriesConverges_log :
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
      ¬ ProofGap.SeriesConverges (fun n : ℕ => logTerm p (n + 2)) := by
  intro p hp hp12 hlog
  let m : ℕ := ⌊1 / p⌋₊
  have hnonneg : 0 ≤ 1 / p := (div_pos zero_lt_one hp).le
  have hfloor : (m : ℝ) ≤ 1 / p := by
    dsimp [m]
    exact Nat.floor_le hnonneg
  have hm : (m : ℝ) * p ≤ 1 := (le_div_iff₀ hp).1 hfloor
  have hnext : 1 / p < ((m + 1 : ℕ) : ℝ) := by
    dsimp [m]
    simpa using Nat.lt_floor_add_one (1 / p)
  have hm1 : 1 < (m + 1 : ℝ) * p := by
    have := (div_lt_iff₀ hp).1 hnext
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hremSum : Summable (fun n : ℕ =>
      logTerm p (n + 2) - truncatedExpansion p m (n + 2)) :=
    summable_of_isBigO_nat (summable_comparison_shift ((m + 1 : ℝ) * p) hm1)
      (gap12 p hp hp12 m hm hm1)
  have htrunc : ProofGap.SeriesConverges (fun n : ℕ => truncatedExpansion p m (n + 2)) := by
    apply seriesConverges_congr
      (seriesConverges_sub hlog
        (seriesConverges_of_summable hremSum))
    intro n
    ring
  have hodd := seriesConverges_oddExpansion p hp m
  have heven : ProofGap.SeriesConverges (fun n : ℕ => evenMagnitudePart p m (n + 2)) := by
    apply seriesConverges_congr (seriesConverges_sub hodd htrunc)
    intro n
    have hsplit := truncated_add_even_eq_odd p m (n + 2) (by omega)
    linarith
  have heven0 : ∀ n : ℕ, 0 ≤ evenMagnitudePart p m (n + 2) := by
    intro n
    unfold evenMagnitudePart
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (one_div_nonneg.mpr (by positivity))
      (le_of_lt (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)))
  exact (gap13 p hp hp12 m hm hm1) (summable_of_nonneg_seriesConverges heven0 heven)

theorem gap14 :
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
      ¬ Summable (fun n : ℕ => logTerm p (n + 2)) := by
  intro p hp hp12 hs
  exact not_seriesConverges_log p hp hp12 (seriesConverges_of_summable hs)

end

end ProofGap.Exercise2677
