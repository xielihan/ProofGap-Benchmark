import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise3094

noncomputable section

open Filter
open scoped BigOperators Topology

def signedPower (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) ((-1 : ℝ) ^ n)

def p (n : ℕ) : ℝ :=
  Real.rpow (signedPower n) (1 / (n : ℝ))

def logarithmicTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Real.log n / (n : ℝ)

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  ∃ L : ℝ,
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, f (k + 1))
      atTop (𝓝 L)

def ConditionallySummableFromOne (f : ℕ → ℝ) : Prop :=
  SummableFromOne f ∧ ¬SummableFromOne (fun n => |f n|)

private theorem signedPower_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < signedPower n := by
  unfold signedPower
  exact Real.rpow_pos_of_pos
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) _

private def amplitude (n : ℕ) : ℝ :=
  Real.log ((n + 3 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)

private theorem amplitude_antitone : Antitone amplitude := by
  intro m n hmn
  apply Real.log_div_self_antitoneOn
  · change Real.exp 1 ≤ ((m + 3 : ℕ) : ℝ)
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  · change Real.exp 1 ≤ ((n + 3 : ℕ) : ℝ)
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  · exact_mod_cast Nat.add_le_add_right hmn 3

private theorem amplitude_tendsto_zero :
    Tendsto amplitude atTop (𝓝 0) := by
  have harg :
      Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop := by
    convert
      (tendsto_atTop_add_const_right atTop (3 : ℝ)
        tendsto_natCast_atTop_atTop) using 1
    funext n
    norm_num
  have hlim :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  simpa only [Function.comp_apply, id_eq, amplitude] using hlim

private theorem alternating_amplitude_tendsto :
    ∃ l : ℝ,
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * amplitude k)
        atTop (𝓝 l) :=
  amplitude_antitone.tendsto_alternating_series_of_tendsto_zero
    amplitude_tendsto_zero

private theorem sum_range_shift_two (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 2), f k) =
      (∑ k ∈ Finset.range 2, f k) +
        ∑ k ∈ Finset.range N, f (k + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.succ_add, Finset.sum_range_succ, ih]
      simp only [Finset.sum_range_succ]
      ring

private theorem logarithmicTerm_add_three (k : ℕ) :
    logarithmicTerm (k + 3) = -((-1 : ℝ) ^ k * amplitude k) := by
  simp only [logarithmicTerm, amplitude, pow_add]
  norm_num
  ring

private theorem logarithmicTerm_ordered_tendsto :
    ∃ L : ℝ,
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N, logarithmicTerm (k + 1))
        atTop (𝓝 L) := by
  obtain ⟨l, hl⟩ := alternating_amplitude_tendsto
  have htail :
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N, logarithmicTerm (k + 3))
        atTop (𝓝 (-l)) := by
    simpa only [logarithmicTerm_add_three,
      Finset.sum_neg_distrib] using hl.neg
  let c : ℝ := ∑ k ∈ Finset.range 2, logarithmicTerm (k + 1)
  refine ⟨c - l, ?_⟩
  apply (tendsto_add_atTop_iff_nat 2).mp
  have hshift :
      Tendsto
        (fun N : ℕ =>
          c + ∑ k ∈ Finset.range N, logarithmicTerm (k + 3))
        atTop (𝓝 (c - l)) := by
    simpa [sub_eq_add_neg] using tendsto_const_nhds.add htail
  refine hshift.congr' (Eventually.of_forall fun N => ?_)
  simpa [c, Nat.add_assoc] using
    (sum_range_shift_two
      (fun k : ℕ => logarithmicTerm (k + 1)) N).symm

private theorem abs_logarithmicTerm_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    |logarithmicTerm n| = Real.log n / (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  unfold logarithmicTerm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg (Real.log_nonneg hn'), abs_of_nonneg hn0]

private theorem abs_logarithmicTerm_not_ordered :
    ¬∃ L : ℝ,
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N, |logarithmicTerm (k + 1)|)
        atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hs : Summable (fun k : ℕ => |logarithmicTerm (k + 1)|) := by
    refine ⟨L, ?_⟩
    exact (hasSum_iff_tendsto_nat_of_nonneg
      (fun k => abs_nonneg (logarithmicTerm (k + 1))) L).2 hL
  have htail : Summable (fun n : ℕ => |logarithmicTerm (n + 3)|) := by
    have h :=
      (summable_nat_add_iff
        (f := fun k : ℕ => |logarithmicTerm (k + 1)|) 2).2 hs
    simpa [Nat.add_assoc] using h
  have hharmonicTail :
      Summable (fun n : ℕ => 1 / (((n + 3 : ℕ) : ℝ))) := by
    refine htail.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rw [abs_logarithmicTerm_of_one_le (n + 3) (by omega)]
    have hpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by positivity
    have hlog : (1 : ℝ) ≤ Real.log ((n + 3 : ℕ) : ℝ) := by
      rw [Real.le_log_iff_exp_le hpos]
      exact Real.exp_one_lt_three.le.trans (by norm_num)
    exact (div_le_div_iff_of_pos_right hpos).2 hlog
  have hharmonic : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => 1 / (n : ℝ)) 3).1 (by
        simpa [Nat.cast_add] using hharmonicTail)
  exact Real.not_summable_one_div_natCast hharmonic

private theorem summableFromOne_congr {f g : ℕ → ℝ}
    (hfg : ∀ n : ℕ, 1 ≤ n → f n = g n) :
    SummableFromOne f ↔ SummableFromOne g := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, hL.congr' (Eventually.of_forall fun N => ?_)⟩
    apply Finset.sum_congr rfl
    intro k hk
    exact hfg (k + 1) (by omega)
  · rintro ⟨L, hL⟩
    refine ⟨L, hL.congr' (Eventually.of_forall fun N => ?_)⟩
    apply Finset.sum_congr rfl
    intro k hk
    exact (hfg (k + 1) (by omega)).symm

/-- Source: `proof_gap/exercise_3094/1.txt`; use real powers and require `n ≥ 1`. -/
theorem gap1 :
    ∀ n : ℕ, 1 ≤ n →
      Real.log (p n) = 1 / (n : ℝ) * Real.log (signedPower n) := by
  intro n hn
  unfold p
  change Real.log (signedPower n ^ (1 / (n : ℝ))) =
    1 / (n : ℝ) * Real.log (signedPower n)
  rw [Real.log_rpow (signedPower_pos n hn)]

/-- Source: `proof_gap/exercise_3094/2.txt`; use the positive-index power law. -/
theorem gap2 :
    ∀ n : ℕ, 1 ≤ n →
      1 / (n : ℝ) * Real.log (signedPower n) = logarithmicTerm n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold signedPower logarithmicTerm
  change 1 / (n : ℝ) * Real.log ((n : ℝ) ^ ((-1 : ℝ) ^ n)) =
    (-1 : ℝ) ^ n * Real.log n / (n : ℝ)
  rw [Real.log_rpow hnpos]
  ring

/-- Source: `proof_gap/exercise_3094/3.txt`. -/
theorem gap3 :
    ∀ n : ℕ, 1 ≤ n → Real.log (p n) = logarithmicTerm n := by
  intro n hn
  exact (gap1 n hn).trans (gap2 n hn)

/-- Source: `proof_gap/exercise_3094/4.txt`. -/
theorem gap4 : ConditionallySummableFromOne logarithmicTerm := by
  exact ⟨logarithmicTerm_ordered_tendsto,
    abs_logarithmicTerm_not_ordered⟩

/-- Source: `proof_gap/exercise_3094/5.txt`. -/
theorem gap5 :
    ConditionallySummableFromOne (fun n => Real.log (p n)) := by
  rcases gap4 with ⟨hconv, habs⟩
  have hpoint :
      ∀ n : ℕ, 1 ≤ n → Real.log (p n) = logarithmicTerm n :=
    gap3
  refine ⟨(summableFromOne_congr hpoint).2 hconv, ?_⟩
  intro h
  apply habs
  exact (summableFromOne_congr fun n hn =>
    congrArg abs (hpoint n hn)).1 h

end

end ProofGap.Exercise3094
