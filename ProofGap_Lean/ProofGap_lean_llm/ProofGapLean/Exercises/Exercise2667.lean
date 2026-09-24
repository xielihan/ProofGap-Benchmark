import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2667

noncomputable section

open Filter
open scoped BigOperators

def weight (n : ℕ) : ℝ :=
  Real.log n ^ 100 / n

def sinePartial (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, Real.sin (k * Real.pi / 4)

def closedForm (n : ℕ) : ℝ :=
  (Real.cos (Real.pi / 8) -
      Real.cos (((n : ℝ) + 1 / 2) * (Real.pi / 4))) /
    (2 * Real.sin (Real.pi / 8))

private theorem closedForm_succ (n : ℕ) :
    closedForm (n + 1) =
      closedForm n + Real.sin ((n + 1 : ℝ) * Real.pi / 4) := by
  have hsin : 0 < Real.sin (Real.pi / 8) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hangle1 :
      (((n + 1 : ℕ) : ℝ) + 1 / 2) * (Real.pi / 4) =
        ((n : ℝ) + 1 / 2) * (Real.pi / 4) + 2 * (Real.pi / 8) := by
    push_cast
    ring
  have hangle2 :
      ((n : ℝ) + 1) * Real.pi / 4 =
        ((n : ℝ) + 1 / 2) * (Real.pi / 4) + Real.pi / 8 := by
    ring
  unfold closedForm
  rw [hangle1, hangle2]
  rw [Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul]
  field_simp [ne_of_gt hsin]
  have hcos_sq :
      Real.cos (Real.pi / 8) ^ 2 = 1 - Real.sin (Real.pi / 8) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 8)]
  rw [hcos_sq]
  ring

private theorem sinePartial_succ (n : ℕ) :
    sinePartial (n + 1) =
      sinePartial n + Real.sin ((n + 1 : ℝ) * Real.pi / 4) := by
  unfold sinePartial
  rw [Finset.sum_Icc_succ_top (by omega)]
  norm_num [Nat.cast_add]

private theorem sinePartial_eq_closedForm (n : ℕ) :
    sinePartial n = closedForm n := by
  induction n with
  | zero =>
      have hangle :
          (((0 : ℕ) : ℝ) + 1 / 2) * (Real.pi / 4) = Real.pi / 8 := by
        norm_num
        ring
      unfold sinePartial closedForm
      rw [show Finset.Icc (1 : ℕ) 0 = ∅ by simp, Finset.sum_empty, hangle]
      simp
  | succ n ih =>
      rw [sinePartial_succ, closedForm_succ, ih]

private theorem sinePartial_eq_sum_range (n : ℕ) :
    sinePartial n =
      ∑ k ∈ Finset.range n,
        Real.sin ((k + 1 : ℕ) * Real.pi / 4) := by
  induction n with
  | zero => simp [sinePartial]
  | succ n ih =>
      rw [sinePartial_succ, Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add]

theorem gap1 :
    Tendsto weight atTop (nhds 0) := by
  unfold weight
  exact Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop

theorem gap2 :
    ∃ N : ℕ, Antitone (fun n : ℕ => weight (n + N)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp 100)
  refine ⟨N, ?_⟩
  intro a b hab
  have haN : Real.exp 100 ≤ ((a + N : ℕ) : ℝ) := by
    exact hN.trans (by exact_mod_cast Nat.le_add_left N a)
  have hbN : Real.exp 100 ≤ ((b + N : ℕ) : ℝ) := by
    exact hN.trans (by exact_mod_cast Nat.le_add_left N b)
  have habR : ((a + N : ℕ) : ℝ) ≤ ((b + N : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hab N
  have hantiBase := Real.log_div_self_rpow_antitoneOn (a := (1 / 100 : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 100)
  have haMem :
      ((a + N : ℕ) : ℝ) ∈ {x : ℝ | Real.exp (1 / (1 / 100 : ℝ)) ≤ x} := by
    change Real.exp (1 / (1 / 100 : ℝ)) ≤ ((a + N : ℕ) : ℝ)
    norm_num
    simpa only [Nat.cast_add] using haN
  have hbMem :
      ((b + N : ℕ) : ℝ) ∈ {x : ℝ | Real.exp (1 / (1 / 100 : ℝ)) ≤ x} := by
    change Real.exp (1 / (1 / 100 : ℝ)) ≤ ((b + N : ℕ) : ℝ)
    norm_num
    simpa only [Nat.cast_add] using hbN
  have hbase := hantiBase haMem hbMem habR
  have hxpos : 0 < ((a + N : ℕ) : ℝ) :=
    (Real.exp_pos 100).trans_le haN
  have hypos : 0 < ((b + N : ℕ) : ℝ) :=
    (Real.exp_pos 100).trans_le hbN
  have hlogy : 0 ≤ Real.log ((b + N : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ Real.exp 100 := by
      rw [← Real.exp_zero]
      exact Real.exp_monotone (by norm_num)
    exact Real.log_nonneg (this.trans hbN)
  have hnonneg :
      0 ≤ Real.log ((b + N : ℕ) : ℝ) /
        Real.rpow ((b + N : ℕ) : ℝ) (1 / 100 : ℝ) :=
    div_nonneg hlogy (Real.rpow_nonneg (le_of_lt hypos) _)
  have hp := pow_le_pow_left₀ hnonneg hbase 100
  have hpow_eq (x : ℝ) (hx : 0 < x) :
      (Real.log x / Real.rpow x (1 / 100 : ℝ)) ^ 100 =
        Real.log x ^ 100 / x := by
    rw [div_pow]
    congr 1
    calc
      (Real.rpow x (1 / 100 : ℝ)) ^ (100 : ℕ) =
          Real.rpow (Real.rpow x (1 / 100 : ℝ)) (100 : ℝ) := by
        exact (Real.rpow_natCast _ 100).symm
      _ = Real.rpow x ((1 / 100 : ℝ) * 100) := by
        exact (Real.rpow_mul (le_of_lt hx) _ _).symm
      _ = x := by
        norm_num
  unfold weight
  change Real.log ((b + N : ℕ) : ℝ) ^ 100 / ((b + N : ℕ) : ℝ) ≤
    Real.log ((a + N : ℕ) : ℝ) ^ 100 / ((a + N : ℕ) : ℝ)
  rw [← hpow_eq _ hypos, ← hpow_eq _ hxpos]
  exact hp

theorem gap3 :
    ∀ n : ℕ, |sinePartial n| = |closedForm n| := by
  intro n
  rw [sinePartial_eq_closedForm]

theorem gap4 :
    ∀ n : ℕ, |closedForm n| ≤ 1 / Real.sin (Real.pi / 8) := by
  intro n
  have hsin : 0 < Real.sin (Real.pi / 8) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hnum :
      |Real.cos (Real.pi / 8) -
          Real.cos (((n : ℝ) + 1 / 2) * (Real.pi / 4))| ≤ 2 := by
    calc
      |Real.cos (Real.pi / 8) -
          Real.cos (((n : ℝ) + 1 / 2) * (Real.pi / 4))| ≤
          |Real.cos (Real.pi / 8)| +
            |Real.cos (((n : ℝ) + 1 / 2) * (Real.pi / 4))| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = 2 := by norm_num
  unfold closedForm
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hsin)]
  calc
    |Real.cos (Real.pi / 8) -
        Real.cos (((n : ℝ) + 1 / 2) * (Real.pi / 4))| /
          (2 * Real.sin (Real.pi / 8)) ≤
        2 / (2 * Real.sin (Real.pi / 8)) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hsin)).2 hnum
    _ = 1 / Real.sin (Real.pi / 8) := by
      field_simp [ne_of_gt hsin]

theorem gap5 :
    ∀ n : ℕ, |sinePartial n| ≤ 1 / Real.sin (Real.pi / 8) := by
  intro n
  rw [gap3 n]
  exact gap4 n

theorem gap6 :
    Bornology.IsBounded (Set.range sinePartial) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1 / Real.sin (Real.pi / 8), ?_⟩
  rintro x ⟨n, rfl⟩
  simpa [Real.norm_eq_abs] using gap5 n

theorem gap7 :
    ProofGap.SeriesConverges
      (fun n : ℕ =>
        weight (n + 1) * Real.sin ((n + 1 : ℝ) * Real.pi / 4)) := by
  let u : ℕ → ℝ := fun n =>
    weight (n + 1) * Real.sin ((n + 1 : ℝ) * Real.pi / 4)
  let v : ℕ → ℝ := fun n =>
    Real.sin (((n + 1 : ℕ) : ℝ) * Real.pi / 4)
  unfold ProofGap.SeriesConverges
  change Summable u (SummationFilter.conditional ℕ)
  obtain ⟨N, hanti⟩ := gap2
  let a : ℕ → ℝ := fun n => weight (n + N + 1)
  let z : ℕ → ℝ := fun n => v (N + n)
  have ha : Antitone a := by
    intro i j hij
    have h := hanti (Nat.add_le_add_right hij 1)
    simpa [a, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have ha0 : Tendsto a atTop (nhds 0) := by
    simpa [a, Nat.add_assoc] using
      gap1.comp (tendsto_add_atTop_nat (N + 1))
  have hvsum (m : ℕ) :
      (∑ i ∈ Finset.range m, v i) = sinePartial m := by
    symm
    simpa [v] using sinePartial_eq_sum_range m
  have htail (r : ℕ) :
      (∑ i ∈ Finset.range r, z i) =
        sinePartial (N + r) - sinePartial N := by
    rw [← hvsum (N + r), ← hvsum N]
    change (∑ i ∈ Finset.range r, v (N + i)) =
      (∑ i ∈ Finset.range (N + r), v i) -
        ∑ i ∈ Finset.range N, v i
    rw [Finset.sum_range_add]
    ring
  have hzbound (r : ℕ) :
      ‖∑ i ∈ Finset.range r, z i‖ ≤
        2 * (1 / Real.sin (Real.pi / 8)) := by
    rw [htail, Real.norm_eq_abs]
    calc
      |sinePartial (N + r) - sinePartial N| ≤
          |sinePartial (N + r)| + |sinePartial N| := abs_sub _ _
      _ ≤ 1 / Real.sin (Real.pi / 8) +
          1 / Real.sin (Real.pi / 8) := add_le_add (gap5 _) (gap5 _)
      _ = 2 * (1 / Real.sin (Real.pi / 8)) := by ring
  have htailC :
      CauchySeq (fun r => ∑ i ∈ Finset.range r, a i • z i) :=
    ha.cauchySeq_series_mul_of_tendsto_zero_of_bounded ha0 hzbound
  have htailU :
      CauchySeq (fun r => ∑ i ∈ Finset.range r, u (N + i)) := by
    simpa [a, z, u, v, smul_eq_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.cast_add] using htailC
  have hshiftC :
      CauchySeq (fun r => ∑ i ∈ Finset.range (N + r), u i) := by
    have h : CauchySeq (fun r =>
        (∑ i ∈ Finset.range r, u (N + i)) +
          ∑ i ∈ Finset.range N, u i) :=
      htailU.add_const
    convert h using 1
    ext r
    rw [Finset.sum_range_add]
    ring
  have hfull : CauchySeq (fun r => ∑ i ∈ Finset.range r, u i) := by
    rw [← cauchySeq_shift N]
    simpa [Nat.add_comm] using hshiftC
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hfull
  refine ⟨s, ?_⟩
  simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_apply] using hs

end

end ProofGap.Exercise2667
