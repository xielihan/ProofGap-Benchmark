import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2808

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  1 / ((2 : ℝ) ^ n * Real.rpow (n : ℝ) x)

def seriesFunction (x : ℝ) : ℝ :=
  ∑' k : ℕ, term (k + 1) x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (m + 1), u k x) - f x| < ε

private theorem continuous_term {n : ℕ} (hn : 1 ≤ n) : Continuous (term n) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn'
  have hp : Continuous (fun x : ℝ => Real.rpow (n : ℝ) x) := by
    have heq :
        (fun x : ℝ => Real.rpow (n : ℝ) x) =
          fun x : ℝ => Real.exp (Real.log (n : ℝ) * x) := by
      funext x
      exact Real.rpow_def_of_pos hnpos x
    rw [heq]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hd : Continuous
      (fun x : ℝ => (2 : ℝ) ^ n * Real.rpow (n : ℝ) x) :=
    continuous_const.mul hp
  have hdne : ∀ x : ℝ,
      (2 : ℝ) ^ n * Real.rpow (n : ℝ) x ≠ 0 := by
    intro x
    have hpowne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hrpowne : Real.rpow (n : ℝ) x ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hnpos x)
    exact mul_ne_zero hpowne hrpowne
  simpa [term] using (continuous_const.div hd hdne)

theorem gap1 :
    ∀ (n : ℕ) (x l : ℝ), 1 ≤ n → 0 ≤ x → x ≤ l → 0 < l →
      1 / Real.rpow (n : ℝ) x ≤ 1 := by
  intro n x l hn hx hxl hl
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn'
  have hrpos : 0 < Real.rpow (n : ℝ) x := Real.rpow_pos_of_pos hnpos x
  apply (div_le_iff₀ hrpos).2
  simpa using Real.one_le_rpow hn' hx

theorem gap2 :
    Summable (fun k : ℕ => 1 / (2 : ℝ) ^ (k + 1)) := by
  have hgeom : Summable (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hshift := hgeom.comp_injective Nat.succ_injective
  simpa [one_div, Nat.succ_eq_add_one] using hshift

theorem gap3 :
    ∀ l : ℝ, 0 < l →
      SeriesUniformlyConvergesOn
        (fun k x => term (k + 1) x)
        (Set.Icc (0 : ℝ) l) seriesFunction := by
  intro l hl
  have hmajor : ∀ k : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) l,
      ‖term (k + 1) x‖ ≤ 1 / (2 : ℝ) ^ (k + 1) := by
    intro k x hx
    have hn : 1 ≤ k + 1 := by omega
    have hnpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < k + 1 by omega)
    have hrpos : 0 < Real.rpow ((k + 1 : ℕ) : ℝ) x :=
      Real.rpow_pos_of_pos hnpos x
    have hterm : 0 ≤ term (k + 1) x := by
      unfold term
      exact le_of_lt (one_div_pos.mpr (mul_pos (pow_pos (by norm_num) _) hrpos))
    have hfactor :
        1 / ((2 : ℝ) ^ (k + 1) * Real.rpow ((k + 1 : ℕ) : ℝ) x) =
          (1 / (2 : ℝ) ^ (k + 1)) *
            (1 / Real.rpow ((k + 1 : ℕ) : ℝ) x) := by
      field_simp [ne_of_gt hrpos]
    rw [Real.norm_eq_abs, abs_of_nonneg hterm, term, hfactor]
    have hb := gap1 (k + 1) x l hn hx.1 hx.2 hl
    simpa using
      (mul_le_mul_of_nonneg_left hb
        (show 0 ≤ 1 / (2 : ℝ) ^ (k + 1) by positivity))
  unfold SeriesUniformlyConvergesOn
  intro ε hε
  have hlim :
      Tendsto
        (fun q : ℕ => ∑ k ∈ Finset.range q, 1 / (2 : ℝ) ^ (k + 1))
        atTop
        (𝓝 (∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1))) :=
    gap2.hasSum.tendsto_sum_nat
  have hevent :
      ∀ᶠ q : ℕ in atTop,
        dist (∑ k ∈ Finset.range q, 1 / (2 : ℝ) ^ (k + 1))
          (∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1)) < ε :=
    (Metric.tendsto_nhds.1 hlim) ε hε
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm x hx
  have hNq : N ≤ m + 1 := le_trans hm (Nat.le_succ m)
  have hclose := hN (m + 1) hNq
  have hsBtail :
      Summable
        (fun k : ℕ => 1 / (2 : ℝ) ^ ((k + (m + 1)) + 1)) :=
    gap2.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)
  have htailBnonneg :
      0 ≤ ∑' k : ℕ, 1 / (2 : ℝ) ^ ((k + (m + 1)) + 1) :=
    tsum_nonneg (fun k => by positivity)
  have hsplitB :
      (∑ k ∈ Finset.range (m + 1), 1 / (2 : ℝ) ^ (k + 1)) +
          (∑' k : ℕ, 1 / (2 : ℝ) ^ ((k + (m + 1)) + 1)) =
        ∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1) :=
    gap2.sum_add_tsum_nat_add (m + 1)
  have hdiffB :
      (∑ k ∈ Finset.range (m + 1), 1 / (2 : ℝ) ^ (k + 1)) -
          (∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1)) =
        -(∑' k : ℕ, 1 / (2 : ℝ) ^ ((k + (m + 1)) + 1)) := by
    linarith
  have htailBlt :
      (∑' k : ℕ, 1 / (2 : ℝ) ^ ((k + (m + 1)) + 1)) < ε := by
    rw [Real.dist_eq, hdiffB, abs_neg, abs_of_nonneg htailBnonneg] at hclose
    exact hclose
  have hax : ∀ k : ℕ,
      ‖term (k + 1) x‖ ≤ 1 / (2 : ℝ) ^ (k + 1) := by
    intro k
    exact hmajor k x hx
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ term (k + 1) x := by
    intro k
    have hnpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < k + 1 by omega)
    have hrpos : 0 < Real.rpow ((k + 1 : ℕ) : ℝ) x :=
      Real.rpow_pos_of_pos hnpos x
    unfold term
    exact le_of_lt (one_div_pos.mpr (mul_pos (pow_pos (by norm_num) _) hrpos))
  have hval : ∀ k : ℕ,
      term (k + 1) x ≤ 1 / (2 : ℝ) ^ (k + 1) := by
    intro k
    simpa [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg k)] using hax k
  have hsA : Summable (fun k : ℕ => term (k + 1) x) :=
    gap2.of_norm_bounded hax
  have hsAtail :
      Summable (fun k : ℕ => term ((k + (m + 1)) + 1) x) :=
    hsA.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)
  have hsplitA :
      (∑ k ∈ Finset.range (m + 1), term (k + 1) x) +
          (∑' k : ℕ, term ((k + (m + 1)) + 1) x) =
        ∑' k : ℕ, term (k + 1) x :=
    hsA.sum_add_tsum_nat_add (m + 1)
  have hdiffA :
      (∑ k ∈ Finset.range (m + 1), term (k + 1) x) -
          (∑' k : ℕ, term (k + 1) x) =
        -(∑' k : ℕ, term ((k + (m + 1)) + 1) x) := by
    linarith
  have htailAnonneg :
      0 ≤ ∑' k : ℕ, term ((k + (m + 1)) + 1) x :=
    tsum_nonneg (fun k => hterm_nonneg (k + (m + 1)))
  change
    |(∑ k ∈ Finset.range (m + 1), term (k + 1) x) -
      (∑' k : ℕ, term (k + 1) x)| < ε
  rw [hdiffA, abs_neg, abs_of_nonneg htailAnonneg]
  have htailDiffHasSum :
      HasSum
        (fun k : ℕ =>
          1 / (2 : ℝ) ^ ((k + (m + 1)) + 1) -
            term ((k + (m + 1)) + 1) x)
        ((∑' k : ℕ, 1 / (2 : ℝ) ^ ((k + (m + 1)) + 1)) -
          (∑' k : ℕ, term ((k + (m + 1)) + 1) x)) :=
    hsBtail.hasSum.sub hsAtail.hasSum
  have htailDiffNonneg :
      0 ≤ ∑' k : ℕ,
        (1 / (2 : ℝ) ^ ((k + (m + 1)) + 1) -
          term ((k + (m + 1)) + 1) x) :=
    tsum_nonneg (fun k => sub_nonneg.mpr (hval (k + (m + 1))))
  have htailAle :
      (∑' k : ℕ, term ((k + (m + 1)) + 1) x) ≤
        ∑' k : ℕ, 1 / (2 : ℝ) ^ ((k + (m + 1)) + 1) := by
    rw [htailDiffHasSum.tsum_eq] at htailDiffNonneg
    exact sub_nonneg.mp htailDiffNonneg
  exact lt_of_le_of_lt htailAle htailBlt

theorem gap4 :
    ∀ (n : ℕ) (l : ℝ), 1 ≤ n → 0 < l →
      ContinuousOn (term n) (Set.Icc (0 : ℝ) l) := by
  intro n l hn hl
  exact (continuous_term hn).continuousOn

theorem gap5 :
    ∀ n : ℕ, 1 ≤ n →
      Tendsto (term n) (𝓝[>] (0 : ℝ)) (𝓝 (1 / (2 : ℝ) ^ n)) := by
  intro n hn
  have h :
      Tendsto (term n) (𝓝 (0 : ℝ)) (𝓝 (term n 0)) :=
    (continuous_term hn).continuousAt
  have hw :
      Tendsto (term n) (𝓝[>] (0 : ℝ)) (𝓝 (term n 0)) :=
    h.mono_left inf_le_left
  simpa [term] using hw

theorem gap6 :
    Tendsto seriesFunction (𝓝[>] (0 : ℝ))
      (𝓝 (∑' k : ℕ, term (k + 1) 0)) := by
  change Tendsto seriesFunction (𝓝[>] (0 : ℝ)) (𝓝 (seriesFunction 0))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  rcases gap3 1 (by norm_num) (ε / 3) hthird with ⟨N, hN⟩
  have hp :
      Tendsto
        (fun x : ℝ => ∑ k ∈ Finset.range (N + 1), term (k + 1) x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ k ∈ Finset.range (N + 1), term (k + 1) 0)) := by
    apply tendsto_finset_sum
    intro k hk
    simpa [term] using gap5 (k + 1) (by omega)
  have hmiddle :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        dist (∑ k ∈ Finset.range (N + 1), term (k + 1) x)
          (∑ k ∈ Finset.range (N + 1), term (k + 1) 0) < ε / 3 :=
    (Metric.tendsto_nhds.1 hp) (ε / 3) hthird
  have hIoc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (by norm_num)
  have hzero := hN N le_rfl 0 (by constructor <;> norm_num)
  filter_upwards [hmiddle, hIoc] with x hmid hx
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
  have hxU := hN N le_rfl x hxmem
  have hxU' :
      |seriesFunction x -
        (∑ k ∈ Finset.range (N + 1), term (k + 1) x)| < ε / 3 := by
    simpa [abs_sub_comm] using hxU
  simp only [Real.dist_eq] at hmid ⊢
  calc
    |seriesFunction x - seriesFunction 0| =
        |(seriesFunction x -
            (∑ k ∈ Finset.range (N + 1), term (k + 1) x)) +
          (((∑ k ∈ Finset.range (N + 1), term (k + 1) x) -
              ∑ k ∈ Finset.range (N + 1), term (k + 1) 0) +
            ((∑ k ∈ Finset.range (N + 1), term (k + 1) 0) -
              seriesFunction 0))| := by
          congr 1
          ring
    _ ≤ |seriesFunction x -
            (∑ k ∈ Finset.range (N + 1), term (k + 1) x)| +
          |((∑ k ∈ Finset.range (N + 1), term (k + 1) x) -
              ∑ k ∈ Finset.range (N + 1), term (k + 1) 0) +
            ((∑ k ∈ Finset.range (N + 1), term (k + 1) 0) -
              seriesFunction 0)| := abs_add_le _ _
    _ ≤ |seriesFunction x -
            (∑ k ∈ Finset.range (N + 1), term (k + 1) x)| +
          (|(∑ k ∈ Finset.range (N + 1), term (k + 1) x) -
              ∑ k ∈ Finset.range (N + 1), term (k + 1) 0| +
            |(∑ k ∈ Finset.range (N + 1), term (k + 1) 0) -
              seriesFunction 0|) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left
            (abs_add_le
              ((∑ k ∈ Finset.range (N + 1), term (k + 1) x) -
                ∑ k ∈ Finset.range (N + 1), term (k + 1) 0)
              ((∑ k ∈ Finset.range (N + 1), term (k + 1) 0) -
                seriesFunction 0))
            |seriesFunction x -
              (∑ k ∈ Finset.range (N + 1), term (k + 1) x)|
    _ < ε := by linarith

theorem gap7 :
    (∑' k : ℕ, term (k + 1) 0) =
      ∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1) := by
  apply tsum_congr
  intro k
  simp [term]

theorem gap8 :
    (∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1)) = 1 := by
  have hgeom :
      HasSum (fun k : ℕ => ((1 / 2 : ℝ) ^ k))
        ((1 - (1 / 2 : ℝ))⁻¹) :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have hshift := hgeom.mul_left (1 / 2 : ℝ)
  calc
    (∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1)) =
        ∑' k : ℕ, (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
          apply tsum_congr
          intro k
          simp [one_div, pow_succ, mul_comm]
    _ = (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹ := hshift.tsum_eq
    _ = 1 := by norm_num

theorem gap9 :
    Tendsto seriesFunction (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := gap6
  rw [gap7, gap8] at h
  exact h

end

end ProofGap.Exercise2808
