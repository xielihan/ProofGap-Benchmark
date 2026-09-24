import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2713

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) / Real.sqrt n

def convolution (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, term i * term (n - i + 1)

def amplitude (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    1 / (Real.sqrt i * Real.sqrt (n - i + 1))

private theorem convolution_facts :
    (∀ n : ℕ,
      convolution n = (-1 : ℝ) ^ (n - 1) * amplitude n) ∧
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k ≤ n →
      1 / (Real.sqrt k * Real.sqrt (n - k + 1)) > 1 / (n : ℝ)) ∧
    (∀ n : ℕ, 2 ≤ n → |convolution n| > 1) ∧
    ¬ Tendsto (fun n : ℕ => convolution (n + 1)) atTop (nhds 0) := by
  have hformula :
      ∀ n : ℕ,
        convolution n = (-1 : ℝ) ^ (n - 1) * amplitude n := by
    intro n
    simp only [convolution, amplitude]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    unfold term
    have hexp :
        (i - 1) + (n - i + 1 - 1) = n - 1 := by
      omega
    have hcast :
        ((n - i + 1 : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hi'.2]
      norm_num
    calc
      ((-1 : ℝ) ^ (i - 1) / Real.sqrt i) *
          ((-1 : ℝ) ^ (n - i + 1 - 1) /
            Real.sqrt ((n - i + 1 : ℕ) : ℝ)) =
          (((-1 : ℝ) ^ (i - 1)) *
            ((-1 : ℝ) ^ (n - i + 1 - 1))) /
              (Real.sqrt i * Real.sqrt ((n - i + 1 : ℕ) : ℝ)) := by
                rw [div_mul_div_comm]
      _ = (-1 : ℝ) ^ (n - 1) /
              (Real.sqrt i * Real.sqrt ((n - i + 1 : ℕ) : ℝ)) := by
            rw [← pow_add, hexp]
      _ = (-1 : ℝ) ^ (n - 1) /
              (Real.sqrt i * Real.sqrt ((n : ℝ) - (i : ℝ) + 1)) := by
            rw [hcast]
      _ = (-1 : ℝ) ^ (n - 1) *
              (1 / (Real.sqrt i *
                Real.sqrt ((n : ℝ) - (i : ℝ) + 1))) := by
            ring
  have hbound :
      ∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k ≤ n →
        1 / (Real.sqrt k * Real.sqrt (n - k + 1)) > 1 / (n : ℝ) := by
    intro n k hn hk hkn
    have hnposNat : 0 < n := by omega
    have hkposNat : 0 < k := by omega
    have hjposNat : 0 < n - k + 1 := by omega
    have hjnNat : n - k + 1 ≤ n := by omega
    have hstrictNat : k < n ∨ n - k + 1 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkposNat
    have hjpos : (0 : ℝ) < ((n - k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hjposNat
    have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hjnR : ((n - k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hjnNat
    have hjcast :
        ((n - k + 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hkn]
      norm_num
    have hprod :
        (k : ℝ) * ((n - k + 1 : ℕ) : ℝ) < (n : ℝ) ^ 2 := by
      rcases hstrictNat with hknStrict | hjnStrict
      · have hknStrictR : (k : ℝ) < (n : ℝ) := by
          exact_mod_cast hknStrict
        have hleft :
            0 < ((n : ℝ) - (k : ℝ)) * ((n - k + 1 : ℕ) : ℝ) :=
          mul_pos (sub_pos.mpr hknStrictR) hjpos
        have hright :
            0 ≤ (n : ℝ) * ((n : ℝ) - ((n - k + 1 : ℕ) : ℝ)) :=
          mul_nonneg (le_of_lt hnpos) (sub_nonneg.mpr hjnR)
        nlinarith
      · have hjnStrictR : ((n - k + 1 : ℕ) : ℝ) < (n : ℝ) := by
          exact_mod_cast hjnStrict
        have hleft :
            0 ≤ ((n : ℝ) - (k : ℝ)) * ((n - k + 1 : ℕ) : ℝ) :=
          mul_nonneg (sub_nonneg.mpr hknR) (le_of_lt hjpos)
        have hright :
            0 < (n : ℝ) * ((n : ℝ) - ((n - k + 1 : ℕ) : ℝ)) :=
          mul_pos hnpos (sub_pos.mpr hjnStrictR)
        nlinarith
    have hkSq :
        (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) :=
      Real.sq_sqrt (le_of_lt hkpos)
    have hjSq :
        (Real.sqrt ((n - k + 1 : ℕ) : ℝ)) ^ 2 =
          ((n - k + 1 : ℕ) : ℝ) :=
      Real.sq_sqrt (le_of_lt hjpos)
    have hdenSq :
        (Real.sqrt (k : ℝ) *
            Real.sqrt ((n - k + 1 : ℕ) : ℝ)) ^ 2 =
          (k : ℝ) * ((n - k + 1 : ℕ) : ℝ) := by
      rw [mul_pow, hkSq, hjSq]
    have hdenpos :
        0 < Real.sqrt (k : ℝ) *
          Real.sqrt ((n - k + 1 : ℕ) : ℝ) :=
      mul_pos (Real.sqrt_pos.2 hkpos) (Real.sqrt_pos.2 hjpos)
    have hdenlt :
        Real.sqrt (k : ℝ) *
            Real.sqrt ((n - k + 1 : ℕ) : ℝ) < (n : ℝ) := by
      by_contra h
      have hge :
          (n : ℝ) ≤ Real.sqrt (k : ℝ) *
            Real.sqrt ((n - k + 1 : ℕ) : ℝ) :=
        le_of_not_gt h
      have hfactor :
          0 ≤
            (Real.sqrt (k : ℝ) *
                Real.sqrt ((n - k + 1 : ℕ) : ℝ) - (n : ℝ)) *
              (Real.sqrt (k : ℝ) *
                Real.sqrt ((n - k + 1 : ℕ) : ℝ) + (n : ℝ)) :=
        mul_nonneg (sub_nonneg.mpr hge)
          (add_nonneg (le_of_lt hdenpos) (le_of_lt hnpos))
      nlinarith
    have hrecip :
        1 / (Real.sqrt (k : ℝ) *
          Real.sqrt ((n - k + 1 : ℕ) : ℝ)) > 1 / (n : ℝ) :=
      one_div_lt_one_div_of_lt hdenpos hdenlt
    simpa [hjcast] using hrecip
  have hamplitude :
      ∀ n : ℕ, 2 ≤ n → amplitude n > 1 := by
    intro n hn
    have hnposNat : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
    have hsum :
        (∑ i ∈ Finset.Icc 1 n, (1 / (n : ℝ))) < amplitude n := by
      unfold amplitude
      refine Finset.sum_lt_sum ?_ ?_
      · intro i hi
        have hi' := Finset.mem_Icc.mp hi
        exact (hbound n i hn hi'.1 hi'.2).le
      · refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
        exact hbound n 1 hn le_rfl (by omega)
    have hcard : (Finset.Icc 1 n).card = n := by
      simp
    have hconst :
        (∑ i ∈ Finset.Icc 1 n, (1 / (n : ℝ))) = 1 := by
      simp [Finset.sum_const, hcard, nsmul_eq_mul, ne_of_gt hnpos]
    rw [hconst] at hsum
    exact hsum
  have habs :
      ∀ n : ℕ, 2 ≤ n → |convolution n| > 1 := by
    intro n hn
    have hamp := hamplitude n hn
    calc
      |convolution n| =
          |(-1 : ℝ) ^ (n - 1)| * |amplitude n| := by
            rw [hformula n, abs_mul]
      _ = amplitude n := by
            simp [abs_of_pos (by linarith : 0 < amplitude n)]
      _ > 1 := hamp
  have hnotend :
      ¬ Tendsto (fun n : ℕ => convolution (n + 1)) atTop (nhds 0) := by
    intro ht
    have hevent :
        ∀ᶠ n : ℕ in atTop, dist (convolution (n + 1)) 0 < 1 :=
      (Metric.tendsto_nhds.1 ht) 1 zero_lt_one
    rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
    have hdist := hN (max N 1) (le_max_left N 1)
    have hn : 1 ≤ max N 1 := le_max_right N 1
    have hab := habs (max N 1 + 1) (by omega)
    have hsmall : |convolution (max N 1 + 1)| < 1 := by
      simpa [Real.dist_eq] using hdist
    linarith
  exact ⟨hformula, hbound, habs, hnotend⟩

theorem gap1 (hconv : Summable (fun n : ℕ => convolution (n + 1))) :
    (∑' n : ℕ, term (n + 1)) ^ 2 =
      ∑' n : ℕ, convolution (n + 1) := by
  exfalso
  exact convolution_facts.2.2.2 hconv.tendsto_atTop_zero

theorem gap2 :
    ∀ n : ℕ,
      convolution n =
        ∑ i ∈ Finset.Icc 1 n, term i * term (n - i + 1) := by
  intro n
  rfl

theorem gap3 :
    ∀ n : ℕ,
      convolution n = (-1 : ℝ) ^ (n - 1) * amplitude n := by
  exact convolution_facts.1

theorem gap4 :
    ∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k ≤ n →
      1 / (Real.sqrt k * Real.sqrt (n - k + 1)) > 1 / (n : ℝ) := by
  exact convolution_facts.2.1

theorem gap5 :
    ∀ n : ℕ, 2 ≤ n → |convolution n| > 1 := by
  exact convolution_facts.2.2.1

theorem gap6 :
    ¬ Tendsto (fun n : ℕ => convolution (n + 1)) atTop (nhds 0) := by
  exact convolution_facts.2.2.2

theorem gap7 :
    Summable (fun n : ℕ => convolution (n + 1)) → False := by
  intro h
  exact convolution_facts.2.2.2 h.tendsto_atTop_zero

theorem gap8 :
    ¬ Summable (fun n : ℕ => convolution (n + 1)) := by
  exact gap7

theorem gap9 :
    ¬ Summable (fun n : ℕ => convolution (n + 1)) := by
  exact gap8

end

end ProofGap.Exercise2713
