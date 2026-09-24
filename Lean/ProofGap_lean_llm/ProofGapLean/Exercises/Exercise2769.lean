import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2769

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) (x : ℝ) : ℝ :=
  (1 - x) * x ^ n

def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), term k x

def limit (x : ℝ) : ℝ :=
  if x < 1 then 1 else 0

def badPoint (n : ℕ) : ℝ :=
  Real.rpow 2 (-1 / ((n + 1 : ℕ) : ℝ))

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private theorem badPoint_facts (n : ℕ) :
    0 ≤ badPoint n ∧ badPoint n < 1 ∧
      badPoint n ^ (n + 1) = (1 / 2 : ℝ) := by
  constructor
  · unfold badPoint
    exact Real.rpow_nonneg (by norm_num) _
  constructor
  · unfold badPoint
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · norm_num
    · exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  · unfold badPoint
    have hden : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hexp :
        (-1 / (((n + 1 : ℕ) : ℝ))) * (((n + 1 : ℕ) : ℝ)) = (-1 : ℝ) := by
      field_simp [hden]
    have hbase :
        0 ≤ Real.rpow 2 (-1 / (((n + 1 : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    calc
      (Real.rpow 2 (-1 / (((n + 1 : ℕ) : ℝ)))) ^ (n + 1) =
          Real.rpow (Real.rpow 2 (-1 / (((n + 1 : ℕ) : ℝ))))
            (((n + 1 : ℕ) : ℝ)) := by
              simpa only [abs_of_nonneg hbase] using
                (Real.rpow_natCast
                  (Real.rpow 2 (-1 / (((n + 1 : ℕ) : ℝ)))) (n + 1)).symm
      _ = Real.rpow 2
          ((-1 / (((n + 1 : ℕ) : ℝ))) * (((n + 1 : ℕ) : ℝ))) := by
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
              (-1 / (((n + 1 : ℕ) : ℝ))) (((n + 1 : ℕ) : ℝ))).symm
      _ = (1 / 2 : ℝ) := by
            rw [hexp]
            norm_num

theorem gap1 (S : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hS : S n x = partialSum n x) :
    S n x = partialSum n x := by
  exact hS

theorem gap2 (n : ℕ) (x : ℝ) :
    partialSum n x =
      (1 - x) * (∑ k ∈ Finset.range (n + 1), x ^ k) := by
  simp only [partialSum, term, Finset.mul_sum]

theorem gap3 (n : ℕ) (x : ℝ) :
    (1 - x) * (∑ k ∈ Finset.range (n + 1), x ^ k) =
      1 - x ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

theorem gap4 (S : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hS : S n x = partialSum n x) :
    S n x = 1 - x ^ (n + 1) := by
  calc
    S n x = partialSum n x := hS
    _ = (1 - x) * (∑ k ∈ Finset.range (n + 1), x ^ k) := gap2 n x
    _ = 1 - x ^ (n + 1) := gap3 n x

theorem gap5 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => partialSum n x) atTop (nhds (limit x)) := by
  by_cases hlt : x < 1
  · have hnorm : ‖x‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hlt
    have hpow : Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
    have hpowSucc : Tendsto (fun n : ℕ => x ^ (n + 1)) atTop (nhds 0) := by
      simpa [pow_succ] using hpow.mul_const x
    have hpartial :
        Tendsto (fun n : ℕ => 1 - x ^ (n + 1)) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hpowSucc)
    simpa [limit, hlt, gap2, gap3] using hpartial
  · have hxone : x = 1 := le_antisymm hx.2 (not_lt.mp hlt)
    subst x
    simp [partialSum, term, limit]

theorem gap6 (n : ℕ) :
    |partialSum n (badPoint n) - limit (badPoint n)| =
      |(1 / 2 : ℝ) - 1| := by
  rw [gap2, gap3, (badPoint_facts n).2.2]
  norm_num [limit, (badPoint_facts n).2.1]

theorem gap7 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    |(1 / 2 : ℝ) - 1| = 1 / 2 := by
  norm_num

theorem gap8 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    (1 / 2 : ℝ) > ε := by
  exact hεhalf

theorem gap9 (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    |partialSum n (badPoint n) - limit (badPoint n)| > ε := by
  rw [gap6 n, gap7 ε hε hεhalf]
  exact hεhalf

theorem gap10 :
    ¬ SeriesUniformlyConvergesOn term (Set.Icc (0 : ℝ) 1) limit := by
  intro h
  unfold SeriesUniformlyConvergesOn at h
  rcases h (1 / 4 : ℝ) (by norm_num) with ⟨N, hN⟩
  have hu := hN N le_rfl (badPoint N)
    ⟨(badPoint_facts N).1, le_of_lt (badPoint_facts N).2.1⟩
  change |partialSum N (badPoint N) - limit (badPoint N)| < (1 / 4 : ℝ) at hu
  have hl := gap9 N (1 / 4 : ℝ) (by norm_num) (by norm_num)
  linarith

theorem gap11 :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, Summable (fun n => term n x)) ∧
    ¬ SeriesUniformlyConvergesOn term (Set.Icc (0 : ℝ) 1) limit := by
  constructor
  · intro x hx
    by_cases hlt : x < 1
    · have hnorm : ‖x‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hlt
      have hs : Summable (fun n : ℕ => x ^ n) :=
        summable_geometric_of_norm_lt_one hnorm
      simpa [term] using hs.mul_left (1 - x)
    · have hxone : x = 1 := le_antisymm hx.2 (not_lt.mp hlt)
      subst x
      simp [term]
  · exact gap10

end

end ProofGap.Exercise2769
