import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise2759

noncomputable section

open Filter
open scoped Topology

def scaled (n : ℕ) (x : ℝ) : ℝ :=
  x / n

def term (n : ℕ) (x : ℝ) : ℝ :=
  scaled n x * Real.log (scaled n x)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => scaled n x) atTop (𝓝 0) := by
  intro x hx
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  simpa [scaled] using
    (tendsto_const_nhds.div_atTop hn :
      Tendsto (fun n : ℕ => x / (n : ℝ)) atTop (𝓝 0))

theorem gap2 :
    Tendsto (fun t : ℝ => t * Real.log t) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  refine Metric.tendsto_nhdsWithin_nhds.2 ?_
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  refine ⟨min 1 ((ε / 2) ^ 2), lt_min zero_lt_one (pow_pos he 2), ?_⟩
  intro t ht hdist
  change 0 < t at ht
  have htδ : t < min 1 ((ε / 2) ^ 2) := by
    simpa [Real.dist_eq, abs_of_pos ht] using hdist
  have ht_one : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
  have ht_sq : t < (ε / 2) ^ 2 := lt_of_lt_of_le htδ (min_le_right _ _)
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsne : Real.sqrt t ≠ 0 := ne_of_gt hspos
  have hs_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
  have hslt : Real.sqrt t < ε / 2 := by
    nlinarith [Real.sqrt_nonneg t]
  have hlogneg : Real.log t < 0 := Real.log_neg ht ht_one
  have hlogbound :
      Real.log (1 / Real.sqrt t) ≤ 1 / Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos (one_div_pos.mpr hspos)
  have hbase :
      -(Real.log t / 2) ≤ 1 / Real.sqrt t - 1 := by
    calc
      -(Real.log t / 2) = -Real.log (Real.sqrt t) := by
        rw [Real.log_sqrt (le_of_lt ht)]
      _ = Real.log (1 / Real.sqrt t) := by
        rw [one_div, Real.log_inv]
      _ ≤ 1 / Real.sqrt t - 1 := hlogbound
  have htdiv : t * (1 / Real.sqrt t) = Real.sqrt t := by
    calc
      t * (1 / Real.sqrt t) =
          (Real.sqrt t) ^ 2 * (1 / Real.sqrt t) := by rw [hs_sq]
      _ = Real.sqrt t := by field_simp [hsne]
  have hfactor : 0 ≤ 2 * t := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbase hfactor
  have hbound : -(t * Real.log t) ≤ 2 * Real.sqrt t := by
    nlinarith [hmul, htdiv]
  have hfinal : |t * Real.log t| < ε := by
    calc
      |t * Real.log t| = -(t * Real.log t) :=
        abs_of_neg (mul_neg_of_pos_of_neg ht hlogneg)
      _ ≤ 2 * Real.sqrt t := hbound
      _ < ε := by linarith
  simpa [Real.dist_eq] using hfinal

theorem gap3 :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx
  apply gap2.comp
  rw [tendsto_nhdsWithin_iff]
  refine ⟨gap1 x hx, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact div_pos hx.1 (Nat.cast_pos.2 hn)

theorem gap4 :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, (0 : ℝ) = 0 := by
  intro x hx
  rfl

theorem gap5 :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  exact gap3

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → x ∈ Set.Ioo (0 : ℝ) 1 →
      |term n x| = |scaled n x * Real.log (scaled n x)| := by
  intro n x hn hx
  rfl

theorem gap7 :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < t → t < δ → |t * Real.log t| < ε := by
  intro ε hε
  rcases (Metric.tendsto_nhdsWithin_nhds.1 gap2) ε hε with
    ⟨δ, hδ, h⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd
  have hdist : dist t 0 < δ := by
    simpa [Real.dist_eq, abs_of_pos ht] using htd
  have hout := h ht hdist
  simpa [Real.dist_eq] using hout

theorem gap8 :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 1 / (n : ℝ) < δ := by
  intro δ hδ
  rcases exists_nat_gt (1 / δ) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) < (n : ℝ) := Nat.cast_lt.2 hn
  have hn_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn_nat
  have hfrac : 1 / δ < (n : ℝ) := lt_trans hN hNn
  apply (div_lt_iff₀ hnpos).2
  simpa [mul_comm] using ((div_lt_iff₀ hδ).1 hfrac)

theorem gap9 :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < scaled n x ∧ scaled n x < δ := by
  intro δ hδ
  rcases gap8 δ hδ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn_nat
  constructor
  · exact div_pos hx.1 hnpos
  · calc
      scaled n x = x / (n : ℝ) := rfl
      _ < 1 / (n : ℝ) := (div_lt_div_iff_of_pos_right hnpos).2 hx.2
      _ < δ := hN n hn

theorem gap10 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → x ∈ Set.Ioo (0 : ℝ) 1 →
      |term n x| = |scaled n x * Real.log (scaled n x)| := by
  exact gap6

theorem gap11 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          |scaled n x * Real.log (scaled n x)| < ε := by
  intro ε hε
  rcases gap7 ε hε with ⟨δ, hδ, hsmall⟩
  rcases gap9 δ hδ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  rcases hN n hn x hx with ⟨hpos, hlt⟩
  exact hsmall (scaled n x) hpos hlt

theorem gap12 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x ∈ Set.Ioo (0 : ℝ) 1, |term n x| < ε := by
  intro ε hε
  rcases gap11 ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa [term] using hN n hn x hx

theorem gap13 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
  intro ε hε
  rcases gap12 ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa using hN n hn x hx

theorem gap14 :
    UniformlyConvergesOn term (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
  exact gap13

end

end ProofGap.Exercise2759
