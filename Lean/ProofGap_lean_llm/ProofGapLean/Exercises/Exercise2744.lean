import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2744

noncomputable section

open Filter
open scoped BigOperators
open scoped Topology

def term (k : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((k : ℝ) * x) / ((k : ℝ) * (k + 1))

def majorant (k : ℕ) : ℝ :=
  1 / ((k : ℝ) * (k + 1))

def series (x : ℝ) : ℝ :=
  ∑' j : ℕ, term (j + 1) x

def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, term k x

def tailPartial (n N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (n + 1) N, term k x

def tail (n : ℕ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, term (n + 1 + j) x

def absoluteTail (n : ℕ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, |term (n + 1 + j) x|

def majorantTail (n : ℕ) : ℝ :=
  ∑' j : ℕ, majorant (n + 1 + j)

def error (n : ℕ) (x : ℝ) : ℝ :=
  |series x - partialSum n x|

def cutoff (ε : ℝ) : ℕ :=
  Nat.floor (1 / ε)

private theorem reciprocal_tendsto_zero (c : ℝ) :
    Tendsto (fun N : ℕ => 1 / ((N : ℝ) + c)) atTop (𝓝 0) := by
  have hden : Tendsto (fun N : ℕ => (N : ℝ) + c) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨m : ℕ, hm⟩ := exists_nat_ge (b - c)
    filter_upwards [eventually_ge_atTop m] with N hN
    have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  simpa [one_div] using (tendsto_inv_atTop_zero.comp hden)

private theorem range_tendsto_atTop :
    Tendsto Finset.range atTop (atTop : Filter (Finset ℕ)) := by
  rw [tendsto_atTop]
  intro s
  induction s using Finset.induction_on with
  | empty =>
      exact Filter.Eventually.of_forall
        (fun N => Finset.empty_subset (Finset.range N))
  | @insert a s ha ih =>
      filter_upwards [ih, eventually_ge_atTop (a + 1)] with N hs hN
      change ∀ ⦃k : ℕ⦄, k ∈ insert a s → k ∈ Finset.range N
      intro k hk
      rcases Finset.mem_insert.mp hk with hka | hks
      · subst k
        exact Finset.mem_range.mpr (by omega)
      · exact hs hks

private theorem majorant_pointwise (k : ℕ) (hk : 1 ≤ k) :
    majorant k = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  unfold majorant
  have hk0 : (k : ℝ) ≠ 0 := by
    positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by
    positivity
  field_simp [hk0, hk1]
  ring

private theorem abs_term_le_majorant (k : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    |term k x| ≤ majorant k := by
  unfold term majorant
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hk1R : 0 < (k : ℝ) + 1 := by positivity
  have hd : 0 < (k : ℝ) * ((k : ℝ) + 1) := mul_pos hkR hk1R
  rw [abs_div, abs_of_pos hd]
  exact (div_le_div_iff_of_pos_right hd).2
    (Real.abs_sin_le_one ((k : ℝ) * x))

private theorem majorant_hasSum (n : ℕ) :
    HasSum (fun j : ℕ => majorant (n + 1 + j)) (1 / ((n : ℝ) + 1)) := by
  have hnonneg : ∀ j : ℕ, 0 ≤ majorant (n + 1 + j) := by
    intro j
    unfold majorant
    positivity
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg
    (1 / ((n : ℝ) + 1))).2
  have hsum : ∀ N : ℕ,
      (∑ j ∈ Finset.range N, majorant (n + 1 + j)) =
        1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + (N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih,
          majorant_pointwise (n + 1 + N) (by omega)]
        push_cast
        ring
  rw [show
    (fun N : ℕ => ∑ j ∈ Finset.range N, majorant (n + 1 + j)) =
      (fun N : ℕ =>
        1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + (N : ℝ) + 1)) by
      funext N
      exact hsum N]
  have hc :
      Tendsto (fun _ : ℕ => 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (1 / ((n : ℝ) + 1))) := tendsto_const_nhds
  have hz := reciprocal_tendsto_zero ((n : ℝ) + 1)
  simpa [add_comm, add_left_comm, add_assoc] using hc.sub hz

private theorem summable_term_tail (n : ℕ) (x : ℝ) :
    Summable (fun j : ℕ => term (n + 1 + j) x) := by
  refine Summable.of_norm_bounded (majorant_hasSum n).summable ?_
  intro j
  simpa [Real.norm_eq_abs] using
    (abs_term_le_majorant (n + 1 + j) x (by omega))

private theorem abs_tsum_le_tsum_abs (f : ℕ → ℝ) (hf : Summable f) :
    |∑' j : ℕ, f j| ≤ ∑' j : ℕ, |f j| := by
  set_option maxHeartbeats 2000000 in
    have habs : Summable (fun j : ℕ => ‖f j‖) := by
      simpa only [Real.norm_eq_abs] using hf.abs
    have hnorm : ‖∑' j : ℕ, f j‖ ≤ ∑' j : ℕ, ‖f j‖ :=
      norm_tsum_le_tsum_norm habs
    simpa only [Real.norm_eq_abs] using hnorm

private theorem sum_Icc_tail_eq_range (f : ℕ → ℝ) (n N : ℕ) :
    (∑ k ∈ Finset.Icc (n + 1) (n + N), f k) =
      ∑ j ∈ Finset.range N, f (n + 1 + j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hI :
          Finset.Icc (n + 1) (n + Nat.succ N) =
            insert (n + N + 1) (Finset.Icc (n + 1) (n + N)) := by
        ext k
        simp
        omega
      rw [hI, Finset.sum_insert (by simp), ih, Finset.sum_range_succ]
      have hf : f (n + N + 1) = f (n + 1 + N) := by
        congr 1
        omega
      rw [hf]
      ring

private theorem full_series_decomposition (n : ℕ) (x : ℝ) :
    series x = partialSum n x + tail n x := by
  have hfull :
      Tendsto
        (fun N : ℕ => ∑ j ∈ Finset.range N, term (j + 1) x)
        atTop (𝓝 (series x)) := by
    have h := (summable_term_tail 0 x).hasSum.comp range_tendsto_atTop
    simpa [series, add_comm, add_left_comm, add_assoc] using h
  have htail :
      Tendsto
        (fun N : ℕ => ∑ j ∈ Finset.range N, term (n + 1 + j) x)
        atTop (𝓝 (tail n x)) := by
    have h := (summable_term_tail n x).hasSum.comp range_tendsto_atTop
    simpa [tail] using h
  have hshift : Tendsto (fun N : ℕ => n + N) atTop atTop := by
    rw [tendsto_atTop]
    intro M
    filter_upwards [eventually_ge_atTop M] with N hN
    omega
  have hleft := hfull.comp hshift
  have hinit :
      (∑ j ∈ Finset.range n, term (j + 1) x) = partialSum n x := by
    simpa [partialSum, add_comm, add_left_comm, add_assoc] using
      (sum_Icc_tail_eq_range (fun k => term k x) 0 n).symm
  have heq : ∀ N : ℕ,
      (∑ j ∈ Finset.range (n + N), term (j + 1) x) =
        partialSum n x +
          ∑ j ∈ Finset.range N, term (n + 1 + j) x := by
    intro N
    have hsplit :=
      Finset.sum_range_add (fun j : ℕ => term (j + 1) x) n N
    rw [hinit] at hsplit
    simpa [add_comm, add_left_comm, add_assoc] using hsplit
  have hright :
      Tendsto
        (fun N : ℕ => partialSum n x +
          ∑ j ∈ Finset.range N, term (n + 1 + j) x)
        atTop (𝓝 (partialSum n x + tail n x)) :=
    tendsto_const_nhds.add htail
  have hright' :
      Tendsto
        (fun N : ℕ => ∑ j ∈ Finset.range (n + N), term (j + 1) x)
        atTop (𝓝 (partialSum n x + tail n x)) := by
    rw [show
      (fun N : ℕ => ∑ j ∈ Finset.range (n + N), term (j + 1) x) =
        (fun N : ℕ => partialSum n x +
          ∑ j ∈ Finset.range N, term (n + 1 + j) x) by
        funext N
        exact heq N]
    exact hright
  exact tendsto_nhds_unique hleft hright'

theorem gap1 :
    ∀ (n : ℕ) (x : ℝ), error n x = |tail n x| := by
  intro n x
  unfold error
  rw [full_series_decomposition n x]
  congr 1
  ring

theorem gap2 :
    ∀ (n : ℕ) (x : ℝ),
      Tendsto (fun N : ℕ => tailPartial n N x) atTop (𝓝 (tail n x)) := by
  intro n x
  have ht :
      Tendsto
        (fun M : ℕ => ∑ j ∈ Finset.range M, term (n + 1 + j) x)
        atTop (𝓝 (tail n x)) := by
    have h := (summable_term_tail n x).hasSum.comp range_tendsto_atTop
    simpa [tail] using h
  have hsub : Tendsto (fun N : ℕ => N - n) atTop atTop := by
    rw [tendsto_atTop]
    intro M
    filter_upwards [eventually_ge_atTop (M + n)] with N hN
    omega
  have hc := ht.comp hsub
  have heq :
      (fun N : ℕ => ∑ j ∈ Finset.range (N - n), term (n + 1 + j) x) =ᶠ[atTop]
        (fun N : ℕ => tailPartial n N x) := by
    filter_upwards [eventually_ge_atTop n] with N hN
    have hn : n + (N - n) = N := by omega
    symm
    unfold tailPartial
    simpa [hn] using
      (sum_Icc_tail_eq_range (fun k => term k x) n (N - n))
  exact hc.congr' heq

theorem gap3 :
    ∀ (n : ℕ) (x : ℝ), |tail n x| ≤ absoluteTail n x := by
  intro n x
  change
    |∑' j : ℕ, term (n + 1 + j) x| ≤
      ∑' j : ℕ, |term (n + 1 + j) x|
  exact abs_tsum_le_tsum_abs _ (summable_term_tail n x)

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), absoluteTail n x ≤ majorantTail n := by
  intro n x
  unfold absoluteTail majorantTail
  exact Summable.tsum_le_tsum
    (fun j => abs_term_le_majorant (n + 1 + j) x (by omega))
    (summable_term_tail n x).abs
    (majorant_hasSum n).summable

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), error n x ≤ majorantTail n := by
  intro n x
  calc
    error n x = |tail n x| := gap1 n x
    _ ≤ absoluteTail n x := gap3 n x
    _ ≤ majorantTail n := gap4 n x

theorem gap6 :
    ∀ k : ℕ, 1 ≤ k →
      majorant k = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  intro k hk
  exact majorant_pointwise k hk

theorem gap7 :
    ∀ n N : ℕ, n + 1 ≤ N →
      (∑ k ∈ Finset.Icc (n + 1) N,
          (1 / (k : ℝ) - 1 / ((k : ℝ) + 1))) =
        1 / ((n : ℝ) + 1) - 1 / ((N : ℝ) + 1) := by
  intro n N hN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hI :
          Finset.Icc (n + 1) ((n + 1) + Nat.succ m) =
            insert ((n + 1) + m + 1) (Finset.Icc (n + 1) ((n + 1) + m)) := by
        ext k
        simp
        omega
      rw [hI, Finset.sum_insert (by simp), ih (by omega)]
      push_cast
      ring

theorem gap8 :
    ∀ n : ℕ,
      Tendsto
        (fun N : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((N : ℝ) + 1))
        atTop (𝓝 (1 / ((n : ℝ) + 1))) := by
  intro n
  have hc :
      Tendsto (fun _ : ℕ => 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (1 / ((n : ℝ) + 1))) := tendsto_const_nhds
  have hz := reciprocal_tendsto_zero (1 : ℝ)
  simpa [add_comm, add_left_comm, add_assoc] using hc.sub hz

theorem gap9 :
    ∀ n : ℕ, majorantTail n = 1 / ((n : ℝ) + 1) := by
  intro n
  unfold majorantTail
  exact (majorant_hasSum n).tsum_eq

theorem gap10 :
    ∀ (n : ℕ) (x ε : ℝ),
      error n x ≤ 1 / ((n : ℝ) + 1) →
      1 / ((n : ℝ) + 1) < ε → error n x < ε := by
  intro n x ε herr hbound
  exact lt_of_le_of_lt herr hbound

theorem gap11 :
    ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      1 / ε - 1 < (n : ℝ) → 1 / ((n : ℝ) + 1) < ε := by
  intro n ε hε hn
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hdiv : 1 / ε < (n : ℝ) + 1 := by linarith
  apply (div_lt_iff₀ hd).2
  have hmul := (div_lt_iff₀ hε).1 hdiv
  simpa [mul_comm] using hmul

theorem gap12 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      1 / ε - 1 < (n : ℝ) → error n x < ε := by
  intro n x ε hε hn
  have herr : error n x ≤ 1 / ((n : ℝ) + 1) := by
    calc
      error n x ≤ majorantTail n := gap5 n x
      _ = 1 / ((n : ℝ) + 1) := gap9 n
  exact gap10 n x ε herr (gap11 n ε hε hn)

theorem gap13 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < ε →
      cutoff ε ≤ n → error n x < ε := by
  intro n x ε hε hcut
  apply gap12 n x ε hε
  have hfloor :
      1 / ε < ((Nat.floor (1 / ε) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one (1 / ε)
  have hcutR : (cutoff ε : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcut
  unfold cutoff at hcutR
  linarith

theorem gap14 :
    cutoff (0.1 : ℝ) = 10 := by
  norm_num [cutoff]

theorem gap15 :
    cutoff (0.01 : ℝ) = 100 := by
  norm_num [cutoff]

theorem gap16 :
    cutoff (0.001 : ℝ) = 1000 := by
  norm_num [cutoff]

end

end ProofGap.Exercise2744
