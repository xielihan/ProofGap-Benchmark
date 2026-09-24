import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2703

noncomputable section

open Filter
open scoped BigOperators

def term (p : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Real.rpow (n + 1) p

def evenPartial (p : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2 * n), term p j

def tailPairs (p : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 n,
    (1 / Real.rpow (2 * k - 1) p - 1 / Real.rpow (2 * k) p)

def tailLimit (p : ℝ) : ℝ :=
  ∑' k : ℕ,
    (1 / Real.rpow (2 * (k + 2) - 1) p -
      1 / Real.rpow (2 * (k + 2)) p)

def truncationError (p : ℝ) (n : ℕ) : ℝ :=
  tailPairs p n - tailLimit p

def sumValue (p : ℝ) : ℝ :=
  ∑'[SummationFilter.conditional ℕ] n : ℕ, term p n

private def amplitude (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (n + 1) p

private theorem amplitude_pos (p : ℝ) (n : ℕ) : 0 < amplitude p n := by
  simp only [amplitude, div_pos_iff]
  exact Or.inl ⟨zero_lt_one, Real.rpow_pos_of_pos (by positivity) p⟩

private theorem amplitude_antitone (p : ℝ) (hp : 0 < p) : Antitone (amplitude p) := by
  intro m n hmn
  dsimp [amplitude]
  gcongr

private theorem amplitude_tendsto_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (amplitude p) atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hrpow := (tendsto_rpow_atTop hp).comp hbase
  convert hrpow.inv_tendsto_atTop using 1
  funext n
  simp [amplitude, Function.comp_def, one_div]

private theorem seriesHasSum_of_tendsto {f : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (nhds s)) :
    HasSum f s (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using h

private theorem term_hasSum (p : ℝ) (hp : 0 < p) :
    HasSum (term p) (sumValue p) (SummationFilter.conditional ℕ) := by
  rcases (amplitude_antitone p hp).tendsto_alternating_series_of_tendsto_zero
      (amplitude_tendsto_zero p hp) with ⟨s, hs⟩
  have hsum : HasSum (term p) s (SummationFilter.conditional ℕ) := by
    apply seriesHasSum_of_tendsto
    convert hs using 1
    funext N
    apply Finset.sum_congr rfl
    intro n hn
    simp [term, amplitude, div_eq_mul_inv]
  simpa [sumValue] using hsum.summable.hasSum

private theorem term_partial_tendsto (p : ℝ) (hp : 0 < p) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, term p n) atTop
      (nhds (sumValue p)) := by
  have h := term_hasSum p hp
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff] at h
  simpa [Function.comp_def] using h

private theorem tendsto_two_mul_nat_atTop :
    Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

private theorem rpow_unit_interval_mvt (p : ℝ) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      1 / Real.rpow x p - 1 / Real.rpow (x + 1) p =
        p / Real.rpow (x + θ) (p + 1) := by
  let f : ℝ → ℝ := fun y => Real.rpow y (-p)
  let f' : ℝ → ℝ := fun y => (-p) * Real.rpow y (-p - 1)
  have hab : x < x + 1 := by linarith
  have hcont : ContinuousOn f (Set.Icc x (x + 1)) := by
    intro y hy
    exact (Real.continuousAt_rpow_const y (-p) (Or.inl (by linarith [hy.1]))).continuousWithinAt
  have hderiv : ∀ y ∈ Set.Ioo x (x + 1), HasDerivAt f (f' y) y := by
    intro y hy
    simpa [f, f'] using
      (Real.hasDerivAt_rpow_const (x := y) (p := -p) (Or.inl (by linarith [hy.1])))
  rcases exists_hasDerivAt_eq_slope f f' hab hcont hderiv with ⟨c, hc, hceq⟩
  refine ⟨c - x, by linarith [hc.1], by linarith [hc.2], ?_⟩
  have hcpos : 0 < c := hx.trans hc.1
  have hnegx : Real.rpow x (-p) = 1 / Real.rpow x p := by
    simpa [one_div] using Real.rpow_neg hx.le p
  have hnegx1 : Real.rpow (x + 1) (-p) = 1 / Real.rpow (x + 1) p := by
    simpa [one_div] using Real.rpow_neg (by linarith : 0 ≤ x + 1) p
  have hnegc : Real.rpow c (-(p + 1)) = 1 / Real.rpow c (p + 1) := by
    simpa [one_div] using Real.rpow_neg hcpos.le (p + 1)
  have hcalc :
      1 / Real.rpow x p - 1 / Real.rpow (x + 1) p =
        p / Real.rpow c (p + 1) := by
    have hceq' :
        (-p) * Real.rpow c (-p - 1) =
          Real.rpow (x + 1) (-p) - Real.rpow x (-p) := by
      simpa [f, f'] using hceq
    calc
      1 / Real.rpow x p - 1 / Real.rpow (x + 1) p =
          Real.rpow x (-p) - Real.rpow (x + 1) (-p) := by rw [hnegx, hnegx1]
      _ = -((-p) * Real.rpow c (-p - 1)) := by rw [hceq']; ring
      _ = p / Real.rpow c (p + 1) := by
        rw [show -p - 1 = -(p + 1) by ring, hnegc]
        ring
  simpa [sub_add_cancel] using hcalc

private def tailSummand (p : ℝ) (k : ℕ) : ℝ :=
  1 / Real.rpow (2 * (k + 2) - 1) p -
    1 / Real.rpow (2 * (k + 2)) p

private def oddMajorant (p : ℝ) (k : ℕ) : ℝ :=
  1 / Real.rpow (2 * k + 3) p

private theorem tailSummand_nonneg (p : ℝ) (hp : 0 < p) (k : ℕ) :
    0 ≤ tailSummand p k := by
  dsimp [tailSummand]
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have ha : 0 < (2 : ℝ) * ((k : ℝ) + 2) - 1 := by linarith
  have hab :
      (2 : ℝ) * ((k : ℝ) + 2) - 1 ≤
        2 * ((k : ℝ) + 2) := by linarith
  apply sub_nonneg.mpr
  apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha p)
  exact Real.rpow_le_rpow ha.le hab hp.le

private theorem tailSummand_le_telescope (p : ℝ) (hp : 0 < p) (k : ℕ) :
    tailSummand p k ≤ oddMajorant p k - oddMajorant p (k + 1) := by
  dsimp [tailSummand, oddMajorant]
  have hfirst :
      (2 : ℝ) * ((k : ℝ) + 2) - 1 = 2 * (k : ℝ) + 3 := by ring
  have hsecond :
      (2 : ℝ) * ((k : ℝ) + 2) = 2 * (k : ℝ) + 4 := by ring
  have hthird :
      (2 : ℝ) * ((k + 1 : ℕ) : ℝ) + 3 = 2 * (k : ℝ) + 5 := by
    norm_num [Nat.cast_add]
    ring
  rw [hfirst, hsecond, hthird]
  have hbase : 0 < (2 : ℝ) * k + 4 := by positivity
  have hpow :
      Real.rpow (2 * (k : ℝ) + 4) p ≤ Real.rpow (2 * (k : ℝ) + 5) p :=
    Real.rpow_le_rpow hbase.le (by linarith) hp.le
  have hle :
      1 / Real.rpow (2 * (k : ℝ) + 5) p ≤
        1 / Real.rpow (2 * (k : ℝ) + 4) p :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hbase p) hpow
  exact sub_le_sub_left hle _

private theorem tailSummand_summable (p : ℝ) (hp : 0 < p) :
    Summable (tailSummand p) := by
  apply summable_of_sum_range_le (tailSummand_nonneg p hp)
  intro N
  calc
    ∑ k ∈ Finset.range N, tailSummand p k ≤
        ∑ k ∈ Finset.range N, (oddMajorant p k - oddMajorant p (k + 1)) := by
      exact Finset.sum_le_sum fun k hk => tailSummand_le_telescope p hp k
    _ = oddMajorant p 0 - oddMajorant p N := by
      exact Finset.sum_range_sub' (oddMajorant p) N
    _ ≤ oddMajorant p 0 := by
      have hpos : 0 < oddMajorant p N := by
        simp [oddMajorant]
        positivity
      linarith

private def pairTerm (p : ℝ) (k : ℕ) : ℝ :=
  1 / Real.rpow (2 * k - 1) p - 1 / Real.rpow (2 * k) p

private theorem sum_shift_two (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), f (i + 2) =
      ∑ k ∈ Finset.Icc 2 (m + 2), f k := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        ∑ i ∈ Finset.range (m + 1 + 1), f (i + 2) =
            (∑ i ∈ Finset.range (m + 1), f (i + 2)) + f (m + 1 + 2) := by
          rw [Finset.sum_range_succ]
        _ = (∑ k ∈ Finset.Icc 2 (m + 2), f k) + f (m + 3) := by
          rw [ih]
        _ = ∑ k ∈ Finset.Icc 2 (m + 3), f k := by
          exact (Finset.sum_Icc_succ_top (f := f) (a := 2) (b := m + 2) (by omega)).symm

private theorem tailSummand_eq_pairTerm (p : ℝ) (i : ℕ) :
    tailSummand p i = pairTerm p (i + 2) := by
  simp [tailSummand, pairTerm, Nat.cast_add]

private theorem sum_tailSummand_range (p : ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), tailSummand p i =
      ∑ k ∈ Finset.Icc 2 (m + 2), pairTerm p k := by
  calc
    ∑ i ∈ Finset.range (m + 1), tailSummand p i =
        ∑ i ∈ Finset.range (m + 1), pairTerm p (i + 2) := by
      exact Finset.sum_congr rfl fun i hi => tailSummand_eq_pairTerm p i
    _ = ∑ k ∈ Finset.Icc 2 (m + 2), pairTerm p k := sum_shift_two _ _

private theorem tailPairs_eq_sum_range (p : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    tailPairs p n = ∑ i ∈ Finset.range (n - 1), tailSummand p i := by
  let m := n - 2
  have hn' : n = m + 2 := by omega
  rw [hn']
  simpa [tailPairs, pairTerm, m] using (sum_tailSummand_range p m).symm

private theorem tendsto_nat_sub_one_atTop :
    Tendsto (fun n : ℕ => n - 1) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b + 1)] with n hn
  omega

private theorem tailPairs_tendsto (p : ℝ) (hp : 0 < p) :
    Tendsto (tailPairs p) atTop (nhds (tailLimit p)) := by
  have hs := (tailSummand_summable p hp).hasSum.tendsto_sum_nat
  have hcomp := hs.comp tendsto_nat_sub_one_atTop
  have heq :
      (fun n => ∑ i ∈ Finset.range (n - 1), tailSummand p i) =ᶠ[atTop]
        tailPairs p := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (tailPairs_eq_sum_range p hn).symm
  simpa [tailLimit, tailSummand] using hcomp.congr' heq

private theorem sum_Icc_telescope (f : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Icc 2 n, (f k - f (k + 1)) = f 2 - f (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

private theorem pseries_difference_le (p : ℝ) (hp : 0 < p) (k : ℕ) (hk : 1 ≤ k) :
    1 / Real.rpow k p - 1 / Real.rpow (k + 1) p ≤
      p / Real.rpow k (p + 1) := by
  rcases rpow_unit_interval_mvt p hp (x := (k : ℝ)) (by positivity) with
    ⟨θ, hθ0, hθ1, heq⟩
  rw [heq]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  gcongr
  · exact Real.rpow_pos_of_pos hkpos (p + 1)
  · exact Real.rpow_le_rpow hkpos.le (by linarith) (by linarith)

private theorem pseries_partial_lower (p : ℝ) (hp : 0 < p) {n : ℕ} (hn : 2 ≤ n) :
    1 / Real.rpow 2 p - 1 / Real.rpow (n + 1) p ≤
      p * ∑ k ∈ Finset.Icc 2 n, 1 / Real.rpow k (p + 1) := by
  calc
    1 / Real.rpow 2 p - 1 / Real.rpow (n + 1) p =
        ∑ k ∈ Finset.Icc 2 n,
          (1 / Real.rpow k p - 1 / Real.rpow (k + 1) p) := by
      simpa [Nat.cast_add] using
        (sum_Icc_telescope (fun k => 1 / Real.rpow k p) hn).symm
    _ ≤ ∑ k ∈ Finset.Icc 2 n, p / Real.rpow k (p + 1) := by
      exact Finset.sum_le_sum fun k hk => pseries_difference_le p hp k <| by
        have hk2 := (Finset.mem_Icc.mp hk).1
        omega
    _ = p * ∑ k ∈ Finset.Icc 2 n, 1 / Real.rpow k (p + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

private theorem term_pair (p : ℝ) (n : ℕ) :
    term p (2 * n) + term p (2 * n + 1) =
      1 / Real.rpow (2 * n + 1) p - 1 / Real.rpow (2 * n + 2) p := by
  simp [term, pow_add, pow_mul, Nat.cast_add]
  ring

private theorem evenPartial_succ (p : ℝ) (n : ℕ) :
    evenPartial p (n + 1) = evenPartial p n +
      (1 / Real.rpow (2 * n + 1) p - 1 / Real.rpow (2 * n + 2) p) := by
  unfold evenPartial
  rw [show 2 * (n + 1) = 2 * n + 2 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  calc
    (∑ x ∈ Finset.range (2 * n), term p x) + term p (2 * n) + term p (2 * n + 1) =
        (∑ x ∈ Finset.range (2 * n), term p x) +
          (term p (2 * n) + term p (2 * n + 1)) := by ring
    _ = (∑ x ∈ Finset.range (2 * n), term p x) +
        (1 / Real.rpow (2 * n + 1) p - 1 / Real.rpow (2 * n + 2) p) := by
      rw [term_pair]

theorem gap1 (p : ℝ) (hp : 0 < p) :
    Monotone (evenPartial p) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [evenPartial_succ]
  apply le_add_of_nonneg_right
  have hmono := amplitude_antitone p hp (Nat.le_succ (2 * n))
  have hdiff :
      0 ≤ 1 / Real.rpow (2 * n + 1) p - 1 / Real.rpow (2 * n + 2) p := by
    convert sub_nonneg.mpr hmono using 1 <;> simp [amplitude, Nat.cast_add] <;> ring
  exact hdiff

theorem gap2 (p : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      evenPartial p n =
        1 - (∑ k ∈ Finset.Icc 1 (n - 1),
          (1 / Real.rpow (2 * k) p -
            1 / Real.rpow (2 * k + 1) p)) -
          1 / Real.rpow (2 * n) p := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        rw [evenPartial_succ]
        norm_num [evenPartial]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have ih' := ih hn1
        rw [evenPartial_succ, ih']
        have hsum := Finset.sum_Icc_succ_top
          (f := fun k : ℕ =>
            1 / Real.rpow (2 * k) p - 1 / Real.rpow (2 * k + 1) p)
          (a := 1) (b := n - 1) (by omega)
        have hnsub : n - 1 + 1 = n := by omega
        rw [hnsub] at hsum
        rw [show n + 1 - 1 = n by omega, hsum]
        norm_num [Nat.cast_add]
        ring

theorem gap3 (p : ℝ) (hp : 0 < p) :
    ∀ n : ℕ, 1 ≤ n → evenPartial p n < 1 := by
  intro n hn
  rw [gap2 p n hn]
  have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 (n - 1),
      (1 / Real.rpow (2 * k) p - 1 / Real.rpow (2 * k + 1) p) := by
    apply Finset.sum_nonneg
    intro k hk
    apply sub_nonneg.mpr
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hbase : (0 : ℝ) < 2 * k := by positivity
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hbase p)
    apply Real.rpow_le_rpow hbase.le (by norm_num) hp.le
  have hlast : 0 < 1 / Real.rpow (2 * n) p := by
    exact one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)
  linarith

theorem gap4 (p : ℝ) (hp : 0 < p) :
    ∀ n : ℕ, 1 ≤ n → evenPartial p n < 1 := by
  exact gap3 p hp

theorem gap5 (p : ℝ) (hp : 0 < p) :
    ∃ L : ℝ, Tendsto (evenPartial p) atTop (nhds L) ∧ L ≤ 1 := by
  have hub : ∀ n, evenPartial p n ≤ 1 := by
    intro n
    cases n with
    | zero => simp [evenPartial]
    | succ n => exact (gap3 p hp (n + 1) (by omega)).le
  have hbdd : BddAbove (Set.range (evenPartial p)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hub n
  refine ⟨⨆ n, evenPartial p n, tendsto_atTop_ciSup (gap1 p hp) hbdd, ?_⟩
  exact ciSup_le hub

theorem gap6 (p : ℝ) (hp : 0 < p) :
    Tendsto (evenPartial p) atTop (nhds (sumValue p)) := by
  simpa [evenPartial, Function.comp_def] using
    (term_partial_tendsto p hp).comp tendsto_two_mul_nat_atTop

theorem gap7 (p : ℝ) (hp : 0 < p) :
    sumValue p ≤ 1 := by
  rcases gap5 p hp with ⟨L, hL, hLle⟩
  have hEq : L = sumValue p := tendsto_nhds_unique hL (gap6 p hp)
  simpa [hEq] using hLle

theorem gap8 (p : ℝ) (hp : 0 < p) :
    sumValue p ≤ 1 := by
  exact gap7 p hp

theorem gap9 (p : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      evenPartial p n = 1 - 1 / Real.rpow 2 p + tailPairs p n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        rw [evenPartial_succ]
        norm_num [evenPartial, tailPairs]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have ih' := ih hn1
        have htail : tailPairs p (n + 1) = tailPairs p n + pairTerm p (n + 1) := by
          unfold tailPairs
          change (∑ k ∈ Finset.Icc 2 (n + 1), pairTerm p k) =
            (∑ k ∈ Finset.Icc 2 n, pairTerm p k) + pairTerm p (n + 1)
          rw [Finset.sum_Icc_succ_top (f := pairTerm p) (a := 2) (b := n) (by omega)]
        rw [evenPartial_succ, ih', htail]
        simp [pairTerm, Nat.cast_add]
        ring

theorem gap10 (p : ℝ) (hp : 0 < p) :
    ∃ θ : ℕ → ℝ,
      (∀ k : ℕ, 2 ≤ k → 0 < θ k ∧ θ k < 1) ∧
      ∀ n : ℕ, 2 ≤ n →
        tailPairs p n =
          ∑ k ∈ Finset.Icc 2 n,
            p / Real.rpow ((2 * k - 1 : ℕ) + θ k) (p + 1) := by
  classical
  have hex : ∀ k : ℕ, 2 ≤ k → ∃ θ : ℝ,
      0 < θ ∧ θ < 1 ∧
        pairTerm p k = p / Real.rpow ((2 * k - 1 : ℕ) + θ) (p + 1) := by
    intro k hk
    have hxNat : 0 < 2 * k - 1 := by omega
    have hx : (0 : ℝ) < (2 * k - 1 : ℕ) := by exact_mod_cast hxNat
    rcases rpow_unit_interval_mvt p hp hx with ⟨θ, hθ0, hθ1, heq⟩
    refine ⟨θ, hθ0, hθ1, ?_⟩
    have hcast0 : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast0] at heq ⊢
    have hcast1 : 2 * (k : ℝ) - 1 + 1 = 2 * (k : ℝ) := by ring
    rw [hcast1] at heq
    simpa [pairTerm] using heq
  let θ : ℕ → ℝ := fun k =>
    if hk : 2 ≤ k then Classical.choose (hex k hk) else 1 / 2
  have hθ : ∀ k : ℕ, 2 ≤ k →
      0 < θ k ∧ θ k < 1 ∧
        pairTerm p k = p / Real.rpow ((2 * k - 1 : ℕ) + θ k) (p + 1) := by
    intro k hk
    simp only [θ, dif_pos hk]
    exact Classical.choose_spec (hex k hk)
  refine ⟨θ, ?_, ?_⟩
  · intro k hk
    exact ⟨(hθ k hk).1, (hθ k hk).2.1⟩
  · intro n hn
    unfold tailPairs
    apply Finset.sum_congr rfl
    intro k hk
    exact (hθ k (Finset.mem_Icc.mp hk).1).2.2

theorem gap11 (p : ℝ) (hp : 0 < p) :
    ∀ n : ℕ, 2 ≤ n →
      tailPairs p n ≥
        p / Real.rpow 2 (p + 1) *
          (∑ k ∈ Finset.Icc 2 n, 1 / Real.rpow k (p + 1)) := by
  rcases gap10 p hp with ⟨θ, hθ, hsum⟩
  intro n hn
  rw [hsum n hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk2 := (Finset.mem_Icc.mp hk).1
  have hθk := hθ k hk2
  have hleft : (0 : ℝ) < (2 * k - 1 : ℕ) + θ k := by
    have hnat : 0 < 2 * k - 1 := by omega
    have hcast : (0 : ℝ) < (2 * k - 1 : ℕ) := by exact_mod_cast hnat
    linarith [hcast, hθk.1]
  have hbase : ((2 * k - 1 : ℕ) : ℝ) + θ k ≤ 2 * (k : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith [hθk.2]
  have hpow :
      Real.rpow (((2 * k - 1 : ℕ) : ℝ) + θ k) (p + 1) ≤
        Real.rpow (2 * (k : ℝ)) (p + 1) :=
    Real.rpow_le_rpow hleft.le hbase (by linarith)
  have hfrac :
      p / Real.rpow (2 * (k : ℝ)) (p + 1) ≤
        p / Real.rpow (((2 * k - 1 : ℕ) : ℝ) + θ k) (p + 1) := by
    gcongr
    exact Real.rpow_pos_of_pos hleft (p + 1)
  calc
    p / Real.rpow 2 (p + 1) * (1 / Real.rpow k (p + 1)) =
        p / Real.rpow (2 * (k : ℝ)) (p + 1) := by
      have hmul :
          Real.rpow (2 * (k : ℝ)) (p + 1) =
            Real.rpow 2 (p + 1) * Real.rpow k (p + 1) :=
        Real.mul_rpow (by norm_num) (by positivity)
      rw [hmul]
      have h2nz : Real.rpow 2 (p + 1) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos (by norm_num) (p + 1))
      have hknz : Real.rpow k (p + 1) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos (by positivity) (p + 1))
      field_simp [h2nz, hknz]
    _ ≤ p / Real.rpow (((2 * k - 1 : ℕ) : ℝ) + θ k) (p + 1) := hfrac

private theorem tail_tsum_shift_le (p : ℝ) (hp : 0 < p) (m : ℕ) :
    ∑' k : ℕ, tailSummand p (k + m) ≤ oddMajorant p m := by
  apply Real.tsum_le_of_sum_range_le
  · intro k
    exact tailSummand_nonneg p hp (k + m)
  · intro N
    calc
      ∑ k ∈ Finset.range N, tailSummand p (k + m) ≤
          ∑ k ∈ Finset.range N,
            (oddMajorant p (k + m) - oddMajorant p (k + m + 1)) := by
        exact Finset.sum_le_sum fun k hk => tailSummand_le_telescope p hp (k + m)
      _ = oddMajorant p m - oddMajorant p (N + m) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Finset.sum_range_sub' (fun k => oddMajorant p (k + m)) N)
      _ ≤ oddMajorant p m := by
        have hnonneg : 0 ≤ oddMajorant p (N + m) := by
          exact (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)).le
        linarith

private theorem truncationError_eq_neg_tsum (p : ℝ) (hp : 0 < p) {n : ℕ}
    (hn : 2 ≤ n) :
    truncationError p n = -∑' k : ℕ, tailSummand p (k + (n - 1)) := by
  have hsplit :
      (∑ i ∈ Finset.range (n - 1), tailSummand p i) +
          (∑' k : ℕ, tailSummand p (k + (n - 1))) =
        ∑' k : ℕ, tailSummand p k :=
    (tailSummand_summable p hp).sum_add_tsum_nat_add (n - 1)
  rw [truncationError, tailPairs_eq_sum_range p hn]
  change (∑ i ∈ Finset.range (n - 1), tailSummand p i) -
      (∑' k : ℕ, tailSummand p k) = _
  linarith

private theorem truncationError_abs_le (p : ℝ) (hp : 0 < p) {n : ℕ} (hn : 2 ≤ n) :
    |truncationError p n| ≤ 1 / Real.rpow n p := by
  rw [truncationError_eq_neg_tsum p hp hn, abs_neg,
    abs_of_nonneg (tsum_nonneg fun k => tailSummand_nonneg p hp _)]
  calc
    ∑' k : ℕ, tailSummand p (k + (n - 1)) ≤ oddMajorant p (n - 1) :=
      tail_tsum_shift_le p hp (n - 1)
    _ ≤ 1 / Real.rpow n p := by
      unfold oddMajorant
      have hnpos : (0 : ℝ) < n := by positivity
      have hbase : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) + 3 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
        linarith
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos p)
      exact Real.rpow_le_rpow hnpos.le hbase hp.le

theorem gap12 (p : ℝ) (hp : 0 < p) :
    (1 / Real.rpow 2 (2 * p + 1) ≤ tailLimit p) ∧
    (∀ n : ℕ,
      tailPairs p n = tailLimit p + truncationError p n) := by
  constructor
  · let lower : ℕ → ℝ := fun n =>
      1 / Real.rpow 2 (p + 1) *
        (1 / Real.rpow 2 p - 1 / Real.rpow (n + 1) p)
    have hbound : ∀ n : ℕ, 2 ≤ n → lower n ≤ tailPairs p n := by
      intro n hn
      have hseries := pseries_partial_lower p hp hn
      have hc : 0 ≤ 1 / Real.rpow 2 (p + 1) :=
        (one_div_pos.mpr (Real.rpow_pos_of_pos (by norm_num) (p + 1))).le
      have hmul := mul_le_mul_of_nonneg_left hseries hc
      calc
        lower n ≤
            1 / Real.rpow 2 (p + 1) *
              (p * ∑ k ∈ Finset.Icc 2 n, 1 / Real.rpow k (p + 1)) := hmul
        _ = p / Real.rpow 2 (p + 1) *
              (∑ k ∈ Finset.Icc 2 n, 1 / Real.rpow k (p + 1)) := by ring
        _ ≤ tailPairs p n := gap11 p hp n hn
    have hpow :
        Real.rpow 2 (2 * p + 1) =
          Real.rpow 2 (p + 1) * Real.rpow 2 p := by
      rw [show 2 * p + 1 = (p + 1) + p by ring]
      exact Real.rpow_add (by norm_num) (p + 1) p
    have hlimitEq :
        1 / Real.rpow 2 (p + 1) * (1 / Real.rpow 2 p - 0) =
          1 / Real.rpow 2 (2 * p + 1) := by
      rw [hpow]
      have h1 : Real.rpow 2 (p + 1) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos (by norm_num) (p + 1))
      have h2 : Real.rpow 2 p ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos (by norm_num) p)
      field_simp [h1, h2]
      ring
    have hlower : Tendsto lower atTop (nhds (1 / Real.rpow 2 (2 * p + 1))) := by
      have hconst :
          Tendsto (fun _ : ℕ => 1 / Real.rpow 2 p) atTop
            (nhds (1 / Real.rpow 2 p)) := tendsto_const_nhds
      have h := (hconst.sub (amplitude_tendsto_zero p hp)).const_mul
        (1 / Real.rpow 2 (p + 1))
      rw [← hlimitEq]
      simpa [lower, amplitude] using h
    exact le_of_tendsto_of_tendsto hlower (tailPairs_tendsto p hp) <|
      eventually_atTop.2 ⟨2, hbound⟩
  · intro n
    unfold truncationError
    ring

theorem gap13 (p : ℝ) (hp : 0 < p) :
    Asymptotics.IsBigO atTop (truncationError p)
      (fun n : ℕ => 1 / Real.rpow n p) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnonneg : 0 ≤ 1 / Real.rpow n p :=
    (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) p)).le
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hnonneg]
  exact truncationError_abs_le p hp hn

theorem gap14 (p : ℝ) (hp : 0 < p) :
    Tendsto (truncationError p) atTop (nhds 0) := by
  have hconst : Tendsto (fun _ : ℕ => tailLimit p) atTop (nhds (tailLimit p)) :=
    tendsto_const_nhds
  simpa [truncationError] using (tailPairs_tendsto p hp).sub hconst

theorem gap15 (p : ℝ) (hp : 0 < p) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N,
        evenPartial p n ≥
          1 - 1 / Real.rpow 2 p +
            1 / Real.rpow 2 (2 * p + 1) - ε := by
  intro ε hε
  have herr : ∀ᶠ n in atTop, -ε < truncationError p n :=
    (tendsto_order.1 (gap14 p hp)).1 (-ε) (by linarith)
  rcases eventually_atTop.1 herr with ⟨N, hN⟩
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have htail := (gap12 p hp).1
  have hid := (gap12 p hp).2 n
  rw [gap9 p n (by omega), hid]
  linarith [hN n hnN]

theorem gap16 (p : ℝ) (hp : 0 < p) :
    1 - 1 / Real.rpow 2 p +
      1 / Real.rpow 2 (2 * p + 1) > 1 / 2 := by
  let x : ℝ := 1 / Real.rpow 2 p
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hden : 1 < Real.rpow 2 p := Real.one_lt_rpow (by norm_num) hp
  have hx1 : x < 1 := by
    dsimp [x]
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden
  have hpow :
      Real.rpow 2 (2 * p + 1) = Real.rpow 2 p * Real.rpow 2 p * 2 := by
    rw [show 2 * p + 1 = (p + p) + 1 by ring]
    calc
      Real.rpow 2 ((p + p) + 1) =
          Real.rpow 2 (p + p) * Real.rpow 2 1 :=
        Real.rpow_add (by norm_num) (p + p) 1
      _ = (Real.rpow 2 p * Real.rpow 2 p) * Real.rpow 2 1 := by
        congr 1
        exact Real.rpow_add (by norm_num) p p
      _ = Real.rpow 2 p * Real.rpow 2 p * 2 := by norm_num
  have hlast : 1 / Real.rpow 2 (2 * p + 1) = x ^ 2 / 2 := by
    dsimp [x]
    calc
      1 / Real.rpow 2 (2 * p + 1) =
          1 / (Real.rpow 2 p * Real.rpow 2 p * 2) := by
        exact congrArg (fun y : ℝ => 1 / y) hpow
      _ = (1 / Real.rpow 2 p) ^ 2 / 2 := by
        have hnz : Real.rpow 2 p ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos (by norm_num) p)
        field_simp [hnz]
  rw [hlast]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hx1)]

theorem gap17 (p : ℝ) (hp : 0 < p) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, evenPartial p n > 1 / 2 - ε := by
  intro ε hε
  rcases gap15 p hp ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hconst := gap16 p hp
  linarith [hN n hn]

theorem gap18 (p : ℝ) (hp : 0 < p) :
    1 / 2 ≤ sumValue p := by
  let c : ℝ :=
    1 - 1 / Real.rpow 2 p + 1 / Real.rpow 2 (2 * p + 1)
  have hc : 0 < c - 1 / 2 := by
    apply sub_pos.mpr
    simpa [c] using gap16 p hp
  rcases gap15 p hp (c - 1 / 2) hc with ⟨N, hN⟩
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (gap6 p hp)
  filter_upwards [eventually_ge_atTop N] with n hn
  have h := hN n hn
  dsimp [c] at h
  linarith

theorem gap19 (p : ℝ) (hp : 0 < p) :
    1 / 2 ≤ sumValue p := by
  exact gap18 p hp

theorem gap20 (p : ℝ) (hp : 0 < p) :
    sumValue p ≤ 1 := by
  exact gap8 p hp

theorem gap21 : (1 / 2 : ℝ) ≤ 1 := by norm_num

theorem gap22 (p : ℝ) (hp : 0 < p) :
    1 / 2 ≤ sumValue p ∧ sumValue p ≤ 1 := by
  exact ⟨gap19 p hp, gap20 p hp⟩

end

end ProofGap.Exercise2703
