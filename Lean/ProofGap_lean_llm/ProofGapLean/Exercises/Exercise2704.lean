import ProofGapLean.Prelude.Analysis
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace ProofGap.Exercise2704

noncomputable section

open Filter
open scoped BigOperators

def rearrangedTerm (p q : ℕ) (j : ℕ) : ℝ :=
  let block := j / (p + q)
  let offset := j % (p + q)
  if offset < p then
    1 / ((2 * (block * p + offset) + 1 : ℕ) : ℝ)
  else
    -(1 / ((2 * (block * q + (offset - p) + 1) : ℕ) : ℝ))

def partialSum (p q : ℕ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, rearrangedTerm p q j

def harmonic (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)

private theorem harmonic_eq_cast (n : ℕ) :
    harmonic n = ((_root_.harmonic n : ℚ) : ℝ) := by
  simp [harmonic, _root_.harmonic]

private theorem tendsto_harmonic_sub_log_local :
    Tendsto (fun n : ℕ => harmonic n - Real.log n)
      atTop (nhds Real.eulerMascheroniConstant) := by
  simpa only [harmonic_eq_cast] using Real.tendsto_harmonic_sub_log

private theorem tendsto_harmonic_error_local :
    Tendsto
      (fun n : ℕ => harmonic n - Real.log n - Real.eulerMascheroniConstant)
      atTop (nhds 0) := by
  have hconstant :
      Tendsto (fun _ : ℕ => Real.eulerMascheroniConstant) atTop
        (nhds Real.eulerMascheroniConstant) := tendsto_const_nhds
  simpa using tendsto_harmonic_sub_log_local.sub hconstant

def cyclePartial (p q : ℕ) (n : ℕ) : ℝ :=
  partialSum p q (n * (p + q))

def target (p q : ℕ) : ℝ :=
  Real.log 2 + (1 / 2 : ℝ) * Real.log ((p : ℝ) / q)

def cycleError (p q : ℕ) (n : ℕ) : ℝ :=
  cyclePartial p q n - target p q

private theorem rearrangedTerm_cycle_pos (p q n r : ℕ)
    (hp : 1 ≤ p) (hr : r < p) :
    rearrangedTerm p q (n * (p + q) + r) =
      1 / ((2 * (n * p + r) + 1 : ℕ) : ℝ) := by
  have hd : 0 < p + q := by omega
  have hrd : r < p + q := by omega
  simp [rearrangedTerm, Nat.mul_comm n (p + q), Nat.mul_add_div hd,
    Nat.mul_add_mod_of_lt hrd, Nat.div_eq_of_lt hrd,
    Nat.mod_eq_of_lt hrd, hr]

private theorem rearrangedTerm_cycle_neg (p q n r : ℕ)
    (hq : 1 ≤ q) (hr : r < q) :
    rearrangedTerm p q (n * (p + q) + (p + r)) =
      -(1 / ((2 * (n * q + r + 1) : ℕ) : ℝ)) := by
  have hd : 0 < p + q := by omega
  have hprd : p + r < p + q := by omega
  simp [rearrangedTerm, Nat.mul_comm n (p + q), Nat.mul_add_div hd,
    Nat.mul_add_mod_of_lt hprd, Nat.div_eq_of_lt hprd,
    Nat.mod_eq_of_lt hprd,
    Nat.not_lt.mpr (Nat.le_add_right p r)]

private theorem partialSum_cycles (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ n : ℕ,
      partialSum p q (n * (p + q)) =
        (∑ k ∈ Finset.range (n * p),
          1 / ((2 * k + 1 : ℕ) : ℝ)) -
        (∑ k ∈ Finset.range (n * q),
          1 / ((2 * k + 2 : ℕ) : ℝ)) := by
  intro n
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      have hpos :
          (∑ r ∈ Finset.range p,
            rearrangedTerm p q (n * (p + q) + r)) =
            ∑ r ∈ Finset.range p,
              1 / ((2 * (n * p + r) + 1 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact rearrangedTerm_cycle_pos p q n r hp (Finset.mem_range.mp hr)
      have hneg :
          (∑ r ∈ Finset.range q,
            rearrangedTerm p q (n * (p + q) + (p + r))) =
            ∑ r ∈ Finset.range q,
              -(1 / ((2 * (n * q + r + 1) : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact rearrangedTerm_cycle_neg p q n r hq (Finset.mem_range.mp hr)
      rw [Nat.add_mul, one_mul, partialSum, Finset.sum_range_add]
      change partialSum p q (n * (p + q)) +
          (∑ j ∈ Finset.range (p + q),
            rearrangedTerm p q (n * (p + q) + j)) = _
      rw [ih, Finset.sum_range_add]
      have htail :
          (∑ x ∈ Finset.range p,
              rearrangedTerm p q (n * (p + q) + x)) +
            ∑ x ∈ Finset.range q,
              rearrangedTerm p q (n * (p + q) + (p + x)) =
            (∑ r ∈ Finset.range p,
              1 / ((2 * (n * p + r) + 1 : ℕ) : ℝ)) +
            ∑ r ∈ Finset.range q,
              -(1 / ((2 * (n * q + r + 1) : ℕ) : ℝ)) := by
        rw [hpos, hneg]
      rw [htail]
      have hodd :
          (∑ k ∈ Finset.range ((n + 1) * p),
            1 / ((2 * k + 1 : ℕ) : ℝ)) =
            (∑ k ∈ Finset.range (n * p),
              1 / ((2 * k + 1 : ℕ) : ℝ)) +
            ∑ r ∈ Finset.range p,
              1 / ((2 * (n * p + r) + 1 : ℕ) : ℝ) := by
        rw [Nat.add_mul, one_mul, Finset.sum_range_add]
      have heven :
          (∑ k ∈ Finset.range ((n + 1) * q),
            1 / ((2 * k + 2 : ℕ) : ℝ)) =
            (∑ k ∈ Finset.range (n * q),
              1 / ((2 * k + 2 : ℕ) : ℝ)) +
            ∑ r ∈ Finset.range q,
              1 / ((2 * (n * q + r + 1) : ℕ) : ℝ) := by
        rw [Nat.add_mul, one_mul, Finset.sum_range_add]
        apply congrArg (fun z : ℝ =>
          (∑ k ∈ Finset.range (n * q),
            1 / ((2 * k + 2 : ℕ) : ℝ)) + z)
        apply Finset.sum_congr rfl
        intro r hr
        congr 3
      rw [Finset.sum_neg_distrib, hodd, heven]
      ring

theorem gap1 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ n : ℕ,
      partialSum p q ((n + 1) * (p + q)) =
        (∑ k ∈ Finset.range ((n + 1) * p),
          1 / ((2 * k + 1 : ℕ) : ℝ)) -
        (∑ k ∈ Finset.range ((n + 1) * q),
          1 / ((2 * k + 2 : ℕ) : ℝ)) := by
  intro n
  exact partialSum_cycles p q hp hq (n + 1)

theorem gap2 :
    ∃ H : ℕ → ℝ, ∀ n : ℕ, H n = harmonic n := by
  exact ⟨harmonic, fun _ => rfl⟩

theorem gap3 :
    ∃ C : ℝ, Tendsto (fun n : ℕ => harmonic (n + 1) - Real.log (n + 1))
      atTop (nhds C) := by
  exact ⟨Real.eulerMascheroniConstant,
    by simpa [Function.comp_def, Nat.cast_add] using
      tendsto_harmonic_sub_log_local.comp (tendsto_add_atTop_nat 1)⟩

theorem gap4 :
    ∃ C : ℝ, Tendsto (fun n : ℕ => harmonic (n + 1) - Real.log (n + 1))
      atTop (nhds C) := by
  exact gap3

theorem gap5 :
    ∀ m : ℕ,
      (∑ k ∈ Finset.range m, 1 / ((2 * k + 2 : ℕ) : ℝ)) =
        (1 / 2 : ℝ) * harmonic m := by
  intro m
  rw [harmonic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hkpos : (0 : ℝ) < 1 + k := by positivity
  field_simp [ne_of_gt hkpos]
  <;> ring

theorem gap6 :
    ∃ C : ℝ, ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (nhds 0) ∧
      ∀ m : ℕ, 1 ≤ m →
        (1 / 2 : ℝ) * harmonic m =
          (1 / 2 : ℝ) * Real.log m + (1 / 2) * C + ε m := by
  refine ⟨Real.eulerMascheroniConstant,
    fun m => (1 / 2 : ℝ) *
      (harmonic m - Real.log m - Real.eulerMascheroniConstant), ?_, ?_⟩
  · simpa using tendsto_harmonic_error_local.const_mul (1 / 2 : ℝ)
  · intro m hm
    ring

theorem gap7 :
    ∃ C : ℝ, ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (nhds 0) ∧
      ∀ m : ℕ, 1 ≤ m →
        (∑ k ∈ Finset.range m, 1 / ((2 * k + 2 : ℕ) : ℝ)) =
          (1 / 2 : ℝ) * Real.log m + C / 2 + ε m := by
  rcases gap6 with ⟨C, ε, hε, hformula⟩
  refine ⟨C, ε, hε, ?_⟩
  intro m hm
  rw [gap5 m, hformula m hm]
  ring

theorem gap8 :
    ∀ k : ℕ,
      (∑ j ∈ Finset.range k, 1 / ((2 * j + 1 : ℕ) : ℝ)) =
        harmonic (2 * k) - (1 / 2 : ℝ) * harmonic k := by
  intro k
  induction k with
  | zero => simp [harmonic]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      unfold harmonic
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      norm_num [Nat.cast_add, Nat.cast_mul]
      have hkpos : (0 : ℝ) < 1 + k := by positivity
      field_simp [ne_of_gt hkpos]
      ring

theorem gap9 :
    ∃ C : ℝ, ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (nhds 0) ∧
      ∀ k : ℕ, 1 ≤ k →
        harmonic (2 * k) - (1 / 2 : ℝ) * harmonic k =
          Real.log 2 + (1 / 2) * Real.log k + C / 2 + ε k := by
  let err : ℕ → ℝ := fun n =>
    harmonic n - Real.log n - Real.eulerMascheroniConstant
  refine ⟨Real.eulerMascheroniConstant,
    fun k => err (2 * k) - (1 / 2 : ℝ) * err k, ?_, ?_⟩
  · have htwo : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
      tendsto_id.const_mul_atTop' (by norm_num)
    simpa [err] using
      (tendsto_harmonic_error_local.comp htwo).sub
        (tendsto_harmonic_error_local.const_mul (1 / 2 : ℝ))
  · intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hlog : Real.log ((2 * k : ℕ) : ℝ) =
        Real.log 2 + Real.log k := by
      rw [Nat.cast_mul]
      norm_num only [Nat.cast_ofNat]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hk0]
    dsimp [err]
    rw [hlog]
    ring

theorem gap10 :
    ∃ C : ℝ, ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (nhds 0) ∧
      ∀ k : ℕ, 1 ≤ k →
        (∑ j ∈ Finset.range k, 1 / ((2 * j + 1 : ℕ) : ℝ)) =
          Real.log 2 + (1 / 2) * Real.log k + C / 2 + ε k := by
  rcases gap9 with ⟨C, ε, hε, hformula⟩
  refine ⟨C, ε, hε, ?_⟩
  intro k hk
  rw [gap8 k]
  exact hformula k hk

theorem gap11 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ n : ℕ,
      cyclePartial p q n = target p q + cycleError p q n := by
  intro n
  unfold cycleError
  ring

theorem gap12 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (cycleError p q) atTop (nhds 0) := by
  let err : ℕ → ℝ := fun m =>
    harmonic m - Real.log m - Real.eulerMascheroniConstant
  let ε : ℕ → ℝ := fun n =>
    err (2 * (n * p)) - (1 / 2 : ℝ) * err (n * p) -
      (1 / 2 : ℝ) * err (n * q)
  have hnp : Tendsto (fun n : ℕ => n * p) atTop atTop := by
    simpa [Nat.mul_comm] using
      tendsto_id.const_mul_atTop' (show 0 < p by omega)
  have hnq : Tendsto (fun n : ℕ => n * q) atTop atTop := by
    simpa [Nat.mul_comm] using
      tendsto_id.const_mul_atTop' (show 0 < q by omega)
  have h2np : Tendsto (fun n : ℕ => 2 * (n * p)) atTop atTop :=
    hnp.const_mul_atTop' (by norm_num)
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa [ε, err] using
      ((tendsto_harmonic_error_local.comp h2np).sub
        ((tendsto_harmonic_error_local.comp hnp).const_mul (1 / 2 : ℝ))).sub
        ((tendsto_harmonic_error_local.comp hnq).const_mul (1 / 2 : ℝ))
  have hformula : ∀ n : ℕ, 1 ≤ n → cycleError p q n = ε n := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hlog_np : Real.log ((n * p : ℕ) : ℝ) =
        Real.log n + Real.log p := by
      rw [Nat.cast_mul, Real.log_mul hn0 hp0]
    have hlog_nq : Real.log ((n * q : ℕ) : ℝ) =
        Real.log n + Real.log q := by
      rw [Nat.cast_mul, Real.log_mul hn0 hq0]
    have hlog_2np : Real.log ((2 * (n * p) : ℕ) : ℝ) =
        Real.log 2 + Real.log n + Real.log p := by
      push_cast
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (mul_ne_zero hn0 hp0), Real.log_mul hn0 hp0]
      ring
    have hlog_pq : Real.log ((p : ℝ) / q) =
        Real.log p - Real.log q := by
      rw [Real.log_div hp0 hq0]
    unfold cycleError cyclePartial
    rw [partialSum_cycles p q hp hq n, gap8 (n * p), gap5 (n * q)]
    dsimp [ε, err, target]
    rw [hlog_2np, hlog_np, hlog_nq, hlog_pq]
    ring
  refine hε.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hformula n hn).symm

theorem gap13 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ n : ℕ,
      cyclePartial p q n = target p q + cycleError p q n := by
  exact gap11 p q hp hq

theorem gap14 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (cycleError p q) atTop (nhds 0) := by
  exact gap12 p q hp hq

theorem gap15 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (cycleError p q) atTop (nhds 0) := by
  exact gap12 p q hp hq

private theorem tendsto_cyclePartial (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (cyclePartial p q) atTop (nhds (target p q)) := by
  have hconstant : Tendsto (fun _ : ℕ => target p q) atTop
      (nhds (target p q)) := tendsto_const_nhds
  have h := hconstant.add (gap12 p q hp hq)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards with n
  exact (gap11 p q hp hq n).symm

theorem gap16 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ n : ℕ,
      partialSum p q (n * (p + q) + 1) =
        cyclePartial p q n + rearrangedTerm p q (n * (p + q)) := by
  intro n
  simp [partialSum, cyclePartial, Finset.sum_range_succ]

theorem gap17 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => rearrangedTerm p q (n * (p + q)))
      atTop (nhds 0) := by
  have hterms : ∀ n : ℕ,
      rearrangedTerm p q (n * (p + q)) =
        1 / ((2 * (n * p) + 1 : ℕ) : ℝ) := by
    intro n
    simpa using rearrangedTerm_cycle_pos p q n 0 hp (by omega)
  have hdenNat : Tendsto (fun n : ℕ => 2 * (n * p) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by
      change n ≤ 2 * (n * p) + 1
      have hnp : n ≤ n * p := by
        simpa using Nat.mul_le_mul_left n hp
      exact hnp.trans (by omega)) tendsto_id
  have hdenReal : Tendsto (fun n : ℕ => ((2 * (n * p) + 1 : ℕ) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hdenNat
  have hinv := (tendsto_inv_atTop_zero :
    Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp hdenReal
  apply hinv.congr'
  filter_upwards with n
  simpa [one_div] using (hterms n).symm

theorem gap18 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (cyclePartial p q) atTop (nhds (target p q)) ∧
    Tendsto (fun n : ℕ => partialSum p q (n * (p + q) + 1))
      atTop (nhds (target p q)) := by
  refine ⟨tendsto_cyclePartial p q hp hq, ?_⟩
  have h := (tendsto_cyclePartial p q hp hq).add (gap17 p q hp hq)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards with n
  exact (gap16 p q hp hq n).symm

theorem gap19 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => partialSum p q (n * (p + q) + 1))
      atTop (nhds (target p q)) := by
  exact (gap18 p q hp hq).2

theorem gap20 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (cyclePartial p q) atTop (nhds (target p q)) := by
  exact tendsto_cyclePartial p q hp hq

private theorem tendsto_rearrangedTerm_cycle_offset
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (r : ℕ) (hr : r < p + q) :
    Tendsto (fun n : ℕ => rearrangedTerm p q (n * (p + q) + r))
      atTop (nhds 0) := by
  by_cases hrp : r < p
  · have hdenNat : Tendsto (fun n : ℕ => 2 * (n * p + r) + 1)
        atTop atTop := tendsto_atTop_mono (fun n : ℕ => by
          change n ≤ 2 * (n * p + r) + 1
          have hnp : n ≤ n * p := by
            simpa using Nat.mul_le_mul_left n hp
          exact hnp.trans (by omega)) tendsto_id
    have hdenReal : Tendsto
        (fun n : ℕ => ((2 * (n * p + r) + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hdenNat
    have hinv := (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp hdenReal
    refine hinv.congr' ?_
    filter_upwards with n
    simpa [one_div] using
      (rearrangedTerm_cycle_pos p q n r hp hrp).symm
  · have hpr : p ≤ r := Nat.le_of_not_gt hrp
    have hrs : r = p + (r - p) := by omega
    have hrsq : r - p < q := by omega
    have hdenNat : Tendsto (fun n : ℕ => 2 * (n * q + (r - p) + 1))
        atTop atTop := tendsto_atTop_mono (fun n : ℕ => by
          change n ≤ 2 * (n * q + (r - p) + 1)
          have hnq : n ≤ n * q := by
            simpa using Nat.mul_le_mul_left n hq
          exact hnq.trans (by omega)) tendsto_id
    have hdenReal : Tendsto
        (fun n : ℕ => ((2 * (n * q + (r - p) + 1) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hdenNat
    have hneg := ((tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp hdenReal).neg
    have hneg0 : Tendsto
        (fun n : ℕ => -(((2 * (n * q + (r - p) + 1) : ℕ) : ℝ)⁻¹))
        atTop (nhds 0) := by simpa using hneg
    refine hneg0.congr' ?_
    filter_upwards with n
    rw [hrs]
    simpa [one_div] using
      (rearrangedTerm_cycle_neg p q n (r - p) hq hrsq).symm

private theorem tendsto_partialSum (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Tendsto (partialSum p q) atTop (nhds (target p q)) := by
  have hd : 0 < p + q := by omega
  have hdiv : Tendsto (fun N : ℕ => N / (p + q)) atTop atTop :=
    le_of_eq (map_div_atTop_eq_nat (p + q) hd)
  let remainder : ℕ → ℝ := fun N =>
    ∑ r ∈ Finset.range (p + q),
      if r < N % (p + q) then
        rearrangedTerm p q ((N / (p + q)) * (p + q) + r)
      else 0
  have hrem : Tendsto remainder atTop (nhds 0) := by
    dsimp [remainder]
    convert tendsto_finset_sum (Finset.range (p + q)) (fun r hr => by
      have hrlt : r < p + q := Finset.mem_range.mp hr
      have hterm :=
        (tendsto_rearrangedTerm_cycle_offset p q hp hq r hrlt).comp hdiv
      have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds
      have hif := hterm.if' (p := fun N : ℕ => r < N % (p + q)) hzero
      simpa [Function.comp_def] using hif) using 1 <;> simp
  have hdecomp : ∀ N : ℕ,
      partialSum p q N =
        cyclePartial p q (N / (p + q)) + remainder N := by
    intro N
    have hmodlt : N % (p + q) < p + q := Nat.mod_lt _ hd
    have hfilter :
        (Finset.range (p + q)).filter (fun r => r < N % (p + q)) =
          Finset.range (N % (p + q)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    conv_lhs => rw [← Nat.div_add_mod' N (p + q)]
    rw [partialSum, Finset.sum_range_add]
    change cyclePartial p q (N / (p + q)) +
        (∑ r ∈ Finset.range (N % (p + q)),
          rearrangedTerm p q ((N / (p + q)) * (p + q) + r)) =
      cyclePartial p q (N / (p + q)) + remainder N
    congr 1
    dsimp [remainder]
    rw [← Finset.sum_filter, hfilter]
  have hcycle := (tendsto_cyclePartial p q hp hq).comp hdiv
  have htotal := hcycle.add hrem
  simp only [add_zero] at htotal
  refine htotal.congr' ?_
  filter_upwards with N
  exact (hdecomp N).symm

theorem gap21 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ProofGap.SeriesHasSum (rearrangedTerm p q) (target p q) := by
  simpa [ProofGap.SeriesHasSum, HasSum, Function.comp_apply, partialSum] using
    tendsto_partialSum p q hp hq

theorem gap22 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ProofGap.SeriesHasSum (rearrangedTerm p q) (target p q) := by
  exact gap21 p q hp hq

end

end ProofGap.Exercise2704
