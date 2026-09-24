import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds

namespace ProofGap.Exercise2662

noncomputable section

open Filter
open scoped BigOperators

def sigma (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ)

def ell (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (k + 1) / k

def r1Term (i : ℕ) : ℝ :=
  if i % 3 = 0 then 1 / ((4 * (i / 3) + 1 : ℕ) : ℝ)
  else if i % 3 = 1 then 1 / ((4 * (i / 3) + 3 : ℕ) : ℝ)
  else -1 / ((2 * (i / 3) + 2 : ℕ) : ℝ)

def r2Term (i : ℕ) : ℝ :=
  if i % 3 = 0 then 1 / ((2 * (i / 3) + 1 : ℕ) : ℝ)
  else if i % 3 = 1 then -1 / ((4 * (i / 3) + 2 : ℕ) : ℝ)
  else -1 / ((4 * (i / 3) + 4 : ℕ) : ℝ)

def partial1 (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, r1Term i

def partial2 (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, r2Term i

def r1Block (j : ℕ) : ℝ :=
  1 / (4 * j + 1 : ℝ) + 1 / (4 * j + 3 : ℝ) -
    1 / (2 * j + 2 : ℝ)

def r2Block (j : ℕ) : ℝ :=
  1 / (2 * j + 1 : ℝ) - 1 / (4 * j + 2 : ℝ) -
    1 / (4 * j + 4 : ℝ)

def sumR1 : ℝ := ∑' i : ℕ, r1Term i
def sumR2 : ℝ := ∑' i : ℕ, r2Term i

private theorem sigma_zero : sigma 0 = 0 := by
  simp [sigma]

private theorem ell_zero : ell 0 = 0 := by
  simp [ell]

private theorem sigma_succ (n : ℕ) :
    sigma (n + 1) = sigma n + 1 / ((n + 1 : ℕ) : ℝ) := by
  have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
  unfold sigma
  rw [hset, Finset.sum_insert hnot]
  ring

private theorem ell_succ (n : ℕ) :
    ell (n + 1) = ell n + (-1 : ℝ) ^ (n + 2) / ((n + 1 : ℕ) : ℝ) := by
  have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
  unfold ell
  rw [hset, Finset.sum_insert hnot]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private theorem sigma_eq_harmonic (n : ℕ) :
    sigma n = (harmonic n : ℝ) := by
  unfold sigma
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    one_div]

private theorem sigma_double_sub_tendsto (p : ℕ → ℕ)
    (hp : Tendsto p atTop atTop) :
    Tendsto (fun n : ℕ => sigma (2 * p n) - sigma (p n)) atTop
      (nhds (Real.log 2)) := by
  have hdouble : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hresDouble := Real.tendsto_harmonic_sub_log.comp (hdouble.comp hp)
  have hresBase := Real.tendsto_harmonic_sub_log.comp hp
  have hresZero := hresDouble.sub hresBase
  have hconst : Tendsto (fun _ : ℕ => Real.log 2) atTop (nhds (Real.log 2)) :=
    tendsto_const_nhds
  have h := hresZero.add hconst
  have h' : Tendsto
      (fun n =>
        (((harmonic (2 * p n) : ℚ) : ℝ) - Real.log ((2 * p n : ℕ) : ℝ)) -
          (((harmonic (p n) : ℚ) : ℝ) - Real.log ((p n : ℕ) : ℝ)) +
          Real.log 2) atTop (nhds (Real.log 2)) := by
    simpa [Function.comp_def] using h
  apply h'.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 1)] with n hn
  rw [sigma_eq_harmonic, sigma_eq_harmonic]
  have hpne : ((p n : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show (((2 * p n : ℕ) : ℝ)) = (2 : ℝ) * (p n : ℝ) by norm_num,
    Real.log_mul (by norm_num) hpne]
  ring

private theorem partial1_succ (m : ℕ) :
    partial1 (m + 1) = partial1 m + r1Term m := by
  unfold partial1
  rw [Finset.sum_range_succ]

private theorem partial2_succ (m : ℕ) :
    partial2 (m + 1) = partial2 m + r2Term m := by
  unfold partial2
  rw [Finset.sum_range_succ]

theorem gap1 :
    ∀ n : ℕ, partial1 (3 * n) = ∑ j ∈ Finset.range n, r1Block j := by
  intro n
  induction n with
  | zero => simp [partial1]
  | succ n ih =>
      have hdiv₁ : (3 * n + 1) / 3 = n := by omega
      have hdiv₂ : (3 * n + 2) / 3 = n := by omega
      rw [show 3 * (n + 1) = 3 * n + 3 by omega,
        show 3 * n + 3 = (3 * n + 2) + 1 by omega, partial1_succ,
        show 3 * n + 2 = (3 * n + 1) + 1 by omega, partial1_succ,
        show 3 * n + 1 = 3 * n + 1 by rfl, partial1_succ,
        ih, Finset.sum_range_succ]
      simp only [r1Term, r1Block]
      simp [Nat.add_mod, hdiv₁, hdiv₂]
      ring

theorem gap2 :
    ∀ n : ℕ,
      partial1 (3 * n) =
        (∑ j ∈ Finset.range n, 1 / (4 * j + 1 : ℝ)) +
        (∑ j ∈ Finset.range n, 1 / (4 * j + 3 : ℝ)) -
        (∑ j ∈ Finset.range n, 1 / (2 * j + 2 : ℝ)) := by
  intro n
  rw [gap1 n]
  simp only [r1Block, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem gap3 :
    ∀ n : ℕ, ell (2 * n) = sigma (2 * n) - sigma n := by
  intro n
  induction n with
  | zero => simp [sigma_zero, ell_zero]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        ell_succ (2 * n + 1), ell_succ (2 * n),
        sigma_succ (2 * n + 1), sigma_succ (2 * n), sigma_succ n, ih]
      rw [Even.neg_one_pow (n := 2 * n + 2) (by use n + 1; omega),
        Odd.neg_one_pow (n := 2 * n + 3) (by use n + 1; omega)]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      have h₁ : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have h₂ : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [h₁, h₂, hn]
      ring

theorem gap4 :
    ∀ n : ℕ, ell (4 * n) = sigma (4 * n) - sigma (2 * n) := by
  intro n
  simpa only [show 4 * n = 2 * (2 * n) by omega] using gap3 (2 * n)

private def oddPart (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, 1 / (2 * j + 1 : ℝ)

private theorem oddPart_succ (n : ℕ) :
    oddPart (n + 1) = oddPart n + 1 / (2 * n + 1 : ℝ) := by
  unfold oddPart
  rw [Finset.sum_range_succ]

private theorem oddPart_eq_sigma (n : ℕ) :
    oddPart n = sigma (2 * n) - (1 / 2 : ℝ) * sigma n := by
  induction n with
  | zero => simp [oddPart, sigma_zero]
  | succ n ih =>
      rw [oddPart_succ, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        sigma_succ (2 * n + 1), sigma_succ (2 * n), sigma_succ n, ih]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      have h₁ : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have h₂ : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [h₁, h₂, hn]
      ring

private theorem quartic_odd_parts (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / (4 * j + 1 : ℝ)) +
      (∑ j ∈ Finset.range n, 1 / (4 * j + 3 : ℝ)) = oddPart (2 * n) := by
  induction n with
  | zero => simp [oddPart]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        oddPart_succ (2 * n + 1), oddPart_succ (2 * n), ← ih]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      ring

private theorem even_part_eq (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / (2 * j + 2 : ℝ)) =
      (1 / 2 : ℝ) * sigma n := by
  have hterm : ∀ j : ℕ,
      1 / (2 * j + 2 : ℝ) = (1 / 2 : ℝ) * (1 / ((j + 1 : ℕ) : ℝ)) := by
    intro j
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hj]
  rw [show (∑ j ∈ Finset.range n, 1 / (2 * j + 2 : ℝ)) =
      ∑ j ∈ Finset.range n, (1 / 2 : ℝ) * (1 / ((j + 1 : ℕ) : ℝ)) by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j,
    ← Finset.mul_sum]
  congr 1
  rw [sigma_eq_harmonic, harmonic]
  norm_num only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem gap5 :
    ∀ n : ℕ,
      partial1 (3 * n) =
        sigma (4 * n) - (1 / 2 : ℝ) * sigma (2 * n) -
          (1 / 2 : ℝ) * sigma n := by
  intro n
  rw [gap2 n, quartic_odd_parts, oddPart_eq_sigma (2 * n), even_part_eq]
  congr 3 <;> omega

theorem gap6 :
    ∀ n : ℕ,
      sigma (4 * n) - (1 / 2 : ℝ) * sigma (2 * n) -
          (1 / 2 : ℝ) * sigma n =
        ell (4 * n) + (1 / 2 : ℝ) * ell (2 * n) := by
  intro n
  rw [gap4 n, gap3 n]
  ring

theorem gap7 :
    ∀ n : ℕ,
      partial1 (3 * n) = ell (4 * n) + (1 / 2 : ℝ) * ell (2 * n) := by
  intro n
  rw [gap5 n, gap6 n]

theorem gap8 :
    Tendsto (fun n : ℕ => ell (4 * (n + 1))) atTop (nhds (Real.log 2)) ∧
      Tendsto (fun n : ℕ => ell (2 * (n + 1))) atTop (nhds (Real.log 2)) := by
  have hp₁ : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hp₂ : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  constructor
  · have h := sigma_double_sub_tendsto (fun n : ℕ => 2 * (n + 1)) hp₂
    apply h.congr'
    filter_upwards [] with n
    calc
      sigma (2 * (2 * (n + 1))) - sigma (2 * (n + 1)) =
          ell (2 * (2 * (n + 1))) := (gap3 (2 * (n + 1))).symm
      _ = ell (4 * (n + 1)) := by congr 1 <;> omega
  · have h := sigma_double_sub_tendsto (fun n : ℕ => n + 1) hp₁
    apply h.congr'
    exact Eventually.of_forall (fun n => (gap3 (n + 1)).symm)

theorem gap9 :
    Tendsto (fun n : ℕ => ell (2 * (n + 1))) atTop (nhds (Real.log 2)) := by
  exact gap8.2

theorem gap10 :
    Tendsto (fun n : ℕ => ell (4 * (n + 1))) atTop (nhds (Real.log 2)) := by
  exact gap8.1

theorem gap11 :
    Tendsto (fun n : ℕ => partial1 (3 * n)) atTop
      (nhds (Real.log 2 + (1 / 2 : ℝ) * Real.log 2)) := by
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ell (2 * (n + 1)))
      atTop (nhds ((1 / 2 : ℝ) * Real.log 2)) :=
    tendsto_const_nhds.mul gap9
  have h := gap10.add hhalf
  have hshift : Tendsto (fun n : ℕ => partial1 (3 * (n + 1))) atTop
      (nhds (Real.log 2 + (1 / 2 : ℝ) * Real.log 2)) := by
    apply h.congr'
    exact Eventually.of_forall (fun n => (gap7 (n + 1)).symm)
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa [Nat.mul_add] using hshift

theorem gap12 :
    Real.log 2 + (1 / 2 : ℝ) * Real.log 2 = (3 / 2 : ℝ) * Real.log 2 := by
  ring

theorem gap13 :
    Tendsto (fun n : ℕ => partial1 (3 * n)) atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
  rw [← gap12]
  exact gap11

private theorem r1_at_block_zero (n : ℕ) :
    r1Term (3 * (n + 1)) = 1 / ((4 * (n + 1) + 1 : ℕ) : ℝ) := by
  have hdiv : (3 * (n + 1)) / 3 = n + 1 := by omega
  simp [r1Term, hdiv]

private theorem r1_at_block_one (n : ℕ) :
    r1Term (3 * (n + 1) + 1) = 1 / ((4 * (n + 1) + 3 : ℕ) : ℝ) := by
  have hdiv : (3 * (n + 1) + 1) / 3 = n + 1 := by omega
  simp [r1Term, hdiv]

private theorem r2_at_block_zero (n : ℕ) :
    r2Term (3 * (n + 1)) = 1 / ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
  have hdiv : (3 * (n + 1)) / 3 = n + 1 := by omega
  simp [r2Term, hdiv]

private theorem r2_at_block_one (n : ℕ) :
    r2Term (3 * (n + 1) + 1) = -1 / ((4 * (n + 1) + 2 : ℕ) : ℝ) := by
  have hdiv : (3 * (n + 1) + 1) / 3 = n + 1 := by omega
  simp [r2Term, hdiv]

private theorem inv_succ_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))

theorem gap14 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        partial1 (3 * (n + 1) + 1) - partial1 (3 * (n + 1)))
      (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have heq : partial1 (3 * (n + 1) + 1) - partial1 (3 * (n + 1)) =
      1 / ((4 * (n + 1) + 1 : ℕ) : ℝ) := by
    rw [partial1_succ, r1_at_block_zero]
    ring
  rw [heq]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hsmall : 0 < (n : ℝ) + 1 := by positivity
  have hlarge : 0 < 4 * ((n : ℝ) + 1) + 1 := by positivity
  simp only [Real.norm_eq_abs, one_mul, abs_of_pos (one_div_pos.mpr hlarge),
    abs_of_pos (one_div_pos.mpr hsmall)]
  exact one_div_le_one_div_of_le hsmall (by linarith)

theorem gap15 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        partial1 (3 * (n + 1) + 2) - partial1 (3 * (n + 1)))
      (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun n => ?_)
  have heq : partial1 (3 * (n + 1) + 2) - partial1 (3 * (n + 1)) =
      1 / ((4 * (n + 1) + 1 : ℕ) : ℝ) +
        1 / ((4 * (n + 1) + 3 : ℕ) : ℝ) := by
    rw [show 3 * (n + 1) + 2 = (3 * (n + 1) + 1) + 1 by omega,
      partial1_succ, partial1_succ, r1_at_block_zero, r1_at_block_one]
    ring
  rw [heq]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hsmall : 0 < (n : ℝ) + 1 := by positivity
  have hlarge₁ : 0 < 4 * ((n : ℝ) + 1) + 1 := by positivity
  have hlarge₂ : 0 < 4 * ((n : ℝ) + 1) + 3 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (add_pos (one_div_pos.mpr hlarge₁) (one_div_pos.mpr hlarge₂)),
    abs_of_pos (one_div_pos.mpr hsmall)]
  have h₁ := one_div_le_one_div_of_le hsmall (by linarith :
    (n : ℝ) + 1 ≤ 4 * ((n : ℝ) + 1) + 1)
  have h₂ := one_div_le_one_div_of_le hsmall (by linarith :
    (n : ℝ) + 1 ≤ 4 * ((n : ℝ) + 1) + 3)
  nlinarith

private theorem tendsto_of_three_residues {u : ℕ → ℝ} {L : ℝ}
    (h0 : Tendsto (fun n : ℕ => u (3 * n)) atTop (nhds L))
    (h1 : Tendsto (fun n : ℕ => u (3 * n + 1)) atTop (nhds L))
    (h2 : Tendsto (fun n : ℕ => u (3 * n + 2)) atTop (nhds L)) :
    Tendsto u atTop (nhds L) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 h0) ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 h1) ε hε
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 h2) ε hε
  let Q : ℕ := max N0 (max N1 N2)
  refine ⟨3 * Q, fun n hn => ?_⟩
  let q : ℕ := n / 3
  have hdecomp : n % 3 + 3 * q = n := by
    dsimp only [q]
    exact Nat.mod_add_div n 3
  have hmodlt : n % 3 < 3 := Nat.mod_lt _ (by omega)
  have hq : Q ≤ q := by
    dsimp only [Q, q]
    omega
  have hq0 : N0 ≤ q := (le_max_left _ _).trans hq
  have hq1 : N1 ≤ q := (le_max_left _ _).trans (le_max_right N0 _ |>.trans hq)
  have hq2 : N2 ≤ q := (le_max_right N1 N2).trans
    (le_max_right N0 _ |>.trans hq)
  interval_cases hrem : n % 3
  · have hnform : n = 3 * q := by omega
    rw [hnform]
    exact hN0 q hq0
  · have hnform : n = 3 * q + 1 := by omega
    rw [hnform]
    exact hN1 q hq1
  · have hnform : n = 3 * q + 2 := by omega
    rw [hnform]
    exact hN2 q hq2

theorem gap16 :
    Tendsto partial1 atTop (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hbase : Tendsto (fun n : ℕ => partial1 (3 * (n + 1))) atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := gap13.comp hsucc
  have herr1 := gap14.trans_tendsto inv_succ_tendsto_zero
  have herr2 := gap15.trans_tendsto inv_succ_tendsto_zero
  have hshift1 : Tendsto (fun n : ℕ => partial1 (3 * (n + 1) + 1)) atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
    have h := hbase.add herr1
    have h' : Tendsto (fun n : ℕ =>
        partial1 (3 * (n + 1)) +
          (partial1 (3 * (n + 1) + 1) - partial1 (3 * (n + 1)))) atTop
        (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
      simpa only [add_zero] using h
    apply h'.congr'
    filter_upwards [] with n
    ring
  have hshift2 : Tendsto (fun n : ℕ => partial1 (3 * (n + 1) + 2)) atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
    have h := hbase.add herr2
    have h' : Tendsto (fun n : ℕ =>
        partial1 (3 * (n + 1)) +
          (partial1 (3 * (n + 1) + 2) - partial1 (3 * (n + 1)))) atTop
        (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
      simpa only [add_zero] using h
    apply h'.congr'
    filter_upwards [] with n
    ring
  have hres1 : Tendsto (fun n : ℕ => partial1 (3 * n + 1)) atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.add_assoc] using hshift1
  have hres2 : Tendsto (fun n : ℕ => partial1 (3 * n + 2)) atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.add_assoc] using hshift2
  exact tendsto_of_three_residues gap13 hres1 hres2

theorem gap17 :
    ProofGap.SeriesHasSum r1Term ((3 / 2 : ℝ) * Real.log 2) := by
  unfold ProofGap.SeriesHasSum
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def, partial1] using gap16

private theorem quartic_even_parts (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / (4 * j + 2 : ℝ)) +
      (∑ j ∈ Finset.range n, 1 / (4 * j + 4 : ℝ)) =
        (1 / 2 : ℝ) * sigma (2 * n) := by
  have hsplit :
      (∑ j ∈ Finset.range n, 1 / (4 * j + 2 : ℝ)) +
        (∑ j ∈ Finset.range n, 1 / (4 * j + 4 : ℝ)) =
          ∑ j ∈ Finset.range (2 * n), 1 / (2 * j + 2 : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ,
          show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        ring
  rw [hsplit, even_part_eq]

theorem gap18 :
    ∀ n : ℕ, partial2 (3 * n) = ∑ j ∈ Finset.range n, r2Block j := by
  intro n
  induction n with
  | zero => simp [partial2]
  | succ n ih =>
      have hdiv₁ : (3 * n + 1) / 3 = n := by omega
      have hdiv₂ : (3 * n + 2) / 3 = n := by omega
      rw [show 3 * (n + 1) = 3 * n + 3 by omega,
        show 3 * n + 3 = (3 * n + 2) + 1 by omega, partial2_succ,
        show 3 * n + 2 = (3 * n + 1) + 1 by omega, partial2_succ,
        partial2_succ, ih, Finset.sum_range_succ]
      simp only [r2Term, r2Block]
      simp [Nat.add_mod, hdiv₁, hdiv₂]
      ring

theorem gap19 :
    ∀ n : ℕ,
      partial2 (3 * n) =
        (∑ j ∈ Finset.range n, 1 / (2 * j + 1 : ℝ)) -
        (∑ j ∈ Finset.range n, 1 / (4 * j + 2 : ℝ)) -
        (∑ j ∈ Finset.range n, 1 / (4 * j + 4 : ℝ)) := by
  intro n
  rw [gap18 n]
  simp only [r2Block, Finset.sum_sub_distrib]

theorem gap20 :
    ∀ n : ℕ,
      partial2 (3 * n) =
        sigma (2 * n) - (1 / 2 : ℝ) * sigma n -
          (1 / 2 : ℝ) * sigma (2 * n) := by
  intro n
  calc
    partial2 (3 * n) = oddPart n -
        ((∑ j ∈ Finset.range n, 1 / (4 * j + 2 : ℝ)) +
          (∑ j ∈ Finset.range n, 1 / (4 * j + 4 : ℝ))) := by
      rw [gap19]
      unfold oddPart
      ring
    _ = (sigma (2 * n) - (1 / 2 : ℝ) * sigma n) -
        (1 / 2 : ℝ) * sigma (2 * n) := by
      rw [oddPart_eq_sigma, quartic_even_parts]
    _ = sigma (2 * n) - (1 / 2 : ℝ) * sigma n -
        (1 / 2 : ℝ) * sigma (2 * n) := by ring

theorem gap21 :
    ∀ n : ℕ,
      sigma (2 * n) - (1 / 2 : ℝ) * sigma n -
          (1 / 2 : ℝ) * sigma (2 * n) =
        (1 / 2 : ℝ) * (sigma (2 * n) - sigma n) := by
  intro n
  ring

theorem gap22 :
    ∀ n : ℕ,
      (1 / 2 : ℝ) * (sigma (2 * n) - sigma n) =
        (1 / 2 : ℝ) * ell (2 * n) := by
  intro n
  rw [gap3 n]

theorem gap23 :
    ∀ n : ℕ, partial2 (3 * n) = (1 / 2 : ℝ) * ell (2 * n) := by
  intro n
  rw [gap20 n, gap21 n, gap22 n]

theorem gap24 :
    Tendsto (fun n : ℕ => partial2 (3 * n)) atTop
      (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have h := hconst.mul gap9
  have hshift : Tendsto (fun n : ℕ => partial2 (3 * (n + 1))) atTop
      (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
    apply h.congr'
    exact Eventually.of_forall (fun n => (gap23 (n + 1)).symm)
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa [Nat.mul_add] using hshift

theorem gap25 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        partial2 (3 * (n + 1) + 1) - partial2 (3 * (n + 1)))
      (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have heq : partial2 (3 * (n + 1) + 1) - partial2 (3 * (n + 1)) =
      1 / ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    rw [partial2_succ, r2_at_block_zero]
    ring
  rw [heq]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hsmall : 0 < (n : ℝ) + 1 := by positivity
  have hlarge : 0 < 2 * ((n : ℝ) + 1) + 1 := by positivity
  simp only [Real.norm_eq_abs, one_mul, abs_of_pos (one_div_pos.mpr hlarge),
    abs_of_pos (one_div_pos.mpr hsmall)]
  exact one_div_le_one_div_of_le hsmall (by linarith)

theorem gap26 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        partial2 (3 * (n + 1) + 2) - partial2 (3 * (n + 1)))
      (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have heq : partial2 (3 * (n + 1) + 2) - partial2 (3 * (n + 1)) =
      1 / ((4 * (n + 1) + 2 : ℕ) : ℝ) := by
    rw [show 3 * (n + 1) + 2 = (3 * (n + 1) + 1) + 1 by omega,
      partial2_succ, partial2_succ, r2_at_block_zero, r2_at_block_one]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have hden : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [heq]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hsmall : 0 < (n : ℝ) + 1 := by positivity
  have hlarge : 0 < 4 * ((n : ℝ) + 1) + 2 := by positivity
  simp only [Real.norm_eq_abs, one_mul, abs_of_pos (one_div_pos.mpr hlarge),
    abs_of_pos (one_div_pos.mpr hsmall)]
  exact one_div_le_one_div_of_le hsmall (by linarith)

theorem gap27 :
    Tendsto partial2 atTop (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hbase : Tendsto (fun n : ℕ => partial2 (3 * (n + 1))) atTop
      (nhds ((1 / 2 : ℝ) * Real.log 2)) := gap24.comp hsucc
  have herr1 := gap25.trans_tendsto inv_succ_tendsto_zero
  have herr2 := gap26.trans_tendsto inv_succ_tendsto_zero
  have hshift1 : Tendsto (fun n : ℕ => partial2 (3 * (n + 1) + 1)) atTop
      (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
    have h := hbase.add herr1
    have h' : Tendsto (fun n : ℕ =>
        partial2 (3 * (n + 1)) +
          (partial2 (3 * (n + 1) + 1) - partial2 (3 * (n + 1)))) atTop
        (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
      simpa only [add_zero] using h
    apply h'.congr'
    filter_upwards [] with n
    ring
  have hshift2 : Tendsto (fun n : ℕ => partial2 (3 * (n + 1) + 2)) atTop
      (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
    have h := hbase.add herr2
    have h' : Tendsto (fun n : ℕ =>
        partial2 (3 * (n + 1)) +
          (partial2 (3 * (n + 1) + 2) - partial2 (3 * (n + 1)))) atTop
        (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
      simpa only [add_zero] using h
    apply h'.congr'
    filter_upwards [] with n
    ring
  have hres1 : Tendsto (fun n : ℕ => partial2 (3 * n + 1)) atTop
      (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.add_assoc] using hshift1
  have hres2 : Tendsto (fun n : ℕ => partial2 (3 * n + 2)) atTop
      (nhds ((1 / 2 : ℝ) * Real.log 2)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.add_assoc] using hshift2
  exact tendsto_of_three_residues gap24 hres1 hres2

theorem gap28 :
    ProofGap.SeriesHasSum r2Term ((1 / 2 : ℝ) * Real.log 2) := by
  unfold ProofGap.SeriesHasSum
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def, partial2] using gap27

theorem gap29 :
    ProofGap.SeriesHasSum r1Term ((3 / 2 : ℝ) * Real.log 2) := by
  exact gap17

theorem gap30 :
    ProofGap.SeriesHasSum r2Term ((1 / 2 : ℝ) * Real.log 2) := by
  exact gap28

end

end ProofGap.Exercise2662
