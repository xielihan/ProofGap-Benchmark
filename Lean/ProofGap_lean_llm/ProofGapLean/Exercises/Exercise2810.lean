import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2810

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def summand (k : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / ((2 * k + 1 : ℕ) : ℝ)) -
    Real.rpow x (1 / ((2 * k - 1 : ℕ) : ℝ))

def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, summand k x

def limitFunction (x : ℝ) : ℝ :=
  if x = 0 ∨ x = 1 then 0 else 1 - x

def badPoint (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (2 * n + 1)

def epsilon0 : ℝ := 1 / 4

def seriesFunction (x : ℝ) : ℝ :=
  ∑' k : ℕ, summand (k + 1) x

def integratedTerm (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, summand n x

def closedIntegralTerm (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) -
    (2 * (n : ℝ) - 1) / (2 * (n : ℝ))

def telescopingIntegralTerm (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ)) - 1 / (2 * (n : ℝ) + 2)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem rpow_zero_pos_aux (p : ℝ) (hp : 0 < p) :
    Real.rpow 0 p = 0 := by
  have hpc : (p : ℂ) ≠ 0 := by
    intro h
    apply hp.ne'
    have hre := congrArg Complex.re h
    simpa using hre
  unfold Real.rpow
  simp [hpc]

private theorem tendsto_recip_odd :
    Tendsto (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hc : Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  simpa [one_div] using tendsto_inv_atTop_zero.comp hc

private theorem tendsto_rpow_recip_odd (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => Real.rpow x (1 / ((2 * n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  have hm :
      Tendsto
        (fun n : ℕ => Real.log x * (1 / ((2 * n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (Real.log x * 0)) :=
    tendsto_const_nhds.mul tendsto_recip_odd
  simpa [Real.rpow_def_of_pos hx] using
    Real.continuous_exp.continuousAt.tendsto.comp hm

private theorem recip_add_one_recip (a : ℝ) (ha : 0 < a) :
    1 / (1 / a + 1) = a / (a + 1) := by
  have ha1 : a + 1 ≠ 0 := by positivity
  have hsumpos : 0 < 1 / a + 1 := by positivity
  field_simp [ha.ne', ha1, hsumpos.ne'] <;> ring

private theorem rpow_intervalIntegrable_aux (p : ℝ) (hp : 0 < p) :
    IntervalIntegrable (fun x : ℝ => Real.rpow x p)
      MeasureTheory.volume 0 1 := by
  have hc : Continuous (fun x : ℝ => Real.rpow x p) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hpair : ContinuousAt (fun y : ℝ => (y, p)) x :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hrpair :
        ContinuousAt
          (fun q : ℝ × ℝ => Real.rpow q.1 q.2) (x, p) :=
      Real.continuousAt_rpow (x, p) (Or.inr hp)
    have htOuter :
        Tendsto (fun q : ℝ × ℝ => Real.rpow q.1 q.2)
          (𝓝 (x, p)) (𝓝 (Real.rpow x p)) :=
      hrpair
    have htInner :
        Tendsto (fun y : ℝ => (y, p)) (𝓝 x) (𝓝 (x, p)) :=
      hpair
    have htComp :
        Tendsto
          ((fun q : ℝ × ℝ => Real.rpow q.1 q.2) ∘
            (fun y : ℝ => (y, p)))
          (𝓝 x) (𝓝 (Real.rpow x p)) :=
      htOuter.comp htInner
    simpa only [Function.comp_apply] using htComp
  exact hc.intervalIntegrable 0 1

private theorem hasSum_summand (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => summand (k + 1) x) (1 - x) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ summand (k + 1) x := by
    intro k
    unfold summand
    apply sub_nonneg.mpr
    have hsub : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have he :
        1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) <
          1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)) := by
      rw [hsub]
      have hsmall : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
        positivity
      have hlarge :
          (((2 * k + 1 : ℕ) : ℝ)) <
            (((2 * (k + 1) + 1 : ℕ) : ℝ)) := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        linarith
      exact one_div_lt_one_div_of_lt hsmall hlarge
    have hrpow :
        Real.rpow x (1 / (((2 * (k + 1) - 1 : ℕ) : ℝ))) <
          Real.rpow x (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ))) :=
      Real.rpow_lt_rpow_of_exponent_gt hx hx1 he
    exact hrpow.le
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg (1 - x)).2 ?_
  have hsum : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, summand (k + 1) x) =
        Real.rpow x (1 / ((2 * n + 1 : ℕ) : ℝ)) - x := by
    intro n
    induction n with
    | zero =>
        simp [summand]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        unfold summand
        have hsub : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [hsub]
        ring
  simpa only [hsum] using
    (tendsto_rpow_recip_odd x hx).sub tendsto_const_nhds

private theorem badPoint_pos (n : ℕ) : 0 < badPoint n := by
  unfold badPoint
  positivity

private theorem badPoint_lt_one (n : ℕ) : badPoint n < 1 := by
  unfold badPoint
  apply (div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * n + 1))).2
  exact one_lt_pow₀ (by norm_num) (by omega)

private theorem badPoint_root (n : ℕ) :
    Real.rpow (badPoint n) (1 / ((2 * n + 1 : ℕ) : ℝ)) = 1 / 2 := by
  unfold badPoint
  rw [← one_div_pow]
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast (x := (1 / 2 : ℝ))
      (n := 2 * n + 1) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by omega))

private theorem tendsto_recip_even_succ :
    Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ) + 2)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => 2 * n + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hc : Tendsto (fun n : ℕ => ((2 * n + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  simpa [one_div, Nat.cast_add, Nat.cast_mul] using
    tendsto_inv_atTop_zero.comp hc

private theorem hasSum_telescopingIntegralTerm :
    HasSum (fun k : ℕ => telescopingIntegralTerm (k + 1)) (1 / 2) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ telescopingIntegralTerm (k + 1) := by
    intro k
    unfold telescopingIntegralTerm
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  refine
    (hasSum_iff_tendsto_nat_of_nonneg hnonneg (1 / 2 : ℝ)).2 ?_
  have hsum : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, telescopingIntegralTerm (k + 1)) =
        1 / 2 - 1 / (2 * (n : ℝ) + 2) := by
    intro n
    induction n with
    | zero =>
        norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        unfold telescopingIntegralTerm
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring
  simpa only [hsum, sub_zero] using
    tendsto_const_nhds.sub tendsto_recip_even_succ

theorem gap1 :
    ∀ (n : ℕ) (x : ℝ), x = 0 ∨ x = 1 → partialSum n x = 0 := by
  intro n x hx
  rcases hx with rfl | rfl
  · unfold partialSum
    apply Finset.sum_eq_zero
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hp1 : 0 < (1 / (((2 * k + 1 : ℕ) : ℝ)) : ℝ) := by
      positivity
    have hp2 : 0 < (1 / (((2 * k - 1 : ℕ) : ℝ)) : ℝ) := by
      have hpos : 0 < 2 * k - 1 := by omega
      positivity
    unfold summand
    simpa only [rpow_zero_pos_aux _ hp1, rpow_zero_pos_aux _ hp2, sub_self]
  · unfold partialSum
    apply Finset.sum_eq_zero
    intro k hk
    simp [summand, Real.rpow]

theorem gap2 :
    ∀ (n : ℕ) (x : ℝ), 0 < x → x < 1 →
      partialSum n x =
        Real.rpow x (1 / ((2 * n + 1 : ℕ) : ℝ)) - x := by
  intro n x hx hx1
  induction n with
  | zero =>
      unfold partialSum
      have hI : Finset.Icc 1 0 = ∅ := by
        ext k
        simp
      rw [hI]
      norm_num
  | succ n ih =>
      change partialSum (n + 1) x =
        Real.rpow x (1 / ((2 * (n + 1) + 1 : ℕ) : ℝ)) - x
      have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp
        omega
      rw [partialSum, hset, Finset.sum_insert]
      · change summand (n + 1) x + partialSum n x = _
        rw [ih]
        unfold summand
        have hsub : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [hsub]
        ring
      · intro hmem
        have hle := (Finset.mem_Icc.mp hmem).2
        omega

theorem gap3 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => partialSum n x) atTop (𝓝 (limitFunction x)) := by
  intro x hx
  by_cases h0 : x = 0
  · subst x
    have hf : (fun n : ℕ => partialSum n 0) = fun _ => 0 := by
      funext n
      exact gap1 n 0 (Or.inl rfl)
    rw [hf]
    simp [limitFunction]
  by_cases h1 : x = 1
  · subst x
    have hf : (fun n : ℕ => partialSum n 1) = fun _ => 0 := by
      funext n
      exact gap1 n 1 (Or.inr rfl)
    rw [hf]
    simp [limitFunction]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 h1
    have hf :
        (fun n : ℕ => partialSum n x) =
          fun n => Real.rpow x (1 / ((2 * n + 1 : ℕ) : ℝ)) - x := by
      funext n
      exact gap2 n x hxpos hxlt
    rw [hf]
    simpa [limitFunction, h0, h1] using
      (tendsto_rpow_recip_odd x hxpos).sub tendsto_const_nhds

theorem gap4 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => partialSum n x) atTop
        (𝓝 (if x = 0 ∨ x = 1 then 0 else 1 - x)) := by
  simpa [limitFunction] using gap3

theorem gap5 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      limitFunction x = if x = 0 ∨ x = 1 then 0 else 1 - x := by
  intro x hx
  rfl

theorem gap6 :
    0 < epsilon0 := by
  norm_num [epsilon0]

theorem gap7 :
    epsilon0 < 1 / 2 := by
  norm_num [epsilon0]

theorem gap8 :
    (0 : ℝ) < 1 / 2 := by
  norm_num

theorem gap9 :
    ∀ n : ℕ,
      |partialSum n (badPoint n) - limitFunction (badPoint n)| = 1 / 2 := by
  intro n
  have hp := badPoint_pos n
  have hlt := badPoint_lt_one n
  rw [gap2 n (badPoint n) hp hlt, badPoint_root n]
  simp only [limitFunction, hp.ne', ne_of_lt hlt, false_or, if_false]
  ring_nf
  norm_num

theorem gap10 :
    (1 / 2 : ℝ) > epsilon0 := by
  norm_num [epsilon0]

theorem gap11 :
    ∀ n : ℕ,
      |partialSum n (badPoint n) - limitFunction (badPoint n)| > epsilon0 := by
  intro n
  rw [gap9 n]
  exact gap10

theorem gap12 :
    ¬ UniformlyConvergesOn partialSum limitFunction (Set.Icc (0 : ℝ) 1) := by
  intro h
  obtain ⟨N, hN⟩ := h epsilon0 gap6
  have hsmall := hN (N + 1) (by omega) (badPoint (N + 1))
    ⟨le_of_lt (badPoint_pos (N + 1)), le_of_lt (badPoint_lt_one (N + 1))⟩
  have hlarge := gap11 (N + 1)
  linarith

theorem gap13 :
    (∫ x in (0 : ℝ)..1, seriesFunction x) =
      ∫ x in (0 : ℝ)..1, 1 - x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x
  intro hx
  rw [Set.uIoc_of_le (by norm_num)] at hx
  by_cases h1 : x = 1
  · subst x
    simp [seriesFunction, summand]
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 h1
    exact (hasSum_summand x hx.1 hxlt).tsum_eq

theorem gap14 :
    (∫ x in (0 : ℝ)..1, 1 - x) = 1 / 2 := by
  have hxint : (∫ x in (0 : ℝ)..1, x) = 1 / 2 := by
    simpa using (integral_rpow (by norm_num : (-1 : ℝ) < 1))
  have hone : (∫ (x : ℝ) in (0 : ℝ)..1, (1 : ℝ)) = 1 := by
    norm_num
  have hconst :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hid :
      IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  calc
    (∫ x in (0 : ℝ)..1, 1 - x) =
        (∫ x in (0 : ℝ)..1, (1 : ℝ)) - (∫ x in (0 : ℝ)..1, x) := by
      exact intervalIntegral.integral_sub hconst hid
    _ = 1 - 1 / 2 := by rw [hone, hxint]
    _ = 1 / 2 := by norm_num

theorem gap15 :
    (∫ x in (0 : ℝ)..1, seriesFunction x) = 1 / 2 := by
  rw [gap13, gap14]

theorem gap16 :
    (∑' k : ℕ, integratedTerm (k + 1)) =
      ∑' k : ℕ, closedIntegralTerm (k + 1) := by
  apply congrArg tsum
  funext k
  unfold integratedTerm summand closedIntegralTerm
  have hnat2 : 0 < 2 * (k + 1) - 1 := by omega
  have hbase1pos :
      0 < (((2 * (k + 1) + 1 : ℕ) : ℝ)) := by
    positivity
  have hbase2pos :
      0 < (((2 * (k + 1) - 1 : ℕ) : ℝ)) := by
    positivity
  have hp1pos :
      0 < (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) : ℝ) := by
    positivity
  have hp2pos :
      0 < (1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)) : ℝ) := by
    positivity
  have hp1 :
      (-1 : ℝ) < 1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) := by
    linarith
  have hp2 :
      (-1 : ℝ) < 1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)) := by
    linarith
  have hcond1 :
      (-1 : ℝ) < 1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) ∨
        ((1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) : ℝ) ≠ -1 ∧
          (0 : ℝ) ∉ Set.uIcc (0 : ℝ) 1) :=
    Or.inl hp1
  have hcond2 :
      (-1 : ℝ) < 1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)) ∨
        ((1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)) : ℝ) ≠ -1 ∧
          (0 : ℝ) ∉ Set.uIcc (0 : ℝ) 1) :=
    Or.inl hp2
  have hkreal : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hnormbase1 : 0 < 2 * ((k : ℝ) + 1) + 1 := by
    nlinarith
  have hnormbase2 : 0 < 2 * ((k : ℝ) + 1) - 1 := by
    nlinarith
  have hzero1 :
      Real.rpow (0 : ℝ) ((2 * ((k : ℝ) + 1) + 1)⁻¹ + 1) = 0 := by
    apply rpow_zero_pos_aux
    have hinv : 0 < (2 * ((k : ℝ) + 1) + 1)⁻¹ := inv_pos.mpr hnormbase1
    linarith
  have hzero2 :
      Real.rpow (0 : ℝ) ((2 * ((k : ℝ) + 1) - 1)⁻¹ + 1) = 0 := by
    apply rpow_zero_pos_aux
    have hinv : 0 < (2 * ((k : ℝ) + 1) - 1)⁻¹ := inv_pos.mpr hnormbase2
    linarith
  have hi1 :
      IntervalIntegrable
        (fun x : ℝ => Real.rpow x (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ))))
        MeasureTheory.volume 0 1 :=
    rpow_intervalIntegrable_aux _ hp1pos
  have hi2 :
      IntervalIntegrable
        (fun x : ℝ => Real.rpow x (1 / (((2 * (k + 1) - 1 : ℕ) : ℝ))))
        MeasureTheory.volume 0 1 :=
    rpow_intervalIntegrable_aux _ hp2pos
  have heval1 :
      (∫ x in (0 : ℝ)..1,
        Real.rpow x (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)))) =
        (((2 * (k + 1) + 1 : ℕ) : ℝ)) /
          ((((2 * (k + 1) + 1 : ℕ) : ℝ)) + 1) := by
    have hraw1 :
        (∫ x in (0 : ℝ)..1,
          Real.rpow x (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)))) =
          (1 - Real.rpow (0 : ℝ)
            ((2 * ((k : ℝ) + 1) + 1)⁻¹ + 1)) /
            ((2 * ((k : ℝ) + 1) + 1)⁻¹ + 1) := by
      simpa using (integral_rpow hcond1)
    rw [hzero1] at hraw1
    calc
      _ = 1 / (1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) + 1) := by
        simpa using hraw1
      _ = _ := recip_add_one_recip _ hbase1pos
  have heval2 :
      (∫ x in (0 : ℝ)..1,
        Real.rpow x (1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)))) =
        (((2 * (k + 1) - 1 : ℕ) : ℝ)) /
          ((((2 * (k + 1) - 1 : ℕ) : ℝ)) + 1) := by
    have hraw2 :
        (∫ x in (0 : ℝ)..1,
          Real.rpow x (1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)))) =
          (1 - Real.rpow (0 : ℝ)
            ((2 * ((k : ℝ) + 1) - 1)⁻¹ + 1)) /
            ((2 * ((k : ℝ) + 1) - 1)⁻¹ + 1) := by
      simpa using (integral_rpow hcond2)
    rw [hzero2] at hraw2
    calc
      _ = 1 / (1 / (((2 * (k + 1) - 1 : ℕ) : ℝ)) + 1) := by
        simpa using hraw2
      _ = _ := recip_add_one_recip _ hbase2pos
  rw [intervalIntegral.integral_sub hi1 hi2, heval1, heval2]
  have hcast1 :
      (((2 * (k + 1) + 1 : ℕ) : ℝ)) =
        2 * (((k + 1 : ℕ) : ℝ)) + 1 := by
    norm_num
  have hle : 1 ≤ 2 * (k + 1) := by omega
  have hcast2 :
      (((2 * (k + 1) - 1 : ℕ) : ℝ)) =
        2 * (((k + 1 : ℕ) : ℝ)) - 1 := by
    rw [Nat.cast_sub hle]
    norm_num
  have hden1 :
      (2 * (((k + 1 : ℕ) : ℝ)) + 1) + 1 =
        2 * (((k + 1 : ℕ) : ℝ)) + 2 := by
    ring
  have hden2 :
      (2 * (((k + 1 : ℕ) : ℝ)) - 1) + 1 =
        2 * (((k + 1 : ℕ) : ℝ)) := by
    ring
  rw [hcast1, hcast2, hden1, hden2] <;> ring

theorem gap17 :
    (∑' k : ℕ, closedIntegralTerm (k + 1)) =
      ∑' k : ℕ, telescopingIntegralTerm (k + 1) := by
  apply congrArg tsum
  funext k
  unfold closedIntegralTerm telescopingIntegralTerm
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  field_simp <;> ring <;> nlinarith

theorem gap18 :
    (∑' k : ℕ, telescopingIntegralTerm (k + 1)) = 1 / 2 := by
  exact hasSum_telescopingIntegralTerm.tsum_eq

theorem gap19 :
    (∑' k : ℕ, integratedTerm (k + 1)) = 1 / 2 := by
  rw [gap16, gap17, gap18]

theorem gap20 :
    (∫ x in (0 : ℝ)..1, seriesFunction x) =
      ∑' k : ℕ, integratedTerm (k + 1) := by
  rw [gap15, gap19]

end

end ProofGap.Exercise2810
