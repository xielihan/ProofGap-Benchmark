import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3005

noncomputable section

open Filter
open scoped BigOperators Topology

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * x ^ n / ((2 * n + 1).factorial : ℝ)

def partialSeries (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), seriesTerm x n

def oddPartial (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (((2 * (n : ℝ)) ^ 2 - 1) / ((2 * n + 1).factorial : ℝ)) *
      t ^ (2 * n + 1)

def factoredOddPartial (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1)) /
      ((2 * n + 1).factorial : ℝ)) * t ^ (2 * n + 1)

def sinhPartial (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)

def coshPartial (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    t ^ (2 * n) / ((2 * n).factorial : ℝ)

def shiftedSinhPartial (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    t ^ (2 * n - 1) / ((2 * n - 1).factorial : ℝ)

def alternatingOddPartial (y : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    ((-1 : ℝ) ^ n * ((2 * (n : ℝ)) ^ 2 - 1) /
      ((2 * n + 1).factorial : ℝ)) * y ^ (2 * n + 1)

def alternatingFactoredOddPartial (y : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    ((-1 : ℝ) ^ n * (2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1) /
      ((2 * n + 1).factorial : ℝ)) * y ^ (2 * n + 1)

def alternatingSinhPartial (y : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (-1 : ℝ) ^ n * y ^ (2 * n - 1) / ((2 * n - 1).factorial : ℝ)

def cosinePartial (y : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (-1 : ℝ) ^ n * y ^ (2 * n) / ((2 * n).factorial : ℝ)

def positiveClosedForm (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (((x + 1) / Real.sqrt x) * Real.sinh (Real.sqrt x) -
      Real.cosh (Real.sqrt x))

def negativeClosedForm (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (((x + 1) / Real.sqrt |x|) * Real.sin (Real.sqrt |x|) -
      Real.cos (Real.sqrt |x|))

private theorem nat_succ_tendsto_atTop :
    Tendsto (fun n : ℕ => n + 1) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  exact eventually_atTop.2 ⟨b, fun a ha => by omega⟩

private theorem sinhPartial_tendsto (t : ℝ) :
    Tendsto (sinhPartial t) atTop (𝓝 (Real.sinh t)) := by
  simpa only [sinhPartial] using
    (Real.hasSum_sinh t).tendsto_sum_nat.comp nat_succ_tendsto_atTop

private theorem coshPartial_tendsto (t : ℝ) :
    Tendsto (coshPartial t) atTop (𝓝 (Real.cosh t)) := by
  simpa only [coshPartial] using
    (Real.hasSum_cosh t).tendsto_sum_nat.comp nat_succ_tendsto_atTop

private theorem sinOddPartial_tendsto (y : ℝ) :
    Tendsto
      (fun N => ∑ n ∈ Finset.range (N + 1),
        (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
          ((2 * n + 1).factorial : ℝ))
      atTop (𝓝 (Real.sin y)) := by
  simpa only using (Real.hasSum_sin y).tendsto_sum_nat.comp nat_succ_tendsto_atTop

private theorem cosinePartial_tendsto (y : ℝ) :
    Tendsto (cosinePartial y) atTop (𝓝 (Real.cos y)) := by
  simpa only [cosinePartial] using
    (Real.hasSum_cos y).tendsto_sum_nat.comp nat_succ_tendsto_atTop

private theorem shiftedSinhPartial_eq (t : ℝ) (N : ℕ) :
    shiftedSinhPartial t N =
      ∑ n ∈ Finset.range N,
        t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  induction N with
  | zero => simp [shiftedSinhPartial]
  | succ N ih =>
      simp only [shiftedSinhPartial] at ih ⊢
      have hset :
          Finset.Icc 1 (N + 1) =
            insert (N + 1) (Finset.Icc 1 N) := by
        ext k
        simp
        omega
      rw [hset, Finset.sum_insert (by simp), Finset.sum_range_succ, ih]
      have he : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
      rw [he]
      ac_rfl

private theorem shiftedSinhPartial_tendsto (t : ℝ) :
    Tendsto (shiftedSinhPartial t) atTop (𝓝 (Real.sinh t)) := by
  have h := (Real.hasSum_sinh t).tendsto_sum_nat
  refine h.congr' (Filter.Eventually.of_forall ?_)
  intro N
  exact (shiftedSinhPartial_eq t N).symm

private theorem alternatingSinhPartial_eq (y : ℝ) (N : ℕ) :
    alternatingSinhPartial y N =
      -(∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
          ((2 * n + 1).factorial : ℝ)) := by
  induction N with
  | zero => simp [alternatingSinhPartial]
  | succ N ih =>
      simp only [alternatingSinhPartial] at ih ⊢
      have hset :
          Finset.Icc 1 (N + 1) =
            insert (N + 1) (Finset.Icc 1 N) := by
        ext k
        simp
        omega
      rw [hset, Finset.sum_insert (by simp), Finset.sum_range_succ, ih]
      have he : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
      rw [he, pow_succ]
      ring

private theorem alternatingSinhPartial_tendsto (y : ℝ) :
    Tendsto (alternatingSinhPartial y) atTop (𝓝 (-Real.sin y)) := by
  have h := (Real.hasSum_sin y).tendsto_sum_nat.neg
  refine h.congr' (Filter.Eventually.of_forall ?_)
  intro N
  exact (alternatingSinhPartial_eq y N).symm

private theorem oddPartial_eq_factoredOddPartial (t : ℝ) (N : ℕ) :
    oddPartial t N = factoredOddPartial t N := by
  unfold oddPartial factoredOddPartial
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem alternatingOddPartial_eq_factored (y : ℝ) (N : ℕ) :
    alternatingOddPartial y N = alternatingFactoredOddPartial y N := by
  unfold alternatingOddPartial alternatingFactoredOddPartial
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem factored_step_identity (z : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (((2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1)) /
        ((2 * k + 1).factorial : ℝ)) * z ^ (2 * k + 1) =
      z ^ 2 * (z ^ (2 * k - 1) / ((2 * k - 1).factorial : ℝ)) -
        z * (z ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
  have heven : 2 * k = (2 * k - 1) + 1 := by omega
  have hfacEvenNat :
      (2 * k).factorial =
        (2 * k) * (2 * k - 1).factorial := by
    calc
      (2 * k).factorial =
          ((2 * k - 1) + 1).factorial :=
        congrArg Nat.factorial heven
      _ = ((2 * k - 1) + 1) *
          (2 * k - 1).factorial := by
        rw [Nat.factorial_succ]
      _ = (2 * k) * (2 * k - 1).factorial :=
        congrArg (fun m : ℕ => m * (2 * k - 1).factorial) heven.symm
  have hfacEven :
      ((2 * k).factorial : ℝ) =
        (2 * (k : ℝ)) * ((2 * k - 1).factorial : ℝ) := by
    exact_mod_cast hfacEvenNat
  have hfacOddNat :
      (2 * k + 1).factorial =
        (2 * k + 1) * (2 * k).factorial := by
    simpa only using (Nat.factorial_succ (2 * k))
  have hfacOdd :
      ((2 * k + 1).factorial : ℝ) =
        (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ) := by
    exact_mod_cast hfacOddNat
  have hpowEven : z ^ (2 * k) = z * z ^ (2 * k - 1) := by
    calc
      z ^ (2 * k) = z ^ ((2 * k - 1) + 1) :=
        congrArg (fun m : ℕ => z ^ m) heven
      _ = z ^ (2 * k - 1) * z := by rw [pow_succ]
      _ = z * z ^ (2 * k - 1) := mul_comm _ _
  have hodd : 2 * k + 1 = 2 + (2 * k - 1) := by omega
  have hpowOdd : z ^ (2 * k + 1) = z ^ 2 * z ^ (2 * k - 1) := by
    calc
      z ^ (2 * k + 1) = z ^ (2 + (2 * k - 1)) :=
        congrArg (fun m : ℕ => z ^ m) hodd
      _ = z ^ 2 * z ^ (2 * k - 1) := by rw [pow_add]
  have hk0 : k ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have htwo : 2 * (k : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hkR
  have hplus : 2 * (k : ℝ) + 1 ≠ 0 := by
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 (by omega)
    nlinarith
  have hfact : ((2 * k - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k - 1)
  rw [hfacOdd, hfacEven, hpowOdd, hpowEven]
  field_simp [htwo, hplus, hfact] <;> ring

private theorem factoredOddPartial_eq_shifted (t : ℝ) (N : ℕ) :
    factoredOddPartial t N =
      t ^ 2 * shiftedSinhPartial t N - t * coshPartial t N := by
  induction N with
  | zero =>
      simp [factoredOddPartial, shiftedSinhPartial, coshPartial]
  | succ N ih =>
      have hf :
          factoredOddPartial t (N + 1) =
            factoredOddPartial t N +
              (((2 * ((N + 1 : ℕ) : ℝ) - 1) *
                  (2 * ((N + 1 : ℕ) : ℝ) + 1)) /
                ((2 * (N + 1) + 1).factorial : ℝ)) *
                t ^ (2 * (N + 1) + 1) := by
        unfold factoredOddPartial
        rw [Finset.sum_range_succ]
      have hset :
          Finset.Icc 1 (N + 1) =
            insert (N + 1) (Finset.Icc 1 N) := by
        ext k
        simp
        omega
      have hs :
          shiftedSinhPartial t (N + 1) =
            shiftedSinhPartial t N +
              t ^ (2 * (N + 1) - 1) /
                ((2 * (N + 1) - 1).factorial : ℝ) := by
        unfold shiftedSinhPartial
        rw [hset, Finset.sum_insert (by simp)]
        ac_rfl
      have hc :
          coshPartial t (N + 1) =
            coshPartial t N +
              t ^ (2 * (N + 1)) /
                ((2 * (N + 1)).factorial : ℝ) := by
        unfold coshPartial
        rw [Finset.sum_range_succ]
      rw [hf, hs, hc, ih, factored_step_identity t (N + 1) (by omega)]
      ring

private theorem alternatingFactoredOddPartial_eq_shifted (y : ℝ) (N : ℕ) :
    alternatingFactoredOddPartial y N =
      y ^ 2 * alternatingSinhPartial y N - y * cosinePartial y N := by
  induction N with
  | zero =>
      simp [alternatingFactoredOddPartial, alternatingSinhPartial, cosinePartial]
  | succ N ih =>
      have hf :
          alternatingFactoredOddPartial y (N + 1) =
            alternatingFactoredOddPartial y N +
              ((-1 : ℝ) ^ (N + 1) *
                (2 * ((N + 1 : ℕ) : ℝ) - 1) *
                (2 * ((N + 1 : ℕ) : ℝ) + 1) /
                ((2 * (N + 1) + 1).factorial : ℝ)) *
                y ^ (2 * (N + 1) + 1) := by
        unfold alternatingFactoredOddPartial
        rw [Finset.sum_range_succ]
      have hset :
          Finset.Icc 1 (N + 1) =
            insert (N + 1) (Finset.Icc 1 N) := by
        ext k
        simp
        omega
      have hs :
          alternatingSinhPartial y (N + 1) =
            alternatingSinhPartial y N +
              (-1 : ℝ) ^ (N + 1) * y ^ (2 * (N + 1) - 1) /
                ((2 * (N + 1) - 1).factorial : ℝ) := by
        unfold alternatingSinhPartial
        rw [hset, Finset.sum_insert (by simp)]
        ac_rfl
      have hc :
          cosinePartial y (N + 1) =
            cosinePartial y N +
              (-1 : ℝ) ^ (N + 1) * y ^ (2 * (N + 1)) /
                ((2 * (N + 1)).factorial : ℝ) := by
        unfold cosinePartial
        rw [Finset.sum_range_succ]
      rw [hf, hs, hc, ih]
      have hstep := factored_step_identity y (N + 1) (by omega)
      have hsigned :
          (((-1 : ℝ) ^ (N + 1) *
              (2 * ((N + 1 : ℕ) : ℝ) - 1) *
              (2 * ((N + 1 : ℕ) : ℝ) + 1) /
              ((2 * (N + 1) + 1).factorial : ℝ)) *
              y ^ (2 * (N + 1) + 1)) =
            (-1 : ℝ) ^ (N + 1) *
              ((((2 * ((N + 1 : ℕ) : ℝ) - 1) *
                  (2 * ((N + 1 : ℕ) : ℝ) + 1)) /
                  ((2 * (N + 1) + 1).factorial : ℝ)) *
                  y ^ (2 * (N + 1) + 1)) := by
        ring
      rw [hsigned, hstep]
      ring

private theorem seriesTerm_summable_sq (t : ℝ) (ht0 : t ≠ 0) :
    Summable (seriesTerm (t ^ 2)) := by
  have hsinh : Summable (fun n : ℕ =>
      t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) :=
    (Real.hasSum_sinh t).summable
  have hcosh : Summable (fun n : ℕ =>
      t ^ (2 * n) / ((2 * n).factorial : ℝ)) :=
    (Real.hasSum_cosh t).summable
  have hcoshTail : Summable (fun n : ℕ =>
      t ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) := by
    exact (summable_nat_add_iff 1).2 hcosh
  have hfactTail : Summable (fun n : ℕ =>
      (((2 * ((n + 1 : ℕ) : ℝ) - 1) *
          (2 * ((n + 1 : ℕ) : ℝ) + 1)) /
        ((2 * (n + 1) + 1).factorial : ℝ)) *
        t ^ (2 * (n + 1) + 1)) := by
    apply ((hsinh.mul_left (t ^ 2)).sub (hcoshTail.mul_left t)).congr
    intro n
    exact (factored_step_identity t (n + 1) (by omega)).symm
  have hfact : Summable (fun n : ℕ =>
      (((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1)) /
        ((2 * n + 1).factorial : ℝ)) * t ^ (2 * n + 1)) :=
    (summable_nat_add_iff 1).1 hfactTail
  apply ((hfact.add hsinh).mul_left (1 / (4 * t))).congr
  intro n
  unfold seriesTerm
  field_simp [ht0]
  ring

private theorem seriesTerm_summable_neg_sq (y : ℝ) (hy0 : y ≠ 0) :
    Summable (seriesTerm (-(y ^ 2))) := by
  apply Summable.of_norm
  apply (seriesTerm_summable_sq y hy0).congr
  intro n
  have hterm :
      seriesTerm (-(y ^ 2)) n =
        (-1 : ℝ) ^ n * seriesTerm (y ^ 2) n := by
    unfold seriesTerm
    rw [neg_pow]
    ring
  have hnonneg : 0 ≤ seriesTerm (y ^ 2) n := by
    unfold seriesTerm
    positivity
  symm
  rw [hterm, norm_mul, norm_pow]
  simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]

private theorem tsum_eq_of_partialSeries_tendsto (x L : ℝ)
    (hs : Summable (seriesTerm x))
    (h : Tendsto (partialSeries x) atTop (𝓝 L)) :
    (∑' n : ℕ, seriesTerm x n) = L := by
  have hts :
      Tendsto (partialSeries x) atTop
        (𝓝 (∑' n : ℕ, seriesTerm x n)) := by
    simpa only [partialSeries] using
      hs.hasSum.tendsto_sum_nat.comp nat_succ_tendsto_atTop
  exact tendsto_nhds_unique hts h

theorem gap1 (x : ℝ) (hx : x = 0) :
    (∑' n : ℕ, seriesTerm x n) = 0 := by
  subst x
  have hterm : ∀ n : ℕ, seriesTerm 0 n = 0 := by
    intro n
    cases n <;> simp [seriesTerm]
  simp only [hterm, tsum_zero]

theorem gap2 (x t : ℝ) (hx : 0 < x) (ht : t = Real.sqrt x) :
    ∃ S : ℕ → ℝ, ∀ N : ℕ, S N = partialSeries (t ^ 2) N := by
  exact ⟨fun N => partialSeries (t ^ 2) N, fun N => rfl⟩

theorem gap3 (x t : ℝ) (hx : 0 < x) (ht : t = Real.sqrt x) (ht0 : t ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N : ℕ, S N = partialSeries (t ^ 2) N) ∧
      ∀ N : ℕ,
        S N = oddPartial t N / (4 * t) + sinhPartial t N / (4 * t) := by
  refine ⟨fun N => partialSeries (t ^ 2) N, fun N => rfl, ?_⟩
  intro N
  simp only [partialSeries, oddPartial, sinhPartial]
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [seriesTerm]
  field_simp
  ring

theorem gap4 (x t : ℝ) (hx : 0 < x) (ht : t = Real.sqrt x) (ht0 : t ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries (t ^ 2) N) ∧
      Tendsto
        (fun N => S N - (factoredOddPartial t N / (4 * t) + Real.sinh t / (4 * t)))
        atTop (𝓝 0) := by
  rcases gap3 x t hx ht ht0 with ⟨S, hS, hdecomp⟩
  refine ⟨S, hS, ?_⟩
  have hconst :
      Tendsto (fun _ : ℕ => Real.sinh t) atTop (𝓝 (Real.sinh t)) :=
    tendsto_const_nhds
  have hzero :
      Tendsto (fun N => sinhPartial t N - Real.sinh t) atTop (𝓝 0) := by
    simpa using (sinhPartial_tendsto t).sub hconst
  have hscaled :
      Tendsto (fun N => (1 / (4 * t)) * (sinhPartial t N - Real.sinh t))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hzero :
      Tendsto (fun N => (1 / (4 * t)) * (sinhPartial t N - Real.sinh t))
        atTop (𝓝 ((1 / (4 * t)) * 0)))
  refine hscaled.congr' (Filter.Eventually.of_forall ?_)
  intro N
  change
    1 / (4 * t) * (sinhPartial t N - Real.sinh t) =
      S N - (factoredOddPartial t N / (4 * t) + Real.sinh t / (4 * t))
  rw [hdecomp N, oddPartial_eq_factoredOddPartial]
  ring

theorem gap5 (x t : ℝ) (hx : 0 < x) (ht : t = Real.sqrt x) (ht0 : t ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries (t ^ 2) N) ∧
      Tendsto
        (fun N =>
          S N -
            ((t ^ 2 * shiftedSinhPartial t N - t * coshPartial t N) / (4 * t) +
              Real.sinh t / (4 * t)))
        atTop (𝓝 0) := by
  rcases gap4 x t hx ht ht0 with ⟨S, hS, hlim⟩
  refine ⟨S, hS, ?_⟩
  refine hlim.congr' (Filter.Eventually.of_forall ?_)
  intro N
  rw [factoredOddPartial_eq_shifted]

theorem gap6 (x t : ℝ) (hx : 0 < x) (ht : t = Real.sqrt x) (ht0 : t ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries (t ^ 2) N) ∧
      Tendsto S atTop
        (𝓝 ((t ^ 2 * Real.sinh t - t * Real.cosh t) / (4 * t) +
          Real.sinh t / (4 * t))) := by
  rcases gap5 x t hx ht ht0 with ⟨S, hS, herr⟩
  refine ⟨S, hS, ?_⟩
  have hnum :
      Tendsto
        (fun N => t ^ 2 * shiftedSinhPartial t N - t * coshPartial t N)
        atTop (𝓝 (t ^ 2 * Real.sinh t - t * Real.cosh t)) :=
    (tendsto_const_nhds.mul (shiftedSinhPartial_tendsto t)).sub
      (tendsto_const_nhds.mul (coshPartial_tendsto t))
  have hscaled :
      Tendsto
        (fun N => (1 / (4 * t)) *
          (t ^ 2 * shiftedSinhPartial t N - t * coshPartial t N))
        atTop
        (𝓝 ((1 / (4 * t)) * (t ^ 2 * Real.sinh t - t * Real.cosh t))) :=
    tendsto_const_nhds.mul hnum
  have happ := hscaled.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.sinh t / (4 * t)) atTop
      (𝓝 (Real.sinh t / (4 * t))))
  have happrox :
      Tendsto
        (fun N =>
          (t ^ 2 * shiftedSinhPartial t N - t * coshPartial t N) / (4 * t) +
            Real.sinh t / (4 * t))
        atTop
        (𝓝 ((t ^ 2 * Real.sinh t - t * Real.cosh t) / (4 * t) +
          Real.sinh t / (4 * t))) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using happ
  have htotal := herr.add happrox
  simpa only [sub_add_cancel, zero_add] using htotal

theorem gap7 (x t : ℝ) (hx : 0 < x) (ht : t = Real.sqrt x) (ht0 : t ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries (t ^ 2) N) ∧
      Tendsto S atTop
        (𝓝 ((1 / 4 : ℝ) * (((t ^ 2 + 1) / t) * Real.sinh t - Real.cosh t))) := by
  rcases gap6 x t hx ht ht0 with ⟨S, hS, hlim⟩
  refine ⟨S, hS, ?_⟩
  have hform :
      (t ^ 2 * Real.sinh t - t * Real.cosh t) / (4 * t) +
          Real.sinh t / (4 * t) =
        (1 / 4 : ℝ) * (((t ^ 2 + 1) / t) * Real.sinh t - Real.cosh t) := by
    field_simp [ht0]
    ring
  simpa only [hform] using hlim

theorem gap8 (x : ℝ) (hx : 0 < x) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop (𝓝 (positiveClosedForm x)) := by
  let t := Real.sqrt x
  have ht0 : t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have ht2 : t ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  rcases gap7 x t hx rfl ht0 with ⟨S, hS, hlim⟩
  refine ⟨S, ?_, ?_⟩
  · intro N
    simpa only [ht2] using hS N
  · simpa only [positiveClosedForm, ht2] using hlim

theorem gap9 (x : ℝ) (hx : 0 < x) :
    ∃ (S : ℕ → ℝ) (L : ℝ),
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop (𝓝 L) ∧
      (∑' n : ℕ, seriesTerm x n) = L := by
  rcases gap8 x hx with ⟨S, hS, hlim⟩
  let t := Real.sqrt x
  have ht0 : t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have ht2 : t ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hsumm : Summable (seriesTerm x) := by
    simpa only [ht2] using seriesTerm_summable_sq t ht0
  have hp : Tendsto (partialSeries x) atTop (𝓝 (positiveClosedForm x)) :=
    hlim.congr' (Filter.Eventually.of_forall fun N => hS N)
  refine ⟨S, positiveClosedForm x, hS, hlim, ?_⟩
  exact tsum_eq_of_partialSeries_tendsto x (positiveClosedForm x) hsumm hp

theorem gap10 (x : ℝ) (hx : 0 < x) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop (𝓝 (positiveClosedForm x)) := by
  exact gap8 x hx

theorem gap11 (x : ℝ) (hx : 0 < x) :
    (∑' n : ℕ, seriesTerm x n) = positiveClosedForm x := by
  rcases gap8 x hx with ⟨S, hS, hlim⟩
  let t := Real.sqrt x
  have ht0 : t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have ht2 : t ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hsumm : Summable (seriesTerm x) := by
    simpa only [ht2] using seriesTerm_summable_sq t ht0
  have hp : Tendsto (partialSeries x) atTop (𝓝 (positiveClosedForm x)) :=
    hlim.congr' (Filter.Eventually.of_forall fun N => hS N)
  exact tsum_eq_of_partialSeries_tendsto x (positiveClosedForm x) hsumm hp

theorem gap12 (x y : ℝ) (hx : x < 0) (hy : y = Real.sqrt |x|) :
    x = -(y ^ 2) := by
  subst y
  have habs : |x| = -x := abs_of_neg hx
  have hsqrt : (Real.sqrt |x|) ^ 2 = |x| := Real.sq_sqrt (abs_nonneg x)
  nlinarith

theorem gap13 (x y : ℝ) (hx : x < 0) (hy : y = Real.sqrt |x|) :
    ∃ S : ℕ → ℝ,
      (∀ N : ℕ, S N = partialSeries x N) ∧
      ∀ N : ℕ,
        S N =
          ∑ n ∈ Finset.range (N + 1),
            (n : ℝ) ^ 2 * (-1 : ℝ) ^ n * y ^ (2 * n) /
              ((2 * n + 1).factorial : ℝ) := by
  refine ⟨fun N => partialSeries x N, fun N => rfl, ?_⟩
  intro N
  have hx' : x = -(y ^ 2) := gap12 x y hx hy
  simp only [partialSeries]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [seriesTerm, hx']
  rw [neg_pow, pow_mul]
  ring

theorem gap14 (x y : ℝ) (hx : x < 0) (hy : y = Real.sqrt |x|) (hy0 : y ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N : ℕ, S N = partialSeries x N) ∧
      ∀ N : ℕ,
        S N =
          alternatingOddPartial y N / (4 * y) +
            (∑ n ∈ Finset.range (N + 1),
              (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
                ((2 * n + 1).factorial : ℝ)) / (4 * y) := by
  rcases gap13 x y hx hy with ⟨S, hS, hseries⟩
  refine ⟨S, hS, ?_⟩
  intro N
  rw [hseries N]
  simp only [alternatingOddPartial]
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  field_simp
  ring

theorem gap15 (x y : ℝ) (hx : x < 0) (hy : y = Real.sqrt |x|) (hy0 : y ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto
        (fun N =>
          S N - (alternatingFactoredOddPartial y N / (4 * y) + Real.sin y / (4 * y)))
        atTop (𝓝 0) := by
  rcases gap14 x y hx hy hy0 with ⟨S, hS, hdecomp⟩
  refine ⟨S, hS, ?_⟩
  have hconst :
      Tendsto (fun _ : ℕ => Real.sin y) atTop (𝓝 (Real.sin y)) :=
    tendsto_const_nhds
  have hzero :
      Tendsto
        (fun N =>
          (∑ n ∈ Finset.range (N + 1),
            (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
              ((2 * n + 1).factorial : ℝ)) - Real.sin y)
        atTop (𝓝 0) := by
    simpa using (sinOddPartial_tendsto y).sub hconst
  have hscaled :
      Tendsto
        (fun N => (1 / (4 * y)) *
          ((∑ n ∈ Finset.range (N + 1),
            (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
              ((2 * n + 1).factorial : ℝ)) - Real.sin y))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hzero :
      Tendsto
        (fun N => (1 / (4 * y)) *
          ((∑ n ∈ Finset.range (N + 1),
            (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
              ((2 * n + 1).factorial : ℝ)) - Real.sin y))
        atTop (𝓝 ((1 / (4 * y)) * 0)))
  refine hscaled.congr' (Filter.Eventually.of_forall ?_)
  intro N
  change
    1 / (4 * y) *
        ((∑ n ∈ Finset.range (N + 1),
          (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
            ((2 * n + 1).factorial : ℝ)) - Real.sin y) =
      S N -
        (alternatingFactoredOddPartial y N / (4 * y) + Real.sin y / (4 * y))
  rw [hdecomp N, alternatingOddPartial_eq_factored]
  ring

theorem gap16 (x y : ℝ) (hx : x < 0) (hy : y = Real.sqrt |x|) (hy0 : y ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto
        (fun N =>
          S N -
            ((y ^ 2 * alternatingSinhPartial y N - y * cosinePartial y N) / (4 * y) +
              Real.sin y / (4 * y)))
        atTop (𝓝 0) := by
  rcases gap15 x y hx hy hy0 with ⟨S, hS, hlim⟩
  refine ⟨S, hS, ?_⟩
  refine hlim.congr' (Filter.Eventually.of_forall ?_)
  intro N
  rw [alternatingFactoredOddPartial_eq_shifted]

theorem gap17 (x y : ℝ) (hx : x < 0) (hy : y = Real.sqrt |x|) (hy0 : y ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop
        (𝓝 ((-y ^ 2 * Real.sin y - y * Real.cos y) / (4 * y) +
          Real.sin y / (4 * y))) := by
  rcases gap16 x y hx hy hy0 with ⟨S, hS, herr⟩
  refine ⟨S, hS, ?_⟩
  have hnum :
      Tendsto
        (fun N => y ^ 2 * alternatingSinhPartial y N - y * cosinePartial y N)
        atTop (𝓝 (y ^ 2 * (-Real.sin y) - y * Real.cos y)) :=
    (tendsto_const_nhds.mul (alternatingSinhPartial_tendsto y)).sub
      (tendsto_const_nhds.mul (cosinePartial_tendsto y))
  have hscaled :
      Tendsto
        (fun N => (1 / (4 * y)) *
          (y ^ 2 * alternatingSinhPartial y N - y * cosinePartial y N))
        atTop
        (𝓝 ((1 / (4 * y)) *
          (y ^ 2 * (-Real.sin y) - y * Real.cos y))) :=
    tendsto_const_nhds.mul hnum
  have happ := hscaled.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.sin y / (4 * y)) atTop
      (𝓝 (Real.sin y / (4 * y))))
  have happrox :
      Tendsto
        (fun N =>
          (y ^ 2 * alternatingSinhPartial y N - y * cosinePartial y N) / (4 * y) +
            Real.sin y / (4 * y))
        atTop
        (𝓝 ((-y ^ 2 * Real.sin y - y * Real.cos y) / (4 * y) +
          Real.sin y / (4 * y))) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_neg, neg_mul] using happ
  have htotal := herr.add happrox
  simpa only [sub_add_cancel, zero_add] using htotal

theorem gap18 (x y : ℝ) (hx : x < 0) (hy : y = Real.sqrt |x|) (hy0 : y ≠ 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop
        (𝓝 ((1 / 4 : ℝ) * (((-y ^ 2 + 1) / y) * Real.sin y - Real.cos y))) := by
  rcases gap17 x y hx hy hy0 with ⟨S, hS, hlim⟩
  refine ⟨S, hS, ?_⟩
  have hform :
      (-y ^ 2 * Real.sin y - y * Real.cos y) / (4 * y) +
          Real.sin y / (4 * y) =
        (1 / 4 : ℝ) * (((-y ^ 2 + 1) / y) * Real.sin y - Real.cos y) := by
    field_simp [hy0]
    ring
  simpa only [hform] using hlim

theorem gap19 (x : ℝ) (hx : x < 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop (𝓝 (negativeClosedForm x)) := by
  let y := Real.sqrt |x|
  have hy : y = Real.sqrt |x| := rfl
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    simpa [abs_of_neg hx] using neg_pos.mpr hx
  have hxy : x = -(y ^ 2) := gap12 x y hx hy
  rcases gap18 x y hx hy hy0 with ⟨S, hS, hlim⟩
  refine ⟨S, hS, ?_⟩
  have hform :
      (1 / 4 : ℝ) * (((-y ^ 2 + 1) / y) * Real.sin y - Real.cos y) =
        negativeClosedForm x := by
    unfold negativeClosedForm
    rw [← hy, hxy]
  simpa only [hform] using hlim

theorem gap20 (x : ℝ) (hx : x < 0) :
    ∃ (S : ℕ → ℝ) (L : ℝ),
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop (𝓝 L) ∧
      (∑' n : ℕ, seriesTerm x n) = L := by
  rcases gap19 x hx with ⟨S, hS, hlim⟩
  let y := Real.sqrt |x|
  have hy : y = Real.sqrt |x| := rfl
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    simpa [abs_of_neg hx] using neg_pos.mpr hx
  have hxy : x = -(y ^ 2) := gap12 x y hx hy
  have hsumm : Summable (seriesTerm x) := by
    rw [hxy]
    exact seriesTerm_summable_neg_sq y hy0
  have hp : Tendsto (partialSeries x) atTop (𝓝 (negativeClosedForm x)) :=
    hlim.congr' (Filter.Eventually.of_forall fun N => hS N)
  refine ⟨S, negativeClosedForm x, hS, hlim, ?_⟩
  exact tsum_eq_of_partialSeries_tendsto x (negativeClosedForm x) hsumm hp

theorem gap21 (x : ℝ) (hx : x < 0) :
    ∃ S : ℕ → ℝ,
      (∀ N, S N = partialSeries x N) ∧
      Tendsto S atTop (𝓝 (negativeClosedForm x)) := by
  exact gap19 x hx

theorem gap22 (x : ℝ) (hx : x < 0) :
    (∑' n : ℕ, seriesTerm x n) = negativeClosedForm x := by
  rcases gap19 x hx with ⟨S, hS, hlim⟩
  let y := Real.sqrt |x|
  have hy : y = Real.sqrt |x| := rfl
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    simpa [abs_of_neg hx] using neg_pos.mpr hx
  have hxy : x = -(y ^ 2) := gap12 x y hx hy
  have hsumm : Summable (seriesTerm x) := by
    rw [hxy]
    exact seriesTerm_summable_neg_sq y hy0
  have hp : Tendsto (partialSeries x) atTop (𝓝 (negativeClosedForm x)) :=
    hlim.congr' (Filter.Eventually.of_forall fun N => hS N)
  exact tsum_eq_of_partialSeries_tendsto x (negativeClosedForm x) hsumm hp

theorem gap23 (x : ℝ) :
    (∑' n : ℕ, seriesTerm x n) =
      if x = 0 then 0
      else if 0 < x then positiveClosedForm x
      else negativeClosedForm x := by
  by_cases hx0 : x = 0
  · simp [hx0, gap1]
  by_cases hxpos : 0 < x
  · simp [hx0, hxpos, gap11 x hxpos]
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
  simp [hx0, hxpos, gap22 x hxneg]

end

end ProofGap.Exercise3005
