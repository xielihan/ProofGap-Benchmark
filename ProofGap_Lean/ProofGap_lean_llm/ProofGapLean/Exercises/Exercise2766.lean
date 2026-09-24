import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2766

noncomputable section

open scoped BigOperators Interval

def riemannSum (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * f (x + i / n)

def limitFunction (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in x..x + 1, f t

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |u n x - F x| < ε

theorem gap1 :
    ∀ (f : ℝ → ℝ) (x : ℝ), limitFunction f x = ∫ t in x..x + 1, f t := by
  intro f x
  rfl

theorem gap2 :
    ∀ (f : ℝ → ℝ) (x : ℝ) (n : ℕ), Continuous f → 0 < n →
      (∫ t in x..x + 1, f t) =
        ∑ i ∈ Finset.range n,
          ∫ t in (x + i / n)..(x + (i + 1) / n), f t := by
  intro f x n hf hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpartial : ∀ k : ℕ, k ≤ n →
      (∑ i ∈ Finset.range k,
        ∫ t in (x + (i : ℝ) / (n : ℝ))..(x + ((i : ℝ) + 1) / (n : ℝ)), f t) =
        ∫ t in x..(x + (k : ℝ) / (n : ℝ)), f t := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp
    | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hk)]
        simpa only [Nat.cast_succ] using
          (intervalIntegral.integral_add_adjacent_intervals
            (hf.intervalIntegrable x (x + (k : ℝ) / (n : ℝ)))
            (hf.intervalIntegrable (x + (k : ℝ) / (n : ℝ))
              (x + ((k : ℝ) + 1) / (n : ℝ))))
  have h := (hpartial n le_rfl).symm
  simpa [div_self hn0] using h

theorem gap3 :
    ∀ (f : ℝ → ℝ) (x : ℝ) (n : ℕ), 0 < n → Continuous f →
      ∃ θ : ℕ → ℝ, (∀ i < n, θ i ∈ Set.Icc (0 : ℝ) 1) ∧
        (∫ t in x..x + 1, f t) =
          ∑ i ∈ Finset.range n,
            (1 / (n : ℝ)) * f (x + i / n + θ i / n) := by
  intro f x n hn hf
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hlocal : ∀ i : ℕ, ∃ θ : ℝ,
      θ ∈ Set.Icc (0 : ℝ) 1 ∧
        (∫ t in (x + (i : ℝ) / (n : ℝ))..
          (x + ((i : ℝ) + 1) / (n : ℝ)), f t) =
          (1 / (n : ℝ)) *
            f (x + (i : ℝ) / (n : ℝ) + θ / (n : ℝ)) := by
    intro i
    let l : ℝ := x + (i : ℝ) / (n : ℝ)
    let r : ℝ := x + ((i : ℝ) + 1) / (n : ℝ)
    have hwidth : r - l = 1 / (n : ℝ) := by
      dsimp [l, r]
      ring
    have hlr : l < r := by
      have hpos : 0 < r - l := by
        rw [hwidth]
        exact one_div_pos.mpr hnR
      exact sub_pos.mp hpos
    let A : ℝ → ℝ := fun z => ∫ t in l..z, f t
    have hAderiv : ∀ z : ℝ, HasDerivAt A (f z) z := by
      intro z
      dsimp [A]
      exact intervalIntegral.integral_hasDerivAt_right
        (hf.intervalIntegrable l z)
        hf.stronglyMeasurable.stronglyMeasurableAtFilter
        hf.continuousAt
    have hAcontinuous : Continuous A := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (hAderiv z).continuousAt
    obtain ⟨c, hc, hcslope⟩ :=
      exists_hasDerivAt_eq_slope A f hlr hAcontinuous.continuousOn
        (fun z _hz => hAderiv z)
    have hslope' : f c = (∫ t in l..r, f t) / (r - l) := by
      simpa [A] using hcslope
    have hden : r - l ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlr)
    have hint' : (∫ t in l..r, f t) = (r - l) * f c := by
      rw [hslope']
      field_simp [hden]
    refine ⟨(n : ℝ) * (c - l), ?_, ?_⟩
    · constructor
      · exact mul_nonneg hnR.le (sub_nonneg.mpr hc.1.le)
      · have hcsub : c - l < r - l := sub_lt_sub_right hc.2 l
        rw [hwidth] at hcsub
        have hscaled : (n : ℝ) * (c - l) < 1 := by
          calc
            (n : ℝ) * (c - l) < (n : ℝ) * (1 / (n : ℝ)) :=
              mul_lt_mul_of_pos_left hcsub hnR
            _ = 1 := by simp [hn0]
        exact hscaled.le
    · have hc_repr : l + ((n : ℝ) * (c - l)) / (n : ℝ) = c := by
        field_simp [hn0]
        ring
      change (∫ t in l..r, f t) =
        (1 / (n : ℝ)) * f (l + ((n : ℝ) * (c - l)) / (n : ℝ))
      calc
        (∫ t in l..r, f t) = (r - l) * f c := hint'
        _ = (1 / (n : ℝ)) *
            f (l + ((n : ℝ) * (c - l)) / (n : ℝ)) := by
          rw [hwidth, hc_repr]
  choose θ hθ using hlocal
  refine ⟨θ, ?_, ?_⟩
  · intro i hi
    exact (hθ i).1
  · rw [gap2 f x n hf hn]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hθ i).2

theorem gap4 :
    ∀ (f : ℝ → ℝ) (x : ℝ) (n : ℕ), 0 < n → Continuous f →
      ∃ θ : ℕ → ℝ, (∀ i < n, θ i ∈ Set.Icc (0 : ℝ) 1) ∧
        limitFunction f x =
          ∑ i ∈ Finset.range n,
            (1 / (n : ℝ)) * f (x + i / n + θ i / n) := by
  intro f x n hn hf
  simpa [limitFunction] using gap3 f x n hn hf

theorem gap5 :
    ∀ (f : ℝ → ℝ) (a b : ℝ), Continuous f →
      UniformContinuousOn f (Set.Icc a (b + 1)) := by
  intro f a b hf
  exact IsCompact.uniformContinuousOn_of_continuous isCompact_Icc hf.continuousOn

theorem gap6 :
    ∀ (f : ℝ → ℝ) (a b : ℝ),
      UniformContinuousOn f (Set.Icc a (b + 1)) →
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x' ∈ Set.Icc a (b + 1), ∀ x'' ∈ Set.Icc a (b + 1),
            |x' - x''| < δ → |f x' - f x''| < ε := by
  intro f a b huc ε hε
  simpa only [Real.dist_eq] using
    (Metric.uniformContinuousOn_iff.mp huc ε hε)

theorem gap7 :
    ∀ (n i : ℕ) (x θ : ℝ), 0 < n → θ ∈ Set.Ico (0 : ℝ) 1 →
      |x + i / n + θ / n - (x + i / n)| < 1 / (n : ℝ) := by
  intro n i x θ hn hθ
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have heq :
      x + (i : ℝ) / (n : ℝ) + θ / (n : ℝ) -
          (x + (i : ℝ) / (n : ℝ)) = θ / (n : ℝ) := by
    ring
  rw [heq, abs_of_nonneg (div_nonneg hθ.1 hnR.le)]
  exact (div_lt_div_iff_of_pos_right hnR).2 hθ.2

theorem gap8 :
    ∀ N n : ℕ, 0 < N → N < n → 1 / (n : ℝ) < 1 / (N : ℝ) := by
  intro N n hN hNn
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_trans hN hNn)
  apply (div_lt_div_iff₀ hnR hNR).2
  norm_num
  exact_mod_cast hNn

theorem gap9 :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hrec : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδ
  have hNR : (0 : ℝ) < (N : ℝ) := lt_trans hrec hN
  have hNnat : 0 < N := by exact_mod_cast hNR
  refine ⟨N, hNnat, ?_⟩
  apply (div_lt_iff₀ hNR).2
  have hmul := (div_lt_iff₀ hδ).1 hN
  simpa [mul_comm] using hmul

theorem gap10 :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        |θ / n| < δ := by
  intro δ hδ
  obtain ⟨N, hNpos, hNδ⟩ := gap9 δ hδ
  refine ⟨N, ?_⟩
  intro n hNn θ hθ
  have hn : 0 < n := lt_trans hNpos hNn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (div_nonneg hθ.1 hnR.le)]
  calc
    θ / (n : ℝ) ≤ 1 / (n : ℝ) :=
      (div_le_div_iff_of_pos_right hnR).2 hθ.2
    _ < 1 / (N : ℝ) := gap8 N n hNpos hNn
    _ < δ := hNδ

theorem gap11 :
    ∀ (a b x : ℝ) (n i : ℕ), x ∈ Set.Icc a b → 0 < n → i < n →
      x + i / n ∈ Set.Icc a (b + 1) := by
  intro a b x n i hx hn hi
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hiR : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
  have hfrac0 : 0 ≤ (i : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg i) hnR.le
  have hfrac1 : (i : ℝ) / (n : ℝ) < 1 :=
    (div_lt_one hnR).2 hiR
  constructor <;> linarith [hx.1, hx.2]

theorem gap12 :
    ∀ (a b x : ℝ) (n i : ℕ) (θ : ℝ), x ∈ Set.Icc a b →
      0 < n → i < n → θ ∈ Set.Icc (0 : ℝ) 1 →
        x + i / n + θ / n ∈ Set.Icc a (b + 1) := by
  intro a b x n i θ hx hn hi hθ
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hi1 : (i : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hisum : (i : ℝ) + θ ≤ (n : ℝ) := by
    linarith [hi1, hθ.2]
  have hq0 : 0 ≤ (i : ℝ) / (n : ℝ) + θ / (n : ℝ) := by
    exact add_nonneg
      (div_nonneg (Nat.cast_nonneg i) hnR.le)
      (div_nonneg hθ.1 hnR.le)
  have hq1 : (i : ℝ) / (n : ℝ) + θ / (n : ℝ) ≤ 1 := by
    rw [← add_div]
    exact (div_le_one hnR).2 hisum
  constructor <;> linarith [hx.1, hx.2]

theorem gap13 :
    ∀ (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (θ : ℕ → ℝ),
      0 < n →
      limitFunction f x =
        ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * f (x + i / n + θ i / n) →
      |limitFunction f x - riemannSum n f x| ≤
        ∑ i ∈ Finset.range n,
          (1 / (n : ℝ)) * |f (x + i / n + θ i / n) - f (x + i / n)| := by
  intro f x n θ hn hrep
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 ≤ 1 / (n : ℝ) := (one_div_pos.mpr hnR).le
  rw [hrep]
  unfold riemannSum
  rw [← Finset.sum_sub_distrib]
  let g : ℕ → ℝ := fun i =>
    (1 / (n : ℝ)) * f (x + (i : ℝ) / (n : ℝ) + θ i / (n : ℝ)) -
      (1 / (n : ℝ)) * f (x + (i : ℝ) / (n : ℝ))
  change |∑ i ∈ Finset.range n, g i| ≤ _
  calc
    |∑ i ∈ Finset.range n, g i| ≤
        ∑ i ∈ Finset.range n, |g i| :=
      Finset.abs_sum_le_sum_abs (s := Finset.range n) (f := g)
    _ = ∑ i ∈ Finset.range n, (1 / (n : ℝ)) *
          |f (x + (i : ℝ) / (n : ℝ) + θ i / (n : ℝ)) -
            f (x + (i : ℝ) / (n : ℝ))| := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [g]
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]

theorem gap14 :
    ∀ (n : ℕ) (ε : ℝ) (h : ℕ → ℝ), 0 < n → 0 < ε →
      (∀ i < n, h i < ε) →
        (∑ i ∈ Finset.range n, (1 / (n : ℝ)) * h i) <
          ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * ε := by
  intro n ε h hn hε hlt
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  apply Finset.sum_lt_sum
  · intro i hi
    exact mul_le_mul_of_nonneg_left
      (le_of_lt (hlt i (Finset.mem_range.mp hi))) hw.le
  · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
    exact mul_lt_mul_of_pos_left (hlt 0 hn) hw

theorem gap15 :
    ∀ (n : ℕ) (ε : ℝ), 0 < n →
      (∑ _i ∈ Finset.range n, (1 / (n : ℝ)) * ε) = ε := by
  intro n ε hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [div_eq_mul_inv, nsmul_eq_mul, mul_assoc, hn0]

theorem gap16 :
    ∀ (f : ℝ → ℝ) (a b ε : ℝ), Continuous f → 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ Set.Icc a b,
        |limitFunction f x - riemannSum n f x| < ε := by
  intro f a b ε hf hε
  obtain ⟨δ, hδ, hmod⟩ :=
    gap6 f a b (gap5 f a b hf) ε hε
  obtain ⟨N, hN⟩ := gap10 δ hδ
  refine ⟨N, ?_⟩
  intro n hNn x hx
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hNn
  obtain ⟨θ, hθ, hrep⟩ := gap4 f x n hn hf
  have hbound := gap13 f x n θ hn hrep
  have hterm : ∀ i < n,
      |f (x + (i : ℝ) / (n : ℝ) + θ i / (n : ℝ)) -
        f (x + (i : ℝ) / (n : ℝ))| < ε := by
    intro i hi
    have hshift := gap12 a b x n i (θ i) hx hn hi (hθ i hi)
    have hbase := gap11 a b x n i hx hn hi
    have hd :
        |x + (i : ℝ) / (n : ℝ) + θ i / (n : ℝ) -
          (x + (i : ℝ) / (n : ℝ))| < δ := by
      have ht := hN n hNn (θ i) (hθ i hi)
      convert ht using 1 <;> ring
    exact hmod _ hshift _ hbase hd
  calc
    |limitFunction f x - riemannSum n f x| ≤
        ∑ i ∈ Finset.range n, (1 / (n : ℝ)) *
          |f (x + (i : ℝ) / (n : ℝ) + θ i / (n : ℝ)) -
            f (x + (i : ℝ) / (n : ℝ))| := hbound
    _ < ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * ε :=
      gap14 n ε (fun i =>
        |f (x + (i : ℝ) / (n : ℝ) + θ i / (n : ℝ)) -
          f (x + (i : ℝ) / (n : ℝ))|) hn hε hterm
    _ = ε := gap15 n ε hn

theorem gap17 :
    ∀ (f : ℝ → ℝ) (a b : ℝ), Continuous f →
      UniformlyConvergesOn (fun n x => riemannSum n f x)
        (limitFunction f) (Set.Icc a b) := by
  intro f a b hf
  intro ε hε
  obtain ⟨N, hN⟩ := gap16 f a b ε hf hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa only [abs_sub_comm] using hN n hn x hx

theorem gap18 :
    ∀ (f : ℝ → ℝ) (a b : ℝ), Continuous f →
      ∃ F : ℝ → ℝ,
        (∀ x : ℝ, F x = ∫ t in x..x + 1, f t) ∧
          UniformlyConvergesOn (fun n x => riemannSum n f x) F (Set.Icc a b) := by
  intro f a b hf
  refine ⟨limitFunction f, ?_, gap17 f a b hf⟩
  intro x
  exact gap1 f x

end

end ProofGap.Exercise2766
