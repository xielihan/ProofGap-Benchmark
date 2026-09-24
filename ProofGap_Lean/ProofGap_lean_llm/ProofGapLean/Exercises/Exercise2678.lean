import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2678

noncomputable section

open Filter

def term (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ n * Real.sin x ^ (2 * n)) / n

def rootValue (x : ℝ) : ℝ :=
  2 * Real.sin x ^ 2

def rootFactor (n : ℕ) : ℝ :=
  Real.rpow n (1 / n)

def ConditionallySummable (x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1)) ∧
    ¬ ProofGap.SeriesConverges (fun n : ℕ => |term x (n + 1)|)

private theorem rootValue_nonneg2678 (x : ℝ) : 0 ≤ rootValue x := by
  unfold rootValue
  positivity

private theorem term_eq_rootValue2678 (x : ℝ) (n : ℕ) :
    term x n = (-1 : ℝ) ^ (n - 1) * rootValue x ^ n / n := by
  unfold term rootValue
  rw [mul_pow, pow_mul]

private theorem abs_term_eq_rootValue2678 (x : ℝ) (n : ℕ) :
    |term x n| = rootValue x ^ n / n := by
  rw [term_eq_rootValue2678]
  have hr := rootValue_nonneg2678 x
  simp [abs_div, abs_mul, abs_pow, abs_of_nonneg hr]

private theorem IccZeroEqRangeSucc2678 (n : ℕ) :
    Finset.Icc 0 n = Finset.range (n + 1) := by
  ext k
  simp

private theorem seriesConvergesIffPrefix2678 (f : ℕ → ℝ) :
    ProofGap.SeriesConverges f ↔
      ∃ s : ℝ, Tendsto (fun n => (Finset.range n).sum f) atTop (nhds s) := by
  simp only [ProofGap.SeriesConverges, Summable]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have hsrect : Tendsto
        (fun x : ℕ × ℕ => (Finset.Icc x.1 x.2).sum f)
        (atBot ×ˢ atTop) (nhds s) := by
      simpa [HasSum, SummationFilter.conditional] using hs
    have hzero : Tendsto (fun _ : ℕ => (0 : ℕ)) atTop atBot := by
      refine tendsto_atBot.2 ?_
      intro b
      exact Eventually.of_forall (fun _ => Nat.zero_le b)
    have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop (b + 1)] with n hn
      omega
    have hrect := hsrect.comp (hzero.prodMk hpred)
    apply hrect.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Function.comp_apply, IccZeroEqRangeSucc2678,
      Nat.sub_add_cancel hn]
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have hsnd : Tendsto (fun x : ℕ × ℕ => x.2)
        (atBot ×ˢ atTop) atTop := tendsto_snd
    have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hprefix := hs.comp (hsucc.comp hsnd)
    have hfst : Tendsto (fun x : ℕ × ℕ => x.1)
        (atBot ×ˢ atTop) atBot := tendsto_fst
    have hle : ∀ᶠ x : ℕ × ℕ in atBot ×ˢ atTop, x.1 ≤ 0 :=
      hfst.eventually (eventually_le_atBot 0)
    have hzero : ∀ᶠ x : ℕ × ℕ in atBot ×ˢ atTop, x.1 = 0 := by
      filter_upwards [hle] with x hx
      omega
    have hrect : Tendsto
        (fun x : ℕ × ℕ => (Finset.Icc x.1 x.2).sum f)
        (atBot ×ˢ atTop) (nhds s) := by
      apply hprefix.congr'
      filter_upwards [hzero] with x hx
      simpa only [Function.comp_apply, hx, IccZeroEqRangeSucc2678]
    simpa [HasSum, SummationFilter.conditional] using hrect

theorem gap1 :
    ∀ x : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.rpow |term x n| (1 / n) = rootValue x / rootFactor n := by
  intro x n hn
  rw [abs_term_eq_rootValue2678]
  unfold rootFactor
  have hn0 : n ≠ 0 := by omega
  have hr := rootValue_nonneg2678 x
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  change (rootValue x ^ n / (n : ℝ)) ^ (1 / (n : ℝ)) =
    rootValue x / ((n : ℝ) ^ (1 / (n : ℝ)))
  rw [Real.div_rpow (pow_nonneg hr n) hnnonneg (1 / (n : ℝ))]
  rw [show (1 / (n : ℝ)) = ((n : ℝ)⁻¹) by simp [one_div]]
  rw [Real.pow_rpow_inv_natCast hr hn0]

theorem gap2 :
    ∀ x : ℝ,
      Tendsto (fun n : ℕ => rootValue x / rootFactor (n + 1))
        atTop (nhds (rootValue x)) := by
  intro x
  have hshift : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto
      (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa using
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hshift)
  have hroot : Tendsto (fun n : ℕ => rootFactor (n + 1))
      atTop (nhds 1) := by
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp hratio
    convert hexp using 1
    · funext n
      simp only [Function.comp_apply]
      unfold rootFactor
      have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      change (((n + 1 : ℕ) : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ))) = _
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    · rw [Real.exp_zero]
  simpa using (tendsto_const_nhds.div hroot one_ne_zero)

theorem gap3 :
    ∀ x : ℝ,
      Tendsto (fun n : ℕ => Real.rpow |term x (n + 1)| (1 / (n + 1 : ℝ)))
        atTop (nhds (rootValue x)) := by
  intro x
  apply (gap2 x).congr'
  filter_upwards with n
  simpa using (gap1 x (n + 1) (by omega)).symm

theorem gap4 :
    ∀ x : ℝ, rootValue x < 1 →
      Summable (fun n : ℕ => |term x (n + 1)|) := by
  intro x hx
  have hr := rootValue_nonneg2678 x
  have hgeo : Summable (fun n : ℕ => rootValue x ^ n) :=
    summable_geometric_of_lt_one hr hx
  have htail : Summable (fun n : ℕ => rootValue x ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 hgeo
  refine htail.of_nonneg_of_le (fun n => abs_nonneg _) ?_
  intro n
  rw [abs_term_eq_rootValue2678]
  have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  have hpow : 0 ≤ rootValue x ^ (n + 1) := pow_nonneg hr _
  have hden1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
  calc
    rootValue x ^ (n + 1) = rootValue x ^ (n + 1) * 1 := by ring
    _ ≤ rootValue x ^ (n + 1) * (n + 1 : ℕ) :=
      mul_le_mul_of_nonneg_left hden1 hpow

theorem gap5 :
    ∀ x : ℝ, rootValue x = 1 →
      ∀ n : ℕ, 1 ≤ n → term x n = (-1 : ℝ) ^ (n - 1) / n := by
  intro x hx n hn
  rw [term_eq_rootValue2678, hx, one_pow, mul_one]

theorem gap6 :
    ∀ x : ℝ, rootValue x = 1 → ConditionallySummable x := by
  intro x hx
  unfold ConditionallySummable
  constructor
  · let f : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
    have hfanti : Antitone f := by
      intro a b hab
      dsimp [f]
      gcongr
    have hfzero : Tendsto f atTop (nhds 0) := by
      convert ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 1)) using 1
    rcases hfanti.tendsto_alternating_series_of_tendsto_zero hfzero with ⟨s, hs⟩
    have hfun : (fun n : ℕ => term x (n + 1)) =
        (fun n : ℕ => (-1 : ℝ) ^ n * f n) := by
      funext n
      rw [gap5 x hx (n + 1) (by omega)]
      simp [f, div_eq_mul_inv]
    rw [hfun]
    exact (seriesConvergesIffPrefix2678 _).2 ⟨s, hs⟩
  · intro habs
    rcases (seriesConvergesIffPrefix2678 _).1 habs with ⟨s, hs⟩
    have hsummable : Summable (fun n : ℕ => |term x (n + 1)|) := by
      refine ⟨s, (hasSum_iff_tendsto_nat_of_nonneg
        (fun n => abs_nonneg (term x (n + 1))) s).2 hs⟩
    have hharmonic : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
      refine hsummable.congr ?_
      intro n
      rw [abs_term_eq_rootValue2678, hx, one_pow]
    apply Real.not_summable_one_div_natCast
    exact (summable_nat_add_iff 1).1 (by
      simpa only [Nat.cast_add, Nat.cast_one] using hharmonic)

theorem gap7 :
    ∀ x : ℝ, 1 < rootValue x → ∀ α : ℝ,
      1 < α → α < rootValue x →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          α ≤ Real.rpow |term x n| (1 / n) := by
  intro x hx α hα hαx
  have hev : ∀ᶠ n : ℕ in atTop,
      α < Real.rpow |term x (n + 1)| (1 / (n + 1 : ℝ)) :=
    (gap3 x).eventually (Ioi_mem_nhds hαx)
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hindex : N ≤ n - 1 := by omega
  have h := hN (n - 1) hindex
  norm_num [Nat.cast_sub hn1] at h
  simpa [Nat.sub_add_cancel hn1] using h.le

theorem gap8 :
    ∀ x : ℝ, 1 < rootValue x → ∀ α : ℝ,
      1 < α → α < rootValue x →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → α ^ n ≤ |term x n| := by
  intro x hx α hα hαx
  rcases gap7 x hx α hα hαx with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hn0 : n ≠ 0 := by omega
  have hroot := hN n hnN
  have hpow : α ^ n ≤
      (Real.rpow |term x n| (1 / (n : ℝ))) ^ n := by
    gcongr
  calc
    α ^ n ≤ (Real.rpow |term x n| (1 / (n : ℝ))) ^ n := hpow
    _ = |term x n| := by
      rw [show (1 / (n : ℝ)) = ((n : ℝ)⁻¹) by simp [one_div]]
      exact Real.rpow_inv_natCast_pow (abs_nonneg _) hn0

theorem gap9 :
    ∀ α : ℝ, 1 < α → ∀ n : ℕ, 1 ≤ n → 1 < α ^ n := by
  intro α hα n hn
  exact one_lt_pow₀ hα (by omega)

theorem gap10 :
    ∀ x : ℝ, 1 < rootValue x →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 < |term x n| := by
  intro x hx
  let α : ℝ := (1 + rootValue x) / 2
  have hα : 1 < α := by dsimp [α]; linarith
  have hαx : α < rootValue x := by dsimp [α]; linarith
  rcases gap8 x hx α hα hαx with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  exact lt_of_lt_of_le (gap9 α hα n hn1) (hN n hnN)

theorem gap11 :
    ∀ x : ℝ, 1 < rootValue x →
      ¬ Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) := by
  intro x hx hlim
  have habs : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa using hlim.abs
  have hev : ∀ᶠ n : ℕ in atTop, |term x (n + 1)| < 1 :=
    habs.eventually (Iio_mem_nhds (by norm_num))
  rcases eventually_atTop.1 hev with ⟨K, hK⟩
  rcases gap10 x hx with ⟨N, hN⟩
  let j := max K N
  have hsmall := hK j (le_max_left K N)
  have hlarge := hN (j + 1) (le_trans (le_max_right K N) (Nat.le_succ j))
  linarith

theorem gap12 :
    ∀ x : ℝ, 1 < rootValue x →
      ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro x hx hs
  exact gap11 x hx hs.tendsto_atTop_zero

end

end ProofGap.Exercise2678
