import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2796_2

noncomputable section

open Filter
open scoped BigOperators Topology

def IsRational (x : ℝ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = x

def EnumeratesRationalsOnUnit (r : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    r k ∈ Set.Icc (0 : ℝ) 1 ∧ IsRational (r k)) ∧
  (∀ x ∈ Set.Icc (0 : ℝ) 1, IsRational x →
    ∃ m : ℕ, 1 ≤ m ∧ r m = x) ∧
  ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → r i = r j → i = j

def term (r : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  |x - r k| / (3 : ℝ) ^ k

def f (r : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, term r (n + 1) x

def v (r : ℕ → ℝ) (x₀ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (|x - r k| - |x₀ - r k|) / ((3 : ℝ) ^ k * (x - x₀))

def slope (r : ℕ → ℝ) (x₀ x : ℝ) : ℝ :=
  (f r x - f r x₀) / (x - x₀)

def remainder (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, if n + 1 = m then 0 else v r x₀ (n + 1) x

def derivativeValue (r : ℕ → ℝ) (x₀ : ℝ) : ℝ :=
  ∑' n : ℕ, (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1))

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem geometric_summable :
    Summable (fun n : ℕ => 1 / (3 : ℝ) ^ (n + 1)) := by
  have h : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [one_div, inv_pow, pow_succ, mul_comm] using
    h.mul_left (1 / 3 : ℝ)

private theorem term_series_summable (r : ℕ → ℝ)
    (hr : ∀ k : ℕ, 1 ≤ k → r k ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    Summable (fun n : ℕ => term r (n + 1) x) := by
  apply Summable.of_norm_bounded (geometric_summable.mul_left (|x| + 1))
  intro n
  have hrn := hr (n + 1) (by omega)
  have hrabs : |r (n + 1)| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hrn.1]
    exact hrn.2
  have hnum : |x - r (n + 1)| ≤ |x| + 1 := by
    exact (abs_sub x (r (n + 1))).trans (by
      simpa [add_comm] using add_le_add_left hrabs |x|)
  have hpow : 0 < (3 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  rw [Real.norm_eq_abs]
  unfold term
  rw [abs_div, abs_abs, abs_of_pos hpow]
  have hdiv := div_le_div_of_nonneg_right hnum hpow.le
  simpa [div_eq_mul_inv, one_div, mul_assoc] using hdiv

private theorem sign_term_norm_le (x : ℝ) (k : ℕ) :
    ‖(1 / (3 : ℝ) ^ k) * Real.sign x‖ ≤ 1 / (3 : ℝ) ^ k := by
  have ha : 0 ≤ 1 / (3 : ℝ) ^ k := by positivity
  have hs : |Real.sign x| ≤ (1 : ℝ) := by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
  simpa using mul_le_mul_of_nonneg_left hs ha

private theorem sign_series_summable (r : ℕ → ℝ) (x₀ : ℝ) :
    Summable (fun n : ℕ =>
      (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1))) := by
  exact Summable.of_norm_bounded geometric_summable
    (fun n => sign_term_norm_le (x₀ - r (n + 1)) (n + 1))

private theorem seriesUniformlyConvergesOn_of_hasSumUniformlyOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ)
    (h : HasSumUniformlyOn u (fun x => ∑' n : ℕ, u n x) s) :
    SeriesUniformlyConvergesOn u s (fun x => ∑' n : ℕ, u n x) := by
  have hu := h.tendstoUniformlyOn_finsetRange
  rw [Metric.tendstoUniformlyOn_iff] at hu
  intro ε hε
  rcases eventually_atTop.1 (hu ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hdist := hN (n + 1) (by omega) x hx
  simpa [Real.dist_eq, abs_sub_comm] using hdist

theorem gap1 (r : ℕ → ℝ) (x₀ x : ℝ)
    (henum : EnumeratesRationalsOnUnit r) (hx : x ≠ x₀) :
    slope r x₀ x = ∑' n : ℕ, v r x₀ (n + 1) x := by
  have hsx := term_series_summable r (fun k hk => (henum.1 k hk).1) x
  have hsx₀ := term_series_summable r (fun k hk => (henum.1 k hk).1) x₀
  unfold slope f
  rw [← hsx.tsum_sub hsx₀, ← tsum_div_const]
  apply tsum_congr
  intro n
  unfold term v
  field_simp [hx]
  <;> ring

theorem gap2 (r : ℕ → ℝ) (x₀ x : ℝ) (k : ℕ) :
    abs (|x - r k| - |x₀ - r k|) ≤
      |(x - r k) - (x₀ - r k)| := by
  exact abs_abs_sub_abs_le_abs_sub _ _

theorem gap3 (r : ℕ → ℝ) (x₀ x : ℝ) (k : ℕ) :
    |(x - r k) - (x₀ - r k)| = |x - x₀| := by
  congr 1
  ring

theorem gap4 (r : ℕ → ℝ) (x₀ x : ℝ) (k : ℕ) :
    abs (|x - r k| - |x₀ - r k|) ≤ |x - x₀| := by
  exact (gap2 r x₀ x k).trans_eq (gap3 r x₀ x k)

theorem gap5 (r : ℕ → ℝ) (x₀ x : ℝ) (k : ℕ)
    (hx : x ≠ x₀) :
    |v r x₀ k x| ≤ 1 / (3 : ℝ) ^ k := by
  have hpow : 0 < (3 : ℝ) ^ k := pow_pos (by norm_num) _
  have hdiff : 0 < |x - x₀| := abs_pos.mpr (sub_ne_zero.mpr hx)
  unfold v
  rw [abs_div, abs_mul, abs_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
  calc
    abs (|x - r k| - |x₀ - r k|) /
          ((3 : ℝ) ^ k * |x - x₀|) ≤
        |x - x₀| / ((3 : ℝ) ^ k * |x - x₀|) :=
      div_le_div_of_nonneg_right (gap4 r x₀ x k)
        (mul_nonneg hpow.le hdiff.le)
    _ = 1 / (3 : ℝ) ^ k := by
      field_simp [hpow.ne', hdiff.ne']

theorem gap6 (r : ℕ → ℝ) (x₀ : ℝ) :
    SeriesUniformlyConvergesOn
      (fun n x => v r x₀ (n + 1) x)
      (Set.Icc (0 : ℝ) 1 \ {x₀})
      (fun x => ∑' n : ℕ, v r x₀ (n + 1) x) := by
  apply seriesUniformlyConvergesOn_of_hasSumUniformlyOn
  apply HasSumUniformlyOn.of_norm_le_summable geometric_summable
  intro n x hx
  have hne : x ≠ x₀ := by simpa using hx.2
  rw [Real.norm_eq_abs]
  exact gap5 r x₀ x (n + 1) hne

private theorem v_tendsto_of_ne (r : ℕ → ℝ) (x₀ : ℝ) (k : ℕ)
    (hne : x₀ ≠ r k) :
    Tendsto (v r x₀ k)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds ((1 / (3 : ℝ) ^ k) * Real.sign (x₀ - r k))) := by
  have hsub : HasDerivAt (fun x : ℝ => x - r k) 1 x₀ :=
    (hasDerivAt_id x₀).sub_const (r k)
  have habs : HasDerivAt (fun x : ℝ => |x - r k|)
      (Real.sign (x₀ - r k)) x₀ := by
    rcases (sub_ne_zero.mpr hne).lt_or_gt with hneg | hpos
    · simpa [Real.sign_of_neg hneg] using
        (hasDerivAt_abs_neg hneg).comp x₀ hsub
    · simpa [Real.sign_of_pos hpos] using
        (hasDerivAt_abs_pos hpos).comp x₀ hsub
  have hs := habs.tendsto_slope.div_const ((3 : ℝ) ^ k)
  have hs' : Tendsto
      (fun x => ((|x - r k| - |x₀ - r k|) / (x - x₀)) / (3 : ℝ) ^ k)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds ((1 / (3 : ℝ) ^ k) * Real.sign (x₀ - r k))) := by
    simpa [slope_fun_def_field, div_eq_mul_inv, mul_comm] using hs
  apply (tendsto_congr' ?_).2 hs'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ x₀ := by simpa using hx
  unfold v
  field_simp [hxne]

theorem gap7 (r : ℕ → ℝ) (x₀ : ℝ) (k : ℕ)
    (hirr : ¬ IsRational x₀)
    (hrat : IsRational (r k)) :
    Tendsto (v r x₀ k)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds ((1 / (3 : ℝ) ^ k) * Real.sign (x₀ - r k))) := by
  apply v_tendsto_of_ne
  intro h
  apply hirr
  simpa [h] using hrat

private theorem v_series_tendsto_at_irrational (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r) (hirr : ¬ IsRational x₀) :
    Tendsto (fun x => ∑' n : ℕ, v r x₀ (n + 1) x)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds (derivativeValue r x₀)) := by
  let u : ℕ → ℝ → ℝ := fun n x => v r x₀ (n + 1) x
  let a : ℕ → ℝ := fun n =>
    (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1))
  have hu : HasSumUniformlyOn u (fun x => ∑' n : ℕ, u n x) ({x₀}ᶜ) := by
    apply HasSumUniformlyOn.of_norm_le_summable geometric_summable
    intro n x hx
    have hne : x ≠ x₀ := by simpa using hx
    simpa [u, Real.norm_eq_abs] using gap5 r x₀ x (n + 1) hne
  have hpartial : ∀ n : ℕ,
      Tendsto (fun x => ∑ k ∈ Finset.range n, u k x)
        (nhdsWithin x₀ ({x₀}ᶜ))
        (nhds (∑ k ∈ Finset.range n, a k)) := by
    intro n
    apply tendsto_finset_sum
    intro k hk
    have hrat := (henum.1 (k + 1) (by omega)).2
    simpa [u, a] using gap7 r x₀ (k + 1) hirr hrat
  have huFilter := hu.tendstoUniformlyOn_finsetRange.tendstoUniformlyOnFilter
  have huPunctured := huFilter.mono_right
    (show nhdsWithin x₀ ({x₀}ᶜ) ≤ Filter.principal ({x₀}ᶜ) from inf_le_right)
  have ha : Tendsto (fun n => ∑ k ∈ Finset.range n, a k) atTop
      (nhds (∑' n : ℕ, a n)) := by
    exact (sign_series_summable r x₀).hasSum.tendsto_sum_nat
  have hlim := huPunctured.tendsto_of_eventually_tendsto
    (Filter.Eventually.of_forall hpartial) ha
  simpa [u, a, derivativeValue] using hlim

theorem gap8 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hirr : ¬ IsRational x₀) :
    Tendsto (slope r x₀)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds (derivativeValue r x₀)) := by
  have heq : slope r x₀ =ᶠ[nhdsWithin x₀ ({x₀}ᶜ)]
      (fun x => ∑' n : ℕ, v r x₀ (n + 1) x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact gap1 r x₀ x henum (by simpa using hx)
  exact (tendsto_congr' heq).2
    (v_series_tendsto_at_irrational r x₀ henum hirr)

theorem gap9 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hirr : ¬ IsRational x₀) :
    Tendsto (fun x => ∑' n : ℕ, v r x₀ (n + 1) x)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds (derivativeValue r x₀)) := by
  exact v_series_tendsto_at_irrational r x₀ henum hirr

theorem gap10 (r : ℕ → ℝ) (x₀ : ℝ) :
    (∑' n : ℕ,
      (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1))) =
      derivativeValue r x₀ := by
  rfl

theorem gap11 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hirr : ¬ IsRational x₀) :
    Tendsto (slope r x₀)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds (derivativeValue r x₀)) := by
  exact gap8 r x₀ henum hirr

theorem gap12 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hirr : ¬ IsRational x₀) :
    HasDerivAt (f r) (derivativeValue r x₀) x₀ := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa [slope_fun_def_field, ProofGap.Exercise2796_2.slope] using
    gap11 r x₀ henum hirr

theorem gap13 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hirr : ¬ IsRational x₀) :
    deriv (f r) x₀ = derivativeValue r x₀ := by
  exact (gap12 r x₀ henum hirr).deriv

theorem gap14 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hrat : IsRational x₀) :
    ∃ m : ℕ, 1 ≤ m ∧ x₀ = r m := by
  rcases henum.2.1 x₀ hx₀ hrat with ⟨m, hmpos, hm⟩
  exact ⟨m, hmpos, hm.symm⟩

private theorem v_series_summable (r : ℕ → ℝ) (x₀ x : ℝ)
    (hx : x ≠ x₀) :
    Summable (fun n : ℕ => v r x₀ (n + 1) x) := by
  exact Summable.of_norm_bounded geometric_summable (fun n => by
    rw [Real.norm_eq_abs]
    exact gap5 r x₀ x (n + 1) hx)

theorem gap15 (r : ℕ → ℝ) (x₀ x : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hrat : IsRational x₀)
    (hx : x ≠ x₀) :
    ∃ m : ℕ, 1 ≤ m ∧ x₀ = r m ∧
      slope r x₀ x = v r x₀ m x + remainder r x₀ m x := by
  rcases gap14 r x₀ henum hx₀ hrat with ⟨m, hmpos, hm⟩
  refine ⟨m, hmpos, hm, ?_⟩
  rw [gap1 r x₀ x henum hx]
  have hsplit := (v_series_summable r x₀ x hx).tsum_eq_add_tsum_ite (m - 1)
  rw [hsplit]
  congr 1
  · simpa [Nat.sub_add_cancel hmpos]
  · unfold remainder
    apply tsum_congr
    intro n
    by_cases hnm : n + 1 = m
    · have hn : n = m - 1 := by omega
      simp [hn, Nat.sub_add_cancel hmpos]
    · have hn : n ≠ m - 1 := by
        intro hn
        apply hnm
        omega
      simp [hn, hnm]

theorem gap16 (r : ℕ → ℝ) (x₀ x : ℝ) (m : ℕ)
    (hm : x₀ = r m) (hx : x ≠ x₀) :
    v r x₀ m x =
      (|x - r m| - |x₀ - r m|) /
        ((3 : ℝ) ^ m * (x - x₀)) := by
  rfl

theorem gap17 (r : ℕ → ℝ) (x₀ x : ℝ) (m : ℕ)
    (hm : x₀ = r m) (hx : x ≠ x₀) :
    (|x - r m| - |x₀ - r m|) /
        ((3 : ℝ) ^ m * (x - x₀)) =
      |x - x₀| / ((3 : ℝ) ^ m * (x - x₀)) := by
  rw [← hm]
  simp

theorem gap18 (x₀ x : ℝ) (m : ℕ) (hx : x ≠ x₀) :
    |x - x₀| / ((3 : ℝ) ^ m * (x - x₀)) =
      (1 / (3 : ℝ) ^ m) * Real.sign (x - x₀) := by
  have hsub : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  rcases hsub.lt_or_gt with hneg | hpos
  · rw [abs_of_neg hneg, Real.sign_of_neg hneg]
    field_simp [hsub, pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)]
  · rw [abs_of_pos hpos, Real.sign_of_pos hpos]
    field_simp [hsub, pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)]

theorem gap19 (r : ℕ → ℝ) (x₀ x : ℝ) (m : ℕ)
    (hm : x₀ = r m) (hx : x ≠ x₀) :
    v r x₀ m x =
      (1 / (3 : ℝ) ^ m) * Real.sign (x - x₀) := by
  calc
    v r x₀ m x =
        (|x - r m| - |x₀ - r m|) /
          ((3 : ℝ) ^ m * (x - x₀)) := gap16 r x₀ x m hm hx
    _ = |x - x₀| / ((3 : ℝ) ^ m * (x - x₀)) :=
      gap17 r x₀ x m hm hx
    _ = (1 / (3 : ℝ) ^ m) * Real.sign (x - x₀) := gap18 x₀ x m hx

private theorem remainder_tendsto (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ)
    (henum : EnumeratesRationalsOnUnit r) (hmpos : 1 ≤ m)
    (hm : x₀ = r m) :
    Tendsto (remainder r x₀ m)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds (∑' n : ℕ, if n + 1 = m then 0 else
        (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1)))) := by
  let u : ℕ → ℝ → ℝ := fun n x =>
    if n + 1 = m then 0 else v r x₀ (n + 1) x
  let a : ℕ → ℝ := fun n =>
    if n + 1 = m then 0 else
      (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1))
  have hu : HasSumUniformlyOn u (fun x => ∑' n : ℕ, u n x) ({x₀}ᶜ) := by
    apply HasSumUniformlyOn.of_norm_le_summable geometric_summable
    intro n x hx
    by_cases hnm : n + 1 = m
    · simp [u, hnm]
    · have hne : x ≠ x₀ := by simpa using hx
      simpa [u, hnm, Real.norm_eq_abs] using
        gap5 r x₀ x (n + 1) hne
  have hpartial : ∀ n : ℕ,
      Tendsto (fun x => ∑ k ∈ Finset.range n, u k x)
        (nhdsWithin x₀ ({x₀}ᶜ))
        (nhds (∑ k ∈ Finset.range n, a k)) := by
    intro n
    apply tendsto_finset_sum
    intro k hk
    by_cases hkm : k + 1 = m
    · simp [u, a, hkm]
    · have hne : x₀ ≠ r (k + 1) := by
        intro heq
        have hre : r (k + 1) = r m := heq.symm.trans hm
        have hindex := henum.2.2 (k + 1) m (by omega) hmpos hre
        exact hkm hindex
      simpa [u, a, hkm] using v_tendsto_of_ne r x₀ (k + 1) hne
  have haSummable : Summable a := by
    apply Summable.of_norm_bounded geometric_summable
    intro n
    by_cases hnm : n + 1 = m
    · simp [a, hnm]
    · simpa [a, hnm] using
        sign_term_norm_le (x₀ - r (n + 1)) (n + 1)
  have huFilter := hu.tendstoUniformlyOn_finsetRange.tendstoUniformlyOnFilter
  have huPunctured := huFilter.mono_right
    (show nhdsWithin x₀ ({x₀}ᶜ) ≤ Filter.principal ({x₀}ᶜ) from inf_le_right)
  have ha : Tendsto (fun n => ∑ k ∈ Finset.range n, a k) atTop
      (nhds (∑' n : ℕ, a n)) := haSummable.hasSum.tendsto_sum_nat
  have hlim := huPunctured.tendsto_of_eventually_tendsto
    (Filter.Eventually.of_forall hpartial) ha
  simpa [u, a, remainder] using hlim

theorem gap20 (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ)
    (henum : EnumeratesRationalsOnUnit r) (hmpos : 1 ≤ m)
    (hm : x₀ = r m) :
    ∃ L : ℝ,
      Tendsto (remainder r x₀ m) (nhdsWithin x₀ ({x₀}ᶜ)) (nhds L) := by
  exact ⟨_, remainder_tendsto r x₀ m henum hmpos hm⟩

theorem gap21 (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ) :
    (∑' n : ℕ, if n + 1 = m then 0 else
      (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1))) =
      ∑' n : ℕ, if n + 1 = m then 0 else
        (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1)) := by
  rfl

theorem gap22 (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ)
    (henum : EnumeratesRationalsOnUnit r) (hmpos : 1 ≤ m)
    (hm : x₀ = r m) :
    Tendsto (remainder r x₀ m)
      (nhdsWithin x₀ ({x₀}ᶜ))
      (nhds (∑' n : ℕ, if n + 1 = m then 0 else
        (1 / (3 : ℝ) ^ (n + 1)) * Real.sign (x₀ - r (n + 1)))) := by
  exact remainder_tendsto r x₀ m henum hmpos hm

theorem gap23 (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ) (hm : x₀ = r m) :
    Tendsto (v r x₀ m)
      (nhdsWithin x₀ (Set.Ioi x₀))
      (nhds (1 / (3 : ℝ) ^ m)) := by
  have heq : v r x₀ m =ᶠ[nhdsWithin x₀ (Set.Ioi x₀)]
      (fun _ => 1 / (3 : ℝ) ^ m) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x ≠ x₀ := ne_of_gt hx
    rw [gap19 r x₀ x m hm hne, Real.sign_of_pos (sub_pos.mpr hx), mul_one]
  exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem gap24 (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ) (hm : x₀ = r m) :
    Tendsto (v r x₀ m)
      (nhdsWithin x₀ (Set.Iio x₀))
      (nhds (-(1 / (3 : ℝ) ^ m))) := by
  have heq : v r x₀ m =ᶠ[nhdsWithin x₀ (Set.Iio x₀)]
      (fun _ => -(1 / (3 : ℝ) ^ m)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x ≠ x₀ := ne_of_lt hx
    rw [gap19 r x₀ x m hm hne, Real.sign_of_neg (sub_neg.mpr hx), mul_neg,
      mul_one]
  exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem gap25 (r : ℕ → ℝ) (x₀ : ℝ) (m : ℕ) (hm : x₀ = r m) :
    ¬ ∃ L : ℝ,
      Tendsto (v r x₀ m) (nhdsWithin x₀ ({x₀}ᶜ)) (nhds L) := by
  rintro ⟨L, hL⟩
  have hright := hL.mono_left (nhdsGT_le_nhdsNE x₀)
  have hleft := hL.mono_left (nhdsLT_le_nhdsNE x₀)
  have hEqRight : 1 / (3 : ℝ) ^ m = L :=
    tendsto_nhds_unique (gap23 r x₀ m hm) hright
  have hEqLeft : -(1 / (3 : ℝ) ^ m) = L :=
    tendsto_nhds_unique (gap24 r x₀ m hm) hleft
  have hpos : 0 < 1 / (3 : ℝ) ^ m := by positivity
  linarith

theorem gap26 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hrat : IsRational x₀) :
    ¬ ∃ L : ℝ,
      Tendsto (slope r x₀) (nhdsWithin x₀ ({x₀}ᶜ)) (nhds L) := by
  rintro ⟨L, hSlope⟩
  rcases gap14 r x₀ henum hx₀ hrat with ⟨m, hmpos, hm⟩
  rcases gap20 r x₀ m henum hmpos hm with ⟨R, hRemainder⟩
  apply (gap25 r x₀ m hm)
  refine ⟨L - R, ?_⟩
  have hdiff := hSlope.sub hRemainder
  apply (tendsto_congr' ?_).2 hdiff
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ x₀ := by simpa using hx
  rcases gap15 r x₀ x henum hx₀ hrat hxne with
    ⟨m', hm'pos, hm', hsplit⟩
  have hre : r m' = r m := hm'.symm.trans hm
  have hindex : m' = m := henum.2.2 m' m hm'pos hmpos hre
  subst m'
  linarith

theorem gap27 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hrat : IsRational x₀) :
    ¬ DifferentiableAt ℝ (f r) x₀ := by
  intro hdiff
  apply (gap26 r x₀ henum hx₀ hrat)
  refine ⟨deriv (f r) x₀, ?_⟩
  simpa [slope_fun_def_field, ProofGap.Exercise2796_2.slope] using
    hdiff.hasDerivAt.tendsto_slope

theorem gap28 (r : ℕ → ℝ) (x₀ : ℝ)
    (henum : EnumeratesRationalsOnUnit r)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (¬ IsRational x₀ → DifferentiableAt ℝ (f r) x₀) ∧
    (IsRational x₀ → ¬ DifferentiableAt ℝ (f r) x₀) := by
  constructor
  · intro hirr
    exact (gap12 r x₀ henum hirr).differentiableAt
  · intro hrat
    exact gap27 r x₀ henum hx₀ hrat

end

end ProofGap.Exercise2796_2
