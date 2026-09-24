import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3098

noncomputable section

open Filter
open scoped Topology

def u (n : ℕ) : ℝ :=
  if n = 0 then 0
  else
    let k := (n + 1) / 2
    if n % 2 = 1 then 1 / Real.sqrt (k + 1) + 1 / ((k : ℝ) + 1)
    else -(1 / Real.sqrt (k + 1))

def a (k : ℕ) : ℝ :=
  u (2 * k - 1) + u (2 * k)

def v (n : ℕ) : ℝ :=
  Real.log (1 + u n)

def b (k : ℕ) : ℝ :=
  v (2 * k - 1) + v (2 * k)

def bClosedForm (k : ℕ) : ℝ :=
  Real.log (1 - 1 / (((k : ℝ) + 1) * Real.sqrt (k + 1)))

-- Statement correction: use the conditional summation filter for convergence in natural order; bare Summable would require absolute convergence.
def SummableFromOne (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => f (k + 1))

private theorem seriesConverges_iff (f : ℕ → ℝ) :
    ProofGap.SeriesConverges f ↔
      ∃ s : ℝ,
        Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 s) := by
  simp only [ProofGap.SeriesConverges, Summable, HasSum,
    SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨s, by simpa [Function.comp_def] using hs⟩
  · exact ⟨s, by simpa [Function.comp_def] using hs⟩

private theorem seriesConverges_of_summable {f : ℕ → ℝ}
    (hf : Summable f) : ProofGap.SeriesConverges f := by
  exact ⟨∑' n, f n,
    hf.hasSum.mono_left (SummationFilter.conditional ℕ).le_atTop⟩

private theorem sum_range_pairs (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i =
      ∑ k ∈ Finset.range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      ring

private theorem tendsto_of_even_odd {f : ℕ → ℝ} {L : ℝ}
    (heven : Tendsto (fun n => f (2 * n)) atTop (𝓝 L))
    (hodd : Tendsto (fun n => f (2 * n + 1)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hNe k (by omega)
  · exact hNo k (by omega)

private theorem u_odd (k : ℕ) :
    u (2 * k + 1) =
      1 / Real.sqrt (k + 2) + 1 / ((k : ℝ) + 2) := by
  have hn : 2 * k + 1 ≠ 0 := by omega
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have hc : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
  simp [u, hn, hmod, hdiv, hc]

private theorem u_even (k : ℕ) :
    u (2 * k + 2) = -(1 / Real.sqrt (k + 2)) := by
  have hn : 2 * k + 2 ≠ 0 := by omega
  have hmod : (2 * k + 2) % 2 = 0 := by omega
  have hdiv : (2 * k + 2 + 1) / 2 = k + 1 := by omega
  simp [u, hn, hmod, hdiv]
  congr 1
  push_cast
  ring

private theorem u_odd_from_one (k : ℕ) (hk : 1 ≤ k) :
    u (2 * k - 1) =
      1 / Real.sqrt (k + 1) + 1 / ((k : ℝ) + 1) := by
  have hn : 2 * k - 1 ≠ 0 := by omega
  have hmod : (2 * k - 1) % 2 = 1 := by omega
  have hdiv : (2 * k - 1 + 1) / 2 = k := by omega
  simp [u, hn, hmod, hdiv]

private theorem u_even_from_one (k : ℕ) (hk : 1 ≤ k) :
    u (2 * k) = -(1 / Real.sqrt (k + 1)) := by
  have hn : 2 * k ≠ 0 := by omega
  have hmod : (2 * k) % 2 = 0 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [u, hn, hmod, hdiv]

private theorem inv_sqrt_shift_tendsto_zero :
    Tendsto (fun k : ℕ => 1 / Real.sqrt (k + 2)) atTop (𝓝 0) := by
  have hn :
      Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hs := Real.tendsto_sqrt_atTop.comp hn
  simpa [one_div, Nat.cast_add] using tendsto_inv_atTop_zero.comp hs

private theorem inv_shift_tendsto_zero :
    Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
  have hn :
      Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  simpa [one_div, Nat.cast_add] using tendsto_inv_atTop_zero.comp hn

private theorem u_tendsto_zero : Tendsto u atTop (𝓝 0) := by
  apply tendsto_of_even_odd
  · apply (tendsto_add_atTop_iff_nat 1).1
    have h := inv_sqrt_shift_tendsto_zero.neg
    simpa [Nat.mul_add, u_even] using h
  · have h := inv_sqrt_shift_tendsto_zero.add inv_shift_tendsto_zero
    convert h using 1
    · funext k
      rw [u_odd]
    · norm_num

private theorem v_tendsto_zero : Tendsto v atTop (𝓝 0) := by
  have hone : Tendsto (fun n : ℕ => 1 + u n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add u_tendsto_zero
  simpa [v, Function.comp_def] using
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hone

theorem gap1 :
    ∃ w : ℕ → ℝ, w = u ∧ ∀ k : ℕ, 1 ≤ k →
      w (2 * k - 1) = 1 / Real.sqrt (k + 1) + 1 / ((k : ℝ) + 1) := by
  refine ⟨u, rfl, ?_⟩
  intro k hk
  exact u_odd_from_one k hk

theorem gap2 :
    ∃ w : ℕ → ℝ, w = u ∧ ∀ k : ℕ, 1 ≤ k →
      w (2 * k) = -(1 / Real.sqrt (k + 1)) := by
  refine ⟨u, rfl, ?_⟩
  intro k hk
  exact u_even_from_one k hk

theorem gap3 :
    ∀ k : ℕ, 1 ≤ k → a k = 1 / ((k : ℝ) + 1) := by
  intro k hk
  unfold a
  rw [u_odd_from_one k hk, u_even_from_one k hk]
  ring

theorem gap4 : ¬SummableFromOne a := by
  intro ha
  rcases (seriesConverges_iff _).mp ha with ⟨s, hs⟩
  have hnonneg : ∀ n : ℕ, 0 ≤ a (n + 1) := by
    intro n
    rw [gap3 (n + 1) (by omega)]
    positivity
  have hsum : HasSum (fun n : ℕ => a (n + 1)) s :=
    (hasSum_iff_tendsto_nat_of_nonneg hnonneg s).2 hs
  have htail :
      Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ))) := by
    apply hsum.summable.congr
    intro n
    rw [gap3 (n + 1) (by omega)]
    congr 1
    push_cast
    ring
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 2).1 (by simpa using htail)

theorem gap5 :
    ∃ w : ℕ → ℝ, w = u ∧ ¬SummableFromOne w := by
  refine ⟨u, rfl, ?_⟩
  intro hu
  rcases (seriesConverges_iff _).mp hu with ⟨s, hs⟩
  have hidx : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have heven := hs.comp hidx
  have hpairs :
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, a (k + 1))
        atTop (𝓝 s) := by
    apply heven.congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [sum_range_pairs]
    apply Finset.sum_congr rfl
    intro k hk
    unfold a
    congr 2 <;> omega
  apply gap4
  exact (seriesConverges_iff _).2 ⟨s, hpairs⟩

theorem gap6 :
    ∀ k : ℕ, 1 ≤ k →
      v (2 * k - 1) =
        Real.log (1 + 1 / Real.sqrt (k + 1) + 1 / ((k : ℝ) + 1)) := by
  intro k hk
  unfold v
  rw [u_odd_from_one k hk]
  congr 1
  ring

theorem gap7 :
    ∀ k : ℕ, 1 ≤ k →
      v (2 * k) = Real.log (1 - 1 / Real.sqrt (k + 1)) := by
  intro k hk
  unfold v
  rw [u_even_from_one k hk]
  congr 1

theorem gap8 :
    ∀ k : ℕ, 1 ≤ k → b k = bClosedForm k := by
  intro k hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (k : ℝ) + 1 := by positivity
  have hspos : 0 < Real.sqrt (k + 1) := Real.sqrt_pos.2 (by positivity)
  have hsone : 1 < Real.sqrt (k + 1) := by
    rw [Real.lt_sqrt (by norm_num)]
    exact_mod_cast (show 1 < k + 1 by omega)
  have hminus : 1 - 1 / Real.sqrt (k + 1) ≠ 0 :=
    ne_of_gt (sub_pos.mpr ((div_lt_one hspos).2 hsone))
  have hplus :
      1 + 1 / Real.sqrt (k + 1) + 1 / ((k : ℝ) + 1) ≠ 0 := by
    positivity
  rw [b, gap6 k hk, gap7 k hk, ← Real.log_mul hplus hminus]
  unfold bClosedForm
  congr 1
  have hnonneg : 0 ≤ (k : ℝ) + 1 := by positivity
  have hs_sq : Real.sqrt (k + 1) ^ 2 = (k : ℝ) + 1 :=
    Real.sq_sqrt hnonneg
  field_simp [hspos.ne']
  nlinarith

private theorem closed_tail_summable :
    Summable (fun n : ℕ => bClosedForm (n + 1)) := by
  let q : ℕ → ℝ :=
    fun n => -(1 / (((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2)))
  have hmajor :
      Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 2 (3 / 2)).2 (by norm_num)
  have hq : Summable q := by
    apply hmajor.neg.congr
    intro n
    have hx : 0 ≤ (n : ℝ) + 2 := by positivity
    have hs_sq : Real.sqrt ((n : ℝ) + 2) ^ 2 = (n : ℝ) + 2 :=
      Real.sq_sqrt hx
    rw [abs_of_nonneg hx, Real.rpow_div_two_eq_sqrt 3 hx]
    dsimp [q]
    have hcub :
        Real.sqrt ((n : ℝ) + 2) ^ 3 =
          ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) := by
      rw [show Real.sqrt ((n : ℝ) + 2) ^ 3 =
        Real.sqrt ((n : ℝ) + 2) ^ 2 * Real.sqrt ((n : ℝ) + 2) by ring,
        hs_sq]
    congr 2
    change Real.rpow (Real.sqrt ((n : ℝ) + 2)) (3 : ℝ) =
      ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2)
    exact (Real.rpow_natCast _ 3).trans hcub
  have hlog := Real.summable_log_one_add_of_summable hq
  apply hlog.congr
  intro n
  unfold bClosedForm
  dsimp [q]
  push_cast
  congr 3 <;> ring

theorem gap9 : SummableFromOne b := by
  apply seriesConverges_of_summable
  apply closed_tail_summable.congr
  intro n
  exact (gap8 (n + 1) (by omega)).symm

theorem gap10 : SummableFromOne v := by
  rcases (seriesConverges_iff _).mp gap9 with ⟨s, hs⟩
  let P : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, v (i + 1)
  have heven : Tendsto (fun n => P (2 * n)) atTop (𝓝 s) := by
    apply hs.congr'
    filter_upwards with n
    unfold P
    rw [sum_range_pairs]
    apply Finset.sum_congr rfl
    intro k hk
    unfold b
    congr 2 <;> omega
  have hvodd : Tendsto (fun n : ℕ => v (2 * n + 1)) atTop (𝓝 0) := by
    apply v_tendsto_zero.comp
    rw [tendsto_atTop]
    intro N
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have hodd : Tendsto (fun n => P (2 * n + 1)) atTop (𝓝 s) := by
    have h :
        Tendsto (fun n => P (2 * n) + v (2 * n + 1)) atTop (𝓝 s) := by
      simpa using heven.add hvodd
    convert h using 1
    funext n
    unfold P
    rw [Finset.sum_range_succ]
  exact (seriesConverges_iff _).2 ⟨s, tendsto_of_even_odd heven hodd⟩

theorem gap11 :
    ∃ w : ℕ → ℝ, w = u ∧
      ¬SummableFromOne w ∧
      SummableFromOne (fun n => Real.log (1 + w n)) := by
  have hu : ¬SummableFromOne u := by
    rcases gap5 with ⟨w, rfl, hw⟩
    exact hw
  exact ⟨u, rfl, hu, gap10⟩

end

end ProofGap.Exercise3098
