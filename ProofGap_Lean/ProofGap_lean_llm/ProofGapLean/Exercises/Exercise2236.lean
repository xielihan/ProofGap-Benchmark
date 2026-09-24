import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2236

noncomputable section

def denominator (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, f t

def numerator (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, t * f t

def phi (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  numerator f x / denominator f x

def comparison (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * f x / f x

def derivativeForm (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / denominator f x ^ 2) *
    (x * f x * denominator f x - f x * numerator f x)

def positiveForm (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f x / denominator f x ^ 2) *
    ∫ t in (0 : ℝ)..x, (x - t) * f t

private lemma hasDerivAt_denominator (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (denominator f) (f x) x := by
  simpa only [denominator] using
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 x)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt

private lemma hasDerivAt_numerator (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (numerator f) (x * f x) x := by
  simpa only [numerator] using
    intervalIntegral.integral_hasDerivAt_right
      ((continuous_id.mul hf).intervalIntegrable 0 x)
      (continuous_id.mul hf).stronglyMeasurable.stronglyMeasurableAtFilter
      (continuous_id.mul hf).continuousAt

private lemma integral_pos_from_Ioo (g : ℝ → ℝ) (hg : Continuous g)
    (x : ℝ) (hx : 0 < x) (hgp : ∀ t, 0 < t → t < x → 0 < g t) :
    0 < ∫ t in (0 : ℝ)..x, g t := by
  let G : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, g t
  have hmono : StrictMonoOn G (Set.Icc 0 x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 x) ?_ ?_
    · intro y hy
      exact (intervalIntegral.integral_hasDerivAt_right
        (hg.intervalIntegrable 0 y)
        hg.stronglyMeasurable.stronglyMeasurableAtFilter
        hg.continuousAt).continuousAt.continuousWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo 0 x := by
        simpa only [interior_Icc, hx] using hy
      change 0 < deriv G y
      rw [(intervalIntegral.integral_hasDerivAt_right
        (hg.intervalIntegrable 0 y)
        hg.stronglyMeasurable.stronglyMeasurableAtFilter
        hg.continuousAt).deriv]
      exact hgp y hy'.1 hy'.2
  have hinc := hmono (show (0 : ℝ) ∈ Set.Icc 0 x from
      ⟨le_rfl, hx.le⟩) (show x ∈ Set.Icc 0 x from ⟨hx.le, le_rfl⟩) hx
  simpa only [G, intervalIntegral.integral_same, sub_zero] using hinc

private lemma denominator_pos (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) (x : ℝ) (hx : 0 < x) :
    0 < denominator f x := by
  unfold denominator
  exact integral_pos_from_Ioo f hf x hx (fun t _ _ => hpos t)

private lemma integral_difference (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, (x - t) * f t) =
      x * denominator f x - numerator f x := by
  calc
    (∫ t in (0 : ℝ)..x, (x - t) * f t) =
        ∫ t in (0 : ℝ)..x, (x * f t - t * f t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
    _ = (∫ t in (0 : ℝ)..x, x * f t) -
        ∫ t in (0 : ℝ)..x, t * f t := by
          have hleft : IntervalIntegrable (fun t : ℝ => x * f t)
              MeasureTheory.volume 0 x :=
            (continuous_const.mul hf).intervalIntegrable 0 x
          have hright : IntervalIntegrable (fun t : ℝ => t * f t)
              MeasureTheory.volume 0 x :=
            (continuous_id.mul hf).intervalIntegrable 0 x
          simpa only [Pi.sub_apply] using
            (intervalIntegral.integral_sub hleft hright)
    _ = x * denominator f x - numerator f x := by
          rw [intervalIntegral.integral_const_mul]
          rfl

private lemma phi_pos_lt (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) (x : ℝ) (hx : 0 < x) :
    0 < phi f x ∧ phi f x < x := by
  have hd : 0 < denominator f x := denominator_pos f hf hpos x hx
  have hn : 0 < numerator f x := by
    unfold numerator
    apply integral_pos_from_Ioo (fun t => t * f t) (continuous_id.mul hf) x hx
    intro t ht _
    exact mul_pos ht (hpos t)
  have hi : 0 < ∫ t in (0 : ℝ)..x, (x - t) * f t := by
    apply integral_pos_from_Ioo (fun t => (x - t) * f t)
      (continuous_const.sub continuous_id |>.mul hf) x hx
    intro t ht0 htx
    exact mul_pos (sub_pos.mpr htx) (hpos t)
  have hj : 0 < x * denominator f x - numerator f x := by
    rw [← integral_difference f hf x]
    exact hi
  constructor
  · exact div_pos hn hd
  · unfold phi
    exact (div_lt_iff₀ hd).2 (sub_pos.mp hj)

private lemma phi_tendsto_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) :
    Tendsto (phi f) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
  have hid : Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero hid ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (phi_pos_lt f hf hpos x hx).1.le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (phi_pos_lt f hf hpos x hx).2.le

private lemma phi_tendsto_zero_Ici (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) (hzero : phi f 0 = 0) :
    Tendsto (phi f) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  have hconst : Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := tendsto_const_nhds
  have hid : Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst hid ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxnonneg : 0 ≤ x := hx
    rcases hxnonneg.eq_or_lt with hxeq | hxpos
    · subst x
      simp [hzero]
    · exact (phi_pos_lt f hf hpos x hxpos).1.le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxnonneg : 0 ≤ x := hx
    rcases hxnonneg.eq_or_lt with hxeq | hxpos
    · subst x
      simp [hzero]
    · exact (phi_pos_lt f hf hpos x hxpos).2.le

private lemma comparison_tendsto_zero (f : ℝ → ℝ)
    (hpos : ∀ x, 0 < f x) :
    Tendsto (comparison f) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have heq : comparison f = fun x : ℝ => x := by
    funext x
    simp only [comparison, div_eq_mul_inv]
    rw [mul_assoc, mul_inv_cancel₀ (hpos x).ne']
    simp
  rw [heq]
  exact tendsto_id.mono_left inf_le_left

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    ∀ L : ℝ,
      Tendsto (phi f) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ↔
        Tendsto (comparison f) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) := by
  intro L
  have hphi := phi_tendsto_zero f hf hpos
  have hcomparison := comparison_tendsto_zero f hpos
  constructor
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h hphi
    subst L
    exact hcomparison
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h hcomparison
    subst L
    exact hphi

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    Tendsto (comparison f) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  exact comparison_tendsto_zero f hpos

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    Tendsto (phi f) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  exact (gap1 f hf hpos 0).2 (gap2 f hf hpos)

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    phi f 0 = 0 → ContinuousOn (phi f) (Set.Ici 0) := by
  intro hzero
  intro x hx
  have hxnonneg : 0 ≤ x := hx
  rcases hxnonneg.eq_or_lt with hxeq | hxpos
  · subst x
    change Tendsto (phi f) (nhdsWithin 0 (Set.Ici 0)) (nhds (phi f 0))
    simpa only [hzero] using phi_tendsto_zero_Ici f hf hpos hzero
  · have hdne : denominator f x ≠ 0 :=
      (denominator_pos f hf hpos x hxpos).ne'
    simpa only [phi] using
      ((hasDerivAt_numerator f hf x).continuousAt.div
        (hasDerivAt_denominator f hf x).continuousAt hdne).continuousWithinAt

theorem gap5 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (x : ℝ) (hx : 0 < x) :
    deriv (phi f) x = derivativeForm f x := by
  have hdne : denominator f x ≠ 0 :=
    (denominator_pos f hf hpos x hx).ne'
  change deriv (fun y => numerator f y / denominator f y) x = derivativeForm f x
  calc
    deriv (fun y => numerator f y / denominator f y) x =
        ((x * f x) * denominator f x - numerator f x * f x) /
          denominator f x ^ 2 :=
      ((hasDerivAt_numerator f hf x).div
        (hasDerivAt_denominator f hf x) hdne).deriv
    _ = derivativeForm f x := by
      unfold derivativeForm
      ring

theorem gap6 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (x : ℝ) (hx : 0 < x) :
    derivativeForm f x = positiveForm f x := by
  rw [derivativeForm, positiveForm, integral_difference f hf x]
  ring

theorem gap7 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (x : ℝ) (hx : 0 < x) :
    0 < positiveForm f x := by
  have hd : 0 < denominator f x := denominator_pos f hf hpos x hx
  have hi : 0 < ∫ t in (0 : ℝ)..x, (x - t) * f t := by
    apply integral_pos_from_Ioo (fun t => (x - t) * f t)
      (continuous_const.sub continuous_id |>.mul hf) x hx
    intro t ht0 htx
    exact mul_pos (sub_pos.mpr htx) (hpos t)
  unfold positiveForm
  exact mul_pos (div_pos (hpos x) (sq_pos_of_pos hd)) hi

theorem gap8 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (x : ℝ) (hx : 0 < x) :
    0 < deriv (phi f) x := by
  rw [gap5 f hf hpos x hx, gap6 f hf hpos x hx]
  exact gap7 f hf hpos x hx

theorem gap9 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    StrictMonoOn (phi f) (Set.Ici 0) := by
  have hcontinuous : ContinuousOn (phi f) (Set.Ici 0) :=
    gap4 f hf hpos (by simp [phi, numerator, denominator])
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) hcontinuous ?_
  intro x hx
  have hxpos : 0 < x := by
    simpa only [interior_Ici] using hx
  exact gap8 f hf hpos x hxpos

theorem gap10 (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    StrictMonoOn (phi f) (Set.Ici 0) := by
  exact gap9 f hf hpos

end

end ProofGap.Exercise2236
