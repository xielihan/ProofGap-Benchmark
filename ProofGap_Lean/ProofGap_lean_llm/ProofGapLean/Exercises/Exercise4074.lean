import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4074

noncomputable section

open MeasureTheory
open scoped Interval

def region : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ p.1 * p.2.1}

def volumeIntegral : ℝ :=
  ∫ p in region, p.1 * p.2.1 ^ 2 * p.2.2 ^ 3

private theorem ae_ne (a : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
  rw [ae_iff]
  simp

private theorem Set.indicator_of_not_mem
    {α β : Type*} [Zero β] {s : Set α} {f : α → β} {x : α}
    (hx : x ∉ s) :
    s.indicator f x = 0 := by
  simp [Set.indicator, hx]

private theorem integral_indicator_Icc_eq_interval
    (a b : ℝ) (g : ℝ → ℝ) (hab : a ≤ b) :
    (∫ x, (Set.Icc a b).indicator g x) = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_ne a] with x hx
  have hlt : a < x ↔ a ≤ x := by
    constructor
    · exact le_of_lt
    · intro hax
      exact lt_of_le_of_ne hax (Ne.symm hx)
  by_cases hmem : x ∈ Set.Icc a b
  · have hmem' : x ∈ Set.Ioc a b := ⟨hlt.mpr hmem.1, hmem.2⟩
    simpa only [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
  · have hmem' : x ∉ Set.Ioc a b := by
      intro h
      apply hmem
      exact ⟨le_of_lt h.1, h.2⟩
    simp [Set.indicator, hmem, hmem']

private theorem monomial_derivative_aux4074 (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (n + 1))
      (((n : ℝ) + 1) * x ^ n) x := by
  induction n with
  | zero =>
      simpa using (hasDerivAt_id x)
  | succ n ih =>
      convert (ih.mul (hasDerivAt_id x)) using 1 <;>
        simp [Nat.succ_eq_add_one, Nat.cast_add, pow_succ] <;>
        ring

theorem gap1 :
    volumeIntegral =
      ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..x,
          ∫ z in (0 : ℝ)..x * y, x * y ^ 2 * z ^ 3 := by
  let f : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => p.1 * p.2.1 ^ 2 * p.2.2 ^ 3
  change
    (∫ p in region, f p) =
      ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..x,
          ∫ z in (0 : ℝ)..x * y, f (x, (y, z))
  have hxc : Continuous (fun p : ℝ × (ℝ × ℝ) => p.1) := continuous_fst
  have hyc : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hzc : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hclosed : IsClosed region := by
    unfold region
    exact
      (isClosed_le continuous_const hxc).inter
        ((isClosed_le hxc continuous_const).inter
          ((isClosed_le continuous_const hyc).inter
            ((isClosed_le hyc hxc).inter
              ((isClosed_le continuous_const hzc).inter
                (isClosed_le hzc (hxc.mul hyc))))))
  have hbox :
      IsCompact
        (Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcompact : IsCompact region := by
    apply hbox.of_isClosed_subset hclosed
    intro p hp
    change
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧
        0 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧
        0 ≤ p.2.2 ∧ p.2.2 ≤ p.1 * p.2.1 at hp
    rcases hp with ⟨hx0, hx1, hy0, hyx, hz0, hzxy⟩
    have hy1 : p.2.1 ≤ 1 := hyx.trans hx1
    have hxy1 : p.1 * p.2.1 ≤ 1 := by
      calc
        p.1 * p.2.1 ≤ p.1 * 1 :=
          mul_le_mul_of_nonneg_left hy1 hx0
        _ = p.1 := mul_one p.1
        _ ≤ 1 := hx1
    exact
      ⟨⟨hx0, hx1⟩,
        ⟨⟨hy0, hy1⟩, ⟨hz0, hzxy.trans hxy1⟩⟩⟩
  have hf_cont : Continuous f := by
    dsimp [f]
    exact (hxc.mul (hyc.pow 2)).mul (hzc.pow 3)
  have hmeas : MeasurableSet region := hclosed.measurableSet
  have hf_on : IntegrableOn f region :=
    hf_cont.continuousOn.integrableOn_compact hcompact
  have hfi : Integrable (region.indicator f) :=
    (MeasureTheory.integrable_indicator_iff hmeas).2 hf_on
  have hsections := hfi.prod_right_ae
  rw [← MeasureTheory.integral_indicator hmeas]
  change
    (∫ p : ℝ × (ℝ × ℝ), region.indicator f p
      ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))) = _
  rw [MeasureTheory.integral_prod _ hfi]
  rw [← integral_indicator_Icc_eq_interval
    0 1
    (fun x =>
      ∫ y in (0 : ℝ)..x,
        ∫ z in (0 : ℝ)..x * y, f (x, (y, z)))
    zero_le_one]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hsections] with x hxint
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    change
      (∫ q : ℝ × ℝ, region.indicator f (x, q)
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = _
    rw [MeasureTheory.integral_prod _ hxint]
    rw [← integral_indicator_Icc_eq_interval
      0 x
      (fun y => ∫ z in (0 : ℝ)..x * y, f (x, (y, z)))
      hx.1]
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) x
    · rw [Set.indicator_of_mem hy]
      have hzfun :
          (fun z => region.indicator f (x, (y, z))) =
            (Set.Icc (0 : ℝ) (x * y)).indicator
              (fun z => f (x, (y, z))) := by
        funext z
        by_cases hz : z ∈ Set.Icc (0 : ℝ) (x * y)
        · have hp : (x, (y, z)) ∈ region := by
            exact ⟨hx.1, hx.2, hy.1, hy.2, hz.1, hz.2⟩
          simpa only [Set.indicator_of_mem hp, Set.indicator_of_mem hz]
        · have hp : (x, (y, z)) ∉ region := by
            intro hp
            apply hz
            exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
          simp [Set.indicator, hp, hz]
      change
        (∫ z : ℝ, region.indicator f (x, (y, z))) =
          ∫ z in (0 : ℝ)..x * y, f (x, (y, z))
      rw [hzfun]
      exact integral_indicator_Icc_eq_interval
        0 (x * y) (fun z => f (x, (y, z)))
        (mul_nonneg hx.1 hy.1)
    · rw [Set.indicator_of_not_mem hy]
      have hzero :
          (fun z => region.indicator f (x, (y, z))) =
            fun _ => 0 := by
        funext z
        have hp : (x, (y, z)) ∉ region := by
          intro hp
          apply hy
          exact ⟨hp.2.2.1, hp.2.2.2.1⟩
        simp [Set.indicator, hp]
      change (∫ z : ℝ, region.indicator f (x, (y, z))) = 0
      rw [hzero]
      simp
  · rw [Set.indicator_of_not_mem hx]
    have hzero :
        (fun q : ℝ × ℝ => region.indicator f (x, q)) =
          fun _ => 0 := by
      funext q
      have hp : (x, q) ∉ region := by
        intro hp
        apply hx
        exact ⟨hp.1, hp.2.1⟩
      simp [Set.indicator, hp]
    change
      (∫ q : ℝ × ℝ, region.indicator f (x, q)
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = 0
    rw [hzero]
    simp

theorem gap2 :
    volumeIntegral = 1 / 364 := by
  rw [gap1]
  have hpow3 (a b : ℝ) :
      (∫ t in a..b, t ^ 3) =
        ((1 : ℝ) / 4) * b ^ 4 - ((1 : ℝ) / 4) * a ^ 4 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      convert
        ((monomial_derivative_aux4074 3 t).const_mul ((1 : ℝ) / 4))
          using 1 <;>
        norm_num <;> ring
    · have hc : Continuous (fun t : ℝ => t ^ 3) := continuous_id.pow 3
      exact hc.continuousOn.intervalIntegrable
  have hpow6 (a b : ℝ) :
      (∫ t in a..b, t ^ 6) =
        ((1 : ℝ) / 7) * b ^ 7 - ((1 : ℝ) / 7) * a ^ 7 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      convert
        ((monomial_derivative_aux4074 6 t).const_mul ((1 : ℝ) / 7))
          using 1 <;>
        norm_num <;> ring
    · have hc : Continuous (fun t : ℝ => t ^ 6) := continuous_id.pow 6
      exact hc.continuousOn.intervalIntegrable
  have hpow12 (a b : ℝ) :
      (∫ t in a..b, t ^ 12) =
        ((1 : ℝ) / 13) * b ^ 13 - ((1 : ℝ) / 13) * a ^ 13 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      convert
        ((monomial_derivative_aux4074 12 t).const_mul ((1 : ℝ) / 13))
          using 1 <;>
        norm_num <;> ring
    · have hc : Continuous (fun t : ℝ => t ^ 12) := continuous_id.pow 12
      exact hc.continuousOn.intervalIntegrable
  have hz (x y : ℝ) :
      (∫ z in (0 : ℝ)..x * y, x * y ^ 2 * z ^ 3) =
        x ^ 5 * y ^ 6 / 4 := by
    calc
      (∫ z in (0 : ℝ)..x * y, x * y ^ 2 * z ^ 3) =
          (x * y ^ 2) * (∫ z in (0 : ℝ)..x * y, z ^ 3) := by
            rw [intervalIntegral.integral_const_mul]
      _ = x ^ 5 * y ^ 6 / 4 := by
        rw [hpow3]
        ring
  simp_rw [hz]
  have hy (x : ℝ) :
      (∫ y in (0 : ℝ)..x, x ^ 5 * y ^ 6 / 4) = x ^ 12 / 28 := by
    have hfun :
        (fun y : ℝ => x ^ 5 * y ^ 6 / 4) =
          fun y => (x ^ 5 / 4) * y ^ 6 := by
      funext y
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hpow6]
    ring
  simp_rw [hy]
  have hx :
      (∫ x in (0 : ℝ)..1, x ^ 12 / 28) = (1 : ℝ) / 364 := by
    have hfun :
        (fun x : ℝ => x ^ 12 / 28) =
          fun x => ((1 : ℝ) / 28) * x ^ 12 := by
      funext x
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hpow12]
    ring
  exact hx

end

end ProofGap.Exercise4074
