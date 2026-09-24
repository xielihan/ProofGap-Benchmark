import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3741

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

def integrand (a x : ℝ) : ℝ :=
  Real.exp (-a * x) / (1 + x ^ 2)

def partialIntegral (a A : ℝ) : ℝ :=
  ∫ x in a..A, integrand a x

def Converges (a : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (partialIntegral a) atTop (𝓝 L)

def comparisonIntegral (a : ℝ) : ℝ :=
  ∫ x in Set.Ioi a, 1 / (1 + x ^ 2)

theorem gap1 (a x : ℝ) (ha : 0 ≤ a) (hx : a ≤ x) :
    integrand a x ≤ 1 / (1 + x ^ 2) := by
  have hx0 : 0 ≤ x := ha.trans hx
  have hax : -a * x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hx0
  have he : Real.exp (-a * x) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr hax
  have hd : 0 ≤ 1 + x ^ 2 := by positivity
  exact div_le_div_of_nonneg_right he hd

theorem gap2 (a : ℝ) (ha : 0 ≤ a) :
    comparisonIntegral a = Real.pi / 2 - Real.arctan a := by
  simpa [comparisonIntegral, one_div] using
    (Real.integral_Ioi_inv_one_add_sq (i := a))

theorem gap3 :
    Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) := by
  exact tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop

theorem gap4 (a : ℝ) (ha : 0 ≤ a) :
    comparisonIntegral a = Real.pi / 2 - Real.arctan a := by
  exact gap2 a ha

theorem gap5 (a : ℝ) (ha : 0 ≤ a) :
    Converges a := by
  have hc : Continuous (integrand a) := by
    unfold integrand
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity
  have hfi : IntegrableOn (integrand a) (Set.Ioi a) := by
    refine MeasureTheory.Integrable.mono'
      integrable_inv_one_add_sq.integrableOn
      hc.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hnonneg : 0 ≤ integrand a x := by
      unfold integrand
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [one_div] using gap1 a x ha hx.le
  refine ⟨∫ x in Set.Ioi a, integrand a x, ?_⟩
  simpa [partialIntegral] using
    (intervalIntegral_tendsto_integral_Ioi a hfi tendsto_id)

theorem gap6 (a x : ℝ) (ha : a < 0) :
    Real.exp (-a * x) = Real.exp (|a| * x) := by
  rw [abs_of_neg ha]

theorem gap7 (a : ℝ) (ha : a < 0) :
    Tendsto (fun x => Real.exp (|a| * x)) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (abs_pos.mpr ha.ne))

theorem gap8 (a : ℝ) (ha : a < 0) :
    Tendsto (fun x => Real.exp (-a * x)) atTop atTop := by
  simpa only [gap6 a _ ha] using gap7 a ha

theorem gap9 (a : ℝ) (ha : a < 0) :
    Tendsto (fun x => Real.exp (|a| * x) / (1 + x ^ 2)) atTop atTop := by
  have hpow :
      Tendsto (fun x : ℝ => Real.exp (|a| * x) / x ^ 2) atTop atTop := by
    simpa only [Real.rpow_two] using
      (tendsto_exp_mul_div_rpow_atTop (2 : ℝ) |a|
        (abs_pos.mpr ha.ne))
  have hlower :
      Tendsto
        (fun x : ℝ => (1 / 2 : ℝ) *
          (Real.exp (|a| * x) / x ^ 2)) atTop atTop :=
    hpow.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
  have hd : 0 < 1 + x ^ 2 := by positivity
  have h2d : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
  have he : 0 ≤ Real.exp (|a| * x) := Real.exp_nonneg _
  calc
    (1 / 2 : ℝ) * (Real.exp (|a| * x) / x ^ 2) =
        Real.exp (|a| * x) / (2 * x ^ 2) := by ring
    _ ≤ Real.exp (|a| * x) / (1 + x ^ 2) := by
      exact (div_le_div_iff₀ (mul_pos (by norm_num) hx2) hd).2
        (mul_le_mul_of_nonneg_left h2d he)

theorem gap10 (a : ℝ) (ha : a < 0) :
    ¬ Converges a := by
  have hc : Continuous (integrand a) := by
    unfold integrand
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity
  have hdiv : Tendsto (integrand a) atTop atTop := by
    convert gap9 a ha using 1
    ext x
    rw [integrand, gap6 a x ha]
  have hge : ∀ᶠ x in atTop, 1 ≤ integrand a x :=
    hdiv.eventually_ge_atTop 1
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hge
  let C : ℝ := max a B
  have hCa : a ≤ C := le_max_left _ _
  have hCB : B ≤ C := le_max_right _ _
  have hpartial : Tendsto (partialIntegral a) atTop atTop := by
    have hlinear :
        Tendsto
          (fun A : ℝ => (∫ x in a..C, integrand a x) + (A - C))
          atTop atTop := by
      have h :=
        tendsto_id.atTop_add
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => (∫ x in a..C, integrand a x) - C)
              atTop (𝓝 ((∫ x in a..C, integrand a x) - C)))
      convert h using 1
      ext A
      simp only [id_eq]
      ring
    refine tendsto_atTop_mono' atTop ?_ hlinear
    filter_upwards [eventually_ge_atTop C] with A hCA
    have hmono :
        (∫ _x in C..A, (1 : ℝ)) ≤
          ∫ x in C..A, integrand a x := by
      refine intervalIntegral.integral_mono_on hCA
        (continuous_const.intervalIntegrable C A)
        (hc.intervalIntegrable C A) ?_
      intro x hx
      exact hB x (hCB.trans hx.1)
    calc
      (∫ x in a..C, integrand a x) + (A - C) =
          (∫ x in a..C, integrand a x) +
            ∫ _x in C..A, (1 : ℝ) := by
              simp [intervalIntegral.integral_const]
      _ ≤ (∫ x in a..C, integrand a x) +
            ∫ x in C..A, integrand a x :=
        add_le_add_right hmono _
      _ = ∫ x in a..A, integrand a x :=
        intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable a C) (hc.intervalIntegrable C A)
      _ = partialIntegral a A := rfl
  rintro ⟨L, hL⟩
  exact not_tendsto_nhds_of_tendsto_atTop hpartial L hL

theorem gap11 (a : ℝ) :
    0 ≤ a ↔ Converges a := by
  constructor
  · exact gap5 a
  · intro hconv
    by_contra hna
    exact gap10 a (lt_of_not_ge hna) hconv

end

end ProofGap.Exercise3741
