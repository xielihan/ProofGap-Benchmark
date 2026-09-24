import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2373
noncomputable section

open Filter MeasureTheory
open scoped Interval

def integrand (x : ℝ) : ℝ :=
  Real.log (Real.sin x) / Real.sqrt x
def leftExpression (x : ℝ) : ℝ :=
  Real.rpow x (5 / 6 : ℝ) * integrand x
def rightExpression (x : ℝ) : ℝ :=
  Real.rpow (x / Real.sin x) (1 / 3 : ℝ) *
    Real.rpow (Real.sin x) (1 / 3 : ℝ) * Real.log (Real.sin x)

private theorem sin_tendsto_nhdsGT_zero :
    Tendsto Real.sin (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto Real.sin (nhds (0 : ℝ)) (nhds (Real.sin 0)) :=
      Real.continuous_sin.continuousAt
    simpa using h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds] with x hx hpi
  exact Real.sin_pos_of_pos_of_lt_pi hx hpi

private theorem sin_div_tendsto_one :
    Tendsto (fun x : ℝ => Real.sin x / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero_right

private theorem div_sin_tendsto_one :
    Tendsto (fun x : ℝ => x / Real.sin x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  simpa [inv_div] using sin_div_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

private theorem expressions_eventually_eq :
    leftExpression =ᶠ[nhdsWithin 0 (Set.Ioi 0)] rightExpression := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds] with x hx hpi
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx hpi
  have hsqrt : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.2 hx
  have hsr : Real.rpow (Real.sin x) (1 / (3 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hs _).ne'
  have hradd : Real.rpow x (1 / 3 + 1 / 2 : ℝ) =
      Real.rpow x (1 / 3 : ℝ) * Real.rpow x (1 / 2 : ℝ) := by
    simpa only using Real.rpow_add hx (1 / 3 : ℝ) (1 / 2 : ℝ)
  have hpowsqrt : Real.rpow x (5 / 6 : ℝ) =
      Real.rpow x (1 / 3 : ℝ) * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow,
      show (5 / 6 : ℝ) = 1 / 3 + 1 / 2 by norm_num]
    exact hradd
  have hrdiv : Real.rpow (x / Real.sin x) (1 / 3 : ℝ) =
      Real.rpow x (1 / 3 : ℝ) / Real.rpow (Real.sin x) (1 / 3 : ℝ) := by
    simpa only using Real.div_rpow hx.le hs.le (1 / 3 : ℝ)
  unfold leftExpression rightExpression integrand
  rw [hpowsqrt, hrdiv]
  field_simp [hsqrt, hsr]

theorem gap1 :
    Tendsto leftExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ↔
      Tendsto rightExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  constructor
  · intro h
    exact h.congr' expressions_eventually_eq
  · intro h
    exact h.congr' expressions_eventually_eq.symm

theorem gap2 :
    Tendsto rightExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hratio : Tendsto (fun x : ℝ => Real.rpow (x / Real.sin x) (1 / 3 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using (Real.continuousAt_rpow_const 1 (1 / 3 : ℝ) (Or.inl one_ne_zero)).tendsto.comp
      div_sin_tendsto_one
  have hlogpow : Tendsto
      (fun x : ℝ => Real.rpow (Real.sin x) (1 / 3 : ℝ) * Real.log (Real.sin x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero
      (by norm_num : (0 : ℝ) < 1 / 3)).comp sin_tendsto_nhdsGT_zero
    simpa [mul_comm] using h
  change Tendsto (fun x : ℝ =>
    Real.rpow (x / Real.sin x) (1 / 3 : ℝ) *
      Real.rpow (Real.sin x) (1 / 3 : ℝ) * Real.log (Real.sin x))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  simpa [mul_assoc] using hratio.mul hlogpow

theorem gap3 :
    Tendsto leftExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact gap1.mpr gap2

private theorem integrand_continuousAt_of_pos_of_lt_pi {x : ℝ}
    (hx : 0 < x) (hpi : x < Real.pi) : ContinuousAt integrand x := by
  unfold integrand
  exact (Real.continuous_sin.continuousAt.log
      (Real.sin_pos_of_pos_of_lt_pi hx hpi).ne').div
    Real.continuous_sqrt.continuousAt (Real.sqrt_ne_zero'.2 hx)

private theorem integrand_continuousOn :
    ContinuousOn integrand (Set.Ioc 0 (Real.pi / 2)) := by
  intro x hx
  exact (integrand_continuousAt_of_pos_of_lt_pi hx.1
    (hx.2.trans_lt (half_lt_self Real.pi_pos))).continuousWithinAt

private theorem integrand_integrableOn :
    IntegrableOn integrand (Set.Icc 0 (Real.pi / 2)) := by
  have hnorm : Tendsto (fun x : ℝ => ‖leftExpression x‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using gap3.norm
  have hevent : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), ‖leftExpression x‖ ≤ 1 := by
    filter_upwards [hnorm.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with x hx
    exact hx.le
  rcases (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset Real.pi_div_two_pos).mp hevent with
    ⟨δ, hδ, hbound⟩
  have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (-5 / 6 : ℝ)) (Set.Ioo 0 δ) := by
    simpa only using (intervalIntegral.integrableOn_Ioo_rpow_iff hδ.1).2
      (by norm_num : (-1 : ℝ) < -5 / 6)
  have hcontNear : ContinuousOn integrand (Set.Ioo 0 δ) :=
    integrand_continuousOn.mono fun x hx =>
      ⟨hx.1, hx.2.le.trans hδ.2⟩
  have hnearIoo : IntegrableOn integrand (Set.Ioo 0 δ) := by
    apply hpow.mono' (hcontNear.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hp : 0 < Real.rpow x (5 / 6 : ℝ) := Real.rpow_pos_of_pos hx.1 _
    have hmul : ‖leftExpression x‖ =
        Real.rpow x (5 / 6 : ℝ) * ‖integrand x‖ := by
      rw [leftExpression, norm_mul, Real.norm_eq_abs, abs_of_pos hp]
    have hle : ‖integrand x‖ ≤ 1 / Real.rpow x (5 / 6 : ℝ) := by
      apply (le_div_iff₀ hp).2
      rw [mul_comm, ← hmul]
      exact hbound hx
    calc
      ‖integrand x‖ ≤ 1 / Real.rpow x (5 / 6 : ℝ) := hle
      _ = Real.rpow x (-5 / 6 : ℝ) := by
        have hneg : Real.rpow x (-5 / 6 : ℝ) =
            (Real.rpow x (5 / 6 : ℝ))⁻¹ := by
          simpa only [show (-5 / 6 : ℝ) = -(5 / 6 : ℝ) by ring] using
            Real.rpow_neg hx.1.le (5 / 6 : ℝ)
        rw [hneg]
        simp
  have hnear : IntegrableOn integrand (Set.Ioc 0 δ) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 hnearIoo
  have hfarCont : ContinuousOn integrand (Set.Icc δ (Real.pi / 2)) :=
    integrand_continuousOn.mono fun x hx => ⟨hδ.1.trans_le hx.1, hx.2⟩
  have hfar : IntegrableOn integrand (Set.Icc δ (Real.pi / 2)) :=
    hfarCont.integrableOn_Icc
  have hIoc : IntegrableOn integrand (Set.Ioc 0 (Real.pi / 2)) := by
    apply (hnear.union hfar).mono
    · intro x hx
      by_cases hxd : x ≤ δ
      · exact Or.inl ⟨hx.1, hxd⟩
      · exact Or.inr ⟨le_of_lt (lt_of_not_ge hxd), hx.2⟩
    · exact le_rfl
  exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hIoc

theorem gap4 :
    ∃ L : ℝ,
      Tendsto (fun a => ∫ x in a..(Real.pi / 2), integrand x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  let L := ∫ x in (0 : ℝ)..(Real.pi / 2), integrand x
  refine ⟨L, ?_⟩
  have hint : IntegrableOn integrand (Set.uIcc 0 (Real.pi / 2)) := by
    simpa [Set.uIcc_of_le Real.pi_div_two_pos.le] using integrand_integrableOn
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hint
  have hzero : (0 : ℝ) ∈ Set.uIcc 0 (Real.pi / 2) := Set.left_mem_uIcc
  have htend : Tendsto (fun a => ∫ x in a..(Real.pi / 2), integrand x)
      (nhdsWithin 0 (Set.uIcc 0 (Real.pi / 2))) (nhds L) := by
    simpa [L] using hcont 0 hzero
  apply htend.mono_left
  rw [nhdsWithin_le_iff]
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds Real.pi_div_two_pos).filter_mono nhdsWithin_le_nhds] with x hx hxb
  rw [Set.uIcc_of_le Real.pi_div_two_pos.le]
  exact ⟨hx.le, hxb.le⟩

end
end ProofGap.Exercise2373
