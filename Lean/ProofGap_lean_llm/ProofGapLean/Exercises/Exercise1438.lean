import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ProofGap.Exercise1438

noncomputable section

def y (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.sqrt x * Real.log x

def domain : Set ℝ := Set.Ici 0
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem eventually_y_eq (x : ℝ) (hx : 0 < x) :
    y =ᶠ[nhds x] fun z : ℝ => Real.sqrt z * Real.log z := by
  filter_upwards [Ioi_mem_nhds hx] with z hz
  change 0 < z at hz
  simp only [y, if_neg hz.ne']

private theorem continuousAt_y_of_pos {x : ℝ} (hx : 0 < x) :
    ContinuousAt y x := by
  have hcont :
      ContinuousAt (fun z : ℝ => Real.sqrt z * Real.log z) x :=
    Real.continuous_sqrt.continuousAt.mul
      (Real.continuousAt_log hx.ne')
  exact hcont.congr_of_eventuallyEq (eventually_y_eq x hx)

private theorem tendsto_sqrt_mul_log :
    Filter.Tendsto (fun x : ℝ => Real.sqrt x * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa [Real.sqrt_eq_rpow, mul_comm] using
    (tendsto_log_mul_rpow_nhdsGT_zero
      (show (0 : ℝ) < 1 / 2 by norm_num))

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = (1 / (2 * Real.sqrt x)) * (Real.log x + 2) := by
  have hsqrt :
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx.ne'
  have hlog : HasDerivAt Real.log (1 / x) x :=
    by simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hprod := hsqrt.mul hlog
  have hyderiv :
      HasDerivAt y
        ((1 / (2 * Real.sqrt x)) * Real.log x +
          Real.sqrt x * (1 / x)) x :=
    hprod.congr_of_eventuallyEq (eventually_y_eq x hx)
  rw [hyderiv.deriv]
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  field_simp [hspos.ne', hx.ne']
  nlinarith [hs2]

theorem gap2 : deriv y (Real.exp (-2)) = 0 := by
  rw [gap1 (Real.exp (-2)) (Real.exp_pos (-2))]
  simp [Real.log_exp]

theorem gap3 (x : ℝ) (h₁ : 0 < x) (h₂ : x < Real.exp (-2)) :
    deriv y x < 0 := by
  rw [gap1 x h₁]
  have hlog : Real.log x < -2 := by
    simpa [Real.log_exp] using Real.log_lt_log h₁ h₂
  exact mul_neg_of_pos_of_neg
    (one_div_pos.mpr (mul_pos (by norm_num) (Real.sqrt_pos.2 h₁)))
    (by linarith)

theorem gap4 (x : ℝ) (hx : Real.exp (-2) < x) :
    0 < deriv y x := by
  have hx0 : 0 < x := lt_trans (Real.exp_pos (-2)) hx
  rw [gap1 x hx0]
  have hlog : -2 < Real.log x := by
    simpa [Real.log_exp] using
      Real.log_lt_log (Real.exp_pos (-2)) hx
  exact mul_pos
    (one_div_pos.mpr (mul_pos (by norm_num) (Real.sqrt_pos.2 hx0)))
    (by linarith)

theorem gap5 : IsMinOn y domain (Real.exp (-2)) := by
  rw [isMinOn_iff]
  intro x hxdom
  change 0 ≤ x at hxdom
  have hcpos : 0 < Real.exp (-2) := Real.exp_pos (-2)
  by_cases hx0 : x = 0
  · subst x
    have hycneg : y (Real.exp (-2)) < 0 := by
      rw [show y (Real.exp (-2)) =
        Real.sqrt (Real.exp (-2)) * Real.log (Real.exp (-2)) by
          simp [y, Real.exp_ne_zero]]
      rw [Real.log_exp]
      exact mul_neg_of_pos_of_neg
        (Real.sqrt_pos.2 (Real.exp_pos (-2))) (by norm_num)
    norm_num [y]
  have hxpos : 0 < x := lt_of_le_of_ne hxdom (Ne.symm hx0)
  by_cases hxc : x < Real.exp (-2)
  · have hcont : ContinuousOn y (Set.Icc x (Real.exp (-2))) := by
      intro z hz
      exact (continuousAt_y_of_pos
        (lt_of_lt_of_le hxpos hz.1)).continuousWithinAt
    have hanti :
        StrictAntiOn y (Set.Icc x (Real.exp (-2))) := by
      apply strictAntiOn_of_deriv_neg
        (convex_Icc x (Real.exp (-2))) hcont
      intro z hz
      rw [interior_Icc] at hz
      exact gap3 z (lt_trans hxpos hz.1) hz.2
    exact hanti.antitoneOn
      ⟨le_rfl, hxc.le⟩ ⟨hxc.le, le_rfl⟩ hxc.le
  · have hcx : Real.exp (-2) ≤ x := le_of_not_gt hxc
    rcases hcx.eq_or_lt with hEq | hlt
    · simpa [hEq]
    · have hcont : ContinuousOn y (Set.Icc (Real.exp (-2)) x) := by
        intro z hz
        exact (continuousAt_y_of_pos
          (lt_of_lt_of_le hcpos hz.1)).continuousWithinAt
      have hmono :
          StrictMonoOn y (Set.Icc (Real.exp (-2)) x) := by
        apply strictMonoOn_of_deriv_pos
          (convex_Icc (Real.exp (-2)) x) hcont
        intro z hz
        rw [interior_Icc] at hz
        exact gap4 z hz.1
      exact hmono.monotoneOn
        ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt.le

theorem gap6 : y (Real.exp (-2)) = -(2 / Real.exp 1) := by
  simp [y, Real.exp_ne_zero, Real.log_exp, ← Real.exp_half,
    Real.exp_neg, div_eq_mul_inv]
  ring

theorem gap7 : Approx (-(2 / Real.exp 1)) (-0.736) 0.001 := by
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hl : (0.735 : ℝ) < 2 / Real.exp 1 := by
    apply (lt_div_iff₀ hepos).2
    nlinarith [Real.exp_one_lt_d9]
  have hu : 2 / Real.exp 1 < (0.737 : ℝ) := by
    apply (div_lt_iff₀ hepos).2
    nlinarith [Real.exp_one_gt_d9]
  unfold Approx
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

theorem gap8 (x : ℝ) (hx : x ∈ Set.Ioo 0 1) : y x < 0 := by
  simp only [Set.mem_Ioo] at hx
  rw [show y x = Real.sqrt x * Real.log x by
    simp [y, ne_of_gt hx.1]]
  exact mul_neg_of_pos_of_neg (Real.sqrt_pos.2 hx.1)
    (Real.log_neg hx.1 hx.2)

theorem gap9 :
    Filter.Tendsto (fun x : ℝ => Real.sqrt x * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact tendsto_sqrt_mul_log

theorem gap10 : IsLocalMaxOn y domain 0 := by
  have hzero : y 0 = 0 := by simp [y]
  change ∀ᶠ x in nhdsWithin (0 : ℝ) domain, y x ≤ y 0
  have hlt :
      ∀ᶠ x in nhdsWithin (0 : ℝ) domain, x < 1 :=
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hlt, self_mem_nhdsWithin] with x hx1 hxdom
  change 0 ≤ x at hxdom
  rw [hzero]
  by_cases hx0 : x = 0
  · subst x
    simp [y]
  · exact (gap8 x ⟨lt_of_le_of_ne hxdom (Ne.symm hx0), hx1⟩).le

theorem gap11 : y 0 = 0 := by
  simp [y]

end
end ProofGap.Exercise1438
