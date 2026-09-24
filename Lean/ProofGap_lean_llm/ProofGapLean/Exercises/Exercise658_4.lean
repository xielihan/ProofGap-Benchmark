import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

namespace ProofGap.Exercise658_4

noncomputable section

def target (x : ℝ) : ℝ := 1 / Real.sin (Real.pi * x)
def model (x : ℝ) : ℝ := 1 / (Real.pi * (1 - x))

/-- Source: `proof_gap/exercise_658_4/1.txt`; exclude the zeros of the displayed denominators. -/
private theorem ratio_identity (x : ℝ) :
    target x / model x =
      Real.pi * (1 - x) / Real.sin (Real.pi * (1 - x)) := by
  have hs :
      Real.sin (Real.pi * (1 - x)) = Real.sin (Real.pi * x) := by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  unfold target model
  rw [hs]
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  exact mul_comm _ _

theorem gap1 (x : ℝ) (hx : x ≠ 1) (hsin : Real.sin (Real.pi * x) ≠ 0) :
    target x / model x =
      (Real.pi * (1 - x)) / Real.sin (Real.pi * (1 - x)) := by
  exact ratio_identity x

/-- Source: `proof_gap/exercise_658_4/2.txt`. -/
theorem gap2 :
    Filter.Tendsto
      (fun x : ℝ => Real.pi * (1 - x) / Real.sin (Real.pi * (1 - x)))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
  have hxlim :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) :=
    Filter.tendsto_id.mono_left inf_le_left
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hsub :
      Filter.Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hone.sub hxlim
  have hpi :
      Filter.Tendsto (fun _ : ℝ => Real.pi)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds Real.pi) :=
    tendsto_const_nhds
  have hzero :
      Filter.Tendsto (fun x : ℝ => Real.pi * (1 - x))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hpi.mul hsub
  have hsinc0 : ContinuousAt Real.sinc (0 : ℝ) :=
    Real.continuous_sinc.continuousAt
  have hsincT :
      Filter.Tendsto Real.sinc (nhds 0) (nhds (Real.sinc 0)) := by
    exact hsinc0
  have hsinc :
      Filter.Tendsto Real.sinc (nhds 0) (nhds 1) := by
    simpa [Real.sinc] using hsincT
  have hinv :
      Filter.Tendsto (fun y : ℝ => (Real.sinc y)⁻¹)
        (nhds 0) (nhds 1) := by
    simpa using hsinc.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  have hcomp :
      Filter.Tendsto
        (fun x : ℝ => (Real.sinc (Real.pi * (1 - x)))⁻¹)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) :=
    hinv.comp hzero
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have ha : Real.pi * (1 - x) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr (Ne.symm hx))
  simp [Real.sinc, ha]

/-- Source: `proof_gap/exercise_658_4/3.txt`. -/
theorem gap3 :
    Filter.Tendsto (fun x : ℝ => target x / model x)
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) := by
  have hfun :
      (fun x : ℝ => target x / model x) =
        (fun x : ℝ =>
          Real.pi * (1 - x) / Real.sin (Real.pi * (1 - x))) := by
    funext x
    exact ratio_identity x
  rw [hfun]
  exact gap2

/-- Source: `proof_gap/exercise_658_4/4.txt`. -/
theorem gap4 :
    Asymptotics.IsEquivalent (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
      target model := by
  have hmodel_ne :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ, model x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    unfold model
    exact one_div_ne_zero
      (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr (Ne.symm hx)))
  change Asymptotics.IsLittleO
    (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
    (fun x : ℝ => target x - model x) model
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  change ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
    ‖target x - model x‖ ≤ c * ‖model x‖
  have hsmall :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
        ‖target x / model x - 1‖ < c := by
    simpa only [dist_eq_norm] using
      ((Metric.tendsto_nhds.1 gap3) c hc)
  filter_upwards [hmodel_ne, hsmall] with x hm hs
  have hid :
      target x - model x =
        (target x / model x - 1) * model x := by
    rw [sub_mul, div_mul_cancel₀ _ hm, one_mul]
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_right (le_of_lt hs) (norm_nonneg _)

/-- Source: `proof_gap/exercise_658_4/5.txt`; unpack the singleton pair. -/
theorem gap5 (C : ℝ) (n : ℕ) (h : (C, n) = (1 / Real.pi, 1)) :
    Asymptotics.IsEquivalent (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
      target (fun x => C * (1 / (1 - x)) ^ n) := by
  have hC : C = 1 / Real.pi := congrArg Prod.fst h
  have hn : n = (1 : ℕ) := congrArg Prod.snd h
  subst C
  subst n
  have hmodel :
      (fun x : ℝ =>
        (1 / Real.pi) * (1 / (1 - x)) ^ (1 : ℕ)) = model := by
    funext x
    simp only [pow_one, model, one_div, mul_inv_rev]
    exact mul_comm _ _
  rw [hmodel]
  exact gap4

end

end ProofGap.Exercise658_4
