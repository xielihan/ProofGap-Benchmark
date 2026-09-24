import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise548

noncomputable section

def original (a α β x : ℝ) : ℝ :=
  (Real.rpow x α - Real.rpow a α) / (Real.rpow x β - Real.rpow a β)
def scaled (a α β x : ℝ) : ℝ :=
  Real.rpow a (α - β) *
    ((Real.rpow (x / a) α - 1) / (Real.rpow (x / a) β - 1))
def exponentialForm (a α β x : ℝ) : ℝ :=
  Real.rpow a (α - β) *
    ((Real.exp (α * Real.log (x / a)) - 1) / (α * Real.log (x / a))) *
    ((β * Real.log (x / a)) / (Real.exp (β * Real.log (x / a)) - 1)) *
    (α / β)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 548, gap 1; restrict real powers to `x>0` and exclude the puncture. -/
private theorem rpow_secant_tendsto (a γ : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun x => (Real.rpow x γ - Real.rpow a γ) / (x - a))
      (nhdsWithin a ({a} : Set ℝ)ᶜ)
      (nhds (Real.exp (γ * Real.log a) * (γ * a⁻¹))) := by
  have hinner :
      HasDerivAt (fun x : ℝ => γ * Real.log x) (γ * a⁻¹) a :=
    (Real.hasDerivAt_log ha.ne').const_mul γ
  have hderiv :
      HasDerivAt (fun x : ℝ => Real.exp (γ * Real.log x))
        (Real.exp (γ * Real.log a) * (γ * a⁻¹)) a := by
    simpa only [Function.comp_apply] using hinner.exp
  have heq :
      (fun x : ℝ => Real.exp (γ * Real.log x)) =ᶠ[nhds a]
        (fun x => Real.rpow x γ) := by
    filter_upwards [Ioi_mem_nhds ha] with x hx
    change Real.exp (γ * Real.log x) = x ^ γ
    calc
      Real.exp (γ * Real.log x) = Real.exp (Real.log x * γ) := by
        congr 1
        ring
      _ = x ^ γ := (Real.rpow_def_of_pos hx γ).symm
  have hrpow :
      HasDerivAt (fun x : ℝ => Real.rpow x γ)
        (Real.exp (γ * Real.log a) * (γ * a⁻¹)) a :=
    hderiv.congr_of_eventuallyEq heq.symm
  rw [hasDerivAt_iff_tendsto_slope] at hrpow
  change
    Filter.Tendsto
      (fun x => (x - a)⁻¹ * (Real.rpow x γ - Real.rpow a γ))
      (nhdsWithin a ({a} : Set ℝ)ᶜ)
      (nhds (Real.exp (γ * Real.log a) * (γ * a⁻¹))) at hrpow
  simpa only [div_eq_mul_inv, mul_comm] using hrpow

theorem gap1 (a α β x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    original a α β x = scaled a α β x := by
  unfold original scaled
  change
    (x ^ α - a ^ α) / (x ^ β - a ^ β) =
      a ^ (α - β) *
        (((x / a) ^ α - 1) / ((x / a) ^ β - 1))
  have hpa (γ : ℝ) : a ^ γ ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha γ)
  have hdiv (γ : ℝ) :
      (x / a) ^ γ = x ^ γ / a ^ γ := by
    rw [Real.div_rpow hx.le ha.le]
  have hsub :
      a ^ (α - β) = a ^ α / a ^ β := by
    rw [Real.rpow_sub ha]
  rw [hdiv α, hdiv β, hsub]
  have hnum :
      x ^ α / a ^ α - 1 = (x ^ α - a ^ α) / a ^ α := by
    field_simp [hpa α] <;> ring
  have hden' :
      x ^ β / a ^ β - 1 = (x ^ β - a ^ β) / a ^ β := by
    field_simp [hpa β] <;> ring
  rw [hnum, hden']
  by_cases hden : x ^ β - a ^ β = 0
  · simp [hden]
  · field_simp [hpa α, hpa β, hden] <;> ring

/-- Exercise 548, gap 2; the displayed factorization also divides by `α`. -/
theorem gap2 (a α β x : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hxa : x ≠ a) (hα : α ≠ 0) (hβ : β ≠ 0) :
    original a α β x = exponentialForm a α β x := by
  rw [gap1 a α β x ha hx hxa]
  unfold scaled exponentialForm
  change
    a ^ (α - β) *
        (((x / a) ^ α - 1) / ((x / a) ^ β - 1)) =
      a ^ (α - β) *
          ((Real.exp (α * Real.log (x / a)) - 1) /
            (α * Real.log (x / a))) *
        ((β * Real.log (x / a)) /
          (Real.exp (β * Real.log (x / a)) - 1)) *
        (α / β)
  have hratio : 0 < x / a := div_pos hx ha
  have hlog : Real.log (x / a) ≠ 0 := by
    intro hz
    have hratio_one : x / a = 1 := by
      calc
        x / a = Real.exp (Real.log (x / a)) :=
          (Real.exp_log hratio).symm
        _ = Real.exp 0 := by rw [hz]
        _ = 1 := Real.exp_zero
    apply hxa
    calc
      x = (x / a) * a := by field_simp [ha.ne']
      _ = a := by rw [hratio_one]; ring
  have hrpow (γ : ℝ) :
      (x / a) ^ γ = Real.exp (γ * Real.log (x / a)) := by
    calc
      (x / a) ^ γ = Real.exp (Real.log (x / a) * γ) :=
        Real.rpow_def_of_pos hratio γ
      _ = Real.exp (γ * Real.log (x / a)) := by
        congr 1
        ring
  rw [hrpow α, hrpow β]
  have hβlog : β * Real.log (x / a) ≠ 0 :=
    mul_ne_zero hβ hlog
  have hEβ : Real.exp (β * Real.log (x / a)) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hβlog
    apply Real.exp_injective
    simpa using he
  field_simp [hα, hβ, hlog, hEβ] <;> ring

/-- Exercise 548, gap 3; replace the malformed `x→a` premise by the limit itself. -/
theorem gap3 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (fun x => Real.log (x / a)) a 0 := by
  unfold HasLimitAt
  have hdiv : ContinuousAt (fun x : ℝ => x / a) a :=
    continuousAt_id.div_const a
  have hle : nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a :=
    inf_le_left
  have hdivlim :
      Filter.Tendsto (fun x : ℝ => x / a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (1 : ℝ)) := by
    simpa [ha.ne'] using hdiv.tendsto.mono_left hle
  have hloglim :
      Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds 0) := by
    simpa using
      (Real.continuousAt_log
        (show (1 : ℝ) ≠ 0 from one_ne_zero)).tendsto
  simpa only [Function.comp_apply] using hloglim.comp hdivlim

/-- Exercise 548, gap 4. -/
theorem gap4 (a α β : ℝ) (ha : 0 < a) (hβ : β ≠ 0) :
    HasLimitAt (original a α β) a ((α / β) * Real.rpow a (α - β)) := by
  unfold HasLimitAt
  have hαlim := rpow_secant_tendsto a α ha
  have hβlim := rpow_secant_tendsto a β ha
  have hdβ :
      Real.exp (β * Real.log a) * (β * a⁻¹) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _)
      (mul_ne_zero hβ (inv_ne_zero ha.ne'))
  have hquot := hαlim.div hβlim hdβ
  have heq :
      (fun x => original a α β x) =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ]
        (fun x =>
          ((Real.rpow x α - Real.rpow a α) / (x - a)) /
            ((Real.rpow x β - Real.rpow a β) / (x - a))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x ≠ a := by simpa using hx
    have hsub : x - a ≠ 0 := sub_ne_zero.mpr hxa
    unfold original
    change
      (x ^ α - a ^ α) / (x ^ β - a ^ β) =
        ((x ^ α - a ^ α) / (x - a)) /
          ((x ^ β - a ^ β) / (x - a))
    by_cases hb : x ^ β - a ^ β = 0
    · simp [hb]
    · field_simp [hsub, hb] <;> ring
  have hvalue :
      (Real.exp (α * Real.log a) * (α * a⁻¹)) /
          (Real.exp (β * Real.log a) * (β * a⁻¹)) =
        (α / β) * Real.rpow a (α - β) := by
    change
      (Real.exp (α * Real.log a) * (α * a⁻¹)) /
          (Real.exp (β * Real.log a) * (β * a⁻¹)) =
        (α / β) * a ^ (α - β)
    have haexp (γ : ℝ) :
        Real.exp (γ * Real.log a) = a ^ γ := by
      calc
        Real.exp (γ * Real.log a) =
            Real.exp (Real.log a * γ) := by
          congr 1
          ring
        _ = a ^ γ := (Real.rpow_def_of_pos ha γ).symm
    have hpow (γ : ℝ) : a ^ γ ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos ha γ)
    have hsubpow : a ^ (α - β) = a ^ α / a ^ β := by
      rw [Real.rpow_sub ha]
    rw [haexp α, haexp β, hsubpow]
    field_simp [hβ, ha.ne', hpow α, hpow β] <;> ring
  rw [← hvalue]
  exact hquot.congr' heq.symm

end

end ProofGap.Exercise548
