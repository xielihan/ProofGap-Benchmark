import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1358

noncomputable section

def HasLimitAt (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

def target (a : ℝ) : ℝ := Real.rpow a a * (Real.log a - 1)
def f₀ (a x : ℝ) : ℝ :=
  (Real.rpow a x - Real.rpow x a) / (x - a)
def f₁ (a x : ℝ) : ℝ :=
  Real.rpow a x * Real.log a - a * Real.rpow x (a - 1)

private theorem f1_at_target (a : ℝ) (ha : 0 < a) :
    f₁ a a = target a := by
  unfold f₁ target
  change (a ^ a : ℝ) * Real.log a -
      a * (a ^ (a - 1) : ℝ) =
    (a ^ a : ℝ) * (Real.log a - 1)
  rw [Real.rpow_sub_one ha.ne']
  field_simp [ha.ne'] <;> ring

private theorem limit_f1 (a : ℝ) (ha : 0 < a) :
    HasLimitAt a (f₁ a) (target a) := by
  have hpow_const : ContinuousAt (fun x : ℝ => Real.rpow a x) a :=
    (Real.continuous_const_rpow ha.ne').continuousAt
  have hpow_var : ContinuousAt (fun x : ℝ => Real.rpow x (a - 1)) a :=
    (Real.hasDerivAt_rpow_const (x := a) (p := a - 1)
      (Or.inl ha.ne')).continuousAt
  have hcont : ContinuousAt (f₁ a) a := by
    unfold f₁
    exact (hpow_const.mul continuousAt_const).sub
      (continuousAt_const.mul hpow_var)
  unfold HasLimitAt
  rw [← f1_at_target a ha]
  exact hcont.tendsto.mono_left inf_le_left

private theorem limit_f0 (a : ℝ) (ha : 0 < a) :
    HasLimitAt a (f₀ a) (target a) := by
  let g : ℝ → ℝ := fun x => Real.rpow a x - Real.rpow x a
  have h₁ : HasDerivAt (fun x : ℝ => Real.rpow a x)
      (Real.rpow a a * Real.log a) a := by
    have hlin : HasDerivAt (fun x : ℝ => Real.log a * x) (Real.log a) a := by
      simpa using (hasDerivAt_id a).const_mul (Real.log a)
    simpa [Real.rpow_def_of_pos ha, Function.comp_def] using
      (Real.hasDerivAt_exp (Real.log a * a)).comp a hlin
  have h₂ : HasDerivAt (fun x : ℝ => Real.rpow x a)
      (a * Real.rpow a (a - 1)) a := by
    simpa using
      (Real.hasDerivAt_rpow_const (x := a) (p := a) (Or.inl ha.ne'))
  have hg : HasDerivAt g (target a) a := by
    rw [← f1_at_target a ha]
    simpa [g, f₁] using h₁.sub h₂
  have heq : slope g a = f₀ a := by
    funext x
    simp [slope, g, f₀, div_eq_mul_inv, mul_comm]
  unfold HasLimitAt
  rw [← heq]
  exact hg.tendsto_slope

theorem gap1 (a : ℝ) (ha : 0 < a) :
    HasLimitAt a (f₀ a) (target a) ↔ HasLimitAt a (f₁ a) (target a) := by
  constructor
  · intro _
    exact limit_f1 a ha
  · intro _
    exact limit_f0 a ha

theorem gap2 (a : ℝ) (ha : 0 < a) :
    HasLimitAt a (f₁ a) (target a) := by
  exact limit_f1 a ha

theorem gap3 (a : ℝ) (ha : 0 < a) :
    HasLimitAt a (f₀ a) (target a) := by
  exact limit_f0 a ha

end

end ProofGap.Exercise1358
