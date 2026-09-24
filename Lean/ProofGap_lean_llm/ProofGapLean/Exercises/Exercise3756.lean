import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3756

noncomputable section

open MeasureTheory

def dampedSine (α x : ℝ) : ℝ :=
  Real.exp (-α * x) * Real.sin x

def tail (α A : ℝ) : ℝ :=
  ∫ x in Set.Ioi A, dampedSine α x

def UniformTail (α₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ < A →
      ∀ α : ℝ, α₀ ≤ α → |tail α A| < ε

theorem gap1 (α₀ α x : ℝ) (hα₀ : 0 < α₀)
    (hα : α₀ ≤ α) (hx : 0 ≤ x) :
    |dampedSine α x| ≤ Real.exp (-α₀ * x) := by
  unfold dampedSine
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hsin : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  have hexp : Real.exp (-α * x) ≤ Real.exp (-α₀ * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    Real.exp (-α * x) * |Real.sin x| ≤
        Real.exp (-α * x) * 1 :=
      mul_le_mul_of_nonneg_left hsin (Real.exp_pos _).le
    _ ≤ Real.exp (-α₀ * x) := by simpa using hexp

theorem gap2 (α₀ : ℝ) (hα₀ : 0 < α₀) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-α₀ * x)) =
      1 / α₀ := by
  rw [integral_exp_mul_Ioi (a := -α₀) (by linarith) (0 : ℝ)]
  simp

theorem gap3 (α₀ : ℝ) (hα₀ : 0 < α₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℝ, ∀ A : ℝ, A₀ < A →
        ∀ α : ℝ, α₀ ≤ α → |tail α A| < ε := by
  intro ε hε
  let A₀ : ℝ := max 0 (-Real.log (ε * α₀) / α₀)
  refine ⟨A₀, ?_⟩
  intro A hA α hα
  have hApos : 0 < A :=
    lt_of_le_of_lt (le_max_left 0 (-Real.log (ε * α₀) / α₀)) hA
  have hmajorant :
      IntegrableOn (fun x : ℝ => Real.exp (-α₀ * x)) (Set.Ioi A) := by
    simpa using
      (integrableOn_exp_mul_Ioi (a := -α₀) (by linarith) A)
  have hbound :
      |tail α A| ≤
        ∫ x in Set.Ioi A, Real.exp (-α₀ * x) := by
    unfold tail
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le
        (f := dampedSine α)
        (g := fun x : ℝ => Real.exp (-α₀ * x))
        (μ := volume.restrict (Set.Ioi A))
        hmajorant
        ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => by
          simpa only [Real.norm_eq_abs] using
            gap1 α₀ α x hα₀ hα (le_of_lt (hApos.trans hx))))
  have hintegral :
      (∫ x in Set.Ioi A, Real.exp (-α₀ * x)) =
        Real.exp (-α₀ * A) / α₀ := by
    rw [integral_exp_mul_Ioi (a := -α₀) (by linarith) A]
    ring
  have hthreshold : -Real.log (ε * α₀) / α₀ < A :=
    lt_of_le_of_lt
      (le_max_right 0 (-Real.log (ε * α₀) / α₀)) hA
  have hloglt : -Real.log (ε * α₀) < A * α₀ :=
    (div_lt_iff₀ hα₀).mp hthreshold
  have hexponent : -α₀ * A < Real.log (ε * α₀) := by
    nlinarith
  have hprod : 0 < ε * α₀ := mul_pos hε hα₀
  have hexplt : Real.exp (-α₀ * A) < ε * α₀ := by
    calc
      Real.exp (-α₀ * A) <
          Real.exp (Real.log (ε * α₀)) :=
        Real.exp_lt_exp.mpr hexponent
      _ = ε * α₀ := Real.exp_log hprod
  have hquot : Real.exp (-α₀ * A) / α₀ < ε :=
    (div_lt_iff₀ hα₀).mpr hexplt
  rw [hintegral] at hbound
  exact hbound.trans_lt hquot

theorem gap4 (α₀ : ℝ) (hα₀ : 0 < α₀) :
    UniformTail α₀ := by
  exact gap3 α₀ hα₀

end

end ProofGap.Exercise3756
