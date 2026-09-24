import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1253

noncomputable section

def g (x : ℝ) : ℝ := 1 / x
def F (f : ℝ → ℝ) (x : ℝ) : ℝ := f x / x

theorem gap1 (x₁ x₂ : ℝ) (hprod : x₁ * x₂ > 0) :
    0 ∉ Set.Icc x₁ x₂ := by
  rintro ⟨hx₁, hx₂⟩
  nlinarith

theorem gap2 (x₁ x₂ : ℝ) (hprod : x₁ * x₂ > 0) :
    DifferentiableOn ℝ g (Set.Icc x₁ x₂) := by
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hzero
    exact gap1 x₁ x₂ hprod (hzero ▸ hx)
  have hinv : DifferentiableAt ℝ (fun y : ℝ => y⁻¹) x :=
    differentiableAt_inv hx0
  rw [show g = fun y : ℝ => y⁻¹ by
    funext y
    simp [g, one_div]]
  exact hinv.differentiableWithinAt

theorem gap3 (f : ℝ → ℝ) (x₁ x₂ : ℝ) (hprod : x₁ * x₂ > 0)
    (hf : DifferentiableOn ℝ f (Set.Icc x₁ x₂)) :
    DifferentiableOn ℝ (F f) (Set.Icc x₁ x₂) := by
  have hmul := hf.mul (gap2 x₁ x₂ hprod)
  rw [show F f = f * g by
    funext x
    simp [F, g, div_eq_mul_inv, one_div]]
  exact hmul

theorem gap4 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f x) :
    deriv g x ^ 2 + deriv (F f) x ^ 2 =
      1 / x ^ 4 * (1 + (x * deriv f x - f x) ^ 2) := by
  have hgfun : g = fun y : ℝ => y⁻¹ := by
    funext y
    simp [g, one_div]
  have hg : deriv g x = -(1 / x ^ 2) := by
    rw [hgfun, deriv_inv]
    simp [one_div]
  have hF :
      deriv (F f) x = (x * deriv f x - f x) / x ^ 2 := by
    have hd := hf.hasDerivAt.div (hasDerivAt_id x) hx
    convert hd.deriv using 1 <;> simp [F] <;> ring
  rw [hg, hF]
  field_simp [hx]

theorem gap5 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    1 / x ^ 4 * (1 + (x * deriv f x - f x) ^ 2) ≠ 0 := by
  apply mul_ne_zero
  · exact one_div_ne_zero (pow_ne_zero 4 hx)
  · positivity

theorem gap6 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f x) :
    deriv g x ^ 2 + deriv (F f) x ^ 2 ≠ 0 := by
  rw [gap4 f x hx hf]
  exact gap5 f x hx

theorem gap7 (x₁ x₂ : ℝ) (hprod : x₁ * x₂ > 0) (horder : x₁ < x₂) :
    g x₁ ≠ g x₂ := by
  have hp0 : x₁ * x₂ ≠ 0 := ne_of_gt hprod
  have hx₁ : x₁ ≠ 0 := fun h => hp0 (by simp [h])
  have hx₂ : x₂ ≠ 0 := fun h => hp0 (by simp [h])
  intro heq
  unfold g at heq
  field_simp [hx₁, hx₂] at heq
  linarith

theorem gap8 (f : ℝ → ℝ) (x₁ x₂ : ℝ) (hprod : x₁ * x₂ > 0)
    (horder : x₁ < x₂) (hf : DifferentiableOn ℝ f (Set.Icc x₁ x₂)) :
    ∃ ξ ∈ Set.Ioo x₁ x₂,
      (F f x₂ - F f x₁) / (g x₂ - g x₁) =
        deriv (F f) ξ / deriv g ξ := by
  have hF := gap3 f x₁ x₂ hprod hf
  have hg := gap2 x₁ x₂ hprod
  obtain ⟨ξ, hξ, hcross⟩ :=
    exists_ratio_deriv_eq_ratio_slope
      (f := F f) (g := g) horder hF.continuousOn
      (hF.mono Set.Ioo_subset_Icc_self) hg.continuousOn
      (hg.mono Set.Ioo_subset_Icc_self)
  have hξ0 : ξ ≠ 0 := by
    intro hz
    exact gap1 x₁ x₂ hprod
      (hz ▸ ⟨hξ.1.le, hξ.2.le⟩)
  have hgfun : g = fun y : ℝ => y⁻¹ := by
    funext y
    simp [g, one_div]
  have hdg : deriv g ξ ≠ 0 := by
    rw [hgfun, deriv_inv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hξ0))
  refine ⟨ξ, hξ, ?_⟩
  rw [div_eq_div_iff
    (sub_ne_zero.mpr (gap7 x₁ x₂ hprod horder).symm) hdg]
  simpa [mul_comm] using hcross.symm

theorem gap9 (f : ℝ → ℝ) (x₁ x₂ ξ : ℝ)
    (hprod : x₁ * x₂ > 0) (hξ : ξ ∈ Set.Ioo x₁ x₂)
    (hf : DifferentiableAt ℝ f ξ)
    (hratio :
      (F f x₂ - F f x₁) / (g x₂ - g x₁) =
        deriv (F f) ξ / deriv g ξ) :
    (f x₂ / x₂ - f x₁ / x₁) / (1 / x₂ - 1 / x₁) =
      ((ξ * deriv f ξ - f ξ) / ξ ^ 2) / (-(1 / ξ ^ 2)) := by
  have hξ0 : ξ ≠ 0 := by
    intro hz
    exact gap1 x₁ x₂ hprod
      (hz ▸ ⟨hξ.1.le, hξ.2.le⟩)
  have hF :
      deriv (F f) ξ = (ξ * deriv f ξ - f ξ) / ξ ^ 2 := by
    have hd := hf.hasDerivAt.div (hasDerivAt_id ξ) hξ0
    convert hd.deriv using 1 <;> simp [F] <;> ring
  have hgfun : g = fun y : ℝ => y⁻¹ := by
    funext y
    simp [g, one_div]
  have hg : deriv g ξ = -(1 / ξ ^ 2) := by
    rw [hgfun, deriv_inv]
    simp [one_div]
  rw [hF, hg] at hratio
  simpa [F, g] using hratio

theorem gap10 (f : ℝ → ℝ) (x₁ x₂ ξ : ℝ)
    (hprod : x₁ * x₂ > 0) (horder : x₁ < x₂) (hξ : ξ ∈ Set.Ioo x₁ x₂)
    (hf : DifferentiableAt ℝ f ξ)
    (hratio :
      (F f x₂ - F f x₁) / (g x₂ - g x₁) =
        deriv (F f) ξ / deriv g ξ) :
    (x₁ * f x₂ - x₂ * f x₁) / (x₁ - x₂) =
      f ξ - ξ * deriv f ξ := by
  have hp0 : x₁ * x₂ ≠ 0 := ne_of_gt hprod
  have hx₁ : x₁ ≠ 0 := fun h => hp0 (by simp [h])
  have hx₂ : x₂ ≠ 0 := fun h => hp0 (by simp [h])
  have hx₁x₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr horder.ne
  have hξ0 : ξ ≠ 0 := by
    intro hz
    exact gap1 x₁ x₂ hprod
      (hz ▸ ⟨hξ.1.le, hξ.2.le⟩)
  calc
    (x₁ * f x₂ - x₂ * f x₁) / (x₁ - x₂) =
        (f x₂ / x₂ - f x₁ / x₁) / (1 / x₂ - 1 / x₁) := by
      field_simp [hx₁, hx₂, hx₁x₂]
    _ = ((ξ * deriv f ξ - f ξ) / ξ ^ 2) / (-(1 / ξ ^ 2)) :=
      gap9 f x₁ x₂ ξ hprod hξ hf hratio
    _ = f ξ - ξ * deriv f ξ := by
      field_simp [hξ0]
      ring

theorem gap11 (f : ℝ → ℝ) (x₁ x₂ : ℝ) (hprod : x₁ * x₂ > 0)
    (horder : x₁ < x₂) (hf : DifferentiableOn ℝ f (Set.Icc x₁ x₂)) :
    ∃ ξ ∈ Set.Ioo x₁ x₂,
      (x₁ * f x₂ - x₂ * f x₁) / (x₁ - x₂) =
        f ξ - ξ * deriv f ξ := by
  rcases gap8 f x₁ x₂ hprod horder hf with ⟨ξ, hξ, hratio⟩
  have hp0 : x₁ * x₂ ≠ 0 := ne_of_gt hprod
  have hx₁ : x₁ ≠ 0 := fun h => hp0 (by simp [h])
  have hx₂ : x₂ ≠ 0 := fun h => hp0 (by simp [h])
  have hx₁x₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr horder.ne
  have hξ0 : ξ ≠ 0 := by
    intro hz
    exact gap1 x₁ x₂ hprod
      (hz ▸ ⟨hξ.1.le, hξ.2.le⟩)
  have hF :
      deriv (F f) ξ = (ξ * deriv f ξ - f ξ) / ξ ^ 2 := by
    have hfξ : DifferentiableAt ℝ f ξ :=
      hf.differentiableAt (Filter.mem_of_superset
        (IsOpen.mem_nhds isOpen_Ioo hξ) Set.Ioo_subset_Icc_self)
    have hd := hfξ.hasDerivAt.div (hasDerivAt_id ξ) hξ0
    convert hd.deriv using 1 <;> simp [F] <;> ring
  have hgfun : g = fun y : ℝ => y⁻¹ := by
    funext y
    simp [g, one_div]
  have hg : deriv g ξ = -(1 / ξ ^ 2) := by
    rw [hgfun, deriv_inv]
    simp [one_div]
  refine ⟨ξ, hξ, ?_⟩
  calc
    (x₁ * f x₂ - x₂ * f x₁) / (x₁ - x₂) =
        (F f x₂ - F f x₁) / (g x₂ - g x₁) := by
      unfold F g
      field_simp [hx₁, hx₂, hx₁x₂]
    _ = deriv (F f) ξ / deriv g ξ := hratio
    _ = f ξ - ξ * deriv f ξ := by
      rw [hF, hg]
      field_simp [hξ0]
      ring

end

end ProofGap.Exercise1253
