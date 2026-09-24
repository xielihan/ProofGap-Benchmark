import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1259

noncomputable section

theorem gap1 (f : ℝ → ℝ) (a b x₀ x : ℝ) (hab : a < b)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hx : x ∈ Set.Ioo a b)
    (hxne : x ≠ x₀)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo (min x x₀) (max x x₀),
      f x - f x₀ = deriv f c * (x - x₀) := by
  have huv : min x x₀ < max x x₀ := min_lt_max.mpr hxne
  have hseg :
      Set.Icc (min x x₀) (max x x₀) ⊆ Set.Ioo a b := by
    intro y hy
    exact ⟨(lt_min hx.1 hx₀.1).trans_le hy.1,
      hy.2.trans_lt (max_lt hx.2 hx₀.2)⟩
  obtain ⟨c, hc, hslope⟩ :=
    exists_deriv_eq_slope f huv
      (hf.continuousOn.mono hseg)
      (hf.mono (Set.Ioo_subset_Icc_self.trans hseg))
  have hden : max x x₀ - min x x₀ ≠ 0 :=
    sub_ne_zero.mpr huv.ne'
  have heq :
      f (max x x₀) - f (min x x₀) =
        deriv f c * (max x x₀ - min x x₀) :=
    (div_eq_iff hden).mp hslope.symm
  refine ⟨c, hc, ?_⟩
  rcases le_total x x₀ with h | h
  · rw [min_eq_left h, max_eq_right h] at heq
    linarith
  · rw [min_eq_right h, max_eq_left h] at heq
    exact heq

theorem gap2 (f : ℝ → ℝ) (a b x₀ x : ℝ) (hab : a < b)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hx : x ∈ Set.Ioo a b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, c ∈ Set.Icc (min x x₀) (max x x₀) := by
  exact ⟨x₀, hx₀, min_le_right _ _, le_max_right _ _⟩

theorem gap3 (f : ℝ → ℝ) (a b x₀ x : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hx : x ∈ Set.Ioo a b)
    (hzero : ∀ z ∈ Set.Ioo a b, deriv f z = 0) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  exact ⟨x₀, hx₀, hzero x₀ hx₀⟩

theorem gap4 (f : ℝ → ℝ) (a b x₀ x : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hx : x ∈ Set.Ioo a b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hzero : ∀ z ∈ Set.Ioo a b, deriv f z = 0) :
    f x - f x₀ = 0 := by
  by_cases hxeq : x = x₀
  · subst x
    simp
  · have hab : a < b := hx₀.1.trans hx₀.2
    rcases gap1 f a b x₀ x hab hx₀ hx hxeq hf with
      ⟨c, hc, heq⟩
    have hcab : c ∈ Set.Ioo a b := by
      exact ⟨(lt_min hx.1 hx₀.1).trans hc.1,
        hc.2.trans (max_lt hx.2 hx₀.2)⟩
    rw [heq, hzero c hcab, zero_mul]

theorem gap5 (f : ℝ → ℝ) (a b x₀ x : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hx : x ∈ Set.Ioo a b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hzero : ∀ z ∈ Set.Ioo a b, deriv f z = 0) :
    f x = f x₀ := by
  exact sub_eq_zero.mp (gap4 f a b x₀ x hx₀ hx hf hzero)

theorem gap6 (f : ℝ → ℝ) (a b x₀ : ℝ) (hab : a < b)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hzero : ∀ z ∈ Set.Ioo a b, deriv f z = 0) :
    ∃ C, ∀ x ∈ Set.Ioo a b, f x = C := by
  refine ⟨f x₀, ?_⟩
  intro x hx
  exact gap5 f a b x₀ x hx₀ hx hf hzero

theorem gap7 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hzero : ∀ z ∈ Set.Ioo a b, deriv f z = 0) :
    ∃ C, ∀ x ∈ Set.Ioo a b, f x = C := by
  have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
    constructor <;> linarith
  exact gap6 f a b ((a + b) / 2) hab hmid hf hzero

end

end ProofGap.Exercise1259
