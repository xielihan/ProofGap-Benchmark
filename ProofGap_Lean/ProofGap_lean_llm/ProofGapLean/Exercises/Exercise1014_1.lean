import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace ProofGap.Exercise1014_1

noncomputable section

open scoped Topology

def differenceQuotient (f : ℝ → ℝ) (x₀ h : ℝ) : ℝ :=
  (f (x₀ + h) - f x₀) / h

def puncturedZero : Filter ℝ := 𝓝[({0} : Set ℝ)ᶜ] 0

theorem gap1 (f g : ℝ → ℝ) (x₀ h : ℝ) (hh : h ≠ 0) :
    differenceQuotient (fun x => f x + g x) x₀ h =
      differenceQuotient f x₀ h + differenceQuotient g x₀ h := by
  unfold differenceQuotient
  field_simp [hh]
  ring

theorem gap2 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableAt ℝ f x₀) :
    ∃ L : ℝ, Tendsto (differenceQuotient f x₀) puncturedZero (𝓝 L) := by
  refine ⟨deriv f x₀, ?_⟩
  simpa [differenceQuotient, puncturedZero, div_eq_mul_inv, smul_eq_mul,
    mul_comm] using hf.hasDerivAt.tendsto_slope_zero

theorem gap3 (g : ℝ → ℝ) (x₀ : ℝ)
    (hg : ¬ DifferentiableAt ℝ g x₀) :
    ¬ ∃ L : ℝ, Tendsto (differenceQuotient g x₀) puncturedZero (𝓝 L) := by
  rintro ⟨L, hL⟩
  apply hg
  have hd : HasDerivAt g L x₀ := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simpa [differenceQuotient, puncturedZero, div_eq_mul_inv, smul_eq_mul,
      mul_comm] using hL
  exact hd.differentiableAt

theorem gap4 (F : ℝ → ℝ) (x₀ : ℝ)
    (hF : DifferentiableAt ℝ F x₀) :
    ∃ L : ℝ, Tendsto (differenceQuotient F x₀) puncturedZero (𝓝 L) := by
  exact gap2 F x₀ hF

theorem gap5 (f g F : ℝ → ℝ) (x₀ h : ℝ)
    (hF : ∀ x, F x = f x + g x) (hh : h ≠ 0) :
    differenceQuotient g x₀ h =
      differenceQuotient F x₀ h - differenceQuotient f x₀ h := by
  unfold differenceQuotient
  rw [hF (x₀ + h), hF x₀]
  field_simp [hh]
  ring

theorem gap6 (f g F : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableAt ℝ f x₀)
    (hFdef : ∀ x, F x = f x + g x)
    (hF : DifferentiableAt ℝ F x₀) :
    ∃ L : ℝ, Tendsto (differenceQuotient g x₀) puncturedZero (𝓝 L) := by
  rcases gap2 f x₀ hf with ⟨Lf, hfL⟩
  rcases gap4 F x₀ hF with ⟨LF, hFL⟩
  refine ⟨LF - Lf, ?_⟩
  apply (hFL.sub hfL).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa [puncturedZero] using hh
  exact (gap5 f g F x₀ h hFdef hh0).symm

theorem gap7 (f g F : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableAt ℝ f x₀)
    (hg : ¬ DifferentiableAt ℝ g x₀)
    (hFdef : ∀ x, F x = f x + g x)
    (hF : DifferentiableAt ℝ F x₀) : False := by
  exact (gap3 g x₀ hg) (gap6 f g F x₀ hf hFdef hF)

theorem gap8 (f g F : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableAt ℝ f x₀)
    (hg : ¬ DifferentiableAt ℝ g x₀)
    (hFdef : ∀ x, F x = f x + g x) :
    ¬ DifferentiableAt ℝ F x₀ := by
  intro hF
  exact gap7 f g F x₀ hf hg hFdef hF

theorem gap9 (f g : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableAt ℝ f x₀)
    (hg : ¬ DifferentiableAt ℝ g x₀) :
    ¬ DifferentiableAt ℝ (fun x => f x + g x) x₀ := by
  exact gap8 f g (fun x => f x + g x) x₀ hf hg (fun _ => rfl)

end

end ProofGap.Exercise1014_1
