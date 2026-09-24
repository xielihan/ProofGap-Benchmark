import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1255

noncomputable section

def BoundedOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, |u x| ≤ M

private lemma exists_mvt_abs (f : ℝ → ℝ) (a b x₁ x₂ : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (hne : x₁ ≠ x₂) :
    ∃ ξ ∈ Set.Ioo (min x₁ x₂) (max x₁ x₂),
      |f x₁ - f x₂| = |x₁ - x₂| * |deriv f ξ| := by
  have huv : min x₁ x₂ < max x₁ x₂ := min_lt_max.mpr hne
  have hseg :
      Set.Icc (min x₁ x₂) (max x₁ x₂) ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨(lt_min hx₁.1 hx₂.1).trans_le hx.1,
      hx.2.trans_lt (max_lt hx₁.2 hx₂.2)⟩
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_deriv_eq_slope f huv
      (hf.continuousOn.mono hseg)
      (hf.mono (Set.Ioo_subset_Icc_self.trans hseg))
  have hden : max x₁ x₂ - min x₁ x₂ ≠ 0 :=
    sub_ne_zero.mpr huv.ne'
  have heq :
      f (max x₁ x₂) - f (min x₁ x₂) =
        deriv f ξ * (max x₁ x₂ - min x₁ x₂) := by
    exact (div_eq_iff hden).mp hslope.symm
  refine ⟨ξ, hξ, ?_⟩
  rcases le_total x₁ x₂ with h12 | h21
  · rw [min_eq_left h12, max_eq_right h12] at heq
    rw [abs_sub_comm (f x₁), heq, abs_mul,
      abs_sub_comm x₁ x₂]
    ring
  · rw [min_eq_right h21, max_eq_left h21] at heq
    rw [heq, abs_mul]
    ring

theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ M, ∀ x ∈ Set.Ioo a b, |deriv f x| ≤ M := by
  exact hbd

theorem gap2 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ δ > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ → x₁ ≠ x₂ →
      ∃ ξ ∈ Set.Ioo (min x₁ x₂) (max x₁ x₂),
        |f x₁ - f x₂| = |x₁ - x₂| * |deriv f ξ| := by
  refine ⟨1, by norm_num, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist hne
  exact exists_mvt_abs f a b x₁ x₂ hf hx₁ hx₂ hne

theorem gap3 (f : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ M, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |f x₁ - f x₂| ≤ M * |x₁ - x₂| := by
  rcases gap1 f a b hbd with ⟨M, hM⟩
  refine ⟨max M 0, ?_⟩
  intro x₁ hx₁ x₂ hx₂
  by_cases hne : x₁ = x₂
  · subst x₂
    simp
  · rcases exists_mvt_abs f a b x₁ x₂ hf hx₁ hx₂ hne with
      ⟨ξ, hξ, heq⟩
    have hξab : ξ ∈ Set.Ioo a b := by
      exact ⟨(lt_min hx₁.1 hx₂.1).trans hξ.1,
        hξ.2.trans (max_lt hx₁.2 hx₂.2)⟩
    rw [heq]
    calc
      |x₁ - x₂| * |deriv f ξ| ≤ |x₁ - x₂| * M :=
        mul_le_mul_of_nonneg_left (hM ξ hξab) (abs_nonneg _)
      _ ≤ |x₁ - x₂| * max M 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _)
      _ = max M 0 * |x₁ - x₂| := by ring

theorem gap4 (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₁ x₂ : ℝ, |x₁ - x₂| < δ →
      M * |x₁ - x₂| < ε := by
  refine ⟨ε / M, div_pos hε hM, ?_⟩
  intro x₁ x₂ hdist
  calc
    M * |x₁ - x₂| < M * (ε / M) :=
      mul_lt_mul_of_pos_left hdist hM
    _ = ε := by field_simp [ne_of_gt hM]

theorem gap5 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    ∃ δ > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ → |f x₁ - f x₂| < ε := by
  rcases gap3 f a b hf hbd with ⟨M, hLip⟩
  have hMpos : 0 < max M 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  rcases gap4 (max M 1) ε hMpos hε with ⟨δ, hδ, hsmall⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  calc
    |f x₁ - f x₂| ≤ M * |x₁ - x₂| := hLip x₁ hx₁ x₂ hx₂
    _ ≤ max M 1 * |x₁ - x₂| :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
    _ < ε := hsmall x₁ x₂ hdist

theorem gap6 (f : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    UniformContinuousOn f (Set.Ioo a b) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  rcases gap5 f a b ε hε hf hbd with ⟨δ, hδ, hsmall⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  simpa only [Real.dist_eq] using
    hsmall x₁ hx₁ x₂ hx₂ (by simpa only [Real.dist_eq] using hdist)

theorem gap7 (f : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hbd : BoundedOn (deriv f) (Set.Ioo a b)) :
    UniformContinuousOn f (Set.Ioo a b) := by
  exact gap6 f a b hf hbd

end

end ProofGap.Exercise1255
