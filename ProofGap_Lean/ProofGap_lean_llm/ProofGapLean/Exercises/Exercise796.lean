import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise796

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x / x
def F (x : ℝ) : ℝ := if x = 0 then 1 else f x

theorem gap1 : Filter.Tendsto f (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hf : f = fun t : ℝ => t⁻¹ * Real.sin t := by
    funext t
    unfold f
    rw [div_eq_mul_inv, mul_comm]
  rw [hf]
  simpa using (Real.hasDerivAt_sin 0).tendsto_slope_zero
theorem gap2 : ContinuousOn F (Set.Icc 0 Real.pi) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases hx0 : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hlim⟩ :=
      (Metric.tendsto_nhdsWithin_nhds.mp gap1) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    by_cases hy0 : y = 0
    · subst y
      simpa using hε
    · have hyc : y ∈ ({0}ᶜ : Set ℝ) := by
        simpa using hy0
      simpa [F, hy0] using (@hlim y hyc hy)
  · have hf : ContinuousAt f x := by
      simpa [f] using
        Real.continuous_sin.continuousAt.div continuousAt_id hx0
    rw [Metric.continuousAt_iff] at hf ⊢
    intro ε hε
    obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
    refine ⟨min δ (dist x 0), lt_min hδ (dist_pos.mpr hx0), ?_⟩
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h
      subst y
      have hbad : dist 0 x < dist x 0 :=
        lt_of_lt_of_le hy (min_le_right _ _)
      rw [dist_comm 0 x] at hbad
      exact (lt_irrefl _ hbad)
    have hyδ : dist y x < δ :=
      lt_of_lt_of_le hy (min_le_left _ _)
    simpa [F, hx0, hy0] using (@hfδ y hyδ)
theorem gap3 : UniformContinuousOn F (Set.Icc 0 Real.pi) := by
  exact isCompact_Icc.uniformContinuousOn_of_continuous gap2
theorem gap4 : UniformContinuousOn f (Set.Ioo 0 Real.pi) := by
  have hF : UniformContinuousOn F (Set.Ioo 0 Real.pi) :=
    gap3.mono (by
      intro x hx
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  rw [Metric.uniformContinuousOn_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := hF ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  simpa [F, ne_of_gt hx.1, ne_of_gt hy.1] using
    hclose x hx y hy hxy
theorem gap5 : UniformContinuousOn f (Set.Ioo 0 Real.pi) := by
  exact gap4

end
end ProofGap.Exercise796
