import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise697

noncomputable section

def y (x : ℝ) : ℝ := Real.sqrt x * Real.arctan (1 / x)

/-- The source regards `sqrt(x) * arctan(1/x)` as a partial formula on
`(0,∞)`.  A singular endpoint is therefore a boundary point omitted from
that domain, rather than a discontinuity of Lean's totalized functions. -/
def SingularPoint (_f : ℝ → ℝ) (a : ℝ) : Prop :=
  a ∉ Set.Ioi (0 : ℝ) ∧ a ∈ closure (Set.Ioi (0 : ℝ))

/-- Exercise 697, gap 1; bind the right-hand endpoint. -/
theorem gap1 :
    Filter.Tendsto y (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont :
      Continuous (fun x : ℝ =>
        Real.sqrt x * (Real.pi / 2 - Real.arctan x)) :=
    Real.continuous_sqrt.mul
      (continuous_const.sub Real.continuous_arctan)
  have hlim :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt x * (Real.pi / 2 - Real.arctan x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      (hcont.tendsto (0 : ℝ)).mono_left inf_le_left
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Set.mem_Ioi] at hx
  simp [y, one_div, Real.arctan_inv_of_pos hx]

/-- Exercise 697, gap 2; interpret singularity relative to
the original partial domain rather than Lean's totalized `sqrt` and division. -/
theorem gap2 : SingularPoint y 0 := by
  simp [SingularPoint, closure_Ioi]

/-- Exercise 697, gap 3; state existence of the finite
right-hand limit without a free singular-point guard. -/
theorem gap3 :
    ∃ L : ℝ, Filter.Tendsto y (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  exact ⟨0, gap1⟩

/-- Exercise 697, gap 4. -/
theorem gap4 (x : ℝ) (hx : x ∈ ({0} : Set ℝ)) :
    SingularPoint y x := by
  have hx0 : x = 0 := by
    simpa using hx
  subst x
  exact gap2

end

end ProofGap.Exercise697
