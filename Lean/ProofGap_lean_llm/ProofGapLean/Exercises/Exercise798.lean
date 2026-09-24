import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise798

noncomputable section

def f (x : ℝ) : ℝ := Real.arctan x

/-- Exercise 798, gap 1. -/
private theorem uniformContinuousOn_rays_of_continuousOn_of_tendsto
    (g : ℝ → ℝ) (a b Ltop Lbot : ℝ)
    (hplus : ContinuousOn g (Set.Ici a))
    (hminus : ContinuousOn g (Set.Iic b))
    (htop : Filter.Tendsto g Filter.atTop (nhds Ltop))
    (hbot : Filter.Tendsto g Filter.atBot (nhds Lbot)) :
    UniformContinuousOn g (Set.Ici a) ∧
      UniformContinuousOn g (Set.Iic b) := by
  constructor
  · rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    have he : ∀ᶠ x in Filter.atTop, dist (g x) Ltop < ε / 2 :=
      (Metric.tendsto_nhds.1 htop) (ε / 2) (half_pos hε)
    obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 he
    let B : ℝ := max A a + 1
    have hAB : A + 1 ≤ B := by
      dsimp [B]
      linarith [le_max_left A a]
    have huc : UniformContinuousOn g (Set.Icc a B) :=
      isCompact_Icc.uniformContinuousOn_of_continuous
        (hplus.mono (fun _ hx => hx.1))
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨d, hd, hdu⟩ := huc ε hε
    refine ⟨min d 1, lt_min hd zero_lt_one, ?_⟩
    intro x hx y hy hxy
    have hxyd : dist x y < d := lt_of_lt_of_le hxy (min_le_left d 1)
    have hxy1 : dist x y < 1 := lt_of_lt_of_le hxy (min_le_right d 1)
    by_cases hboth : x ≤ B ∧ y ≤ B
    · exact hdu x ⟨hx, hboth.1⟩ y ⟨hy, hboth.2⟩ hxyd
    · have hout : B < x ∨ B < y := by
        by_cases hxB : x ≤ B
        · right
          exact lt_of_not_ge (fun hyB => hboth ⟨hxB, hyB⟩)
        · left
          exact lt_of_not_ge hxB
      rw [Real.dist_eq] at hxy1
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hxy1
      have hxA : A ≤ x := by
        rcases hout with hxout | hyout
        · linarith
        · linarith
      have hyA : A ≤ y := by
        rcases hout with hxout | hyout
        · linarith
        · linarith
      calc
        dist (g x) (g y) ≤ dist (g x) Ltop + dist Ltop (g y) :=
          dist_triangle (g x) Ltop (g y)
        _ = dist (g x) Ltop + dist (g y) Ltop := by
          rw [dist_comm Ltop (g y)]
        _ < ε / 2 + ε / 2 := add_lt_add (hA x hxA) (hA y hyA)
        _ = ε := by linarith
  · rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    have he : ∀ᶠ x in Filter.atBot, dist (g x) Lbot < ε / 2 :=
      (Metric.tendsto_nhds.1 hbot) (ε / 2) (half_pos hε)
    obtain ⟨A, hA⟩ := Filter.eventually_atBot.1 he
    let C : ℝ := min A b - 1
    have hCA : C + 1 ≤ A := by
      dsimp [C]
      linarith [min_le_left A b]
    have huc : UniformContinuousOn g (Set.Icc C b) :=
      isCompact_Icc.uniformContinuousOn_of_continuous
        (hminus.mono (fun _ hx => hx.2))
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨d, hd, hdu⟩ := huc ε hε
    refine ⟨min d 1, lt_min hd zero_lt_one, ?_⟩
    intro x hx y hy hxy
    have hxyd : dist x y < d := lt_of_lt_of_le hxy (min_le_left d 1)
    have hxy1 : dist x y < 1 := lt_of_lt_of_le hxy (min_le_right d 1)
    by_cases hboth : C ≤ x ∧ C ≤ y
    · exact hdu x ⟨hboth.1, hx⟩ y ⟨hboth.2, hy⟩ hxyd
    · have hout : x < C ∨ y < C := by
        by_cases hxC : C ≤ x
        · right
          exact lt_of_not_ge (fun hyC => hboth ⟨hxC, hyC⟩)
        · left
          exact lt_of_not_ge hxC
      rw [Real.dist_eq] at hxy1
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hxy1
      have hxA : x ≤ A := by
        rcases hout with hxout | hyout
        · linarith
        · linarith
      have hyA : y ≤ A := by
        rcases hout with hxout | hyout
        · linarith
        · linarith
      calc
        dist (g x) (g y) ≤ dist (g x) Lbot + dist Lbot (g y) :=
          dist_triangle (g x) Lbot (g y)
        _ = dist (g x) Lbot + dist (g y) Lbot := by
          rw [dist_comm Lbot (g y)]
        _ < ε / 2 + ε / 2 := add_lt_add (hA x hxA) (hA y hyA)
        _ = ε := by linarith

theorem gap1 : ContinuousOn f (Set.Iic 1) := by
  simpa [f] using Real.continuous_arctan.continuousOn

/-- Exercise 798, gap 2. -/
theorem gap2 : ContinuousOn f (Set.Ici 0) := by
  simpa [f] using Real.continuous_arctan.continuousOn

/-- Exercise 798, gap 3. -/
theorem gap3 : Filter.Tendsto f Filter.atTop (nhds (Real.pi / 2)) := by
  change Filter.map Real.arctan Filter.atTop ≤ nhds (Real.pi / 2)
  exact le_trans Real.tendsto_arctan_atTop inf_le_left

/-- Exercise 798, gap 4. -/
theorem gap4 : Filter.Tendsto f Filter.atBot (nhds (-Real.pi / 2)) := by
  change Filter.map Real.arctan Filter.atBot ≤ nhds (-Real.pi / 2)
  rw [neg_div]
  exact le_trans Real.tendsto_arctan_atBot inf_le_left

/-- Exercise 798, gap 5. -/
theorem gap5 : UniformContinuousOn f (Set.Ici 0) := by
  exact (uniformContinuousOn_rays_of_continuousOn_of_tendsto
    f 0 1 (Real.pi / 2) (-Real.pi / 2) gap2 gap1 gap3 gap4).1

/-- Exercise 798, gap 6. -/
theorem gap6 : UniformContinuousOn f (Set.Iic 1) := by
  exact (uniformContinuousOn_rays_of_continuousOn_of_tendsto
    f 0 1 (Real.pi / 2) (-Real.pi / 2) gap2 gap1 gap3 gap4).2

/-- Exercise 798, gap 7; remove the function-valued `δ₁(ε)` shadowing. -/
theorem gap7 :
    ∀ ε > 0, ∃ δ₁ > 0, ∀ x₁ ∈ Set.Iic (1 : ℝ), ∀ x₂ ∈ Set.Iic (1 : ℝ),
      |x₁ - x₂| < δ₁ → |f x₁ - f x₂| < ε := by
  simpa only [Metric.uniformContinuousOn_iff, Real.dist_eq] using gap6

/-- Exercise 798, gap 8; remove the function-valued `δ₂(ε)` shadowing. -/
theorem gap8 :
    ∀ ε > 0, ∃ δ₂ > 0, ∀ x₁ ∈ Set.Ici (0 : ℝ), ∀ x₂ ∈ Set.Ici (0 : ℝ),
      |x₁ - x₂| < δ₂ → |f x₁ - f x₂| < ε := by
  simpa only [Metric.uniformContinuousOn_iff, Real.dist_eq] using gap5

/-- Exercise 798, gap 9; move `δ` under `ε` and make it small enough for the overlap argument. -/
theorem gap9 :
    ∀ ε > 0, ∃ δ > 0, δ ≤ 1 ∧ ∀ x₁ x₂ : ℝ, |x₁ - x₂| < δ →
      (x₁ ∈ Set.Iic (1 : ℝ) ∧ x₂ ∈ Set.Iic (1 : ℝ)) ∨
      (x₁ ∈ Set.Ici (0 : ℝ) ∧ x₂ ∈ Set.Ici (0 : ℝ)) := by
  intro ε _hε
  refine ⟨1, zero_lt_one, le_rfl, ?_⟩
  intro x1 x2 hdist
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hdist
  by_cases hx1 : x1 ≤ 1
  · by_cases hx2 : x2 ≤ 1
    · exact Or.inl ⟨hx1, hx2⟩
    · have hx2' : (1 : ℝ) < x2 := lt_of_not_ge hx2
      refine Or.inr ⟨?_, ?_⟩
      · change 0 ≤ x1
        linarith
      · change 0 ≤ x2
        linarith
  · have hx1' : (1 : ℝ) < x1 := lt_of_not_ge hx1
    refine Or.inr ⟨?_, ?_⟩
    · change 0 ≤ x1
      linarith
    · change 0 ≤ x2
      linarith

/-- Exercise 798, gap 10; move `δ` under `ε`. -/
theorem gap10 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂ : ℝ,
      |x₁ - x₂| < δ → |f x₁ - f x₂| < ε := by
  intro ε hε
  obtain ⟨d1, hd1, h1⟩ := gap7 ε hε
  obtain ⟨d2, hd2, h2⟩ := gap8 ε hε
  obtain ⟨d3, hd3, _hd3_le, h3⟩ := gap9 1 (Nat.zero_lt_succ 0)
  refine ⟨min (min d1 d2) d3, ?_, ?_⟩
  · exact lt_min (lt_min hd1 hd2) hd3
  · intro x1 x2 hdist
    have hdist1 : |x1 - x2| < d1 :=
      lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_left _ _))
    have hdist2 : |x1 - x2| < d2 :=
      lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_right _ _))
    have hdist3 : |x1 - x2| < d3 :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    rcases h3 x1 x2 hdist3 with hleft | hright
    · exact h1 x1 hleft.1 x2 hleft.2 hdist1
    · exact h2 x1 hright.1 x2 hright.2 hdist2

/-- Exercise 798, gap 11. -/
theorem gap11 : UniformContinuous f := by
  simpa only [Metric.uniformContinuous_iff, Real.dist_eq] using gap10

/-- Exercise 798, gap 12. -/
theorem gap12 : UniformContinuous f := by
  exact gap11

end

end ProofGap.Exercise798
