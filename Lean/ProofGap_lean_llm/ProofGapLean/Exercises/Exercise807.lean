import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise807

noncomputable section

def oscSet (f : ℝ → ℝ) (a b δ : ℝ) : Set ℝ :=
  {|f x - f y| | (x ∈ Set.Ioo a b) (y ∈ Set.Ioo a b) (h : |x - y| ≤ δ)}
def ω (f : ℝ → ℝ) (a b δ : ℝ) : ℝ := sSup (oscSet f a b δ)

theorem gap1 (f : ℝ → ℝ) (a b ε : ℝ)
    (hu : UniformContinuousOn f (Set.Ioo a b)) (hε : 0 < ε) :
    ∃ δ' > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → |f x₁ - f x₂| < ε / 2 := by
  rcases (Metric.uniformContinuousOn_iff.mp hu) (ε / 2) (half_pos hε) with
    ⟨δ', hδ', h⟩
  refine ⟨δ', hδ', ?_⟩
  intro x₁ hx₁ x₂ hx₂ hx
  have hd : dist x₁ x₂ < δ' := by
    simpa [Real.dist_eq] using hx
  simpa [Real.dist_eq] using h x₁ hx₁ x₂ hx₂ hd
theorem gap2 (f : ℝ → ℝ) (a b ε δ' : ℝ)
    (h : ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → |f x₁ - f x₂| < ε / 2) :
    ∀ δ, 0 < δ → δ < δ' → ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| ≤ δ → |f x₁ - f x₂| < ε / 2 := by
  intro δ hδ hδ' x₁ hx₁ x₂ hx₂ hle
  exact h x₁ hx₁ x₂ hx₂ (lt_of_le_of_lt hle hδ')
theorem gap3 (f : ℝ → ℝ) (a b δ : ℝ) :
    ω f a b δ = sSup (oscSet f a b δ) := by
  rfl
theorem gap4 (f : ℝ → ℝ) (a b ε δ : ℝ)
    (hε : 0 ≤ ε)
    (h : ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| ≤ δ → |f x₁ - f x₂| < ε / 2) :
    ω f a b δ ≤ ε / 2 := by
  rw [ω]
  by_cases hne : (oscSet f a b δ).Nonempty
  · refine csSup_le hne ?_
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    exact le_of_lt (h x hx y hy hxy)
  · have hempty : oscSet f a b δ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp
    positivity
theorem gap5 (ε : ℝ) (hε : 0 < ε) : ε / 2 < ε := by
  exact half_lt_self hε
theorem gap6 (f : ℝ → ℝ) (a b ε δ : ℝ)
    (h₁ : ω f a b δ ≤ ε / 2) (h₂ : 0 < ε) : ω f a b δ < ε := by
  exact lt_of_le_of_lt h₁ (gap5 ε h₂)
theorem gap7 (f : ℝ → ℝ) (a b : ℝ)
    (hu : UniformContinuousOn f (Set.Ioo a b)) :
    Filter.Tendsto (ω f a b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases gap1 f a b ε hu hε with ⟨δ', hδ', huc⟩
  have hlt : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < δ' :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ')
  filter_upwards [hlt, self_mem_nhdsWithin] with δ hδlt hδpos
  by_cases hs : (Set.Ioo a b).Nonempty
  · have hzero : 0 ∈ oscSet f a b δ := by
      rcases hs with ⟨x, hx⟩
      refine ⟨x, hx, x, hx, ?_, by simp⟩
      simpa using (le_of_lt hδpos)
    have hne : (oscSet f a b δ).Nonempty := ⟨0, hzero⟩
    have hbdd : BddAbove (oscSet f a b δ) := by
      refine ⟨ε / 2, ?_⟩
      rintro z ⟨x, hx, y, hy, hxy, rfl⟩
      exact le_of_lt (huc x hx y hy (lt_of_le_of_lt hxy hδlt))
    have hlower : 0 ≤ ω f a b δ := by
      rw [ω]
      exact le_csSup hbdd hzero
    have hupper : ω f a b δ ≤ ε / 2 := by
      rw [ω]
      refine csSup_le hne ?_
      rintro z ⟨x, hx, y, hy, hxy, rfl⟩
      exact le_of_lt (huc x hx y hy (lt_of_le_of_lt hxy hδlt))
    simpa [Real.dist_eq, abs_of_nonneg hlower] using
      (lt_of_le_of_lt hupper (gap5 ε hε))
  · have hosc : oscSet f a b δ = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, hx, y, hy, hxy, rfl⟩
      exact hs ⟨x, hx⟩
    simp [ω, hosc, hε]
theorem gap8 (f : ℝ → ℝ) (a b : ℝ)
    (hlim : Filter.Tendsto (ω f a b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ ε > 0, ∃ δ' > 0, ∀ δ, 0 < δ ∧ δ < δ' → ω f a b δ < ε := by
  intro ε hε
  have hev : {δ : ℝ | dist (ω f a b δ) 0 < ε} ∈
      nhdsWithin 0 (Set.Ioi 0) :=
    (Metric.tendsto_nhds.mp hlim) ε hε
  rw [Metric.mem_nhdsWithin_iff] at hev
  rcases hev with ⟨δ', hδ', hev⟩
  refine ⟨δ', hδ', ?_⟩
  intro δ hδ
  have hball : δ ∈ Metric.ball (0 : ℝ) δ' := by
    simpa [Real.dist_eq, abs_of_pos hδ.1] using hδ.2
  have hout := hev ⟨hball, hδ.1⟩
  have habs : |ω f a b δ| < ε := by
    simpa [Real.dist_eq] using hout
  exact lt_of_le_of_lt (le_abs_self (ω f a b δ)) habs

theorem gap9 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε) :
    ∃ δ' > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → x₁ = x₂ → |f x₁ - f x₂| = 0 := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist heq
  subst x₂
  simp
theorem gap10 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε) :
    ∃ δ' > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → x₁ = x₂ → 0 < ε := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist heq
  exact hε
theorem gap11 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε) :
    ∃ δ' > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → x₁ = x₂ → |f x₁ - f x₂| < ε := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist heq
  subst x₂
  simpa using hε
theorem gap12 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε) :
    ∃ δ' > 0, ∃ δstar > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → x₁ ≠ x₂ → 0 < δstar := by
  refine ⟨ε, hε, 1, by decide, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist hne
  decide
theorem gap13 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε) :
    ∃ δ' > 0, ∃ δstar, 0 < δstar ∧ δstar < δ' := by
  exact ⟨2, by decide, 1, by decide, by decide⟩
theorem gap14 (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε) :
    ∃ δ' > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → x₁ ≠ x₂ → 0 < δ' := by
  refine ⟨ε, hε, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist hne
  exact hε
theorem gap15 (f : ℝ → ℝ) (a b ε δ' δstar : ℝ)
    (hδ : 0 < δstar) (hbdd : BddAbove (oscSet f a b δstar)) :
    ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → |x₁ - x₂| ≤ δstar →
        |f x₁ - f x₂| ≤ ω f a b δstar := by
  intro x₁ hx₁ x₂ hx₂ hdist hle
  rw [ω]
  apply le_csSup hbdd
  exact ⟨x₁, hx₁, x₂, hx₂, hle, rfl⟩
theorem gap16 (f : ℝ → ℝ) (a b ε δstar : ℝ)
    (hlim : Filter.Tendsto (ω f a b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hε : 0 < ε) :
    ∃ δstar > 0, ω f a b δstar < ε := by
  rcases gap8 f a b hlim ε hε with ⟨d, hd, h⟩
  refine ⟨d / 2, half_pos hd, ?_⟩
  apply h (d / 2)
  exact ⟨half_pos hd, half_lt_self hd⟩
theorem gap17 (f : ℝ → ℝ) (a b ε : ℝ)
    (hlim : Filter.Tendsto (ω f a b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hbdd : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), BddAbove (oscSet f a b δ))
    (hε : 0 < ε) :
    ∃ δ' > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ' → x₁ ≠ x₂ → |f x₁ - f x₂| < ε := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hl : l.NeBot := by
    dsimp [l]
    exact mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  letI : Filter.NeBot l := hl
  have hsmall : ∀ᶠ δ in l, ω f a b δ < ε := by
    have hdist := (Metric.tendsto_nhds.mp hlim) ε hε
    filter_upwards [hdist] with δ hδ
    have habs : |ω f a b δ| < ε := by simpa [Real.dist_eq] using hδ
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hbdd' : ∀ᶠ δ in l, BddAbove (oscSet f a b δ) := by
    simpa [l] using hbdd
  have hpos : ∀ᶠ δ in l, 0 < δ := self_mem_nhdsWithin
  rcases (hsmall.and (hbdd'.and hpos)).exists with ⟨δ, hω, hb, hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist hne
  exact lt_of_le_of_lt
    (gap15 f a b ε δ δ hδ hb x₁ hx₁ x₂ hx₂ hdist (le_of_lt hdist)) hω
theorem gap18 (f : ℝ → ℝ) (a b : ℝ)
    (hlim : Filter.Tendsto (ω f a b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hbdd : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), BddAbove (oscSet f a b δ)) :
    UniformContinuousOn f (Set.Ioo a b) := by
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  rcases gap17 f a b ε hlim hbdd hε with ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  have habs : |x₁ - x₂| < δ := by simpa [Real.dist_eq] using hdist
  by_cases heq : x₁ = x₂
  · subst x₂
    simpa [Real.dist_eq] using hε
  · simpa [Real.dist_eq] using hmod x₁ hx₁ x₂ hx₂ habs heq
theorem gap19 (f : ℝ → ℝ) (a b : ℝ) :
    UniformContinuousOn f (Set.Ioo a b) ↔
      Filter.Tendsto (ω f a b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), BddAbove (oscSet f a b δ) := by
  constructor
  · intro hu
    refine ⟨gap7 f a b hu, ?_⟩
    rcases gap1 f a b 2 hu (by norm_num) with ⟨d, hd, hmod⟩
    have hlt : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < d :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hd)
    filter_upwards [hlt] with δ hδ
    refine ⟨1, ?_⟩
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    have hz := hmod x hx y hy (lt_of_le_of_lt hxy hδ)
    norm_num at hz
    exact le_of_lt hz
  · rintro ⟨hlim, hbdd⟩
    exact gap18 f a b hlim hbdd

end

end ProofGap.Exercise807
