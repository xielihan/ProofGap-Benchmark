import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise804

def boundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Bornology.IsBounded (f '' s)

def UCModulus (f : ℝ → ℝ) (s : Set ℝ) (δ ε : ℝ) : Prop :=
  ∀ x₁ ∈ s, ∀ x₂ ∈ s, |x₁ - x₂| < δ → |f x₁ - f x₂| < ε

/-- Exercise 804, gap 1; remove shadowing endpoint
quantifiers. -/
theorem gap1 (f g : ℝ → ℝ) (a b : ℝ)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ₁ > 0,
      UCModulus f (Set.Ioo a b) δ₁ (ε / 2) := by
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hf) (ε / 2) (by linarith) with
    ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  simpa only [Real.dist_eq] using
    hmod x₁ hx₁ x₂ hx₂ (by simpa only [Real.dist_eq] using hdist)

/-- Exercise 804, gap 2; remove shadowing endpoints. -/
theorem gap2 (f g : ℝ → ℝ) (a b : ℝ)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ₂ > 0,
      UCModulus g (Set.Ioo a b) δ₂ (ε / 2) := by
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hg) (ε / 2) (by linarith) with
    ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  simpa only [Real.dist_eq] using
    hmod x₁ hx₁ x₂ hx₂ (by simpa only [Real.dist_eq] using hdist)

/-- Exercise 804, gap 3; repair the quantifier order so
`δ` may depend on `ε`. -/
theorem gap3 (f g : ℝ → ℝ) (a b : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ →
      |f x₁ + g x₁ - (f x₂ + g x₂)| ≤
        |f x₁ - f x₂| + |g x₁ - g x₂| := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  calc
    |f x₁ + g x₁ - (f x₂ + g x₂)| =
        |(f x₁ - f x₂) + (g x₁ - g x₂)| := by congr 1 <;> ring
    _ ≤ |f x₁ - f x₂| + |g x₁ - g x₂| := abs_add_le _ _

/-- Exercise 804, gap 4; repair the quantifier order and
use the two half-ε moduli. -/
theorem gap4 (f g : ℝ → ℝ) (a b ε δ : ℝ)
    (hf : UCModulus f (Set.Ioo a b) δ (ε / 2))
    (hg : UCModulus g (Set.Ioo a b) δ (ε / 2)) :
    ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      |x₁ - x₂| < δ →
        |f x₁ - f x₂| + |g x₁ - g x₂| < ε / 2 + ε / 2 := by
  intro x₁ hx₁ x₂ hx₂ hdist
  have hf' := hf x₁ hx₁ x₂ hx₂ hdist
  have hg' := hg x₁ hx₁ x₂ hx₂ hdist
  linarith

/-- Exercise 804, gap 5; the equality is independent of
`δ,x₁,x₂`. -/
theorem gap5 (ε : ℝ) : ε / 2 + ε / 2 = ε := by
  ring

/-- Exercise 804, gap 6; repair the modulus quantifiers. -/
theorem gap6 (f g : ℝ → ℝ) (a b : ℝ)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ > 0,
      UCModulus (fun x => f x + g x) (Set.Ioo a b) δ ε := by
  intro ε hε
  rcases gap1 f g a b hf hg ε hε with ⟨δ₁, hδ₁, hf₁⟩
  rcases gap2 f g a b hf hg ε hε with ⟨δ₂, hδ₂, hg₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  have hd₁ : |x₁ - x₂| < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd₂ : |x₁ - x₂| < δ₂ := lt_of_lt_of_le hdist (min_le_right _ _)
  have htri :
      |f x₁ + g x₁ - (f x₂ + g x₂)| ≤
        |f x₁ - f x₂| + |g x₁ - g x₂| := by
    calc
      |f x₁ + g x₁ - (f x₂ + g x₂)| =
          |(f x₁ - f x₂) + (g x₁ - g x₂)| := by congr 1 <;> ring
      _ ≤ |f x₁ - f x₂| + |g x₁ - g x₂| := abs_add_le _ _
  have hsum : |f x₁ - f x₂| + |g x₁ - g x₂| < ε := by
    have h₁ := hf₁ x₁ hx₁ x₂ hx₂ hd₁
    have h₂ := hg₂ x₁ hx₁ x₂ hx₂ hd₂
    linarith
  exact lt_of_le_of_lt htri hsum

/-- Exercise 804, gap 7. -/
theorem gap7 (f g : ℝ → ℝ) (a b : ℝ)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    UniformContinuousOn (fun x => f x + g x) (Set.Ioo a b) := by
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  rcases gap6 f g a b hf hg ε hε with ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  simpa only [Real.dist_eq] using
    hmod x₁ hx₁ x₂ hx₂ (by simpa only [Real.dist_eq] using hdist)

/-- Exercise 804, gap 8; remove shadowing endpoints. -/
theorem gap8 (F : ℝ → ℝ) (a b : ℝ)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ > 0, UCModulus F (Set.Ioo a b) δ ε := by
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hF) ε hε with ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  simpa only [Real.dist_eq] using
    hmod x₁ hx₁ x₂ hx₂ (by simpa only [Real.dist_eq] using hdist)

/-- Exercise 804, gap 9; make `δ` depend on `ε`. -/
theorem gap9 (F : ℝ → ℝ) (a b : ℝ)
    (hab : a < b)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂,
      a < x₁ → x₁ < a + δ → a < x₂ → x₂ < a + δ →
        |F x₁ - F x₂| < ε := by
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hF) ε hε with ⟨d, hd, hmod⟩
  let δ := min (d / 2) ((b - a) / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hd) (half_pos (sub_pos.mpr hab))
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁lo hx₁hi hx₂lo hx₂hi
  have hδd : δ ≤ d / 2 := min_le_left _ _
  have hδab : δ ≤ (b - a) / 2 := min_le_right _ _
  have hx₁ : x₁ ∈ Set.Ioo a b := ⟨hx₁lo, by linarith⟩
  have hx₂ : x₂ ∈ Set.Ioo a b := ⟨hx₂lo, by linarith⟩
  have hdist : dist x₁ x₂ < d := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  simpa only [Real.dist_eq] using hmod x₁ hx₁ x₂ hx₂ hdist

/-- Exercise 804, gap 10; make `δ` depend on `ε`. -/
theorem gap10 (F : ℝ → ℝ) (a b : ℝ)
    (hab : a < b)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂,
      b - δ < x₁ → x₁ < b → b - δ < x₂ → x₂ < b →
        |F x₁ - F x₂| < ε := by
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hF) ε hε with ⟨d, hd, hmod⟩
  let δ := min (d / 2) ((b - a) / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hd) (half_pos (sub_pos.mpr hab))
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁lo hx₁hi hx₂lo hx₂hi
  have hδd : δ ≤ d / 2 := min_le_left _ _
  have hδab : δ ≤ (b - a) / 2 := min_le_right _ _
  have hx₁ : x₁ ∈ Set.Ioo a b := ⟨by linarith, hx₁hi⟩
  have hx₂ : x₂ ∈ Set.Ioo a b := ⟨by linarith, hx₂hi⟩
  have hdist : dist x₁ x₂ < d := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  simpa only [Real.dist_eq] using hmod x₁ hx₁ x₂ hx₂ hdist

/-- Exercise 804, gap 11; replace the undefined symbol
`F(a+0)` by existence of the right-hand endpoint limit. -/
theorem gap11 (F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    ∃ La, Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds La) := by
  let l := nhdsWithin a (Set.Ioi a)
  have hl : l.NeBot := by
    dsimp [l]
    exact mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  letI : Filter.NeBot l := hl
  have hmap : (Filter.map F l).NeBot := inferInstance
  have hc : Cauchy (Filter.map F l) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨hmap, ?_⟩
    intro ε hε
    rcases (Metric.uniformContinuousOn_iff.mp hF) ε hε with
      ⟨δ, hδ, hmod⟩
    let r := min (δ / 2) ((b - a) / 2)
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (half_pos hδ) (half_pos (sub_pos.mpr hab))
    refine ⟨F '' Set.Ioo a (a + r), ?_, ?_⟩
    · change F ⁻¹' (F '' Set.Ioo a (a + r)) ∈ l
      have hu : Set.Iio (a + r) ∈ l :=
        (show l ≤ nhds a from inf_le_left) (Iio_mem_nhds (by linarith))
      have hi : Set.Ioo a (a + r) ∈ l := by
        filter_upwards [self_mem_nhdsWithin, hu] with x hax hxu
        exact ⟨hax, hxu⟩
      exact Filter.mem_of_superset hi (Set.subset_preimage_image F _)
    · intro y₁ hy₁ y₂ hy₂
      rcases hy₁ with ⟨x₁, hx₁, rfl⟩
      rcases hy₂ with ⟨x₂, hx₂, rfl⟩
      have hrδ : r ≤ δ / 2 := min_le_left _ _
      have hrab : r ≤ (b - a) / 2 := min_le_right _ _
      have hx₁lo : a < x₁ := hx₁.1
      have hx₁hi : x₁ < a + r := hx₁.2
      have hx₂lo : a < x₂ := hx₂.1
      have hx₂hi : x₂ < a + r := hx₂.2
      have hx₁I : x₁ ∈ Set.Ioo a b := ⟨hx₁lo, by linarith⟩
      have hx₂I : x₂ ∈ Set.Ioo a b := ⟨hx₂lo, by linarith⟩
      apply hmod x₁ hx₁I x₂ hx₂I
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith
      · linarith
  rcases cauchy_iff_exists_le_nhds.mp hc with ⟨La, hLa⟩
  exact ⟨La, hLa⟩

/-- Exercise 804, gap 12; replace `F(b-0)` by existence of
the left-hand endpoint limit. -/
theorem gap12 (F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    ∃ Lb, Filter.Tendsto F (nhdsWithin b (Set.Iio b)) (nhds Lb) := by
  let l := nhdsWithin b (Set.Iio b)
  have hl : l.NeBot := by
    dsimp [l]
    exact mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  letI : Filter.NeBot l := hl
  have hmap : (Filter.map F l).NeBot := inferInstance
  have hc : Cauchy (Filter.map F l) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨hmap, ?_⟩
    intro ε hε
    rcases (Metric.uniformContinuousOn_iff.mp hF) ε hε with
      ⟨δ, hδ, hmod⟩
    let r := min (δ / 2) ((b - a) / 2)
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (half_pos hδ) (half_pos (sub_pos.mpr hab))
    refine ⟨F '' Set.Ioo (b - r) b, ?_, ?_⟩
    · change F ⁻¹' (F '' Set.Ioo (b - r) b) ∈ l
      have hu : Set.Ioi (b - r) ∈ l :=
        (show l ≤ nhds b from inf_le_left) (Ioi_mem_nhds (by linarith))
      have hi : Set.Ioo (b - r) b ∈ l := by
        filter_upwards [self_mem_nhdsWithin, hu] with x hxb hxu
        exact ⟨hxu, hxb⟩
      exact Filter.mem_of_superset hi (Set.subset_preimage_image F _)
    · intro y₁ hy₁ y₂ hy₂
      rcases hy₁ with ⟨x₁, hx₁, rfl⟩
      rcases hy₂ with ⟨x₂, hx₂, rfl⟩
      have hrδ : r ≤ δ / 2 := min_le_left _ _
      have hrab : r ≤ (b - a) / 2 := min_le_right _ _
      have hx₁lo : b - r < x₁ := hx₁.1
      have hx₁hi : x₁ < b := hx₁.2
      have hx₂lo : b - r < x₂ := hx₂.1
      have hx₂hi : x₂ < b := hx₂.2
      have hx₁I : x₁ ∈ Set.Ioo a b := ⟨by linarith, hx₁hi⟩
      have hx₂I : x₂ ∈ Set.Ioo a b := ⟨by linarith, hx₂hi⟩
      apply hmod x₁ hx₁I x₂ hx₂I
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith
      · linarith
  rcases cauchy_iff_exists_le_nhds.mp hc with ⟨Lb, hLb⟩
  exact ⟨Lb, hLb⟩

/-- Exercise 804, gap 13; bind the previously undefined
extension `F⋆`. -/
theorem gap13 (F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    ∃ Fstar : ℝ → ℝ, ContinuousOn Fstar (Set.Icc a b) ∧
      ∀ x ∈ Set.Ioo a b, Fstar x = F x := by
  rcases gap11 F a b hab hF with ⟨La, hLa⟩
  rcases gap12 F a b hab hF with ⟨Lb, hLb⟩
  let Fstar : ℝ → ℝ := fun x =>
    if x = a then La else if x = b then Lb else F x
  refine ⟨Fstar, ?_, ?_⟩
  · intro x hx
    by_cases hxa : x = a
    · subst x
      have hvalue : Fstar a = La := by simp [Fstar]
      change Filter.map Fstar (nhdsWithin a (Set.Icc a b)) ≤ nhds (Fstar a)
      rw [hvalue]
      intro U hU
      change Fstar ⁻¹' U ∈ nhdsWithin a (Set.Icc a b)
      have hpre : F ⁻¹' U ∈ nhdsWithin a (Set.Ioi a) := hLa hU
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with
        ⟨V, hV, hsub⟩
      have hVI : V ∩ Set.Iio b ∈ nhds a := by
        filter_upwards [hV, Iio_mem_nhds hab] with y hyV hyb
        exact ⟨hyV, hyb⟩
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨V ∩ Set.Iio b, hVI, ?_⟩
      intro y hy
      by_cases hya : y = a
      · subst y
        change Fstar a ∈ U
        simpa [Fstar] using mem_of_mem_nhds hU
      · have hay : a < y := lt_of_le_of_ne hy.2.1 (Ne.symm hya)
        have hyb : y < b := hy.1.2
        have hFy : F y ∈ U := hsub ⟨hy.1.1, hay⟩
        change Fstar y ∈ U
        simpa [Fstar, hya, ne_of_lt hyb] using hFy
    · by_cases hxb : x = b
      · subst x
        have hvalue : Fstar b = Lb := by simp [Fstar, hab.ne']
        change Filter.map Fstar (nhdsWithin b (Set.Icc a b)) ≤ nhds (Fstar b)
        rw [hvalue]
        intro U hU
        change Fstar ⁻¹' U ∈ nhdsWithin b (Set.Icc a b)
        have hpre : F ⁻¹' U ∈ nhdsWithin b (Set.Iio b) := hLb hU
        rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with
          ⟨V, hV, hsub⟩
        have hVI : V ∩ Set.Ioi a ∈ nhds b := by
          filter_upwards [hV, Ioi_mem_nhds hab] with y hyV hya
          exact ⟨hyV, hya⟩
        refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
          ⟨V ∩ Set.Ioi a, hVI, ?_⟩
        intro y hy
        by_cases hyb : y = b
        · subst y
          change Fstar b ∈ U
          simpa [Fstar, hab.ne'] using mem_of_mem_nhds hU
        · have hyb' : y < b := lt_of_le_of_ne hy.2.2 hyb
          have hya : a < y := hy.1.2
          have hFy : F y ∈ U := hsub ⟨hy.1.1, hyb'⟩
          change Fstar y ∈ U
          simpa [Fstar, ne_of_gt hya, hyb] using hFy
      · have hxi : x ∈ Set.Ioo a b :=
          ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
        have hvalue : Fstar x = F x := by simp [Fstar, hxa, hxb]
        have ht := hF.continuousOn x hxi
        change Filter.map Fstar (nhdsWithin x (Set.Icc a b)) ≤ nhds (Fstar x)
        rw [hvalue]
        intro U hU
        change Fstar ⁻¹' U ∈ nhdsWithin x (Set.Icc a b)
        have hpre : F ⁻¹' U ∈ nhdsWithin x (Set.Ioo a b) := ht hU
        rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with
          ⟨V, hV, hsub⟩
        have hIoo : Set.Ioo a b ∈ nhds x := by
          filter_upwards [Ioi_mem_nhds hxi.1, Iio_mem_nhds hxi.2] with y hay hyb
          exact ⟨hay, hyb⟩
        have hVI : V ∩ Set.Ioo a b ∈ nhds x := by
          filter_upwards [hV, hIoo] with y hyV hyI
          exact ⟨hyV, hyI⟩
        refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
          ⟨V ∩ Set.Ioo a b, hVI, ?_⟩
        intro y hy
        have hay : a < y := hy.1.2.1
        have hyb : y < b := hy.1.2.2
        have hFy : F y ∈ U := hsub hy.1
        change Fstar y ∈ U
        simpa [Fstar, ne_of_gt hay, ne_of_lt hyb] using hFy
  · intro x hx
    simp [Fstar, ne_of_gt hx.1, ne_of_lt hx.2]

/-- Exercise 804, gap 14; bind the continuous extension. -/
theorem gap14 (F Fstar : ℝ → ℝ) (a b : ℝ)
    (hstar : ContinuousOn Fstar (Set.Icc a b)) :
    boundedOn Fstar (Set.Icc a b) := by
  exact (isCompact_Icc.image_of_continuousOn hstar).isBounded

/-- Exercise 804, gap 15; add `a<b`. -/
theorem gap15 (F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    boundedOn F (Set.Ioo a b) := by
  rcases gap13 F a b hab hF with ⟨Fstar, hstar, hEq⟩
  have hbounded : Bornology.IsBounded (Fstar '' Set.Icc a b) :=
    gap14 F Fstar a b hstar
  apply hbounded.subset
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, ⟨hx.1.le, hx.2.le⟩, hEq x hx⟩

/-- Exercise 804, gap 16; remove irrelevant universally
quantified `f,g`. -/
theorem gap16 (F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hF : UniformContinuousOn F (Set.Ioo a b)) :
    boundedOn F (Set.Ioo a b) := by
  exact gap15 F a b hab hF

/-- Exercise 804, gap 17; remove shadowing endpoints. -/
theorem gap17 (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    ∃ L > 0, ∃ M > 0, ∀ x ∈ Set.Ioo a b,
      |f x| ≤ L ∧ |g x| ≤ M := by
  have hbf := gap15 f a b hab hf
  have hbg := gap15 g a b hab hg
  rcases (Metric.isBounded_iff_subset_ball 0).mp hbf with ⟨rf, hrf⟩
  rcases (Metric.isBounded_iff_subset_ball 0).mp hbg with ⟨rg, hrg⟩
  refine ⟨max rf 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    max rg 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  have hfx : |f x| < rf := by
    have hm := hrf (show f x ∈ f '' Set.Ioo a b from ⟨x, hx, rfl⟩)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hm
  have hgx : |g x| < rg := by
    have hm := hrg (show g x ∈ g '' Set.Ioo a b from ⟨x, hx, rfl⟩)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hm
  exact ⟨le_trans hfx.le (le_max_left _ _),
    le_trans hgx.le (le_max_left _ _)⟩

/-- Exercise 804, gap 18; bind positive bounds before using
them in denominators. -/
theorem gap18 (f g : ℝ → ℝ) (a b L M : ℝ)
    (hL : 0 < L) (hM : 0 < M)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ > 0,
      UCModulus f (Set.Ioo a b) δ (ε / (2 * M)) ∧
      UCModulus g (Set.Ioo a b) δ (ε / (2 * L)) := by
  intro ε hε
  have heM : 0 < ε / (2 * M) := div_pos hε (mul_pos (by norm_num) hM)
  have heL : 0 < ε / (2 * L) := div_pos hε (mul_pos (by norm_num) hL)
  rcases (Metric.uniformContinuousOn_iff.mp hf) _ heM with ⟨δf, hδf, hfm⟩
  rcases (Metric.uniformContinuousOn_iff.mp hg) _ heL with ⟨δg, hδg, hgm⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ hd
    simpa only [Real.dist_eq] using hfm x₁ hx₁ x₂ hx₂
      (by simpa only [Real.dist_eq] using
        (lt_of_lt_of_le hd (min_le_left δf δg)))
  · intro x₁ hx₁ x₂ hx₂ hd
    simpa only [Real.dist_eq] using hgm x₁ hx₁ x₂ hx₂
      (by simpa only [Real.dist_eq] using
        (lt_of_lt_of_le hd (min_le_right δf δg)))

/-- Exercise 804, gap 19; the algebraic identity needs no
existential `δ`. -/
theorem gap19 (f g : ℝ → ℝ) (x₁ x₂ : ℝ) :
    |f x₁ * g x₁ - f x₂ * g x₂| =
      |(f x₁ - f x₂) * g x₁ + f x₂ * (g x₁ - g x₂)| := by
  apply congrArg abs
  ring

/-- Exercise 804, gap 20; add the bounds and two modulus
hypotheses used in the estimate. -/
theorem gap20 (f g : ℝ → ℝ) (a b L M ε δ x₁ x₂ : ℝ)
    (hL : 0 < L) (hM : 0 < M)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (hbf : |f x₂| ≤ L) (hbg : |g x₁| ≤ M)
    (hf : UCModulus f (Set.Ioo a b) δ (ε / (2 * M)))
    (hg : UCModulus g (Set.Ioo a b) δ (ε / (2 * L)))
    (hd : |x₁ - x₂| < δ) :
    |(f x₁ - f x₂) * g x₁ + f x₂ * (g x₁ - g x₂)| <
      ε / (2 * M) * M + ε / (2 * L) * L := by
  have hf' := hf x₁ hx₁ x₂ hx₂ hd
  have hg' := hg x₁ hx₁ x₂ hx₂ hd
  calc
    |(f x₁ - f x₂) * g x₁ + f x₂ * (g x₁ - g x₂)| ≤
        |(f x₁ - f x₂) * g x₁| + |f x₂ * (g x₁ - g x₂)| :=
      abs_add_le _ _
    _ = |f x₁ - f x₂| * |g x₁| + |f x₂| * |g x₁ - g x₂| := by
      rw [abs_mul, abs_mul]
    _ ≤ |f x₁ - f x₂| * M + L * |g x₁ - g x₂| :=
      add_le_add
        (mul_le_mul_of_nonneg_left hbg (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hbf (abs_nonneg _))
    _ < ε / (2 * M) * M + L * (ε / (2 * L)) :=
      add_lt_add
        (mul_lt_mul_of_pos_right hf' hM)
        (mul_lt_mul_of_pos_left hg' hL)
    _ = ε / (2 * M) * M + ε / (2 * L) * L := by ring

/-- Exercise 804, gap 21; add nonzero bounds. -/
theorem gap21 (ε L M : ℝ) (hL : L ≠ 0) (hM : M ≠ 0) :
    ε / (2 * M) * M + ε / (2 * L) * L = ε := by
  field_simp [hL, hM]
  ring

/-- Exercise 804, gap 22; repair the modulus quantifiers. -/
theorem gap22 (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    ∀ ε > 0, ∃ δ > 0,
      UCModulus (fun x => f x * g x) (Set.Ioo a b) δ ε := by
  intro ε hε
  rcases gap17 f g a b hab hf hg with ⟨L, hL, M, hM, hbounds⟩
  rcases gap18 f g a b L M hL hM hf hg ε hε with
    ⟨δ, hδ, hfm, hgm⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hd
  have hb₁ := hbounds x₁ hx₁
  have hb₂ := hbounds x₂ hx₂
  calc
    |f x₁ * g x₁ - f x₂ * g x₂| =
        |(f x₁ - f x₂) * g x₁ + f x₂ * (g x₁ - g x₂)| :=
      gap19 f g x₁ x₂
    _ < ε / (2 * M) * M + ε / (2 * L) * L :=
      gap20 f g a b L M ε δ x₁ x₂ hL hM hx₁ hx₂ hb₂.1 hb₁.2 hfm hgm hd
    _ = ε := gap21 ε L M hL.ne' hM.ne'

/-- Exercise 804, gap 23; add `a<b`, needed for boundedness
of uniformly continuous functions on the bounded interval. -/
theorem gap23 (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    UniformContinuousOn (fun x => f x * g x) (Set.Ioo a b) := by
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  rcases gap22 f g a b hab hf hg ε hε with ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  simpa only [Real.dist_eq] using
    hmod x₁ hx₁ x₂ hx₂ (by simpa only [Real.dist_eq] using hdist)

/-- Exercise 804, gap 24. -/
theorem gap24 (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    UniformContinuousOn (fun x => f x * g x) (Set.Ioo a b) := by
  exact gap23 f g a b hab hf hg

/-- Exercise 804, gap 25. -/
theorem gap25 (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : UniformContinuousOn f (Set.Ioo a b))
    (hg : UniformContinuousOn g (Set.Ioo a b)) :
    UniformContinuousOn (fun x => f x + g x) (Set.Ioo a b) ∧
      UniformContinuousOn (fun x => f x * g x) (Set.Ioo a b) := by
  exact ⟨gap7 f g a b hf hg, gap24 f g a b hab hf hg⟩

end ProofGap.Exercise804
