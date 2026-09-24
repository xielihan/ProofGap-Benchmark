import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise3368

open Filter
open scoped Topology

noncomputable section

def UniquePreimageOn (φ : ℝ → ℝ) (J : Set ℝ) (t : ℝ) : Prop :=
  ∃! y : ℝ, y ∈ J ∧ φ y = t

def RangeCondition (f φ : ℝ → ℝ) (I J : Set ℝ) : Prop :=
  Set.MapsTo f I (φ '' J)

theorem gap1 (f φ : ℝ → ℝ) (a b c d x₀ y₀ : ℝ)
    (hf : ContinuousOn f (Set.Ioo a b))
    (hφmono : StrictMonoOn φ (Set.Ioo c d))
    (hφcont : ContinuousOn φ (Set.Ioo c d))
    (hx₀ : x₀ ∈ Set.Ioo a b) (hy₀ : y₀ ∈ Set.Ioo c d)
    (hxy : φ y₀ = f x₀) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Ioo (x₀ - ε) (x₀ + ε) ∩ Set.Ioo a b,
        UniquePreimageOn φ (Set.Ioo c d) (f x) := by
  let y₁ := (c + y₀) / 2
  let y₂ := (y₀ + d) / 2
  have hy₁ : y₁ ∈ Set.Ioo c d := by
    dsimp [y₁]
    constructor <;> linarith [hy₀.1, hy₀.2]
  have hy₂ : y₂ ∈ Set.Ioo c d := by
    dsimp [y₂]
    constructor <;> linarith [hy₀.1, hy₀.2]
  have hy₁₀ : y₁ < y₀ := by
    dsimp [y₁]
    linarith [hy₀.1]
  have hy₀₂ : y₀ < y₂ := by
    dsimp [y₂]
    linarith [hy₀.2]
  have hy₁₂ : y₁ < y₂ := hy₁₀.trans hy₀₂
  have hleft : φ y₁ < f x₀ := by
    rw [← hxy]
    exact hφmono hy₁ hy₀ hy₁₀
  have hright : f x₀ < φ y₂ := by
    rw [← hxy]
    exact hφmono hy₀ hy₂ hy₀₂
  let η := min (f x₀ - φ y₁) (φ y₂ - f x₀)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (sub_pos.mpr hleft) (sub_pos.mpr hright)
  rcases (Metric.continuousWithinAt_iff.1 (hf x₀ hx₀)) η hη with
    ⟨ε, hε, hfε⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx
  have hdist : dist x x₀ < ε := by
    rw [Real.dist_eq]
    exact abs_lt.2 ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  have hfdist := hfε hx.2 hdist
  have habs : |f x - f x₀| < η := by
    simpa [Real.dist_eq] using hfdist
  have habsLeft : |f x - f x₀| < f x₀ - φ y₁ :=
    lt_of_lt_of_le habs (min_le_left _ _)
  have habsRight : |f x - f x₀| < φ y₂ - f x₀ :=
    lt_of_lt_of_le habs (min_le_right _ _)
  have hxleft : φ y₁ < f x := by
    have := (abs_lt.mp habsLeft).1
    linarith
  have hxright : f x < φ y₂ := by
    have := (abs_lt.mp habsRight).2
    linarith
  have hsub : Set.Icc y₁ y₂ ⊆ Set.Ioo c d := by
    intro y hy
    exact ⟨lt_of_lt_of_le hy₁.1 hy.1, lt_of_le_of_lt hy.2 hy₂.2⟩
  have hxmem : f x ∈ Set.Icc (φ y₁) (φ y₂) := ⟨hxleft.le, hxright.le⟩
  rcases intermediate_value_Icc (f := φ) hy₁₂.le (hφcont.mono hsub) hxmem with
    ⟨y, hy, hφy⟩
  have hyJ := hsub hy
  refine ⟨y, ⟨hyJ, hφy⟩, ?_⟩
  intro z hz
  exact hφmono.injOn hz.1 hyJ (hz.2.trans hφy.symm)

theorem gap2 (f φ : ℝ → ℝ) (a b c d x₀ y₀ : ℝ)
    (hφmono : StrictMonoOn φ (Set.Ioo c d))
    (hx₀ : x₀ ∈ Set.Ioo a b) (hy₀ : y₀ ∈ Set.Ioo c d)
    (hxy : φ y₀ = f x₀) :
    ∀ y ∈ Set.Ioo c d, φ y = f x₀ → y = y₀ := by
  intro y hy h
  exact hφmono.injOn hy hy₀ (h.trans hxy.symm)

theorem gap3 (f φ : ℝ → ℝ) (a b c d : ℝ)
    (hφmono : StrictMonoOn φ (Set.Ioo c d))
    (hrange : RangeCondition f φ (Set.Ioo a b) (Set.Ioo c d)) :
    ∀ x ∈ Set.Ioo a b,
      UniquePreimageOn φ (Set.Ioo c d) (f x) := by
  intro x hx
  rcases hrange hx with ⟨y, hy, hφy⟩
  refine ⟨y, ⟨hy, hφy⟩, ?_⟩
  intro z hz
  exact hφmono.injOn hz.1 hy (hz.2.trans hφy.symm)

theorem gap4 (f φ : ℝ → ℝ) (a b c d : ℝ)
    (hf : ContinuousOn f (Set.Ioo a b))
    (hφmono : StrictMonoOn φ (Set.Ioo c d))
    (hφcont : ContinuousOn φ (Set.Ioo c d))
    (hrange : RangeCondition f φ (Set.Ioo a b) (Set.Ioo c d)) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Set.Ioo a b) ∧
      ∀ x ∈ Set.Ioo a b,
        g x ∈ Set.Ioo c d ∧ φ (g x) = f x := by
  have hu := gap3 f φ a b c d hφmono hrange
  let g : ℝ → ℝ := fun x =>
    if hx : x ∈ Set.Ioo a b then
      Classical.choose (hu x hx).exists
    else 0
  have hg : ∀ x (hx : x ∈ Set.Ioo a b),
      g x ∈ Set.Ioo c d ∧ φ (g x) = f x := by
    intro x hx
    dsimp [g]
    rw [dif_pos hx]
    exact Classical.choose_spec (hu x hx).exists
  refine ⟨g, ?_, hg⟩
  intro x₀ hx₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let y₀ := g x₀
  have hy₀ : y₀ ∈ Set.Ioo c d := (hg x₀ hx₀).1
  let r := min (ε / 2) (min ((y₀ - c) / 2) ((d - y₀) / 2))
  have hr : 0 < r := by
    dsimp [r]
    apply lt_min
    · linarith
    · apply lt_min <;> linarith [hy₀.1, hy₀.2]
  have hre : r < ε := by
    have hrε : r ≤ ε / 2 := by
      dsimp [r]
      exact min_le_left _ _
    linarith
  have hrcHalf : r ≤ (y₀ - c) / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hrdHalf : r ≤ (d - y₀) / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hrc : r < y₀ - c := by
    linarith [hy₀.1]
  have hrd : r < d - y₀ := by
    linarith [hy₀.2]
  let y₁ := y₀ - r
  let y₂ := y₀ + r
  have hy₁ : y₁ ∈ Set.Ioo c d := by
    dsimp [y₁]
    constructor <;> linarith [hy₀.1, hy₀.2, hrc, hr]
  have hy₂ : y₂ ∈ Set.Ioo c d := by
    dsimp [y₂]
    constructor <;> linarith [hy₀.1, hy₀.2, hrd, hr]
  have hy₁₀ : y₁ < y₀ := by
    dsimp [y₁]
    linarith
  have hy₀₂ : y₀ < y₂ := by
    dsimp [y₂]
    linarith
  have hleft : φ y₁ < f x₀ := by
    rw [← (hg x₀ hx₀).2]
    exact hφmono hy₁ hy₀ hy₁₀
  have hright : f x₀ < φ y₂ := by
    rw [← (hg x₀ hx₀).2]
    exact hφmono hy₀ hy₂ hy₀₂
  let η := min (f x₀ - φ y₁) (φ y₂ - f x₀)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (sub_pos.mpr hleft) (sub_pos.mpr hright)
  rcases (Metric.continuousWithinAt_iff.1 (hf x₀ hx₀)) η hη with
    ⟨δ, hδ, hfδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx hdist
  have hfdist := hfδ hx hdist
  have habs : |f x - f x₀| < η := by
    simpa [Real.dist_eq] using hfdist
  have habsLeft : |f x - f x₀| < f x₀ - φ y₁ :=
    lt_of_lt_of_le habs (min_le_left _ _)
  have habsRight : |f x - f x₀| < φ y₂ - f x₀ :=
    lt_of_lt_of_le habs (min_le_right _ _)
  have hxleft : φ y₁ < f x := by
    have := (abs_lt.mp habsLeft).1
    linarith
  have hxright : f x < φ y₂ := by
    have := (abs_lt.mp habsRight).2
    linarith
  have hgx := hg x hx
  have hy₁x : y₁ < g x := by
    by_contra h
    have hle : g x ≤ y₁ := le_of_not_gt h
    have hp := hφmono.monotoneOn hgx.1 hy₁ hle
    rw [hgx.2] at hp
    linarith
  have hxy₂ : g x < y₂ := by
    by_contra h
    have hle : y₂ ≤ g x := le_of_not_gt h
    have hp := hφmono.monotoneOn hy₂ hgx.1 hle
    rw [hgx.2] at hp
    linarith
  have habsy : |g x - y₀| < r := by
    apply abs_lt.2
    constructor <;> dsimp [y₁, y₂] at hy₁x hxy₂ ⊢ <;> linarith
  rw [Real.dist_eq]
  change |g x - y₀| < ε
  exact habsy.trans hre

def φExample (y : ℝ) : ℝ :=
  Real.sin y + Real.sinh y

noncomputable def inverseExample : ℝ → ℝ :=
  Function.invFun φExample

theorem gap5 (y : ℝ) :
    deriv φExample y = Real.cos y + Real.cosh y := by
  change deriv (fun z : ℝ => Real.sin z + Real.sinh z) y =
    Real.cos y + Real.cosh y
  exact ((Real.hasDerivAt_sin y).add (Real.hasDerivAt_sinh y)).deriv

theorem gap6 (y : ℝ) :
    0 < Real.cos y + Real.cosh y := by
  have hcos : -1 ≤ Real.cos y := Real.neg_one_le_cos y
  have hcosh : 1 ≤ Real.cosh y := Real.one_le_cosh y
  by_contra hpos
  have hsum : Real.cos y + Real.cosh y ≤ 0 := le_of_not_gt hpos
  have heq : Real.cosh y = 1 := by
    linarith
  have hprod : Real.exp y * Real.exp (-y) = 1 := by
    calc
      Real.exp y * Real.exp (-y) = Real.exp (y + -y) :=
        (Real.exp_add y (-y)).symm
      _ = 1 := by norm_num
  have hexpsum : Real.exp y + Real.exp (-y) = 2 := by
    rw [Real.cosh_eq] at heq
    linarith
  have hmul := congrArg (fun t : ℝ => Real.exp y * t) hexpsum
  have hsq : (Real.exp y - 1) * (Real.exp y - 1) = 0 := by
    nlinarith [hprod, hmul]
  have hzero : Real.exp y - 1 = 0 := by
    rcases mul_eq_zero.mp hsq with h | h
    · exact h
    · exact h
  have hexp : Real.exp y = 1 := by
    linarith
  have hy : y = 0 := by
    apply Real.exp_injective
    simpa using hexp
  subst y
  norm_num at hsum

theorem gap7 (y : ℝ) :
    0 < deriv φExample y := by
  rw [gap5]
  exact gap6 y

theorem gap8 :
    StrictMono φExample := by
  have hcont : Continuous φExample := by
    simpa [φExample] using
      (Real.continuous_sin.add Real.continuous_sinh)
  have hm : StrictMonoOn φExample Set.univ := by
    refine strictMonoOn_of_deriv_pos convex_univ hcont.continuousOn ?_
    intro x hx
    exact gap7 x
  intro x y hxy
  exact hm (Set.mem_univ x) (Set.mem_univ y) hxy

theorem gap9 :
    Tendsto φExample atBot atBot := by
  refine tendsto_atBot.2 ?_
  intro b
  let M : ℝ := max 1 (3 - 2 * b)
  have hMone : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hMone
  filter_upwards [eventually_le_atBot (-Real.log M)] with y hy
  have hexpNeg : M ≤ Real.exp (-y) := by
    rw [← Real.exp_log hMpos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlarge : 3 - 2 * b ≤ Real.exp (-y) :=
    le_trans (le_max_right _ _) hexpNeg
  have hsmall : Real.exp y ≤ 1 := by
    have hy0 : y ≤ 0 := by linarith
    simpa using (Real.exp_le_exp.mpr hy0)
  have hs := Real.sin_le_one y
  rw [φExample, Real.sinh_eq]
  linarith

theorem gap10 :
    Tendsto φExample atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  let M : ℝ := max 1 (2 * b + 3)
  have hMone : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hMone
  filter_upwards [eventually_ge_atTop (Real.log M)] with y hy
  have hexp : M ≤ Real.exp y := by
    rw [← Real.exp_log hMpos]
    exact Real.exp_le_exp.mpr hy
  have hlarge : 2 * b + 3 ≤ Real.exp y :=
    le_trans (le_max_right _ _) hexp
  have hnegSmall : Real.exp (-y) ≤ 1 := by
    have hy0 : 0 ≤ y := by linarith
    simpa using (Real.exp_le_exp.mpr (neg_nonpos.mpr hy0))
  have hs := Real.neg_one_le_sin y
  rw [φExample, Real.sinh_eq]
  linarith

theorem gap11 :
    ∀ x : ℝ, ∃! y : ℝ, φExample y = x := by
  have hcont : Continuous φExample := by
    simpa [φExample] using
      (Real.continuous_sin.add Real.continuous_sinh)
  intro x
  rcases (tendsto_atBot.1 gap9 x).exists with ⟨a, ha⟩
  rcases (tendsto_atTop.1 gap10 x).exists with ⟨b, hb⟩
  have hab : a ≤ b := by
    by_contra h
    have hba : b < a := lt_of_not_ge h
    have hstrict := gap8 hba
    linarith
  have hxmem : x ∈ Set.Icc (φExample a) (φExample b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc (f := φExample) hab hcont.continuousOn hxmem with
    ⟨y, hy, hφy⟩
  refine ⟨y, hφy, ?_⟩
  intro z hz
  exact gap8.injective (hz.trans hφy.symm)

theorem gap12 :
    Continuous inverseExample := by
  have hsurj : Function.Surjective φExample := fun x => (gap11 x).exists
  have hinv : ∀ x : ℝ, φExample (inverseExample x) = x := by
    intro x
    change φExample (Function.invFun φExample x) = x
    exact Function.rightInverse_invFun hsurj x
  rw [Metric.continuous_iff]
  intro x ε hε
  let y₀ := inverseExample x
  let y₁ := y₀ - ε / 2
  let y₂ := y₀ + ε / 2
  have hy₁₀ : y₁ < y₀ := by
    dsimp [y₁]
    linarith
  have hy₀₂ : y₀ < y₂ := by
    dsimp [y₂]
    linarith
  have hy₀eq : φExample y₀ = x := by
    dsimp [y₀]
    exact hinv x
  have hleft : φExample y₁ < x := by
    rw [← hy₀eq]
    exact gap8 hy₁₀
  have hright : x < φExample y₂ := by
    rw [← hy₀eq]
    exact gap8 hy₀₂
  let δ := min (x - φExample y₁) (φExample y₂ - x)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (sub_pos.mpr hleft) (sub_pos.mpr hright)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have habs : |z - x| < δ := by
    simpa [Real.dist_eq] using hz
  have hδleft : δ ≤ x - φExample y₁ := by
    dsimp [δ]
    exact min_le_left _ _
  have hδright : δ ≤ φExample y₂ - x := by
    dsimp [δ]
    exact min_le_right _ _
  have hzleft : φExample y₁ < z := by
    have h := (abs_lt.mp habs).1
    linarith
  have hzright : z < φExample y₂ := by
    have h := (abs_lt.mp habs).2
    linarith
  have hzinv : φExample (inverseExample z) = z := hinv z
  have hy₁z : y₁ < inverseExample z := by
    by_contra h
    have hle : inverseExample z ≤ y₁ := le_of_not_gt h
    have hp := gap8.monotone hle
    rw [hzinv] at hp
    linarith
  have hzy₂ : inverseExample z < y₂ := by
    by_contra h
    have hle : y₂ ≤ inverseExample z := le_of_not_gt h
    have hp := gap8.monotone hle
    rw [hzinv] at hp
    linarith
  rw [Real.dist_eq]
  change |inverseExample z - inverseExample x| < ε
  apply abs_lt.2
  constructor <;> dsimp [y₁, y₂, y₀] at hy₁z hzy₂ ⊢ <;> linarith

def positiveExample (y : ℝ) : ℝ :=
  Real.exp (-y)

def nonpositiveExample (x : ℝ) : ℝ :=
  -(Real.sin x) ^ 2

theorem gap13 (y : ℝ) :
    0 < positiveExample y := by
  unfold positiveExample
  exact Real.exp_pos (-y)

theorem gap14 (x : ℝ) :
    nonpositiveExample x ≤ 0 := by
  unfold nonpositiveExample
  exact neg_nonpos.mpr (sq_nonneg (Real.sin x))

theorem gap15 :
    ¬ ∃ x₀ y₀ : ℝ, positiveExample y₀ = nonpositiveExample x₀ := by
  rintro ⟨x₀, y₀, h⟩
  have hp := gap13 y₀
  have hn := gap14 x₀
  rw [h] at hp
  exact (not_lt_of_ge hn) hp

theorem gap16 (x : ℝ) :
    ¬ ∃ y : ℝ, positiveExample y = nonpositiveExample x := by
  rintro ⟨y, h⟩
  exact gap15 ⟨x, y, h⟩

theorem gap17 (f φ : ℝ → ℝ) (a b c d : ℝ)
    (hφmono : StrictMonoOn φ (Set.Ioo c d)) :
    (∀ x ∈ Set.Ioo a b,
      UniquePreimageOn φ (Set.Ioo c d) (f x)) ↔
        RangeCondition f φ (Set.Ioo a b) (Set.Ioo c d) := by
  constructor
  · intro h x hx
    rcases h x hx with ⟨y, hy, huniq⟩
    exact ⟨y, hy.1, hy.2⟩
  · intro hrange
    exact gap3 f φ a b c d hφmono hrange

end

end ProofGap.Exercise3368
