import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise403

noncomputable section

def HasLimitAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds b)

def EpsilonLimitAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < |x - a| → |x - a| < δ → |f x - b| < ε

def HasLeftLimitAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a (Set.Iio a)) (nhds b)

def EpsilonLeftLimitAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < a - x → a - x < δ → |f x - b| < ε

def HasRightLimitAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds b)

def EpsilonRightLimitAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < x - a → x - a < δ → |f x - b| < ε

def g (x : ℝ) : ℝ := x + 1

/-- Source: `proof_gap/exercise_403/1.txt`. -/
theorem gap1 : ∀ a b : ℝ, ∀ f : ℝ → ℝ,
    HasLimitAt f a b ↔ EpsilonLimitAt f a b := by
  intro a b f
  unfold HasLimitAt EpsilonLimitAt
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hxpos hxd
    have hxmem : x ∈ ({a} : Set ℝ)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact sub_ne_zero.mp (abs_pos.mp hxpos)
    have hdist : dist x a < δ := by
      simpa only [Real.dist_eq] using hxd
    have hout : dist (f x) b < ε := by
      apply hδprop
      · exact hxmem
      · exact hdist
    simpa only [Real.dist_eq] using hout
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hxmem hxd
    have hne : x ≠ a := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    have hxpos : 0 < |x - a| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    have hxabs : |x - a| < δ := by
      simpa only [Real.dist_eq] using hxd
    have hout := hδprop x hxpos hxabs
    simpa only [Real.dist_eq] using hout

/-- Source: `proof_gap/exercise_403/2.txt`. -/
theorem gap2 : HasLimitAt (fun x : ℝ => x + 1) 1 2 := by
  rw [gap1]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x _ hxd
  have heq : x + 1 - 2 = x - 1 := by ring
  rwa [heq]

/-- Source: `proof_gap/exercise_403/3.txt`. -/
theorem gap3 : ∀ a b : ℝ, ∀ f : ℝ → ℝ,
    HasLeftLimitAt f a b ↔ EpsilonLeftLimitAt f a b := by
  intro a b f
  unfold HasLeftLimitAt EpsilonLeftLimitAt
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hxpos hxd
    have hxa : x < a := sub_pos.mp hxpos
    have hxmem : x ∈ Set.Iio a := hxa
    have hdist : dist x a < δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hxa)]
      simpa only [neg_sub] using hxd
    have hout : dist (f x) b < ε := by
      apply hδprop
      · exact hxmem
      · exact hdist
    simpa only [Real.dist_eq] using hout
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hxmem hxd
    have hxa : x < a := hxmem
    have hxpos : 0 < a - x := sub_pos.mpr hxa
    have hxδ : a - x < δ := by
      simpa only [Real.dist_eq, abs_of_neg (sub_neg.mpr hxa), neg_sub] using hxd
    have hout := hδprop x hxpos hxδ
    simpa only [Real.dist_eq] using hout

/-- Source: `proof_gap/exercise_403/4.txt`; define the previously free example `g(x)=x+1`. -/
theorem gap4 : HasLeftLimitAt g 1 2 := by
  rw [gap3]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hxpos hxd
  unfold g
  have hxa : x < 1 := sub_pos.mp hxpos
  have heq : x + 1 - 2 = x - 1 := by ring
  rw [heq, abs_of_neg (sub_neg.mpr hxa)]
  simpa only [neg_sub] using hxd

/-- Source: `proof_gap/exercise_403/5.txt`. -/
theorem gap5 : ∀ a b : ℝ, ∀ f : ℝ → ℝ,
    HasRightLimitAt f a b ↔ EpsilonRightLimitAt f a b := by
  intro a b f
  unfold HasRightLimitAt EpsilonRightLimitAt
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hxpos hxd
    have hax : a < x := sub_pos.mp hxpos
    have hxmem : x ∈ Set.Ioi a := hax
    have hdist : dist x a < δ := by
      rw [Real.dist_eq, abs_of_pos hxpos]
      exact hxd
    have hout : dist (f x) b < ε := by
      apply hδprop
      · exact hxmem
      · exact hdist
    simpa only [Real.dist_eq] using hout
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hxmem hxd
    have hax : a < x := hxmem
    have hxpos : 0 < x - a := sub_pos.mpr hax
    have hxδ : x - a < δ := by
      simpa only [Real.dist_eq, abs_of_pos hxpos] using hxd
    have hout := hδprop x hxpos hxδ
    simpa only [Real.dist_eq] using hout

/-- Source: `proof_gap/exercise_403/6.txt`; define the previously free example `g(x)=x+1`. -/
theorem gap6 : HasRightLimitAt g 1 2 := by
  rw [gap5]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hxpos hxd
  unfold g
  have heq : x + 1 - 2 = x - 1 := by ring
  rw [heq, abs_of_pos hxpos]
  exact hxd

end

end ProofGap.Exercise403
