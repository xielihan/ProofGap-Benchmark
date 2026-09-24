import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise669_2

noncomputable section

def dyadic (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ n
def DyadicCondition (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ n ≥ 1, ∃ δ > 0, ∀ x,
    |x - x₀| < δ → |f x - f x₀| < dyadic n

/-- Source: `proof_gap/exercise_669_2/1.txt`. -/
theorem gap1 (ε : ℝ) (hε : 0 < ε) :
    ∃ n ≥ 1, dyadic n < ε := by
  have hlim :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max N 1, le_max_right N 1, ?_⟩
  simpa [dyadic, div_pow] using
    hN (max N 1) (le_max_left N 1)

/-- Source: `proof_gap/exercise_669_2/2.txt`; bind the dyadic continuity hypothesis. -/
theorem gap2 (f : ℝ → ℝ) (x₀ ε : ℝ)
    (hdyadic : DyadicCondition f x₀) (hε : 0 < ε) :
    ∃ n ≥ 1, ∃ δ > 0, ∀ x,
      |x - x₀| < δ → |f x - f x₀| < dyadic n := by
  exact ⟨1, le_rfl, hdyadic 1 le_rfl⟩

/-- Source: `proof_gap/exercise_669_2/3.txt`; remove shadowed existential binders. -/
theorem gap3 (f : ℝ → ℝ) (x₀ ε : ℝ)
    (hdyadic : DyadicCondition f x₀) (hε : 0 < ε) :
    ∃ n ≥ 1, ∃ δ > 0, ∀ x,
      |x - x₀| < δ →
        |f x - f x₀| < dyadic n ∧ dyadic n < ε := by
  obtain ⟨n, hn, hnε⟩ := gap1 ε hε
  obtain ⟨δ, hδ, hbound⟩ := hdyadic n hn
  refine ⟨n, hn, δ, hδ, ?_⟩
  intro x hx
  exact ⟨hbound x hx, hnε⟩

/-- Source: `proof_gap/exercise_669_2/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (x₀ : ℝ)
    (hdyadic : DyadicCondition f x₀) :
    ContinuousAt f x₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨n, hn, δ, hδ, hbound⟩ := gap3 f x₀ ε hdyadic hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hpair := hbound x (by simpa [Real.dist_eq] using hx)
  have hout : |f x - f x₀| < ε := lt_trans hpair.1 hpair.2
  simpa [Real.dist_eq] using hout

/-- Source: `proof_gap/exercise_669_2/5.txt`; corrected equivalence with dyadic epsilon tests. -/
theorem gap5 (f : ℝ → ℝ) (x₀ : ℝ) :
    ContinuousAt f x₀ ↔ DyadicCondition f x₀ := by
  constructor
  · intro hcont
    intro n hn
    have hpos : 0 < dyadic n := by
      unfold dyadic
      exact one_div_pos.mpr (pow_pos (by norm_num) n)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hbound⟩ := hcont (dyadic n) hpos
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    have hout := hbound (by simpa [Real.dist_eq] using hx)
    simpa [Real.dist_eq] using hout
  · intro hdyadic
    exact gap4 f x₀ hdyadic

end

end ProofGap.Exercise669_2
