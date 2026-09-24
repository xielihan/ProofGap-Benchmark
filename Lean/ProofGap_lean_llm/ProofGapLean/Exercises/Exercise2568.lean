import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2568

noncomputable section

def squareSeq (a : ℕ → ℝ) (n : ℕ) : ℝ := (a n) ^ 2
def harmonic (n : ℕ) : ℝ := 1 / (n : ℝ)

def TailSummable (u : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  Summable (fun k : ℕ => u (k + n₀))

theorem gap1
    (a : ℕ → ℝ) (hsum : Summable a)
    (hnonneg : ∀ n, 0 ≤ a n) :
    Tendsto a atTop (nhds 0) := by
  exact hsum.tendsto_atTop_zero

theorem gap2
    (a : ℕ → ℝ) (hsum : Summable a)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hzero : Tendsto a atTop (nhds 0)) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀, 0 ≤ a n ∧ a n < 1 := by
  have hlt : ∀ᶠ n in atTop, a n < 1 :=
    (tendsto_order.1 hzero).2 1 zero_lt_one
  rcases (Filter.eventually_atTop.1 hlt) with ⟨N, hN⟩
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  exact ⟨hnonneg n, hN n (le_trans (le_max_right _ _) hn)⟩

theorem gap3
    (a : ℕ → ℝ)
    (heventual : ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n ≥ n₀, 0 ≤ a n ∧ a n < 1) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
      0 ≤ squareSeq a n ∧ squareSeq a n ≤ a n := by
  rcases heventual with ⟨n₀, hn₀, hbound⟩
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn
  have ha := hbound n hn
  constructor
  · exact sq_nonneg (a n)
  · simp only [squareSeq]
    nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2.le)]

theorem gap4
    (a : ℕ → ℝ) (hsum : Summable a) :
    ∀ n₀ : ℕ, TailSummable a n₀ := by
  intro n₀
  exact (summable_nat_add_iff n₀).2 hsum

theorem gap5
    (a : ℕ → ℝ)
    (hsum : Summable a)
    (hsquareBound : ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
      0 ≤ squareSeq a n ∧ squareSeq a n ≤ a n)
    (htail : ∀ n₀ : ℕ, TailSummable a n₀) :
    ∃ n₀ : ℕ, TailSummable (squareSeq a) n₀ := by
  rcases hsquareBound with ⟨n₀, hn₀, hbound⟩
  refine ⟨n₀, ?_⟩
  apply Summable.of_nonneg_of_le
  · intro k
    exact (hbound (k + n₀) (by omega)).1
  · intro k
    exact (hbound (k + n₀) (by omega)).2
  · exact htail n₀

theorem gap6
    (a : ℕ → ℝ)
    (htailSquare : ∃ n₀ : ℕ, TailSummable (squareSeq a) n₀) :
    Summable (squareSeq a) := by
  rcases htailSquare with ⟨n₀, htail⟩
  exact (summable_nat_add_iff n₀).1 htail

theorem gap7 :
    Summable (squareSeq harmonic) := by
  refine (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).congr ?_
  intro n
  simp only [squareSeq, harmonic, one_div, inv_pow]

theorem gap8 :
    ¬ Summable harmonic := by
  intro hsum
  apply Real.not_summable_one_div_natCast
  apply hsum.congr
  intro n
  simp only [harmonic, one_div]

theorem gap9
    (hsquare : Summable (squareSeq harmonic))
    (hdiv : ¬ Summable harmonic) :
    ¬ (Summable (squareSeq harmonic) → Summable harmonic) := by
  intro himp
  exact hdiv (himp hsquare)

theorem gap10
    (hsquare : Summable (squareSeq harmonic))
    (hfailure : ¬ (Summable (squareSeq harmonic) → Summable harmonic)) :
    Summable (squareSeq harmonic) ∧
      ¬ (Summable (squareSeq harmonic) → Summable harmonic) := by
  exact ⟨hsquare, hfailure⟩

end

end ProofGap.Exercise2568
