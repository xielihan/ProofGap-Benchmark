import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2706_1

noncomputable section

theorem gap1 (a b c : ℕ → ℝ)
    (hc : ∀ n, c n = a n + b n)
    (ha : Summable a) (hb : ¬ Summable b)
    (hconv : Summable c) :
    Summable b ∧ ∑' n, b n = (∑' n, c n) - ∑' n, a n := by
  have hs : Summable b := by
    simpa [hc] using hconv.sub ha
  exact (hb hs).elim

theorem gap2 (a b c : ℕ → ℝ)
    (hc : ∀ n, c n = a n + b n)
    (ha : Summable a) (hb : ¬ Summable b)
    (hconv : Summable c) :
    Summable b := by
  exact (gap1 a b c hc ha hb hconv).1

theorem gap3 (a b c : ℕ → ℝ)
    (hc : ∀ n, c n = a n + b n)
    (ha : Summable a) (hb : ¬ Summable b) :
    Summable c → False := by
  intro hconv
  exact hb (gap2 a b c hc ha hb hconv)

theorem gap4 (a b c : ℕ → ℝ)
    (hc : ∀ n, c n = a n + b n)
    (ha : Summable a) (hb : ¬ Summable b) :
    ¬ Summable c := by
  exact gap3 a b c hc ha hb

theorem gap5 (a b c : ℕ → ℝ)
    (hc : ∀ n, c n = a n + b n)
    (ha : Summable a) (hb : ¬ Summable b) :
    ¬ Summable c := by
  exact gap4 a b c hc ha hb

end

end ProofGap.Exercise2706_1
