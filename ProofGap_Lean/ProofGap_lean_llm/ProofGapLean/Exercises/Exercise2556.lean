import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2556

def alternatingTerm (n : ℕ) : ℝ := (-1 : ℝ) ^ (n - 1)

theorem gap1 : ∀ n : ℕ, alternatingTerm n = (-1 : ℝ) ^ (n - 1) := by
  intro n
  rfl

theorem gap2
    (a : ℕ → ℝ)
    (ha : ∀ n, a n = alternatingTerm n) :
    ¬ ∃ L : ℝ, Tendsto a atTop (nhds L) := by
  rintro ⟨L, hL⟩
  have hnhds : Set.Ioo (L - 1) (L + 1) ∈ nhds L :=
    Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hL.eventually hnhds)
  have hp := hN (2 * N + 1) (by omega)
  have hm := hN (2 * N + 1 + 1) (by omega)
  have hone : alternatingTerm (2 * N + 1) = 1 := by
    simp [alternatingTerm, pow_mul]
  have hneg : alternatingTerm (2 * N + 1 + 1) = -1 := by
    simp [alternatingTerm, pow_succ, pow_mul]
  rw [ha (2 * N + 1), hone] at hp
  rw [ha (2 * N + 1 + 1), hneg] at hm
  linarith [hp.2, hm.1]

theorem gap3
    (a : ℕ → ℝ)
    (ha : ∀ n, a n = alternatingTerm n)
    (hdiv : ¬ ∃ L : ℝ, Tendsto a atTop (nhds L)) :
    ¬ Tendsto a atTop (nhds 0) := by
  intro hzero'
  exact hdiv ⟨0, hzero'⟩

theorem gap4
    (a : ℕ → ℝ)
    (ha : ∀ n, a n = alternatingTerm n)
    (hdiv : ¬ ∃ L : ℝ, Tendsto a atTop (nhds L))
    (hzero : ¬ Tendsto a atTop (nhds 0)) :
    ¬ Summable alternatingTerm := by
  intro hs
  have ha' : a = alternatingTerm := funext ha
  rw [ha'] at hzero
  exact hzero hs.tendsto_atTop_zero

end ProofGap.Exercise2556
