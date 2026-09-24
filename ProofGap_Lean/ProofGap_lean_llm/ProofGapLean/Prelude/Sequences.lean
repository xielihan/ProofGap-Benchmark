import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Filters, real topology, asymptotics, and shared sequence notions. -/

open Filter
open scoped Topology
export Filter (Tendsto atTop atBot)

namespace ProofGap

def ClusterSet (x : ℕ → ℝ) : Set ℝ :=
  {a | ∃ p : ℕ → ℕ, StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 a)}

def ConvergentSeq (x : ℕ → ℝ) : Prop :=
  ∃ a : ℝ, Tendsto x atTop (𝓝 a)

/-- Convergence of a real series in its natural order.

Mathlib's bare `Summable` uses the unconditional summation filter.  Textbook
real series, including conditionally convergent alternating series, instead
use the ordered partial sums over `0, …, n - 1`.
-/
def SeriesHasSum (a : ℕ → ℝ) (s : ℝ) : Prop :=
  HasSum a s (SummationFilter.conditional ℕ)

/-- A real series converges in its natural order. -/
def SeriesConverges (a : ℕ → ℝ) : Prop :=
  Summable a (SummationFilter.conditional ℕ)

noncomputable def seqLiminf (x : ℕ → ℝ) : ℝ :=
  sInf (ClusterSet x)

noncomputable def seqLimsup (x : ℕ → ℝ) : ℝ :=
  sSup (ClusterSet x)

end ProofGap
