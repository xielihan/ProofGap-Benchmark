import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Bases

open Filter Topology

namespace ProofGap.Exercise122

def blockStart (n : ℕ) : ℕ :=
  n * (n - 1) / 2

def Construction (x a : ℕ → ℝ) : Prop :=
  ∀ n i : ℕ, 1 ≤ i → i ≤ n →
    x (blockStart n + i) = a i + 1 / ((n : ℝ) + 1)

private theorem clusterSet_iff_mapClusterPt (x : ℕ → ℝ) (v : ℝ) :
    v ∈ ProofGap.ClusterSet x ↔ MapClusterPt v atTop x := by
  constructor
  · rintro ⟨p, hp, hlim⟩
    exact hlim.mapClusterPt.of_comp hp.tendsto_atTop
  · intro hv
    exact TopologicalSpace.FirstCountableTopology.tendsto_subseq hv

private theorem clusterSet_isClosed (x : ℕ → ℝ) :
    IsClosed (ProofGap.ClusterSet x) := by
  have heq :
      ProofGap.ClusterSet x =
        {v : ℝ | MapClusterPt v atTop x} := by
    ext v
    exact clusterSet_iff_mapClusterPt x v
  rw [heq]
  exact isClosed_setOf_clusterPt

private theorem blockStart_succ (n : ℕ) :
    blockStart (n + 1) = blockStart n + n := by
  simpa [blockStart] using Nat.triangle_succ n

private theorem reciprocal_shift_tendsto (i : ℕ) :
    Tendsto (fun k : ℕ => 1 / (((i + k : ℕ) : ℝ) + 1))
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun k : ℕ => i + k) atTop atTop := by
    apply tendsto_atTop.2
    intro Q
    filter_upwards [eventually_ge_atTop Q] with k hk
    omega
  have hcast :
      Tendsto (fun k : ℕ => ((i + k : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hindex
  have hden :
      Tendsto (fun k : ℕ => ((i + k : ℕ) : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => by linarith) hcast
  simpa [one_div] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hden)

/-- Source: `proof_gap/exercise_122/1.txt`. -/
theorem gap1
    (x a : ℕ → ℝ)
    (h : ∀ n : ℕ, 0 < n → a n ∈ ProofGap.ClusterSet x) :
    ∀ n : ℕ, 0 < n → a n ∈ ProofGap.ClusterSet x := by
  exact h

/-- Source: `proof_gap/exercise_122/2.txt`. -/
theorem gap2
    (x a : ℕ → ℝ)
    (h : ∀ n : ℕ, 0 < n → a n ∈ ProofGap.ClusterSet x) :
    ProofGap.ClusterSet a ⊆ ProofGap.ClusterSet x := by
  intro v hv
  rcases hv with ⟨p, hp, hlim⟩
  apply (clusterSet_isClosed x).mem_of_tendsto hlim
  have hevent : ∀ᶠ k : ℕ in atTop, 0 < p k :=
    hp.tendsto_atTop (eventually_ge_atTop 1)
  filter_upwards [hevent] with k hk
  exact h (p k) hk

/-- Source: `proof_gap/exercise_122/3.txt`; the triangular ellipsis is explicit. -/
theorem gap3
    (x a : ℕ → ℝ)
    (hconstruct : Construction x a) :
    ∀ n : ℕ, 0 < n → a n ∈ ProofGap.ClusterSet x := by
  intro i hi
  let p : ℕ → ℕ := fun k => blockStart (i + k) + i
  have hp : StrictMono p := strictMono_nat_of_lt_succ fun k => by
    dsimp [p]
    rw [show i + (k + 1) = (i + k) + 1 by omega, blockStart_succ]
    omega
  refine ⟨p, hp, ?_⟩
  have h :
      Tendsto
        (fun k : ℕ => a i + 1 / (((i + k : ℕ) : ℝ) + 1))
        atTop (𝓝 (a i + 0)) :=
    tendsto_const_nhds.add (reciprocal_shift_tendsto i)
  norm_num at h
  apply h.congr'
  filter_upwards with k
  have hx := hconstruct (i + k) i (by omega) (by omega)
  simpa [p, Function.comp_apply] using hx.symm

end ProofGap.Exercise122
