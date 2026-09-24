import ProofGapLean.Prelude.Sequences
import ProofGapLean.Exercises.Exercise131_1

open Filter Topology

namespace ProofGap.Exercise131_2

noncomputable section

def sumSeq (x y : ℕ → ℝ) (n : ℕ) : ℝ := x n + y n

private theorem clusterSet_subset_closure_range (x : ℕ → ℝ) :
    ProofGap.ClusterSet x ⊆ closure (Set.range x) := by
  intro v hv
  rcases hv with ⟨p, hp, hlim⟩
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards with k
  exact subset_closure ⟨p k, rfl⟩

private theorem clusterSet_bddAbove
    (x : ℕ → ℝ) (hx : Bornology.IsBounded (Set.range x)) :
    BddAbove (ProofGap.ClusterSet x) :=
  ((hx.closure).subset (clusterSet_subset_closure_range x)).bddAbove

private theorem clusterSet_bddBelow
    (x : ℕ → ℝ) (hx : Bornology.IsBounded (Set.range x)) :
    BddBelow (ProofGap.ClusterSet x) :=
  ((hx.closure).subset (clusterSet_subset_closure_range x)).bddBelow

/-- Source: `proof_gap/exercise_131_2/1.txt`. -/
theorem gap1 (x y : ℕ → ℝ)
    (hxy : Bornology.IsBounded (Set.range (sumSeq x y))) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (sumSeq x y ∘ p) atTop
        (𝓝 (ProofGap.seqLimsup (sumSeq x y))) := by
  exact ProofGap.Exercise131_1.gap1 (sumSeq x y) hxy

/-- Source: `proof_gap/exercise_131_2/2.txt`. -/
theorem gap2 (x : ℕ → ℝ) (p : ℕ → ℕ) (τ : ℝ)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hp : StrictMono p)
    (h : Tendsto (x ∘ p) atTop (𝓝 τ)) :
    τ ≤ ProofGap.seqLimsup x := by
  exact le_csSup (clusterSet_bddAbove x hbounded) ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_131_2/3.txt`. -/
theorem gap3 (x y : ℕ → ℝ) (p : ℕ → ℕ) (r τ : ℝ)
    (hsum : Tendsto (sumSeq x y ∘ p) atTop (𝓝 r))
    (hx : Tendsto (x ∘ p) atTop (𝓝 τ)) :
    Tendsto (y ∘ p) atTop (𝓝 (r - τ)) := by
  simpa [sumSeq, Function.comp_def] using hsum.sub hx

/-- Source: `proof_gap/exercise_131_2/4.txt`. -/
theorem gap4 (y : ℕ → ℝ) (p : ℕ → ℕ) (v : ℝ)
    (hp : StrictMono p) (h : Tendsto (y ∘ p) atTop (𝓝 v)) :
    v ∈ ProofGap.ClusterSet y := by
  exact ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_131_2/5.txt`. -/
theorem gap5 (y : ℕ → ℝ) (v : ℝ)
    (hbounded : Bornology.IsBounded (Set.range y))
    (h : v ∈ ProofGap.ClusterSet y) :
    v ≤ ProofGap.seqLimsup y := by
  exact le_csSup (clusterSet_bddAbove y hbounded) h

/-- Source: `proof_gap/exercise_131_2/6.txt`. -/
theorem gap6 (x y : ℕ → ℝ) :
    ProofGap.seqLimsup (sumSeq x y) =
      ProofGap.seqLimsup (sumSeq x y) := by
  rfl

/-- Source: `proof_gap/exercise_131_2/7.txt`. -/
theorem gap7 (r τ : ℝ) (y : ℕ → ℝ)
    (h : r - τ ≤ ProofGap.seqLimsup y) :
    r ≤ τ + ProofGap.seqLimsup y := by
  linarith

/-- Source: `proof_gap/exercise_131_2/8.txt`. -/
theorem gap8 (x y : ℕ → ℝ) (τ : ℝ)
    (h : τ ≤ ProofGap.seqLimsup x) :
    τ + ProofGap.seqLimsup y ≤
      ProofGap.seqLimsup x + ProofGap.seqLimsup y := by
  linarith

/-- Source: `proof_gap/exercise_131_2/9.txt`. -/
theorem gap9 (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLimsup (sumSeq x y) ≤
      ProofGap.seqLimsup x + ProofGap.seqLimsup y := by
  simpa [sumSeq, ProofGap.Exercise131_1.sumSeq] using
    ProofGap.Exercise131_1.gap8 x y hx hy

/-- Source: `proof_gap/exercise_131_2/10.txt`; realize the liminf of the sum. -/
theorem gap10 (x y : ℕ → ℝ)
    (hxy : Bornology.IsBounded (Set.range (sumSeq x y))) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (sumSeq x y ∘ p) atTop
        (𝓝 (ProofGap.seqLiminf (sumSeq x y))) := by
  simpa [sumSeq, ProofGap.Exercise131_1.sumSeq] using
    ProofGap.Exercise131_1.gap9 x y hxy

/-- Source: `proof_gap/exercise_131_2/11.txt`. -/
theorem gap11 (x : ℕ → ℝ) (p : ℕ → ℕ) (τ' : ℝ)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hp : StrictMono p)
    (h : Tendsto (x ∘ p) atTop (𝓝 τ')) :
    τ' ≥ ProofGap.seqLiminf x := by
  exact csInf_le (clusterSet_bddBelow x hbounded) ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_131_2/12.txt`. -/
theorem gap12 (x y : ℕ → ℝ) (p : ℕ → ℕ) (r' τ' : ℝ)
    (hx : Tendsto (x ∘ p) atTop (𝓝 τ'))
    (hy : Tendsto (y ∘ p) atTop (𝓝 r')) :
    Tendsto (sumSeq x y ∘ p) atTop (𝓝 (r' + τ')) := by
  have h := hx.add hy
  simpa [sumSeq, Function.comp_def, add_comm] using h

/-- Source: `proof_gap/exercise_131_2/13.txt`. -/
theorem gap13 (x y : ℕ → ℝ) (p : ℕ → ℕ) (v : ℝ)
    (hp : StrictMono p)
    (h : Tendsto (sumSeq x y ∘ p) atTop (𝓝 v)) :
    v ∈ ProofGap.ClusterSet (sumSeq x y) := by
  exact ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_131_2/14.txt`; correct the reversed source direction. -/
theorem gap14 (x y : ℕ → ℝ) (v : ℝ)
    (hbounded : Bornology.IsBounded (Set.range (sumSeq x y)))
    (h : v ∈ ProofGap.ClusterSet (sumSeq x y)) :
    ProofGap.seqLiminf (sumSeq x y) ≤ v := by
  exact csInf_le (clusterSet_bddBelow (sumSeq x y) hbounded) h

/-- Source: `proof_gap/exercise_131_2/15.txt`; use a subsequence realizing the sum liminf. -/
theorem gap15 (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf (sumSeq x y) ≥
      ProofGap.seqLiminf x + ProofGap.seqLiminf y := by
  simpa [sumSeq, ProofGap.Exercise131_1.sumSeq] using
    ProofGap.Exercise131_1.gap17 x y hx hy

/-- Source: `proof_gap/exercise_131_2/16.txt`. -/
theorem gap16 (x y : ℕ → ℝ) (r' τ' : ℝ)
    (hx : ProofGap.seqLiminf x ≤ τ')
    (hy : ProofGap.seqLiminf y ≤ r') :
    r' + τ' ≥ ProofGap.seqLiminf x + ProofGap.seqLiminf y := by
  linarith

/-- Source: `proof_gap/exercise_131_2/17.txt`. -/
theorem gap17 (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf (sumSeq x y) ≥
      ProofGap.seqLiminf x + ProofGap.seqLiminf y := by
  exact gap15 x y hx hy

/-- Source: `proof_gap/exercise_131_2/18.txt`. -/
theorem gap18 (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf x + ProofGap.seqLiminf y ≤
        ProofGap.seqLiminf (sumSeq x y) ∧
      ProofGap.seqLimsup (sumSeq x y) ≤
        ProofGap.seqLimsup x + ProofGap.seqLimsup y := by
  exact ⟨gap17 x y hx hy, gap9 x y hx hy⟩

end

end ProofGap.Exercise131_2
