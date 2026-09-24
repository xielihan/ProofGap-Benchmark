import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Sequences

open Filter Topology

namespace ProofGap.Exercise131_1

noncomputable section

def sumSeq (x y : ℕ → ℝ) (n : ℕ) : ℝ := x n + y n

private theorem clusterSet_isClosed (x : ℕ → ℝ) :
    IsClosed (ProofGap.ClusterSet x) := by
  have heq :
      ProofGap.ClusterSet x = {v : ℝ | MapClusterPt v atTop x} := by
    ext v
    constructor
    · rintro ⟨p, hp, hlim⟩
      exact hlim.mapClusterPt.of_comp hp.tendsto_atTop
    · intro hv
      exact TopologicalSpace.FirstCountableTopology.tendsto_subseq hv
  rw [heq]
  exact isClosed_setOf_clusterPt

private theorem clusterSet_nonempty
    (x : ℕ → ℝ) (hx : Bornology.IsBounded (Set.range x)) :
    (ProofGap.ClusterSet x).Nonempty := by
  rcases tendsto_subseq_of_bounded hx (fun n => ⟨n, rfl⟩) with
    ⟨v, hv, p, hp, hlim⟩
  exact ⟨v, p, hp, hlim⟩

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

private theorem sumSeq_bounded
    (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    Bornology.IsBounded (Set.range (sumSeq x y)) := by
  rcases hx.subset_closedBall 0 with ⟨rx, hrx⟩
  rcases hy.subset_closedBall 0 with ⟨ry, hry⟩
  apply (Metric.isBounded_iff_subset_closedBall 0).2
  refine ⟨rx + ry, ?_⟩
  rintro z ⟨n, rfl⟩
  have hxabs : |x n| ≤ rx := by
    simpa [Real.dist_eq] using hrx ⟨n, rfl⟩
  have hyabs : |y n| ≤ ry := by
    simpa [Real.dist_eq] using hry ⟨n, rfl⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  simp only [sumSeq, sub_zero]
  exact (abs_add_le _ _).trans (add_le_add hxabs hyabs)

private theorem tendsto_y_of_sum_x
    (x y : ℕ → ℝ) (p : ℕ → ℕ) (α β : ℝ)
    (hsum : Tendsto (sumSeq x y ∘ p) atTop (𝓝 α))
    (hx : Tendsto (x ∘ p) atTop (𝓝 β)) :
    Tendsto (y ∘ p) atTop (𝓝 (α - β)) := by
  simpa [sumSeq, Function.comp_def] using hsum.sub hx

/-- Source: `proof_gap/exercise_131_1/1.txt`; boundedness ensures realization of limsup. -/
theorem gap1 (x : ℕ → ℝ) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (x ∘ p) atTop (𝓝 (ProofGap.seqLimsup x)) := by
  exact (clusterSet_isClosed x).csSup_mem
    (clusterSet_nonempty x hx) (clusterSet_bddAbove x hx)

/-- Source: `proof_gap/exercise_131_1/2.txt`. -/
theorem gap2 (y : ℕ → ℝ) (p : ℕ → ℕ) (β : ℝ)
    (hbounded : Bornology.IsBounded (Set.range y))
    (hp : StrictMono p)
    (hy : Tendsto (y ∘ p) atTop (𝓝 β)) :
    β ≤ ProofGap.seqLimsup y := by
  exact le_csSup (clusterSet_bddAbove y hbounded) ⟨p, hp, hy⟩

/-- Source: `proof_gap/exercise_131_1/3.txt`. -/
theorem gap3 (x y : ℕ → ℝ) (p : ℕ → ℕ) (α β : ℝ)
    (hx : Tendsto (x ∘ p) atTop (𝓝 α))
    (hy : Tendsto (y ∘ p) atTop (𝓝 β)) :
    Tendsto (sumSeq x y ∘ p) atTop (𝓝 (α + β)) := by
  simpa [sumSeq, Function.comp_def] using hx.add hy

/-- Source: `proof_gap/exercise_131_1/4.txt`. -/
theorem gap4 (x y : ℕ → ℝ) (p : ℕ → ℕ) (α β : ℝ)
    (hp : StrictMono p)
    (hlim : Tendsto (sumSeq x y ∘ p) atTop (𝓝 (α + β))) :
    α + β ∈ ProofGap.ClusterSet (sumSeq x y) := by
  exact ⟨p, hp, hlim⟩

/-- Source: `proof_gap/exercise_131_1/5.txt`; the source inequality is reversed. -/
theorem gap5 (x y : ℕ → ℝ) (α β : ℝ)
    (hbounded : Bornology.IsBounded (Set.range (sumSeq x y)))
    (hcluster : α + β ∈ ProofGap.ClusterSet (sumSeq x y)) :
    α + β ≤ ProofGap.seqLimsup (sumSeq x y) := by
  exact le_csSup (clusterSet_bddAbove (sumSeq x y) hbounded) hcluster

/-- Source: `proof_gap/exercise_131_1/6.txt`; retain the corrected direction. -/
theorem gap6 (x y : ℕ → ℝ) (α β : ℝ)
    (hbounded : Bornology.IsBounded (Set.range (sumSeq x y)))
    (hcluster : α + β ∈ ProofGap.ClusterSet (sumSeq x y)) :
    α + β ≤ ProofGap.seqLimsup (sumSeq x y) := by
  exact gap5 x y α β hbounded hcluster

/-- Source: `proof_gap/exercise_131_1/7.txt`. -/
theorem gap7 (x y : ℕ → ℝ) (α β : ℝ)
    (hα : α = ProofGap.seqLimsup x)
    (hβ : β ≤ ProofGap.seqLimsup y) :
    α + β ≤ ProofGap.seqLimsup x + ProofGap.seqLimsup y := by
  linarith

/-- Source: `proof_gap/exercise_131_1/8.txt`; use the valid bounded-sequence theorem. -/
theorem gap8 (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLimsup (sumSeq x y) ≤
      ProofGap.seqLimsup x + ProofGap.seqLimsup y := by
  let z := sumSeq x y
  have hz : Bornology.IsBounded (Set.range z) :=
    sumSeq_bounded x y hx hy
  rcases gap1 z hz with ⟨p, hp, hsum⟩
  rcases tendsto_subseq_of_bounded hx
      (x := x ∘ p) (fun n => ⟨p n, rfl⟩) with
    ⟨β, hβcl, q, hq, hxlim⟩
  have hpq : StrictMono (p ∘ q) := hp.comp hq
  have hsum' :
      Tendsto (z ∘ (p ∘ q)) atTop (𝓝 (ProofGap.seqLimsup z)) := by
    simpa [Function.comp_def] using hsum.comp hq.tendsto_atTop
  have hxlim' :
      Tendsto (x ∘ (p ∘ q)) atTop (𝓝 β) := by
    simpa [Function.comp_def] using hxlim
  have hylim :
      Tendsto (y ∘ (p ∘ q)) atTop
        (𝓝 (ProofGap.seqLimsup z - β)) :=
    tendsto_y_of_sum_x x y (p ∘ q) (ProofGap.seqLimsup z) β
      hsum' hxlim'
  have hβmem : β ∈ ProofGap.ClusterSet x := ⟨p ∘ q, hpq, hxlim'⟩
  have hγmem :
      ProofGap.seqLimsup z - β ∈ ProofGap.ClusterSet y :=
    ⟨p ∘ q, hpq, hylim⟩
  have hβ : β ≤ ProofGap.seqLimsup x :=
    le_csSup (clusterSet_bddAbove x hx) hβmem
  have hγ : ProofGap.seqLimsup z - β ≤ ProofGap.seqLimsup y :=
    le_csSup (clusterSet_bddAbove y hy) hγmem
  dsimp [z] at *
  linarith

/-- Source: `proof_gap/exercise_131_1/9.txt`. -/
theorem gap9 (x y : ℕ → ℝ)
    (hxy : Bornology.IsBounded (Set.range (sumSeq x y))) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (sumSeq x y ∘ p) atTop
        (𝓝 (ProofGap.seqLiminf (sumSeq x y))) := by
  exact (clusterSet_isClosed (sumSeq x y)).csInf_mem
    (clusterSet_nonempty (sumSeq x y) hxy)
    (clusterSet_bddBelow (sumSeq x y) hxy)

/-- Source: `proof_gap/exercise_131_1/10.txt`. -/
theorem gap10 (x : ℕ → ℝ) (p : ℕ → ℕ) (β' : ℝ)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hp : StrictMono p)
    (h : Tendsto (x ∘ p) atTop (𝓝 β')) :
    ProofGap.seqLiminf x ≤ β' := by
  exact csInf_le (clusterSet_bddBelow x hbounded) ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_131_1/11.txt`. -/
theorem gap11 (x y : ℕ → ℝ) (p : ℕ → ℕ) (α' β' : ℝ)
    (hsum : Tendsto (sumSeq x y ∘ p) atTop (𝓝 α'))
    (hx : Tendsto (x ∘ p) atTop (𝓝 β')) :
    Tendsto (y ∘ p) atTop (𝓝 (α' - β')) := by
  exact tendsto_y_of_sum_x x y p α' β' hsum hx

/-- Source: `proof_gap/exercise_131_1/12.txt`. -/
theorem gap12 (y : ℕ → ℝ) (p : ℕ → ℕ) (v : ℝ)
    (hp : StrictMono p) (h : Tendsto (y ∘ p) atTop (𝓝 v)) :
    v ∈ ProofGap.ClusterSet y := by
  exact ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_131_1/13.txt`. -/
theorem gap13 (y : ℕ → ℝ) (v : ℝ)
    (hbounded : Bornology.IsBounded (Set.range y))
    (h : v ∈ ProofGap.ClusterSet y) :
    ProofGap.seqLiminf y ≤ v := by
  exact csInf_le (clusterSet_bddBelow y hbounded) h

/-- Source: `proof_gap/exercise_131_1/14.txt`. -/
theorem gap14 (x y : ℕ → ℝ) :
    ProofGap.seqLiminf (sumSeq x y) =
      ProofGap.seqLiminf (sumSeq x y) := by
  rfl

/-- Source: `proof_gap/exercise_131_1/15.txt`. -/
theorem gap15 (α' β' : ℝ) (y : ℕ → ℝ)
    (h : ProofGap.seqLiminf y ≤ α' - β') :
    α' ≥ β' + ProofGap.seqLiminf y := by
  linarith

/-- Source: `proof_gap/exercise_131_1/16.txt`. -/
theorem gap16 (x y : ℕ → ℝ) (β' : ℝ)
    (h : ProofGap.seqLiminf x ≤ β') :
    β' + ProofGap.seqLiminf y ≥
      ProofGap.seqLiminf x + ProofGap.seqLiminf y := by
  linarith

/-- Source: `proof_gap/exercise_131_1/17.txt`. -/
theorem gap17 (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf (sumSeq x y) ≥
      ProofGap.seqLiminf x + ProofGap.seqLiminf y := by
  let z := sumSeq x y
  have hz : Bornology.IsBounded (Set.range z) :=
    sumSeq_bounded x y hx hy
  rcases gap9 x y hz with ⟨p, hp, hsum⟩
  rcases tendsto_subseq_of_bounded hx
      (x := x ∘ p) (fun n => ⟨p n, rfl⟩) with
    ⟨β, hβcl, q, hq, hxlim⟩
  have hpq : StrictMono (p ∘ q) := hp.comp hq
  have hsum' :
      Tendsto (z ∘ (p ∘ q)) atTop (𝓝 (ProofGap.seqLiminf z)) := by
    simpa [Function.comp_def] using hsum.comp hq.tendsto_atTop
  have hxlim' :
      Tendsto (x ∘ (p ∘ q)) atTop (𝓝 β) := by
    simpa [Function.comp_def] using hxlim
  have hylim :
      Tendsto (y ∘ (p ∘ q)) atTop
        (𝓝 (ProofGap.seqLiminf z - β)) :=
    tendsto_y_of_sum_x x y (p ∘ q) (ProofGap.seqLiminf z) β
      hsum' hxlim'
  have hβmem : β ∈ ProofGap.ClusterSet x := ⟨p ∘ q, hpq, hxlim'⟩
  have hγmem :
      ProofGap.seqLiminf z - β ∈ ProofGap.ClusterSet y :=
    ⟨p ∘ q, hpq, hylim⟩
  have hβ : ProofGap.seqLiminf x ≤ β :=
    csInf_le (clusterSet_bddBelow x hx) hβmem
  have hγ : ProofGap.seqLiminf y ≤ ProofGap.seqLiminf z - β :=
    csInf_le (clusterSet_bddBelow y hy) hγmem
  dsimp [z] at *
  linarith

/-- Source: `proof_gap/exercise_131_1/18.txt`. -/
theorem gap18 (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf x + ProofGap.seqLiminf y ≤
        ProofGap.seqLiminf (sumSeq x y) ∧
      ProofGap.seqLimsup (sumSeq x y) ≤
        ProofGap.seqLimsup x + ProofGap.seqLimsup y := by
  exact ⟨gap17 x y hx hy, gap8 x y hx hy⟩

end

end ProofGap.Exercise131_1
