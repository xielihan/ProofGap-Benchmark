import ProofGapLean.Prelude.Sequences
import ProofGapLean.Exercises.Exercise132_1

open Filter Topology

namespace ProofGap.Exercise132_2

noncomputable section

def prodSeq (x y : ℕ → ℝ) (n : ℕ) : ℝ := x n * y n
def Nonnegative (x : ℕ → ℝ) : Prop := ∀ n : ℕ, 0 ≤ x n

def ExtendedUpperProductBound (x y : ℕ → ℝ) : Prop :=
  ¬ BddAbove (Set.range y) ∨
    ProofGap.seqLimsup (prodSeq x y) ≤
      ProofGap.seqLimsup x * ProofGap.seqLimsup y

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

/-- Source: `proof_gap/exercise_132_2/1.txt`. -/
theorem gap1 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hyb : Bornology.IsBounded (Set.range y))
    (hprod : Bornology.IsBounded (Set.range (prodSeq x y))) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (prodSeq x y ∘ p) atTop
        (𝓝 (ProofGap.seqLimsup (prodSeq x y))) ∧
      0 ≤ ProofGap.seqLimsup (prodSeq x y) := by
  simpa [prodSeq, Nonnegative, ProofGap.Exercise132_1.prodSeq,
    ProofGap.Exercise132_1.Nonnegative] using
    ProofGap.Exercise132_1.gap1 (prodSeq x y)
      (fun n => mul_nonneg (hx0 n) (hy0 n)) hprod

/-- Source: `proof_gap/exercise_132_2/2.txt`. -/
theorem gap2 (x : ℕ → ℝ) (p : ℕ → ℕ) (β : ℝ)
    (hx0 : Nonnegative x) (h : Tendsto (x ∘ p) atTop (𝓝 β)) :
    0 ≤ β := by
  exact ProofGap.Exercise132_1.gap2 x p β hx0 h

/-- Source: `proof_gap/exercise_132_2/3.txt`. -/
theorem gap3 (x y : ℕ → ℝ) (p : ℕ → ℕ) (α : ℝ)
    (hβ : Tendsto (x ∘ p) atTop (𝓝 0))
    (hyb : Bornology.IsBounded (Set.range y)) :
    Tendsto (prodSeq x y ∘ p) atTop (𝓝 0) := by
  rcases hyb.subset_closedBall 0 with ⟨R, hR⟩
  have hxnorm :
      Tendsto (fun k : ℕ => |x (p k)|) atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hβ.norm
  have hupper :
      Tendsto (fun k : ℕ => R * |x (p k)|) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hxnorm
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k => norm_nonneg _
  · apply Filter.Eventually.of_forall
    intro k
    have hyabs : |y (p k)| ≤ R := by
      simpa [Real.dist_eq] using hR ⟨p k, rfl⟩
    simp only [prodSeq, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
  · simpa [Real.norm_eq_abs, mul_comm] using hupper

/-- Source: `proof_gap/exercise_132_2/4.txt`. -/
theorem gap4 (α : ℝ) (hα : α = 0) : α = 0 := by
  exact hα

/-- Source: `proof_gap/exercise_132_2/5.txt`. -/
theorem gap5 (x : ℕ → ℝ) (p : ℕ → ℕ) (β : ℝ)
    (hβ : Tendsto (x ∘ p) atTop (𝓝 β)) (hpos : 0 < β) :
    ∀ᶠ i in atTop, 0 < x (p i) := by
  exact hβ.eventually (Ioi_mem_nhds hpos)

/-- Source: `proof_gap/exercise_132_2/6.txt`. -/
theorem gap6 (x y : ℕ → ℝ) (p : ℕ → ℕ) (α β : ℝ)
    (hprod : Tendsto (prodSeq x y ∘ p) atTop (𝓝 α))
    (hx : Tendsto (x ∘ p) atTop (𝓝 β)) (hβ : 0 < β) :
    Tendsto (y ∘ p) atTop (𝓝 (α / β)) := by
  apply ProofGap.Exercise132_1.gap16 x y p α β _ hx hβ.ne'
  simpa [prodSeq, ProofGap.Exercise132_1.prodSeq] using hprod

/-- Source: `proof_gap/exercise_132_2/7.txt`. -/
theorem gap7 (y : ℕ → ℝ) (p : ℕ → ℕ) (v : ℝ)
    (hp : StrictMono p) (h : Tendsto (y ∘ p) atTop (𝓝 v)) :
    v ∈ ProofGap.ClusterSet y := by
  exact ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_132_2/8.txt`. -/
theorem gap8 (y : ℕ → ℝ) (v : ℝ)
    (hbounded : Bornology.IsBounded (Set.range y))
    (h : v ∈ ProofGap.ClusterSet y) :
    v ≤ ProofGap.seqLimsup y := by
  exact le_csSup (clusterSet_bddAbove y hbounded) h

/-- Source: `proof_gap/exercise_132_2/9.txt`. -/
theorem gap9 (x y : ℕ → ℝ) :
    ProofGap.seqLimsup (prodSeq x y) =
      ProofGap.seqLimsup (prodSeq x y) := by
  rfl

/-- Source: `proof_gap/exercise_132_2/10.txt`. -/
theorem gap10 (α β ly : ℝ)
    (hβ : 0 < β) (h : α / β ≤ ly) :
    α ≤ β * ly := by
  simpa [mul_comm] using (div_le_iff₀ hβ).mp h

/-- Source: `proof_gap/exercise_132_2/11.txt`. -/
theorem gap11 (lx ly β : ℝ)
    (hβ : β ≤ lx) (hβ0 : 0 ≤ β) (hly0 : 0 ≤ ly) :
    β * ly ≤ lx * ly := by
  exact mul_le_mul_of_nonneg_right hβ hly0

/-- Source: `proof_gap/exercise_132_2/12.txt`. -/
theorem gap12 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hxb : Bornology.IsBounded (Set.range x))
    (hyb : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLimsup (prodSeq x y) ≤
      ProofGap.seqLimsup x * ProofGap.seqLimsup y := by
  simpa [prodSeq, Nonnegative, ProofGap.Exercise132_1.prodSeq,
    ProofGap.Exercise132_1.Nonnegative] using
    ProofGap.Exercise132_1.gap8 x y hx0 hy0 hxb hyb

/-- Source: `proof_gap/exercise_132_2/13.txt`; +∞ limsup is unboundedness above. -/
theorem gap13 (y : ℕ → ℝ) (hy0 : Nonnegative y)
    (hunbounded : ¬ Bornology.IsBounded (Set.range y)) :
    ¬ BddAbove (Set.range y) := by
  intro habove
  apply hunbounded
  apply isBounded_iff_bddBelow_bddAbove.2
  refine ⟨⟨0, ?_⟩, habove⟩
  intro v hv
  rcases hv with ⟨n, hn⟩
  rw [← hn]
  exact hy0 n

/-- Source: `proof_gap/exercise_132_2/14.txt`; the extended-real upper bound is automatic. -/
theorem gap14 (x y : ℕ → ℝ)
    (hy : ¬ BddAbove (Set.range y)) :
    ExtendedUpperProductBound x y := by
  exact Or.inl hy

/-- Source: `proof_gap/exercise_132_2/15.txt`. -/
theorem gap15 (y : ℕ → ℝ)
    (hy0 : Nonnegative y)
    (hyb : Bornology.IsBounded (Set.range y)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (y ∘ p) atTop (𝓝 (ProofGap.seqLiminf y)) ∧
      0 ≤ ProofGap.seqLiminf y := by
  have heq :
      ProofGap.Exercise132_1.prodSeq y (fun _ : ℕ => (1 : ℝ)) = y := by
    funext n
    simp [ProofGap.Exercise132_1.prodSeq]
  have hprod_bdd :
      Bornology.IsBounded
        (Set.range
          (ProofGap.Exercise132_1.prodSeq y (fun _ : ℕ => (1 : ℝ)))) := by
    rw [heq]
    exact hyb
  rcases ProofGap.Exercise132_1.gap11 y (fun _ : ℕ => (1 : ℝ)) hprod_bdd with
    ⟨p, hp, hlim⟩
  rw [heq] at hlim
  refine ⟨p, hp, hlim, ?_⟩
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards with k
  exact hy0 (p k)

/-- Source: `proof_gap/exercise_132_2/16.txt`. -/
theorem gap16 (x : ℕ → ℝ) (p : ℕ → ℕ) (τ : ℝ)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hp : StrictMono p)
    (h : Tendsto (x ∘ p) atTop (𝓝 τ)) :
    τ ≥ ProofGap.seqLiminf x := by
  exact csInf_le (clusterSet_bddBelow x hbounded) ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_132_2/17.txt`. -/
theorem gap17 (x : ℕ → ℝ) (hx0 : Nonnegative x) :
    ProofGap.seqLiminf x ≥ 0 := by
  unfold ProofGap.seqLiminf
  by_cases hne : (ProofGap.ClusterSet x).Nonempty
  · apply le_csInf hne
    intro v hv
    rcases hv with ⟨p, hp, hlim⟩
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards with k
    exact hx0 (p k)
  · have heq : ProofGap.ClusterSet x = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [heq, Real.sInf_empty]

/-- Source: `proof_gap/exercise_132_2/18.txt`. -/
theorem gap18 (τ : ℝ) (h : 0 ≤ τ) : 0 ≤ τ := by
  exact h

/-- Source: `proof_gap/exercise_132_2/19.txt`. -/
theorem gap19 (x y : ℕ → ℝ) (p : ℕ → ℕ) (τ r : ℝ)
    (hx : Tendsto (x ∘ p) atTop (𝓝 τ))
    (hy : Tendsto (y ∘ p) atTop (𝓝 r)) :
    Tendsto (prodSeq x y ∘ p) atTop (𝓝 (τ * r)) := by
  simpa [prodSeq, Function.comp_def] using hx.mul hy

/-- Source: `proof_gap/exercise_132_2/20.txt`. -/
theorem gap20 (x y : ℕ → ℝ) (p : ℕ → ℕ) (v : ℝ)
    (hp : StrictMono p) (h : Tendsto (prodSeq x y ∘ p) atTop (𝓝 v)) :
    v ∈ ProofGap.ClusterSet (prodSeq x y) := by
  exact ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_132_2/21.txt`. -/
theorem gap21 (lx ly τ r : ℝ)
    (hx : lx ≤ τ) (hy : ly ≤ r)
    (hlx0 : 0 ≤ lx) (hly0 : 0 ≤ ly)
    (hτ0 : 0 ≤ τ) (hr0 : 0 ≤ r) :
    lx * ly ≤ τ * r := by
  exact mul_le_mul hx hy hly0 hτ0

/-- Source: `proof_gap/exercise_132_2/22.txt`. -/
theorem gap22 (x y : ℕ → ℝ) (v : ℝ)
    (hbounded : Bornology.IsBounded (Set.range (prodSeq x y)))
    (h : v ∈ ProofGap.ClusterSet (prodSeq x y)) :
    v ≥ ProofGap.seqLiminf (prodSeq x y) := by
  exact csInf_le (clusterSet_bddBelow (prodSeq x y) hbounded) h

/-- Source: `proof_gap/exercise_132_2/23.txt`. -/
theorem gap23 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hxb : Bornology.IsBounded (Set.range x))
    (hyb : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf x * ProofGap.seqLiminf y ≤
      ProofGap.seqLiminf (prodSeq x y) := by
  simpa [prodSeq, Nonnegative, ProofGap.Exercise132_1.prodSeq,
    ProofGap.Exercise132_1.Nonnegative] using
    ProofGap.Exercise132_1.gap22 x y hx0 hy0 hxb hyb

/-- Source: `proof_gap/exercise_132_2/24.txt`; use an explicit extended upper case. -/
theorem gap24 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hlower : ProofGap.seqLiminf x * ProofGap.seqLiminf y ≤
      ProofGap.seqLiminf (prodSeq x y))
    (hupper : ExtendedUpperProductBound x y) :
    ProofGap.seqLiminf x * ProofGap.seqLiminf y ≤
        ProofGap.seqLiminf (prodSeq x y) ∧
      ExtendedUpperProductBound x y := by
  exact ⟨hlower, hupper⟩

end

end ProofGap.Exercise132_2
