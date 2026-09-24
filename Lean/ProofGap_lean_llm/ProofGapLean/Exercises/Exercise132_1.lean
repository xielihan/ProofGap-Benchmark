import ProofGapLean.Prelude.Sequences
import ProofGapLean.Exercises.Exercise131_1
import Mathlib.Topology.MetricSpace.Sequences

open Filter Topology

namespace ProofGap.Exercise132_1

noncomputable section

def prodSeq (x y : ℕ → ℝ) (n : ℕ) : ℝ := x n * y n

def Nonnegative (x : ℕ → ℝ) : Prop := ∀ n : ℕ, 0 ≤ x n

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

private theorem prodSeq_bounded
    (x y : ℕ → ℝ)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y)) :
    Bornology.IsBounded (Set.range (prodSeq x y)) := by
  rcases hx.subset_closedBall 0 with ⟨rx, hrx⟩
  rcases hy.subset_closedBall 0 with ⟨ry, hry⟩
  have hrx0 : 0 ≤ rx := by
    have := hrx ⟨0, rfl⟩
    exact (dist_nonneg.trans this)
  have hry0 : 0 ≤ ry := by
    have := hry ⟨0, rfl⟩
    exact (dist_nonneg.trans this)
  apply (Metric.isBounded_iff_subset_closedBall 0).2
  refine ⟨rx * ry, ?_⟩
  rintro z ⟨n, rfl⟩
  have hxabs : |x n| ≤ rx := by
    simpa [Real.dist_eq] using hrx ⟨n, rfl⟩
  have hyabs : |y n| ≤ ry := by
    simpa [Real.dist_eq] using hry ⟨n, rfl⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  simp only [prodSeq, sub_zero, abs_mul]
  exact mul_le_mul hxabs hyabs (abs_nonneg _) hrx0

/-- Source: `proof_gap/exercise_132_1/1.txt`; boundedness realizes limsup. -/
theorem gap1 (x : ℕ → ℝ) (hx0 : Nonnegative x)
    (hxb : Bornology.IsBounded (Set.range x)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (x ∘ p) atTop (𝓝 (ProofGap.seqLimsup x)) ∧
      0 ≤ ProofGap.seqLimsup x := by
  rcases ProofGap.Exercise131_1.gap1 x hxb with ⟨p, hp, hlim⟩
  refine ⟨p, hp, hlim, ?_⟩
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards with k
  exact hx0 (p k)

/-- Source: `proof_gap/exercise_132_1/2.txt`. -/
theorem gap2 (y : ℕ → ℝ) (p : ℕ → ℕ) (β : ℝ)
    (hy0 : Nonnegative y) (hy : Tendsto (y ∘ p) atTop (𝓝 β)) :
    0 ≤ β := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hy
  filter_upwards with k
  exact hy0 (p k)

/-- Source: `proof_gap/exercise_132_1/3.txt`. -/
theorem gap3 (y : ℕ → ℝ) (p : ℕ → ℕ) (β : ℝ)
    (hbounded : Bornology.IsBounded (Set.range y))
    (hp : StrictMono p)
    (hy : Tendsto (y ∘ p) atTop (𝓝 β)) :
    β ≤ ProofGap.seqLimsup y := by
  exact le_csSup (clusterSet_bddAbove y hbounded) ⟨p, hp, hy⟩

/-- Source: `proof_gap/exercise_132_1/4.txt`. -/
theorem gap4 (x y : ℕ → ℝ) (p : ℕ → ℕ) (α β : ℝ)
    (hx : Tendsto (x ∘ p) atTop (𝓝 α))
    (hy : Tendsto (y ∘ p) atTop (𝓝 β)) :
    Tendsto (prodSeq x y ∘ p) atTop (𝓝 (α * β)) := by
  simpa [prodSeq, Function.comp_def] using hx.mul hy

/-- Source: `proof_gap/exercise_132_1/5.txt`. -/
theorem gap5 (x y : ℕ → ℝ) (p : ℕ → ℕ) (v : ℝ)
    (hp : StrictMono p) (h : Tendsto (prodSeq x y ∘ p) atTop (𝓝 v)) :
    v ∈ ProofGap.ClusterSet (prodSeq x y) := by
  exact ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_132_1/6.txt`; correct the reversed cluster inequality. -/
theorem gap6 (x y : ℕ → ℝ) (v : ℝ)
    (hbounded : Bornology.IsBounded (Set.range (prodSeq x y)))
    (h : v ∈ ProofGap.ClusterSet (prodSeq x y)) :
    v ≤ ProofGap.seqLimsup (prodSeq x y) := by
  exact le_csSup (clusterSet_bddAbove (prodSeq x y) hbounded) h

/-- Source: `proof_gap/exercise_132_1/7.txt`. -/
theorem gap7 (x y : ℕ → ℝ) (α β : ℝ)
    (hα : α = ProofGap.seqLimsup x) (hα0 : 0 ≤ α)
    (hβ : β ≤ ProofGap.seqLimsup y) (hβ0 : 0 ≤ β) :
    α * β ≤ ProofGap.seqLimsup x * ProofGap.seqLimsup y := by
  subst α
  have hysup0 : 0 ≤ ProofGap.seqLimsup y := hβ0.trans hβ
  exact mul_le_mul le_rfl hβ hβ0 (by assumption)

/-- Source: `proof_gap/exercise_132_1/8.txt`; use a subsequence realizing product limsup. -/
theorem gap8 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hxb : Bornology.IsBounded (Set.range x))
    (hyb : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLimsup (prodSeq x y) ≤
      ProofGap.seqLimsup x * ProofGap.seqLimsup y := by
  have hprod_bdd := prodSeq_bounded x y hxb hyb
  rcases gap1 (prodSeq x y)
      (fun n => mul_nonneg (hx0 n) (hy0 n)) hprod_bdd with
    ⟨p, hp, hprod, hprod0⟩
  rcases tendsto_subseq_of_bounded hxb
      (x := x ∘ p) (fun n => ⟨p n, rfl⟩) with
    ⟨β, hβcl, q, hq, hxlim⟩
  have hpq : StrictMono (p ∘ q) := hp.comp hq
  rcases tendsto_subseq_of_bounded hyb
      (x := y ∘ (p ∘ q)) (fun n => ⟨(p ∘ q) n, rfl⟩) with
    ⟨γ, hγcl, r, hr, hylim⟩
  have hpqr : StrictMono ((p ∘ q) ∘ r) := hpq.comp hr
  have hprod' :
      Tendsto (prodSeq x y ∘ ((p ∘ q) ∘ r)) atTop
        (𝓝 (ProofGap.seqLimsup (prodSeq x y))) := by
    simpa [Function.comp_def] using
      (hprod.comp hq.tendsto_atTop).comp hr.tendsto_atTop
  have hxlim' :
      Tendsto (x ∘ ((p ∘ q) ∘ r)) atTop (𝓝 β) := by
    simpa [Function.comp_def] using hxlim.comp hr.tendsto_atTop
  have hylim' :
      Tendsto (y ∘ ((p ∘ q) ∘ r)) atTop (𝓝 γ) := by
    simpa [Function.comp_def] using hylim
  have hmul :
      Tendsto (prodSeq x y ∘ ((p ∘ q) ∘ r))
        atTop (𝓝 (β * γ)) := by
    simpa [prodSeq, Function.comp_def] using hxlim'.mul hylim'
  have heq : ProofGap.seqLimsup (prodSeq x y) = β * γ :=
    tendsto_nhds_unique hprod' hmul
  have hβmem : β ∈ ProofGap.ClusterSet x := ⟨(p ∘ q) ∘ r, hpqr, hxlim'⟩
  have hγmem : γ ∈ ProofGap.ClusterSet y := ⟨(p ∘ q) ∘ r, hpqr, hylim'⟩
  have hβle : β ≤ ProofGap.seqLimsup x :=
    le_csSup (clusterSet_bddAbove x hxb) hβmem
  have hγle : γ ≤ ProofGap.seqLimsup y :=
    le_csSup (clusterSet_bddAbove y hyb) hγmem
  have hβ0 : 0 ≤ β := gap2 x ((p ∘ q) ∘ r) β hx0 hxlim'
  have hγ0 : 0 ≤ γ := gap2 y ((p ∘ q) ∘ r) γ hy0 hylim'
  have hxsup0 : 0 ≤ ProofGap.seqLimsup x := hβ0.trans hβle
  rw [heq]
  exact mul_le_mul hβle hγle hγ0 hxsup0

/-- Source: `proof_gap/exercise_132_1/9.txt`. -/
theorem gap9 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hzero : ProofGap.seqLiminf x = 0) :
    ProofGap.seqLiminf x * ProofGap.seqLiminf y ≤
      ProofGap.seqLiminf (prodSeq x y) := by
  rw [hzero, zero_mul]
  unfold ProofGap.seqLiminf
  by_cases hne : (ProofGap.ClusterSet (prodSeq x y)).Nonempty
  · apply le_csInf hne
    intro v hv
    rcases hv with ⟨p, hp, hlim⟩
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards with k
    exact mul_nonneg (hx0 (p k)) (hy0 (p k))
  · have heq : ProofGap.ClusterSet (prodSeq x y) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [heq, Real.sInf_empty]

/-- Source: `proof_gap/exercise_132_1/10.txt`; remove the rebound N₀. -/
theorem gap10 (x : ℕ → ℝ)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hpos : 0 < ProofGap.seqLiminf x) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ < n → 0 < x n := by
  by_contra hnot
  push_neg at hnot
  have hfreq : ∃ᶠ n : ℕ in atTop, x n ≤ 0 := by
    rw [frequently_atTop']
    intro N
    rcases hnot N with ⟨n, hn, hxn⟩
    exact ⟨n, hn, hxn⟩
  rcases extraction_of_frequently_atTop hfreq with ⟨p, hp, hp_nonpos⟩
  rcases tendsto_subseq_of_bounded hbounded
      (x := x ∘ p) (fun n => ⟨p n, rfl⟩) with
    ⟨β, hβcl, q, hq, hlim⟩
  have hpq : StrictMono (p ∘ q) := hp.comp hq
  have hlim' : Tendsto (x ∘ (p ∘ q)) atTop (𝓝 β) := by
    simpa [Function.comp_def] using hlim
  have hβnonpos : β ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlim' tendsto_const_nhds
    filter_upwards with k
    exact hp_nonpos (q k)
  have hβmem : β ∈ ProofGap.ClusterSet x := ⟨p ∘ q, hpq, hlim'⟩
  have hinfle : ProofGap.seqLiminf x ≤ β :=
    csInf_le (clusterSet_bddBelow x hbounded) hβmem
  linarith

/-- Source: `proof_gap/exercise_132_1/11.txt`; choose one coherent subsequence. -/
theorem gap11 (x y : ℕ → ℝ)
    (hprod : Bornology.IsBounded (Set.range (prodSeq x y))) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (prodSeq x y ∘ p) atTop
        (𝓝 (ProofGap.seqLiminf (prodSeq x y))) := by
  have heq :
      ProofGap.Exercise131_1.sumSeq (prodSeq x y)
        (fun _ : ℕ => (0 : ℝ)) = prodSeq x y := by
    funext n
    simp [ProofGap.Exercise131_1.sumSeq]
  have hsum_bdd :
      Bornology.IsBounded
        (Set.range
          (ProofGap.Exercise131_1.sumSeq (prodSeq x y)
            (fun _ : ℕ => (0 : ℝ)))) := by
    rw [heq]
    exact hprod
  rcases ProofGap.Exercise131_1.gap9 (prodSeq x y)
      (fun _ : ℕ => (0 : ℝ)) hsum_bdd with ⟨p, hp, hlim⟩
  rw [heq] at hlim
  exact ⟨p, hp, hlim⟩

/-- Source: `proof_gap/exercise_132_1/12.txt`. -/
theorem gap12 (x : ℕ → ℝ) (p : ℕ → ℕ) (β' : ℝ)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hp : StrictMono p)
    (h : Tendsto (x ∘ p) atTop (𝓝 β')) :
    β' ≥ ProofGap.seqLiminf x := by
  exact csInf_le (clusterSet_bddBelow x hbounded) ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_132_1/13.txt`. -/
theorem gap13 (x : ℕ → ℝ) (βstar : ℝ)
    (h : ProofGap.seqLiminf x = βstar) :
    ProofGap.seqLiminf x = βstar := by
  exact h

/-- Source: `proof_gap/exercise_132_1/14.txt`. -/
theorem gap14 (βstar : ℝ) (h : 0 < βstar) : 0 < βstar := by
  exact h

/-- Source: `proof_gap/exercise_132_1/15.txt`. -/
theorem gap15 (x : ℕ → ℝ) (β' : ℝ)
    (hlo : 0 < ProofGap.seqLiminf x)
    (hβ : ProofGap.seqLiminf x ≤ β') :
    0 < β' := by
  linarith

/-- Source: `proof_gap/exercise_132_1/16.txt`. -/
theorem gap16 (x y : ℕ → ℝ) (p : ℕ → ℕ) (α' β' : ℝ)
    (hprod : Tendsto (prodSeq x y ∘ p) atTop (𝓝 α'))
    (hx : Tendsto (x ∘ p) atTop (𝓝 β'))
    (hβ : β' ≠ 0) :
    Tendsto (y ∘ p) atTop (𝓝 (α' / β')) := by
  have hdiv :
      Tendsto
        (fun k : ℕ => (prodSeq x y ∘ p) k / (x ∘ p) k)
        atTop (𝓝 (α' / β')) :=
    hprod.div hx hβ
  apply hdiv.congr'
  have hevent : ∀ᶠ k : ℕ in atTop, (x ∘ p) k ≠ 0 :=
    hx.eventually (isOpen_compl_singleton.mem_nhds hβ)
  filter_upwards [hevent] with k hk
  simp only [prodSeq, Function.comp_apply]
  have hk' : x (p k) ≠ 0 := by simpa [Function.comp_apply] using hk
  exact mul_div_cancel_left₀ (y (p k)) hk'

/-- Source: `proof_gap/exercise_132_1/17.txt`. -/
theorem gap17 (y : ℕ → ℝ) (p : ℕ → ℕ) (v : ℝ)
    (hp : StrictMono p) (h : Tendsto (y ∘ p) atTop (𝓝 v)) :
    v ∈ ProofGap.ClusterSet y := by
  exact ⟨p, hp, h⟩

/-- Source: `proof_gap/exercise_132_1/18.txt`. -/
theorem gap18 (y : ℕ → ℝ) (v : ℝ)
    (hbounded : Bornology.IsBounded (Set.range y))
    (h : v ∈ ProofGap.ClusterSet y) :
    v ≥ ProofGap.seqLiminf y := by
  exact csInf_le (clusterSet_bddBelow y hbounded) h

/-- Source: `proof_gap/exercise_132_1/19.txt`. -/
theorem gap19 (x y : ℕ → ℝ) :
    ProofGap.seqLiminf (prodSeq x y) =
      ProofGap.seqLiminf (prodSeq x y) := by
  rfl

/-- Source: `proof_gap/exercise_132_1/20.txt`. -/
theorem gap20 (α' β' l : ℝ)
    (hβ : 0 < β') (hdiv : l ≤ α' / β') :
    α' ≥ β' * l := by
  exact (le_div_iff₀' hβ).mp hdiv

/-- Source: `proof_gap/exercise_132_1/21.txt`. -/
theorem gap21 (lx ly β' : ℝ)
    (hlx : lx ≤ β') (hlx0 : 0 ≤ lx) (hly0 : 0 ≤ ly) :
    β' * ly ≥ lx * ly := by
  exact mul_le_mul_of_nonneg_right hlx hly0

/-- Source: `proof_gap/exercise_132_1/22.txt`. -/
theorem gap22 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hxb : Bornology.IsBounded (Set.range x))
    (hyb : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf (prodSeq x y) ≥
      ProofGap.seqLiminf x * ProofGap.seqLiminf y := by
  have hprod_bdd := prodSeq_bounded x y hxb hyb
  rcases gap11 x y hprod_bdd with ⟨p, hp, hprod⟩
  rcases tendsto_subseq_of_bounded hxb
      (x := x ∘ p) (fun n => ⟨p n, rfl⟩) with
    ⟨β, hβcl, q, hq, hxlim⟩
  have hpq : StrictMono (p ∘ q) := hp.comp hq
  rcases tendsto_subseq_of_bounded hyb
      (x := y ∘ (p ∘ q)) (fun n => ⟨(p ∘ q) n, rfl⟩) with
    ⟨γ, hγcl, r, hr, hylim⟩
  have hpqr : StrictMono ((p ∘ q) ∘ r) := hpq.comp hr
  have hprod' :
      Tendsto (prodSeq x y ∘ ((p ∘ q) ∘ r)) atTop
        (𝓝 (ProofGap.seqLiminf (prodSeq x y))) := by
    simpa [Function.comp_def] using
      (hprod.comp hq.tendsto_atTop).comp hr.tendsto_atTop
  have hxlim' :
      Tendsto (x ∘ ((p ∘ q) ∘ r)) atTop (𝓝 β) := by
    simpa [Function.comp_def] using hxlim.comp hr.tendsto_atTop
  have hylim' :
      Tendsto (y ∘ ((p ∘ q) ∘ r)) atTop (𝓝 γ) := by
    simpa [Function.comp_def] using hylim
  have hmul :
      Tendsto (prodSeq x y ∘ ((p ∘ q) ∘ r))
        atTop (𝓝 (β * γ)) := by
    simpa [prodSeq, Function.comp_def] using hxlim'.mul hylim'
  have heq : ProofGap.seqLiminf (prodSeq x y) = β * γ :=
    tendsto_nhds_unique hprod' hmul
  have hβmem : β ∈ ProofGap.ClusterSet x := ⟨(p ∘ q) ∘ r, hpqr, hxlim'⟩
  have hγmem : γ ∈ ProofGap.ClusterSet y := ⟨(p ∘ q) ∘ r, hpqr, hylim'⟩
  have hβge : ProofGap.seqLiminf x ≤ β :=
    csInf_le (clusterSet_bddBelow x hxb) hβmem
  have hγge : ProofGap.seqLiminf y ≤ γ :=
    csInf_le (clusterSet_bddBelow y hyb) hγmem
  have hβ0 : 0 ≤ β := gap2 x ((p ∘ q) ∘ r) β hx0 hxlim'
  have hγ0 : 0 ≤ γ := gap2 y ((p ∘ q) ∘ r) γ hy0 hylim'
  have hly0 : 0 ≤ ProofGap.seqLiminf y := by
    apply le_csInf ⟨γ, hγmem⟩
    intro v hv
    rcases hv with ⟨s, hs, hvlim⟩
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hvlim
    filter_upwards with k
    exact hy0 (s k)
  rw [heq]
  exact mul_le_mul hβge hγge hly0 hβ0

/-- Source: `proof_gap/exercise_132_1/23.txt`. -/
theorem gap23 (x y : ℕ → ℝ)
    (hx0 : Nonnegative x) (hy0 : Nonnegative y)
    (hxb : Bornology.IsBounded (Set.range x))
    (hyb : Bornology.IsBounded (Set.range y)) :
    ProofGap.seqLiminf x * ProofGap.seqLiminf y ≤
        ProofGap.seqLiminf (prodSeq x y) ∧
      ProofGap.seqLimsup (prodSeq x y) ≤
        ProofGap.seqLimsup x * ProofGap.seqLimsup y := by
  exact ⟨gap22 x y hx0 hy0 hxb hyb, gap8 x y hx0 hy0 hxb hyb⟩

end

end ProofGap.Exercise132_1
