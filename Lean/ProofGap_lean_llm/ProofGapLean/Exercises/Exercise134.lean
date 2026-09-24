import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Sequences

open Filter Topology

namespace ProofGap.Exercise134

noncomputable section

def Nonnegative (x : ℕ → ℝ) : Prop := ∀ n : ℕ, 0 ≤ x n

def addWitness (x : ℕ → ℝ) (p : ℕ → ℕ) (A : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ Set.range p then A else -x n

def mulWitness (p : ℕ → ℕ) (A : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ Set.range p then A else 0

def UniversalEqualityProperty (x : ℕ → ℝ) : Prop :=
  ∀ y : ℕ → ℝ,
    ProofGap.seqLimsup (fun n => x n + y n) =
        ProofGap.seqLimsup x + ProofGap.seqLimsup y ∨
      ProofGap.seqLimsup (fun n => x n * y n) =
        ProofGap.seqLimsup x * ProofGap.seqLimsup y

private theorem clusterSet_subset_closure_range (x : ℕ → ℝ) :
    ProofGap.ClusterSet x ⊆ closure (Set.range x) := by
  intro v hv
  rcases hv with ⟨p, hp, hlim⟩
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards with k
  exact subset_closure ⟨p k, rfl⟩

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

private theorem clusterSet_bddAbove
    (x : ℕ → ℝ) (hx : Bornology.IsBounded (Set.range x)) :
    BddAbove (ProofGap.ClusterSet x) :=
  ((hx.closure).subset (clusterSet_subset_closure_range x)).bddAbove

private theorem clusterSet_bddBelow
    (x : ℕ → ℝ) (hx : Bornology.IsBounded (Set.range x)) :
    BddBelow (ProofGap.ClusterSet x) :=
  ((hx.closure).subset (clusterSet_subset_closure_range x)).bddBelow

private theorem tendsto_of_bounded_of_liminf_eq_limsup
    (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (heq : ProofGap.seqLiminf x = ProofGap.seqLimsup x) :
    Tendsto x atTop (𝓝 (ProofGap.seqLiminf x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra h
  push_neg at h
  have hfreq :
      ∃ᶠ n in atTop, ε ≤ dist (x n) (ProofGap.seqLiminf x) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hdist⟩ := h N
    exact ⟨n, hn, hdist⟩
  obtain ⟨p, hp, hpdist⟩ := extraction_of_frequently_atTop hfreq
  rcases tendsto_subseq_of_bounded hxb
      (x := x ∘ p) (fun n => ⟨p n, rfl⟩) with
    ⟨v, hv, q, hq, hlim⟩
  have hpq : StrictMono (p ∘ q) := hp.comp hq
  have hlim' : Tendsto (x ∘ (p ∘ q)) atTop (𝓝 v) := by
    simpa [Function.comp_def] using hlim
  have hv_mem : v ∈ ProofGap.ClusterSet x := ⟨p ∘ q, hpq, hlim'⟩
  have hlo : ProofGap.seqLiminf x ≤ v :=
    csInf_le (clusterSet_bddBelow x hxb) hv_mem
  have hhi : v ≤ ProofGap.seqLimsup x :=
    le_csSup (clusterSet_bddAbove x hxb) hv_mem
  have hv_eq : v = ProofGap.seqLiminf x := by
    apply le_antisymm
    · simpa [heq] using hhi
    · exact hlo
  have hdistlim :
      Tendsto (fun n => dist (x (p (q n))) (ProofGap.seqLiminf x))
        atTop (𝓝 (dist v (ProofGap.seqLiminf x))) := by
    exact hlim'.dist tendsto_const_nhds
  have hdist_ge : ε ≤ dist v (ProofGap.seqLiminf x) := by
    apply ge_of_tendsto hdistlim
    filter_upwards with n
    exact hpdist (q n)
  rw [hv_eq, dist_self] at hdist_ge
  exact (not_le_of_gt hε) hdist_ge

private theorem seqLimsup_eq_of_range_limit
    (z : ℕ → ℝ) (p : ℕ → ℕ) (L : ℝ)
    (hp : StrictMono p)
    (hlim : Tendsto (z ∘ p) atTop (𝓝 L))
    (hoff : ∀ n, n ∉ Set.range p → z n ≤ 0)
    (hL0 : 0 ≤ L) :
    ProofGap.seqLimsup z = L := by
  have hLmem : L ∈ ProofGap.ClusterSet z := ⟨p, hp, hlim⟩
  have hub : ∀ v ∈ ProofGap.ClusterSet z, v ≤ L := by
    intro v hv
    rcases hv with ⟨q, hq, hvlim⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    have hp_upper :
        ∀ᶠ k in atTop, z (p k) < L + ε :=
      (tendsto_order.1 hlim).2 (L + ε) (by linarith)
    rw [eventually_atTop] at hp_upper
    rcases hp_upper with ⟨K, hK⟩
    have hz_upper : ∀ᶠ n in atTop, z n ≤ L + ε := by
      filter_upwards [Ici_mem_atTop (p K)] with n hn
      by_cases hnrange : n ∈ Set.range p
      · rcases hnrange with ⟨k, rfl⟩
        have hKk : K ≤ k := (hp.le_iff_le).mp hn
        exact (hK k hKk).le
      · exact (hoff n hnrange).trans (by linarith)
    apply le_of_tendsto hvlim
    exact hq.tendsto_atTop hz_upper
  have hb : BddAbove (ProofGap.ClusterSet z) := ⟨L, hub⟩
  apply le_antisymm
  · exact csSup_le ⟨L, hLmem⟩ hub
  · exact le_csSup hb hLmem

/-- Source: `proof_gap/exercise_134/1.txt`; boundedness realizes liminf. -/
theorem gap1 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Tendsto (x ∘ p) atTop (𝓝 (ProofGap.seqLiminf x)) := by
  exact (clusterSet_isClosed x).csInf_mem
    (clusterSet_nonempty x hxb) (clusterSet_bddBelow x hxb)

/-- Source: `proof_gap/exercise_134/2.txt`; y depends on A and p. -/
theorem gap2 (x : ℕ → ℝ) (p : ℕ → ℕ) (A : ℝ)
    (hA : 0 < A)
    (hx0 : Nonnegative x)
    (hp : StrictMono p)
    (hlim : Tendsto (x ∘ p) atTop (𝓝 (ProofGap.seqLiminf x))) :
    ProofGap.seqLimsup (fun n => x n + addWitness x p A n) =
      ProofGap.seqLiminf x + A := by
  let z : ℕ → ℝ := fun n => x n + addWitness x p A n
  have hon (k : ℕ) : z (p k) = x (p k) + A := by
    simp [z, addWitness, Set.mem_range]
  have hoff (n : ℕ) (hn : n ∉ Set.range p) : z n ≤ 0 := by
    simp [z, addWitness, hn]
  have hlinf0 : 0 ≤ ProofGap.seqLiminf x := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards with k
    exact hx0 (p k)
  have hzlim :
      Tendsto (z ∘ p) atTop (𝓝 (ProofGap.seqLiminf x + A)) := by
    simpa [Function.comp_def, hon] using hlim.add_const A
  exact seqLimsup_eq_of_range_limit z p (ProofGap.seqLiminf x + A)
    hp hzlim hoff (by linarith)

/-- Source: `proof_gap/exercise_134/3.txt`. -/
theorem gap3 (x : ℕ → ℝ) (p : ℕ → ℕ) (A : ℝ)
    (hA : 0 < A) (hx0 : Nonnegative x) (hp : StrictMono p) :
    ProofGap.seqLimsup (addWitness x p A) = A := by
  have hon (k : ℕ) : addWitness x p A (p k) = A := by
    simp [addWitness, Set.mem_range]
  have hoff (n : ℕ) (hn : n ∉ Set.range p) :
      addWitness x p A n ≤ 0 := by
    simp [addWitness, hn]
    exact hx0 n
  have hlim :
      Tendsto (addWitness x p A ∘ p) atTop (𝓝 A) := by
    simpa [Function.comp_def, hon] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A))
  exact seqLimsup_eq_of_range_limit (addWitness x p A) p A
    hp hlim hoff hA.le

/-- Source: `proof_gap/exercise_134/4.txt`. -/
theorem gap4 (x : ℕ → ℝ) (A : ℝ)
    (heq : ProofGap.seqLiminf x + A = ProofGap.seqLimsup x + A) :
    ProofGap.seqLiminf x + A = ProofGap.seqLimsup x + A := by
  exact heq

/-- Source: `proof_gap/exercise_134/5.txt`. -/
theorem gap5 (x : ℕ → ℝ) (A : ℝ)
    (heq : ProofGap.seqLiminf x + A = ProofGap.seqLimsup x + A) :
    ProofGap.seqLiminf x = ProofGap.seqLimsup x := by
  linarith

/-- Source: `proof_gap/exercise_134/6.txt`. -/
theorem gap6 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (heq : ProofGap.seqLiminf x = ProofGap.seqLimsup x) :
    ProofGap.ConvergentSeq x := by
  exact ⟨ProofGap.seqLiminf x,
    tendsto_of_bounded_of_liminf_eq_limsup x hxb heq⟩

/-- Source: `proof_gap/exercise_134/7.txt`; y depends on A and p. -/
theorem gap7 (x : ℕ → ℝ) (p : ℕ → ℕ) (A : ℝ)
    (hA : 0 < A)
    (hx0 : Nonnegative x)
    (hp : StrictMono p)
    (hlim : Tendsto (x ∘ p) atTop (𝓝 (ProofGap.seqLiminf x))) :
    ProofGap.seqLimsup (fun n => x n * mulWitness p A n) =
      A * ProofGap.seqLiminf x := by
  let z : ℕ → ℝ := fun n => x n * mulWitness p A n
  have hon (k : ℕ) : z (p k) = A * x (p k) := by
    simp [z, mulWitness, Set.mem_range, mul_comm]
  have hoff (n : ℕ) (hn : n ∉ Set.range p) : z n ≤ 0 := by
    simp [z, mulWitness, hn]
  have hlinf0 : 0 ≤ ProofGap.seqLiminf x := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards with k
    exact hx0 (p k)
  have hzlim :
      Tendsto (z ∘ p) atTop (𝓝 (A * ProofGap.seqLiminf x)) := by
    simpa [Function.comp_def, hon] using
      (tendsto_const_nhds.mul hlim :
        Tendsto (fun k => A * x (p k)) atTop
          (𝓝 (A * ProofGap.seqLiminf x)))
  exact seqLimsup_eq_of_range_limit z p (A * ProofGap.seqLiminf x)
    hp hzlim hoff (mul_nonneg hA.le hlinf0)

/-- Source: `proof_gap/exercise_134/8.txt`. -/
theorem gap8 (x : ℕ → ℝ) (A : ℝ)
    (hA : 0 < A)
    (heq : A * ProofGap.seqLiminf x = A * ProofGap.seqLimsup x) :
    A * ProofGap.seqLiminf x = A * ProofGap.seqLimsup x := by
  exact heq

/-- Source: `proof_gap/exercise_134/9.txt`. -/
theorem gap9 (x : ℕ → ℝ) (A : ℝ)
    (hA : 0 < A)
    (heq : A * ProofGap.seqLiminf x = A * ProofGap.seqLimsup x) :
    ProofGap.seqLiminf x = ProofGap.seqLimsup x := by
  exact (mul_left_cancel₀ (ne_of_gt hA)) heq

/-- Source: `proof_gap/exercise_134/10.txt`. -/
theorem gap10 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (heq : ProofGap.seqLiminf x = ProofGap.seqLimsup x) :
    ProofGap.ConvergentSeq x := by
  exact gap6 x hxb heq

/-- Source: `proof_gap/exercise_134/11.txt`; retain boundedness and coherent witnesses. -/
theorem gap11 (x : ℕ → ℝ)
    (hx0 : Nonnegative x)
    (hxb : Bornology.IsBounded (Set.range x))
    (hproperty : UniversalEqualityProperty x) :
    ProofGap.ConvergentSeq x := by
  rcases gap1 x hxb with ⟨p, hp, hlim⟩
  let A : ℝ := 1
  let y := addWitness x p A
  have hA : 0 < A := by simp [A]
  have hlinf0 : 0 ≤ ProofGap.seqLiminf x := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards with k
    exact hx0 (p k)
  have hy_on (k : ℕ) : y (p k) = A := by
    simp [y, addWitness, Set.mem_range]
  have hy_off (n : ℕ) (hn : n ∉ Set.range p) : y n ≤ 0 := by
    simp [y, addWitness, hn]
    exact hx0 n
  have hylim : Tendsto (y ∘ p) atTop (𝓝 A) := by
    simpa [Function.comp_def, hy_on] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A))
  have hysup : ProofGap.seqLimsup y = A :=
    seqLimsup_eq_of_range_limit y p A hp hylim hy_off hA.le
  let s : ℕ → ℝ := fun n => x n + y n
  have hs_on (k : ℕ) : s (p k) = x (p k) + A := by
    simp [s, hy_on]
  have hs_off (n : ℕ) (hn : n ∉ Set.range p) : s n ≤ 0 := by
    simp [s, y, addWitness, hn]
  have hslim :
      Tendsto (s ∘ p) atTop
        (𝓝 (ProofGap.seqLiminf x + A)) := by
    simpa [Function.comp_def, hs_on] using hlim.add_const A
  have hssup :
      ProofGap.seqLimsup s = ProofGap.seqLiminf x + A :=
    seqLimsup_eq_of_range_limit s p (ProofGap.seqLiminf x + A)
      hp hslim hs_off (by linarith)
  let m : ℕ → ℝ := fun n => x n * y n
  have hm_on (k : ℕ) : m (p k) = A * x (p k) := by
    simp [m, hy_on, mul_comm]
  have hm_off (n : ℕ) (hn : n ∉ Set.range p) : m n ≤ 0 := by
    simp [m, y, addWitness, hn]
    simpa [pow_two] using sq_nonneg (x n)
  have hmlim :
      Tendsto (m ∘ p) atTop
        (𝓝 (A * ProofGap.seqLiminf x)) := by
    simpa [Function.comp_def, hm_on] using
      (tendsto_const_nhds.mul hlim : Tendsto
        (fun k => A * x (p k)) atTop
        (𝓝 (A * ProofGap.seqLiminf x)))
  have hmsup :
      ProofGap.seqLimsup m = A * ProofGap.seqLiminf x :=
    seqLimsup_eq_of_range_limit m p (A * ProofGap.seqLiminf x)
      hp hmlim hm_off (mul_nonneg hA.le hlinf0)
  rcases hproperty y with hadd | hmul
  · have heq :
        ProofGap.seqLiminf x + A = ProofGap.seqLimsup x + A := by
      calc
        ProofGap.seqLiminf x + A = ProofGap.seqLimsup s := hssup.symm
        _ = ProofGap.seqLimsup x + ProofGap.seqLimsup y := by
          simpa [s] using hadd
        _ = ProofGap.seqLimsup x + A := by rw [hysup]
    exact gap6 x hxb (gap5 x A heq)
  · have heq :
        A * ProofGap.seqLiminf x = A * ProofGap.seqLimsup x := by
      calc
        A * ProofGap.seqLiminf x = ProofGap.seqLimsup m := hmsup.symm
        _ = ProofGap.seqLimsup x * ProofGap.seqLimsup y := by
          simpa [m] using hmul
        _ = A * ProofGap.seqLimsup x := by rw [hysup]; ring
    exact gap10 x hxb (gap9 x A hA heq)

end

end ProofGap.Exercise134
