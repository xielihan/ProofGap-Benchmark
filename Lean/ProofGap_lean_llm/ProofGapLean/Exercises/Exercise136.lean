import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Sequences

open Filter Topology

namespace ProofGap.Exercise136

noncomputable section

def increment (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 1) - x n

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

/-- Source: `proof_gap/exercise_136/1.txt`. -/
theorem gap1 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x)) :
    ProofGap.seqLiminf x ∈ ProofGap.ClusterSet x := by
  exact (clusterSet_isClosed x).csInf_mem
    (clusterSet_nonempty x hxb) (clusterSet_bddBelow x hxb)

/-- Source: `proof_gap/exercise_136/2.txt`. -/
theorem gap2 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x)) :
    ProofGap.seqLimsup x ∈ ProofGap.ClusterSet x := by
  exact (clusterSet_isClosed x).csSup_mem
    (clusterSet_nonempty x hxb) (clusterSet_bddAbove x hxb)

/-- Source: `proof_gap/exercise_136/3.txt`; remove irrelevant a and N binders. -/
theorem gap3 (x : ℕ → ℝ)
    (hstep : Tendsto (increment x) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N' : ℕ, ∀ n : ℕ, N' < n → |x (n + 1) - x n| < ε := by
  intro ε hε
  have hev := (Metric.tendsto_atTop.1 hstep) ε hε
  rcases hev with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn.le
  simpa [increment, Real.dist_eq] using this

/-- Source: `proof_gap/exercise_136/4.txt`; both crossing witnesses depend on a and N. -/
theorem gap4 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x)) :
    ∀ a : ℝ, ProofGap.seqLiminf x < a → a < ProofGap.seqLimsup x →
      ∀ N : ℕ, ∃ n' n'' : ℕ,
        N < n' ∧ N < n'' ∧ x n' < a ∧ a < x n'' := by
  intro a hainf hasup N
  rcases gap1 x hxb with ⟨p, hp, hp_lim⟩
  rcases gap2 x hxb with ⟨q, hq, hq_lim⟩
  have hp_below : ∀ᶠ k in atTop, x (p k) < a :=
    hp_lim.eventually (Iio_mem_nhds hainf)
  have hq_above : ∀ᶠ k in atTop, a < x (q k) :=
    hq_lim.eventually (Ioi_mem_nhds hasup)
  have hp_large : ∀ᶠ k in atTop, N < p k :=
    hp.tendsto_atTop (Ioi_mem_atTop N)
  have hq_large : ∀ᶠ k in atTop, N < q k :=
    hq.tendsto_atTop (Ioi_mem_atTop N)
  rcases (hp_below.and hp_large).exists with ⟨i, hi_below, hi_large⟩
  rcases (hq_above.and hq_large).exists with ⟨j, hj_above, hj_large⟩
  exact ⟨p i, q j, hi_large, hj_large, hi_below, hj_above⟩

/-- Source: `proof_gap/exercise_136/5.txt`; choose the last crossing index coherently. -/
theorem gap5 (x : ℕ → ℝ) (a : ℝ) (n' n'' : ℕ)
    (hord : n' < n'') (hbelow : x n' < a) (habove : a < x n'') :
    ∃ nstar : ℕ, n' ≤ nstar ∧ nstar ≤ n'' - 1 := by
  exact ⟨n', le_rfl, by omega⟩

/-- Source: `proof_gap/exercise_136/6.txt`. -/
theorem gap6 (x : ℕ → ℝ) (a : ℝ) (n' n'' : ℕ)
    (hord : n' < n'') (hbelow : x n' < a) (habove : a < x n'') :
    ∃ nstar : ℕ, n' ≤ nstar ∧ nstar < n'' ∧ x nstar < a := by
  exact ⟨n', le_rfl, hord, hbelow⟩

/-- Source: `proof_gap/exercise_136/7.txt`. -/
theorem gap7 (x : ℕ → ℝ) (a : ℝ) (n' n'' : ℕ)
    (hord : n' < n'') (hbelow : x n' < a) (habove : a < x n'') :
    ∃ nstar : ℕ, n' ≤ nstar ∧ nstar < n'' ∧
      x nstar < a ∧ a ≤ x (nstar + 1) := by
  classical
  let P : ℕ → Prop := fun n => n' ≤ n ∧ x n < a
  let nstar := Nat.findGreatest P (n'' - 1)
  have hn'_bound : n' ≤ n'' - 1 := by omega
  have hPstart : P n' := ⟨le_rfl, hbelow⟩
  have hn'_star : n' ≤ nstar :=
    Nat.le_findGreatest hn'_bound hPstart
  have hstar_bound : nstar ≤ n'' - 1 := Nat.findGreatest_le _
  have hPstar : P nstar :=
    Nat.findGreatest_spec hn'_bound hPstart
  refine ⟨nstar, hn'_star, by omega, hPstar.2, ?_⟩
  by_contra hnext
  have hnext_below : x (nstar + 1) < a := lt_of_not_ge hnext
  have hnext_ne : nstar + 1 ≠ n'' := by
    intro heq
    rw [heq] at hnext_below
    linarith
  have hnext_bound : nstar + 1 ≤ n'' - 1 := by omega
  exact (Nat.findGreatest_is_greatest (Nat.lt_succ_self nstar) hnext_bound)
    ⟨by omega, hnext_below⟩

/-- Source: `proof_gap/exercise_136/8.txt`. -/
theorem gap8 (n' nstar N : ℕ)
    (hN : N < n') (hstar : n' ≤ nstar) :
    N < nstar := by
  omega

/-- Source: `proof_gap/exercise_136/9.txt`. -/
theorem gap9 (nstar N N' : ℕ)
    (hN : max N N' < nstar) :
    N' < nstar := by
  omega

/-- Source: `proof_gap/exercise_136/10.txt`. -/
theorem gap10 (x : ℕ → ℝ) (a : ℝ) (nstar : ℕ)
    (hbelow : x nstar < a) (habove : a ≤ x (nstar + 1)) :
    |x nstar - a| ≤ |x (nstar + 1) - x nstar| := by
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
  linarith

/-- Source: `proof_gap/exercise_136/11.txt`. -/
theorem gap11 (x : ℕ → ℝ) (ε : ℝ) (nstar N : ℕ)
    (hstep : ∀ n : ℕ, N < n → |x (n + 1) - x n| < ε)
    (hN : N < nstar) :
    |x (nstar + 1) - x nstar| < ε := by
  exact hstep nstar hN

/-- Source: `proof_gap/exercise_136/12.txt`. -/
theorem gap12 (x : ℕ → ℝ) (a ε : ℝ) (nstar : ℕ)
    (hcross : |x nstar - a| ≤ |x (nstar + 1) - x nstar|)
    (hstep : |x (nstar + 1) - x nstar| < ε) :
    |x nstar - a| < ε := by
  exact hcross.trans_lt hstep

/-- Source: `proof_gap/exercise_136/13.txt`; p depends on a. -/
theorem gap13 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (increment x) atTop (𝓝 0)) :
    ∀ a : ℝ, ProofGap.seqLiminf x < a → a < ProofGap.seqLimsup x →
      ∃ p : ℕ → ℕ, StrictMono p ∧
        ∀ k : ℕ, 0 < k → |x (p k) - a| < 1 / (k : ℝ) := by
  intro a hainf hasup
  have hnear :
      ∀ (N k : ℕ), ∃ n : ℕ,
        N < n ∧ |x n - a| < 1 / ((k + 1 : ℕ) : ℝ) := by
    intro N k
    have hε : (0 : ℝ) < 1 / ((k + 1 : ℕ) : ℝ) := by positivity
    rcases gap3 x hstep _ hε with ⟨Nstep, hNstep⟩
    rcases gap4 x hxb a hainf hasup (max N Nstep) with
      ⟨n', n₀, hn', hn₀, hn'_below, hn₀_above⟩
    rcases gap4 x hxb a hainf hasup n' with
      ⟨m, n'', hm, hn'', hm_below, hn''_above⟩
    rcases gap7 x a n' n'' (by omega) hn'_below hn''_above with
      ⟨nstar, hn'star, hstarlt, hstar_below, hstar_above⟩
    have hNstar : N < nstar := by omega
    have hNstepstar : Nstep < nstar := by omega
    have hcross :=
      gap10 x a nstar hstar_below hstar_above
    have hsmall :=
      gap11 x (1 / ((k + 1 : ℕ) : ℝ)) nstar Nstep hNstep hNstepstar
    exact ⟨nstar, hNstar, gap12 x a _ nstar hcross hsmall⟩
  classical
  let p : ℕ → ℕ :=
    Nat.rec (Classical.choose (hnear 0 0))
      (fun k n => Classical.choose (hnear n k))
  have hp_step : ∀ k : ℕ, p k < p (k + 1) := by
    intro k
    simpa [p] using (Classical.choose_spec (hnear (p k) k)).1
  have hp : StrictMono p := strictMono_nat_of_lt_succ hp_step
  refine ⟨p, hp, ?_⟩
  intro k hk
  cases k with
  | zero => omega
  | succ j =>
      simpa [p] using (Classical.choose_spec (hnear (p j) j)).2

/-- Source: `proof_gap/exercise_136/14.txt`; move exists p inside forall a. -/
theorem gap14 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (increment x) atTop (𝓝 0)) :
    ∀ a : ℝ, ProofGap.seqLiminf x < a → a < ProofGap.seqLimsup x →
      ∃ p : ℕ → ℕ, StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 a) := by
  intro a hainf hasup
  rcases gap13 x hxb hstep a hainf hasup with ⟨p, hp, hpclose⟩
  refine ⟨p, hp, ?_⟩
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hrecip :
      Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hev : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / (k : ℝ) < ε :=
    (tendsto_order.1 hrecip).2 ε hε
  rw [eventually_atTop] at hev
  rcases hev with ⟨K, hK⟩
  refine ⟨max K 1, fun k hk => ?_⟩
  have hkK : K ≤ k := (le_max_left K 1).trans hk
  have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
  rw [Real.dist_eq]
  exact (hpclose k (by omega)).trans (hK k hkK)

/-- Source: `proof_gap/exercise_136/15.txt`. -/
theorem gap15 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (increment x) atTop (𝓝 0)) :
    ∀ a : ℝ, ProofGap.seqLiminf x < a → a < ProofGap.seqLimsup x →
      a ∈ ProofGap.ClusterSet x := by
  intro a hainf hasup
  exact gap14 x hxb hstep a hainf hasup

/-- Source: `proof_gap/exercise_136/16.txt`. -/
theorem gap16 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (increment x) atTop (𝓝 0)) :
    ∀ a : ℝ, ProofGap.seqLiminf x < a → a < ProofGap.seqLimsup x →
      a ∈ ProofGap.ClusterSet x := by
  exact gap15 x hxb hstep

/-- Source: `proof_gap/exercise_136/17.txt`; retain the hypotheses dropped in the source. -/
theorem gap17 (x : ℕ → ℝ)
    (hxb : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (increment x) atTop (𝓝 0)) :
    ∀ a : ℝ, a ∈ Set.Icc (ProofGap.seqLiminf x) (ProofGap.seqLimsup x) →
      a ∈ ProofGap.ClusterSet x := by
  intro a ha
  rcases ha with ⟨hainf, hasup⟩
  rcases hainf.eq_or_lt with rfl | hainf
  · exact gap1 x hxb
  rcases hasup.eq_or_lt with rfl | hasup
  · exact gap2 x hxb
  · exact gap16 x hxb hstep a hainf hasup

end

end ProofGap.Exercise136
