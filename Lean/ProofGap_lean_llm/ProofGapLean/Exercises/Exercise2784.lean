import ProofGapLean.Prelude.Analysis
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2784

noncomputable section

open scoped BigOperators

def UniformlySummableNormOn (f : ℕ → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℕ, ∀ x ∈ s,
    (∑ j ∈ Finset.range p, |f (n + j + 1) x|) < ε

def UniformCauchyOn (f : ℕ → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℕ, ∀ x ∈ s,
    |∑ j ∈ Finset.range p, f (n + j + 1) x| < ε

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem uniformCauchyOn_exists_uniformLimit
    (f : ℕ → ℝ → ℝ) (s : Set ℝ)
    (hc : UniformCauchyOn f s) :
    ∃ g : ℝ → ℝ, SeriesUniformlyConvergesOn f s g := by
  classical
  let P : ℕ → ℝ → ℝ := fun n x =>
    ∑ k ∈ Finset.range (n + 1), f k x
  have hsplit (x : ℝ) (n p : ℕ) :
      P (n + p) x =
        P n x + ∑ j ∈ Finset.range p, f (n + j + 1) x := by
    dsimp [P]
    rw [show n + p + 1 = (n + 1) + p by omega,
      Finset.sum_range_add]
    refine congrArg
      (fun z : ℝ => (∑ k ∈ Finset.range (n + 1), f k x) + z) ?_
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun q : ℕ => f q x)
      (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
  have hseq (x : {x : ℝ // x ∈ s}) :
      CauchySeq (fun n => P n x.1) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    rcases le_total m n with hmn | hnm
    · have ht := hN m hm (n - m) x.1 x.2
      have hs := hsplit x.1 m (n - m)
      rw [Nat.add_sub_of_le hmn] at hs
      simpa [Real.dist_eq, hs] using ht
    · have ht := hN n hn (m - n) x.1 x.2
      have hs := hsplit x.1 n (m - n)
      rw [Nat.add_sub_of_le hnm] at hs
      simpa [Real.dist_eq, hs] using ht
  have hlim : ∀ x : {x : ℝ // x ∈ s},
      ∃ y : ℝ, Tendsto (fun n => P n x.1) atTop (nhds y) := by
    intro x
    exact cauchySeq_tendsto_of_complete (hseq x)
  choose g hg using hlim
  let G : ℝ → ℝ := fun x =>
    if hx : x ∈ s then g ⟨x, hx⟩ else 0
  refine ⟨G, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hconv : Tendsto (fun m => P m x) atTop (nhds (G x)) := by
    simpa [G, hx] using hg ⟨x, hx⟩
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨M, hM⟩ := hconv (ε / 2) (half_pos hε)
  let m := max n M
  have hnm : n ≤ m := le_max_left _ _
  have hMm : M ≤ m := le_max_right _ _
  have htRaw := hN n hn (m - n) x hx
  have hs := hsplit x n (m - n)
  rw [Nat.add_sub_of_le hnm] at hs
  have ht : |P m x - P n x| < ε / 2 := by
    simpa [hs] using htRaw
  have hclose : |P m x - G x| < ε / 2 := by
    simpa [Real.dist_eq] using hM m hMm
  change |P n x - G x| < ε
  calc
    |P n x - G x| ≤
        |P n x - P m x| + |P m x - G x| := by
      rw [show P n x - G x =
        (P n x - P m x) + (P m x - G x) by ring]
      exact abs_add_le _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add (by simpa [abs_sub_comm] using ht) hclose
    _ = ε := by ring

theorem gap1 (f : ℕ → ℝ → ℝ) (s : Set ℝ)
    (habs : UniformlySummableNormOn f s) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℕ, ∀ x ∈ s,
      (∑ j ∈ Finset.range p, |f (n + j + 1) x|) < ε := by
  exact habs

theorem gap2 (f : ℕ → ℝ → ℝ) (n p : ℕ) (x : ℝ) :
    |∑ j ∈ Finset.range p, f (n + j + 1) x| ≤
      ∑ j ∈ Finset.range p, |f (n + j + 1) x| := by
  induction p with
  | zero => simp
  | succ p ih =>
      simp only [Finset.sum_range_succ]
      exact (abs_add_le _ _).trans (add_le_add ih (le_refl _))

theorem gap3 (f : ℕ → ℝ → ℝ) (s : Set ℝ)
    (habs : UniformlySummableNormOn f s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ p : ℕ, ∀ x ∈ s,
      (∑ j ∈ Finset.range p, |f (n + j + 1) x|) < ε := by
  exact habs ε hε

theorem gap4 (f : ℕ → ℝ → ℝ) (s : Set ℝ)
    (habs : UniformlySummableNormOn f s) :
    UniformCauchyOn f s := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap3 f s habs ε hε
  refine ⟨N, ?_⟩
  intro n hn p x hx
  exact lt_of_le_of_lt (gap2 f n p x) (hN n hn p x hx)

theorem gap5 (f : ℕ → ℝ → ℝ) (s : Set ℝ)
    (habs : UniformlySummableNormOn f s) :
    ∃ g : ℝ → ℝ, SeriesUniformlyConvergesOn f s g := by
  exact uniformCauchyOn_exists_uniformLimit f s (gap4 f s habs)

theorem gap6 (f : ℕ → ℝ → ℝ) (a b : ℝ) (A : ℝ → ℝ)
    (habs : SeriesUniformlyConvergesOn
      (fun n x => |f n x|) (Set.Icc a b) A) :
    ∃ S : ℝ → ℝ, SeriesUniformlyConvergesOn f (Set.Icc a b) S := by
  apply uniformCauchyOn_exists_uniformLimit f (Set.Icc a b)
  intro ε hε
  obtain ⟨N, hN⟩ := habs (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro n hn p x hx
  let Q : ℕ → ℝ := fun m =>
    ∑ k ∈ Finset.range (m + 1), |f k x|
  have hsplit :
      Q (n + p) = Q n +
        ∑ j ∈ Finset.range p, |f (n + j + 1) x| := by
    dsimp [Q]
    rw [show n + p + 1 = (n + 1) + p by omega,
      Finset.sum_range_add]
    refine congrArg
      (fun z : ℝ => (∑ k ∈ Finset.range (n + 1), |f k x|) + z) ?_
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun q : ℕ => |f q x|)
      (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
  have hnp : N ≤ n + p := by omega
  have hnclose : |Q n - A x| < ε / 2 := by
    simpa [Q] using hN n hn x hx
  have hfarclose : |Q (n + p) - A x| < ε / 2 := by
    simpa [Q] using hN (n + p) hnp x hx
  have hdiff : |Q (n + p) - Q n| < ε := by
    calc
      |Q (n + p) - Q n| =
          |(Q (n + p) - A x) + (A x - Q n)| := by
            congr 1
            ring
      _ ≤ |Q (n + p) - A x| + |A x - Q n| := abs_add_le _ _
      _ < ε / 2 + ε / 2 :=
        add_lt_add hfarclose (by simpa [abs_sub_comm] using hnclose)
      _ = ε := by ring
  have htail :
      (∑ j ∈ Finset.range p, |f (n + j + 1) x|) < ε := by
    calc
      (∑ j ∈ Finset.range p, |f (n + j + 1) x|) =
          Q (n + p) - Q n := by rw [hsplit]; ring
      _ ≤ |Q (n + p) - Q n| := le_abs_self _
      _ < ε := hdiff
  exact lt_of_le_of_lt (gap2 f n p x) htail

end

end ProofGap.Exercise2784
