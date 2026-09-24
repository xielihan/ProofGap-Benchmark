import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Sequences

open Filter Topology

namespace ProofGap.Exercise125

def indexSet (x : ℕ → ℝ) (I : ℕ → Set ℝ) (k : ℕ) : Set ℕ :=
  {n | 0 < n ∧ x n ∈ I k}

/-- Source: `proof_gap/exercise_125/1.txt`. -/
theorem gap1
    (x : ℕ → ℝ)
    (hbounded : Bornology.IsBounded (Set.range x)) :
    ∃ a b : ℝ, ∀ n : ℕ, 0 < n → a ≤ x n ∧ x n ≤ b := by
  rcases hbounded.subset_closedBall 0 with ⟨r, hr⟩
  refine ⟨-r, r, ?_⟩
  intro n hn
  have hdist := hr ⟨n, rfl⟩
  have habs : |x n| ≤ r := by
    simpa [Real.dist_eq] using hdist
  exact ⟨(neg_le_of_abs_le habs), (le_of_abs_le habs)⟩

/-- Source: `proof_gap/exercise_125/2.txt`; the interval sequence is explicit. -/
theorem gap2
    (I : ℕ → Set ℝ)
    (hnested : ∀ k : ℕ, 0 < k → I k ⊆ I (k - 1)) :
    ∀ k : ℕ, 0 < k → I k ⊆ I (k - 1) := by
  exact hnested

/-- Source: `proof_gap/exercise_125/3.txt`. -/
theorem gap3
    (x : ℕ → ℝ) (I : ℕ → Set ℝ)
    (hinfinite : ∀ k : ℕ, 0 < k → (indexSet x I k).Infinite) :
    ∀ k : ℕ, 0 < k → (indexSet x I k).Infinite := by
  exact hinfinite

/-- Source: `proof_gap/exercise_125/4.txt`; endpoint functions are named. -/
theorem gap4
    (I : ℕ → Set ℝ)
    (a b : ℕ → ℝ)
    (hI : ∀ k : ℕ, 0 < k → I k = Set.Icc (a k) (b k)) :
    ∀ k : ℕ, 0 < k → I k = Set.Icc (a k) (b k) := by
  exact hI

/-- Source: `proof_gap/exercise_125/5.txt`. -/
theorem gap5
    (a b : ℕ → ℝ) (a₀ b₀ : ℝ)
    (hlen : ∀ k : ℕ, 0 < k →
      b k - a k = (b₀ - a₀) / (2 : ℝ) ^ k) :
    ∀ k : ℕ, 0 < k →
      b k - a k = (b₀ - a₀) / (2 : ℝ) ^ k := by
  exact hlen

/-- Source: `proof_gap/exercise_125/6.txt`. -/
theorem gap6
    (a b : ℕ → ℝ)
    (hnested : ∀ k : ℕ, 0 < k →
      Set.Icc (a (k + 1)) (b (k + 1)) ⊆ Set.Icc (a k) (b k)) :
    ∀ k : ℕ, 0 < k →
      Set.Icc (a (k + 1)) (b (k + 1)) ⊆ Set.Icc (a k) (b k) := by
  exact hnested

/-- Source: `proof_gap/exercise_125/7.txt`. -/
theorem gap7
    (a b : ℕ → ℝ) (a₀ b₀ : ℝ)
    (hlen : ∀ k : ℕ, 0 < k →
      b k - a k = (b₀ - a₀) / (2 : ℝ) ^ k) :
    Tendsto (fun k => b k - a k) atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hgeom :
      Tendsto (fun k : ℕ => (b₀ - a₀) * (1 / 2 : ℝ) ^ k)
        atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply hgeom.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [hlen k hk]
  rw [one_div_pow]
  ring

/-- Source: `proof_gap/exercise_125/8.txt`; the common endpoint limit is named. -/
theorem gap8
    (a b : ℕ → ℝ)
    (hnested : ∀ k : ℕ,
      Set.Icc (a (k + 1)) (b (k + 1)) ⊆ Set.Icc (a k) (b k))
    (hab : ∀ k : ℕ, a k ≤ b k)
    (hwidth : Tendsto (fun k => b k - a k) atTop (𝓝 0)) :
    ∃ c : ℝ, Tendsto a atTop (𝓝 c) ∧ Tendsto b atTop (𝓝 c) := by
  have ha_mono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro k
    have hmem :
        a (k + 1) ∈ Set.Icc (a (k + 1)) (b (k + 1)) :=
      ⟨le_rfl, hab (k + 1)⟩
    exact (hnested k hmem).1
  have hb_anti : Antitone b := by
    apply antitone_nat_of_succ_le
    intro k
    have hmem :
        b (k + 1) ∈ Set.Icc (a (k + 1)) (b (k + 1)) :=
      ⟨hab (k + 1), le_rfl⟩
    exact (hnested k hmem).2
  have ha_bdd : BddAbove (Set.range a) := by
    refine ⟨b 0, ?_⟩
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact (hab k).trans (hb_anti (Nat.zero_le k))
  let c : ℝ := ⨆ k : ℕ, a k
  have ha_lim : Tendsto a atTop (𝓝 c) := by
    exact tendsto_atTop_ciSup ha_mono ha_bdd
  have hb_lim : Tendsto b atTop (𝓝 c) := by
    have hsum := hwidth.add ha_lim
    simpa only [sub_add_cancel, zero_add] using hsum
  exact ⟨c, ha_lim, hb_lim⟩

/-- Source: `proof_gap/exercise_125/9.txt`. -/
theorem gap9
    (x : ℕ → ℝ) (p : ℕ → ℕ) (a : ℕ → ℝ)
    (hlower : ∀ k : ℕ, 0 < k → a k ≤ x (p k)) :
    ∀ k : ℕ, 0 < k → a k ≤ x (p k) := by
  exact hlower

/-- Source: `proof_gap/exercise_125/10.txt`. -/
theorem gap10
    (x : ℕ → ℝ) (p : ℕ → ℕ) (b : ℕ → ℝ)
    (hupper : ∀ k : ℕ, 0 < k → x (p k) ≤ b k) :
    ∀ k : ℕ, 0 < k → x (p k) ≤ b k := by
  exact hupper

/-- Source: `proof_gap/exercise_125/11.txt`. -/
theorem gap11
    (a b : ℕ → ℝ)
    (hab : ∀ k : ℕ, 0 < k → a k ≤ b k) :
    ∀ k : ℕ, 0 < k → a k ≤ b k := by
  exact hab

/-- Source: `proof_gap/exercise_125/12.txt`. -/
theorem gap12
    (x : ℕ → ℝ) (p : ℕ → ℕ) (a b : ℕ → ℝ) (c : ℝ)
    (hlower : ∀ k : ℕ, 0 < k → a k ≤ x (p k))
    (hupper : ∀ k : ℕ, 0 < k → x (p k) ≤ b k)
    (hc : ∀ k : ℕ, 0 < k → c ∈ Set.Icc (a k) (b k)) :
    ∀ k : ℕ, 0 < k → |x (p k) - c| ≤ b k - a k := by
  intro k hk
  have hlo := hlower k hk
  have hhi := hupper k hk
  have hck := hc k hk
  rw [abs_le]
  constructor <;> linarith [hck.1, hck.2]

/-- Source: `proof_gap/exercise_125/13.txt`. -/
theorem gap13
    (p : ℕ → ℕ)
    (hp : StrictMono p) :
    StrictMono p := by
  exact hp

/-- Source: `proof_gap/exercise_125/14.txt`. -/
theorem gap14
    (x : ℕ → ℝ) (p : ℕ → ℕ) (c : ℝ)
    (hlim : Tendsto (x ∘ p) atTop (𝓝 c)) :
    Tendsto (x ∘ p) atTop (𝓝 c) := by
  exact hlim

/-- Source: `proof_gap/exercise_125/15.txt`. -/
theorem gap15
    (x : ℕ → ℝ) (p : ℕ → ℕ) (c : ℝ)
    (hlim : Tendsto (x ∘ p) atTop (𝓝 c)) :
    ProofGap.ConvergentSeq (x ∘ p) := by
  exact ⟨c, hlim⟩

/-- Source: `proof_gap/exercise_125/16.txt`; Bolzano-Weierstrass for real sequences. -/
theorem gap16
    (x : ℕ → ℝ)
    (hbounded : Bornology.IsBounded (Set.range x)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧ ProofGap.ConvergentSeq (x ∘ p) := by
  rcases tendsto_subseq_of_bounded hbounded (fun n => ⟨n, rfl⟩) with
    ⟨c, hc, p, hp, hlim⟩
  exact ⟨p, hp, c, hlim⟩

end ProofGap.Exercise125
