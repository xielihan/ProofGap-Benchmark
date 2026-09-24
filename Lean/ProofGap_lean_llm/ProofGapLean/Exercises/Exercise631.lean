import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise631

noncomputable section

def puncturedLimit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

def indexedSum (f : ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun m => f (α (m * n)))

def sumRatio (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  indexedSum φ α n / indexedSum ψ α n

def UniformlySmall (α : ℕ → ℝ) : Prop :=
  ∀ δ > 0, ∃ N : ℕ, ∀ n > N, ∀ m ∈ Finset.Icc 1 n,
    |α (m * n)| < δ

/-- Source: `proof_gap/exercise_631/1.txt`. -/
theorem gap1 (φ ψ : ℝ → ℝ)
    (hlim : puncturedLimit (fun x => φ x / ψ x) 0 1) :
    ∀ ε > 0, ∃ δ > 0, ∀ x,
      0 < |x| → |x| < δ → |φ x / ψ x - 1| < ε := by
  intro ε hε
  rw [puncturedLimit, Metric.tendsto_nhdsWithin_nhds] at hlim
  obtain ⟨δ, hδ, hclose⟩ := hlim ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx0 hxδ
  have hxmem : x ∈ ({0} : Set ℝ)ᶜ := by
    simpa using (abs_pos.mp hx0)
  have hout := hclose hxmem (by simpa [Real.dist_eq] using hxδ)
  simpa [Real.dist_eq] using hout

/-- Source: `proof_gap/exercise_631/2.txt`; add the omitted punctured-neighborhood premise. -/
theorem gap2 (φ ψ : ℝ → ℝ) (x ε : ℝ) (hε : 0 < ε)
    (hψ : 0 < ψ x) (hclose : |φ x / ψ x - 1| < ε) :
    (1 - ε) * ψ x < φ x := by
  have hratio : 1 - ε < φ x / ψ x := by
    have hlo := (abs_lt.mp hclose).1
    linarith
  exact (lt_div_iff₀ hψ).mp hratio

/-- Source: `proof_gap/exercise_631/3.txt`; add the omitted punctured-neighborhood premise. -/
theorem gap3 (φ ψ : ℝ → ℝ) (x ε : ℝ) (hε : 0 < ε)
    (hψ : 0 < ψ x) (hclose : |φ x / ψ x - 1| < ε) :
    φ x < (1 + ε) * ψ x := by
  have hratio : φ x / ψ x < 1 + ε := by
    have hhi := (abs_lt.mp hclose).2
    linarith
  exact (div_lt_iff₀ hψ).mp hratio

/-- Source: `proof_gap/exercise_631/4.txt`; positivity of `ψ` is required. -/
theorem gap4 (ψ : ℝ → ℝ) (x ε : ℝ) (hε : 0 < ε)
    (hψ : 0 < ψ x) :
    (1 - ε) * ψ x < (1 + ε) * ψ x := by
  apply mul_lt_mul_of_pos_right _ hψ
  linarith

/-- Source: `proof_gap/exercise_631/5.txt`; remove shadowed binders and bind the uniform-smallness premise. -/
theorem gap5 (α : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : UniformlySmall α) (hnz : ∀ k, α k ≠ 0) :
    ∃ N : ℕ, ∀ n > N, ∀ m ∈ Finset.Icc 1 n,
      0 < |α (m * n)| ∧ |α (m * n)| < δ := by
  obtain ⟨N, hN⟩ := hsmall δ hδ
  refine ⟨N, ?_⟩
  intro n hn m hm
  exact ⟨abs_pos.mpr (hnz (m * n)), hN n hn m hm⟩

/-- Source: `proof_gap/exercise_631/6.txt`; bind the local ratio estimate used at `α(mn)`. -/
theorem gap6 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (m n : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hψ : ∀ x, 0 < ψ x)
    (hclose : |φ (α (m * n)) / ψ (α (m * n)) - 1| < ε) :
    (1 - ε) * ψ (α (m * n)) < φ (α (m * n)) := by
  exact gap2 φ ψ (α (m * n)) ε hε (hψ _) hclose

/-- Source: `proof_gap/exercise_631/7.txt`; bind the local ratio estimate used at `α(mn)`. -/
theorem gap7 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (m n : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hψ : ∀ x, 0 < ψ x)
    (hclose : |φ (α (m * n)) / ψ (α (m * n)) - 1| < ε) :
    φ (α (m * n)) < (1 + ε) * ψ (α (m * n)) := by
  exact gap3 φ ψ (α (m * n)) ε hε (hψ _) hclose

/-- Source: `proof_gap/exercise_631/8.txt`. -/
theorem gap8 (ψ : ℝ → ℝ) (α : ℕ → ℝ) (m n : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hψ : ∀ x, 0 < ψ x) :
    (1 - ε) * ψ (α (m * n)) <
      (1 + ε) * ψ (α (m * n)) := by
  exact gap4 ψ (α (m * n)) ε hε (hψ _)

/-- Source: `proof_gap/exercise_631/9.txt`; use an explicit finite sum and its pointwise hypotheses. -/
theorem gap9 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hn : 0 < n)
    (hpoint : ∀ m ∈ Finset.Icc 1 n,
      (1 - ε) * ψ (α (m * n)) < φ (α (m * n))) :
    (1 - ε) * indexedSum ψ α n < indexedSum φ α n := by
  unfold indexedSum
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro m hm
    exact le_of_lt (hpoint m hm)
  · refine ⟨1, Finset.mem_Icc.mpr ⟨by simp, by omega⟩, ?_⟩
    exact hpoint 1 (Finset.mem_Icc.mpr ⟨by simp, by omega⟩)

/-- Source: `proof_gap/exercise_631/10.txt`; use an explicit finite sum and its pointwise hypotheses. -/
theorem gap10 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hn : 0 < n)
    (hpoint : ∀ m ∈ Finset.Icc 1 n,
      φ (α (m * n)) < (1 + ε) * ψ (α (m * n))) :
    indexedSum φ α n < (1 + ε) * indexedSum ψ α n := by
  unfold indexedSum
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro m hm
    exact le_of_lt (hpoint m hm)
  · refine ⟨1, Finset.mem_Icc.mpr ⟨by simp, by omega⟩, ?_⟩
    exact hpoint 1 (Finset.mem_Icc.mpr ⟨by simp, by omega⟩)

/-- Source: `proof_gap/exercise_631/11.txt`. -/
theorem gap11 (ψ : ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hψ : ∀ x, 0 < ψ x) (hn : 0 < n) :
    (1 - ε) * indexedSum ψ α n <
      (1 + ε) * indexedSum ψ α n := by
  have hn1 : 1 ≤ n := by omega
  have hone : 1 ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩
  have hsum : 0 < indexedSum ψ α n := by
    unfold indexedSum
    have hle :
        ψ (α (1 * n)) ≤
          (Finset.Icc 1 n).sum (fun m => ψ (α (m * n))) := by
      exact Finset.single_le_sum (fun m _ => (hψ (α (m * n))).le) hone
    exact lt_of_lt_of_le (hψ (α (1 * n))) hle
  exact gap4 (fun _ => indexedSum ψ α n) 0 ε hε hsum

/-- Source: `proof_gap/exercise_631/12.txt`; division requires positivity of the denominator sum. -/
theorem gap12 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hden : 0 < indexedSum ψ α n)
    (hlower : (1 - ε) * indexedSum ψ α n < indexedSum φ α n) :
    1 - ε < sumRatio φ ψ α n := by
  unfold sumRatio
  exact (lt_div_iff₀ hden).mpr hlower

/-- Source: `proof_gap/exercise_631/13.txt`; division requires positivity of the denominator sum. -/
theorem gap13 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hden : 0 < indexedSum ψ α n)
    (hupper : indexedSum φ α n < (1 + ε) * indexedSum ψ α n) :
    sumRatio φ ψ α n < 1 + ε := by
  unfold sumRatio
  exact (div_lt_iff₀ hden).mpr hupper

/-- Source: `proof_gap/exercise_631/14.txt`. -/
theorem gap14 (ε : ℝ) (hε : 0 < ε) : 1 - ε < 1 + ε := by
  linarith

/-- Source: `proof_gap/exercise_631/15.txt`; bind the eventual squeeze assumptions. -/
theorem gap15 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ)
    (hsqueeze : ∀ ε > 0, ∃ N, ∀ n > N,
      1 - ε < sumRatio φ ψ α n ∧ sumRatio φ ψ α n < 1 + ε) :
    Filter.Tendsto (sumRatio φ ψ α) Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hsqueeze ε hε
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn' : n > N := by omega
  have hbounds := hN n hn'
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hbounds.1, hbounds.2]

/-- Source: `proof_gap/exercise_631/16.txt`; state the product-limit implication explicitly. -/
theorem gap16 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (L : ℝ)
    (hratio : Filter.Tendsto (sumRatio φ ψ α) Filter.atTop (nhds 1))
    (hψ : Filter.Tendsto (indexedSum ψ α) Filter.atTop (nhds L))
    (hden : ∀ᶠ n in Filter.atTop, indexedSum ψ α n ≠ 0) :
    Filter.Tendsto (indexedSum φ α) Filter.atTop (nhds (1 * L)) := by
  have hprod :
      Filter.Tendsto
        (fun n => sumRatio φ ψ α n * indexedSum ψ α n)
        Filter.atTop (nhds (1 * L)) :=
    hratio.mul hψ
  refine hprod.congr' ?_
  filter_upwards [hden] with n hn
  simp [sumRatio, hn]

/-- Source: `proof_gap/exercise_631/17.txt`. -/
theorem gap17 (ψ : ℝ → ℝ) (α : ℕ → ℝ) (L : ℝ)
    (hψ : Filter.Tendsto (indexedSum ψ α) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => 1 * indexedSum ψ α n) Filter.atTop (nhds L) := by
  simpa only [one_mul] using hψ

/-- Source: `proof_gap/exercise_631/18.txt`; bind both represented limits. -/
theorem gap18 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (L : ℝ)
    (hφ : Filter.Tendsto (indexedSum φ α) Filter.atTop (nhds L))
    (hψ : Filter.Tendsto (indexedSum ψ α) Filter.atTop (nhds L)) :
    ∃ A, Filter.Tendsto (indexedSum φ α) Filter.atTop (nhds A) ∧
      Filter.Tendsto (indexedSum ψ α) Filter.atTop (nhds A) := by
  exact ⟨L, hφ, hψ⟩

/-- Source: `proof_gap/exercise_631/19.txt`; corrected final theorem with its convergence hypotheses. -/
theorem gap19 (φ ψ : ℝ → ℝ) (α : ℕ → ℝ) (L : ℝ)
    (hratio : Filter.Tendsto (sumRatio φ ψ α) Filter.atTop (nhds 1))
    (hψ : Filter.Tendsto (indexedSum ψ α) Filter.atTop (nhds L))
    (hden : ∀ᶠ n in Filter.atTop, indexedSum ψ α n ≠ 0) :
    Filter.Tendsto (indexedSum φ α) Filter.atTop (nhds L) := by
  simpa using (gap16 φ ψ α L hratio hψ hden)

end

end ProofGap.Exercise631
