import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise146

open Filter Topology

namespace ProofGap.Exercise147

noncomputable section

def harmonic (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i
def harmonicTail (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / i

def EulerExpansion (C : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 < n → harmonic n = C + Real.log n + ε n) ∧
  Tendsto ε atTop (𝓝 0)

/-- Source: `proof_gap/exercise_147/1.txt`; use one coherent error witness. -/
theorem gap1 : ∃ C ε, EulerExpansion C ε := by
  rcases ProofGap.Exercise146.gap17 with ⟨C, hC⟩
  rcases ProofGap.Exercise146.gap20 C hC with ⟨ε, hε, hε0⟩
  refine ⟨C, ε, ?_, hε0⟩
  intro n hn
  simpa [harmonic, ProofGap.Exercise146.harmonic] using hε n hn

/-- Source: `proof_gap/exercise_147/2.txt`. -/
theorem gap2 (C : ℝ) (ε : ℕ → ℝ) (h : EulerExpansion C ε) :
    ∀ n : ℕ, 0 < n →
      harmonic (2 * n) = C + Real.log (2 * n) + ε (2 * n) := by
  intro n hn
  simpa [Nat.cast_mul] using h.1 (2 * n) (by positivity)

/-- Source: `proof_gap/exercise_147/3.txt`. -/
theorem gap3 (C : ℝ) (ε : ℕ → ℝ) (h : EulerExpansion C ε) :
    Tendsto ε atTop (𝓝 0) := by
  exact h.2

/-- Source: `proof_gap/exercise_147/4.txt`. -/
theorem gap4 (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ε (2 * n)) atTop (𝓝 0) := by
  apply hε.comp
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

private theorem epsilonComboLimit (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => Real.log 2 + ε (2 * n) - ε n)
      atTop (𝓝 (Real.log 2)) := by
  convert (tendsto_const_nhds.add (gap4 ε hε)).sub hε using 1 <;> ring

private theorem transformedLimit (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      Real.log ((2 * n : ℕ) : ℝ) - Real.log (n : ℝ) + ε (2 * n) - ε n)
      atTop (𝓝 (Real.log 2)) := by
  apply (epsilonComboLimit ε hε).congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn' : 0 < (n : ℝ) := by positivity
  rw [show Real.log (((2 * n : ℕ) : ℝ)) - Real.log (n : ℝ) =
    Real.log 2 by
      push_cast
      rw [Real.log_mul (by norm_num) (ne_of_gt hn')]
      ring]

private theorem harmonic_add_tail (n : ℕ) :
    harmonic (2 * n) = harmonic n + harmonicTail n := by
  unfold harmonic harmonicTail
  rw [← Finset.sum_union]
  · congr 1
    ext i
    simp
    omega
  · rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    simp only [Finset.mem_Icc] at hi₁ hi₂
    omega

/-- Source: `proof_gap/exercise_147/5.txt`; both sides are given their common finite limit. -/
theorem gap5 (C : ℝ) (ε : ℕ → ℝ) (h : EulerExpansion C ε) :
    Tendsto harmonicTail atTop (𝓝 (Real.log 2)) ∧
    Tendsto (fun n : ℕ =>
      Real.log ((2 * n : ℕ) : ℝ) - Real.log (n : ℝ) + ε (2 * n) - ε n)
      atTop (𝓝 (Real.log 2)) := by
  have htrans :
      Tendsto (fun n : ℕ =>
        Real.log ((2 * n : ℕ) : ℝ) - Real.log (n : ℝ) + ε (2 * n) - ε n)
        atTop (𝓝 (Real.log 2)) :=
    transformedLimit ε h.2
  refine ⟨?_, htrans⟩
  apply htrans.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have h2n : 0 < 2 * n := by positivity
  have ht := harmonic_add_tail n
  rw [h.1 (2 * n) h2n, h.1 n hn] at ht
  linarith

/-- Source: `proof_gap/exercise_147/6.txt`; n=0 is irrelevant to the tail limit. -/
theorem gap6 (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      Real.log ((2 * n : ℕ) : ℝ) - Real.log (n : ℝ) + ε (2 * n) - ε n)
      atTop (𝓝 (Real.log 2)) ↔
    Tendsto (fun n => Real.log 2 + ε (2 * n) - ε n)
      atTop (𝓝 (Real.log 2)) := by
  constructor
  · intro _
    exact epsilonComboLimit ε hε
  · intro _
    exact transformedLimit ε hε

/-- Source: `proof_gap/exercise_147/7.txt`. -/
theorem gap7 (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => Real.log 2 + ε (2 * n) - ε n)
      atTop (𝓝 (Real.log 2)) := by
  exact epsilonComboLimit ε hε

/-- Source: `proof_gap/exercise_147/8.txt`. -/
theorem gap8 : Tendsto harmonicTail atTop (𝓝 (Real.log 2)) := by
  rcases gap1 with ⟨C, ε, h⟩
  exact (gap5 C ε h).1

/-- Source: `proof_gap/exercise_147/9.txt`. -/
theorem gap9 : Tendsto harmonicTail atTop (𝓝 (Real.log 2)) := by
  exact gap8

end

end ProofGap.Exercise147
