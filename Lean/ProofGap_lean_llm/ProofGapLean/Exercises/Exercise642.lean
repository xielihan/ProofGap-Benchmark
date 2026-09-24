import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise642

noncomputable section

def f (x : ℝ) : ℝ := Real.sin (1 / x)
def witnessSeq (x₀ : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * ((n : ℝ) + 1) * Real.pi + x₀)

/-- Source: `proof_gap/exercise_642/1.txt`. -/
private theorem sin_nat_period (x : ℝ) :
    ∀ n : ℕ, Real.sin (2 * (n : ℝ) * Real.pi + x) = Real.sin x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Real.sin (2 * (Nat.succ n : ℝ) * Real.pi + x) =
            Real.sin ((2 * (n : ℝ) * Real.pi + x) + 2 * Real.pi) := by
          congr 1
          rw [Nat.cast_succ]
          ring
        _ = Real.sin (2 * (n : ℝ) * Real.pi + x) :=
          Real.sin_add_two_pi _
        _ = Real.sin x := ih

theorem gap1 (α : ℝ) (hα : |α| ≤ 1) :
    ∃ x₀ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2),
      Real.sin x₀ = α := by
  rcases abs_le.mp hα with ⟨hlo, hhi⟩
  exact ⟨Real.arcsin α, Real.arcsin_mem_Icc α,
    Real.sin_arcsin hlo hhi⟩

/-- Source: `proof_gap/exercise_642/2.txt`; bind the explicitly constructed sequence. -/
theorem gap2 (x₀ : ℝ) :
    Filter.Tendsto (witnessSeq x₀) Filter.atTop (nhds 0) := by
  have hden :
      Filter.Tendsto
        (fun n : ℕ => 2 * ((n : ℝ) + 1) * Real.pi + x₀)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    let c : ℝ := 2 * Real.pi
    let k : ℝ := c + x₀
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos (by norm_num) Real.pi_pos
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - k) / c)
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hscaled : b - k < (N : ℝ) * c :=
      (div_lt_iff₀ hc).mp hN
    have hb : b < (N : ℝ) * c + k := by
      calc
        b = (b - k) + k := by ring
        _ < (N : ℝ) * c + k := by
          simpa [add_comm] using add_lt_add_right hscaled k
    have hmul : c * (N : ℝ) ≤ c * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hc.le
    calc
      b ≤ (N : ℝ) * c + k := hb.le
      _ = c * (N : ℝ) + k := by ring
      _ ≤ c * (n : ℝ) + k := by
        simpa [add_comm] using add_le_add_right hmul k
      _ = 2 * ((n : ℝ) + 1) * Real.pi + x₀ := by
        dsimp [c, k]
        ring
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hwitness :
      witnessSeq x₀ =
        (fun n : ℕ => (2 * ((n : ℝ) + 1) * Real.pi + x₀)⁻¹) := by
    funext n
    simp only [witnessSeq, one_div]
  rw [hwitness]
  simpa only [Function.comp_apply] using hinv.comp hden

/-- Source: `proof_gap/exercise_642/3.txt`; bind `α,x₀` before choosing the sequence. -/
theorem gap3 (α x₀ : ℝ) (hx₀ : Real.sin x₀ = α) :
    ∀ n, f (witnessSeq x₀ n) =
      Real.sin (1 / witnessSeq x₀ n) := by
  intro n
  rfl

/-- Source: `proof_gap/exercise_642/4.txt`; remove the unbound existential sequence. -/
theorem gap4 (x₀ : ℝ) :
    ∀ n, Real.sin (1 / witnessSeq x₀ n) =
      Real.sin (2 * ((n : ℝ) + 1) * Real.pi + x₀) := by
  intro n
  simp [witnessSeq, one_div]

/-- Source: `proof_gap/exercise_642/5.txt`; bind the selected inverse-sine witness. -/
theorem gap5 (α x₀ : ℝ) (hx₀ : Real.sin x₀ = α) :
    ∀ n : ℕ, Real.sin (2 * ((n : ℝ) + 1) * Real.pi + x₀) = α := by
  intro n
  calc
    Real.sin (2 * ((n : ℝ) + 1) * Real.pi + x₀) = Real.sin x₀ := by
      simpa [Nat.cast_succ] using sin_nat_period x₀ (Nat.succ n)
    _ = α := hx₀

/-- Source: `proof_gap/exercise_642/6.txt`; use the explicit witness sequence. -/
theorem gap6 (α x₀ : ℝ) (hx₀ : Real.sin x₀ = α) :
    ∀ n, f (witnessSeq x₀ n) = α := by
  intro n
  calc
    f (witnessSeq x₀ n) =
        Real.sin (1 / witnessSeq x₀ n) := gap3 α x₀ hx₀ n
    _ = Real.sin (2 * ((n : ℝ) + 1) * Real.pi + x₀) := gap4 x₀ n
    _ = Real.sin x₀ := by
      simpa [Nat.cast_succ] using
        (sin_nat_period x₀ (Nat.succ n))
    _ = α := hx₀

/-- Source: `proof_gap/exercise_642/7.txt`; the sequence depends on `α`. -/
theorem gap7 (α : ℝ) (hα : |α| ≤ 1) :
    ∃ u : ℕ → ℝ,
      Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds α) := by
  rcases gap1 α hα with ⟨x₀, _, hx₀⟩
  refine ⟨witnessSeq x₀, ?_⟩
  have hfun :
      (fun n : ℕ => f (witnessSeq x₀ n)) = (fun _ : ℕ => α) := by
    funext n
    exact gap6 α x₀ hx₀ n
  rw [hfun]
  exact tendsto_const_nhds

/-- Source: `proof_gap/exercise_642/8.txt`. -/
theorem gap8 (α : ℝ) (hα : -1 ≤ α ∧ α ≤ 1) :
    ∃ u : ℕ → ℝ, Filter.Tendsto u Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds α) := by
  have habs : |α| ≤ 1 := abs_le.2 hα
  rcases gap1 α habs with ⟨x₀, _, hx₀⟩
  refine ⟨witnessSeq x₀, gap2 x₀, ?_⟩
  have hfun :
      (fun n : ℕ => f (witnessSeq x₀ n)) = (fun _ : ℕ => α) := by
    funext n
    exact gap6 α x₀ hx₀ n
  rw [hfun]
  exact tendsto_const_nhds

end

end ProofGap.Exercise642
