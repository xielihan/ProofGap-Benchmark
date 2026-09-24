import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2706_2

noncomputable section

def a (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n

def b (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1)

def c (n : ℕ) : ℝ :=
  a n + b n

def a' (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

def b' (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

def c' (n : ℕ) : ℝ :=
  a' n + b' n

theorem gap1 :
    ¬ Summable (fun n : ℕ => a (n + 1)) := by
  intro h
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    simpa [a] using h.tendsto_atTop_zero.norm
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hone hconst
  norm_num at this

theorem gap2 :
    ¬ Summable (fun n : ℕ => b (n + 1)) := by
  intro h
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    simpa [b] using h.tendsto_atTop_zero.norm
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hone hconst
  norm_num at this

theorem gap3 :
    ∀ n : ℕ, c n = 0 := by
  intro n
  simp [c, a, b, pow_succ]

theorem gap4 :
    Summable (fun n : ℕ => c (n + 1)) := by
  simpa [gap3] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

theorem gap5 :
    ∀ n : ℕ, c' n = 2 / ((n : ℝ) + 1) := by
  intro n
  simp [c', a', b']
  ring

theorem gap6 :
    ¬ Summable a' := by
  intro h
  change Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) at h
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
  simpa [one_div, Nat.cast_add] using h

theorem gap7 :
    ¬ Summable b' := by
  simpa [a', b'] using gap6

theorem gap8 :
    ¬ Summable c' := by
  intro h
  apply gap6
  have hhalf := h.mul_left (1 / 2 : ℝ)
  convert hhalf using 1
  funext n
  rw [gap5]
  unfold a'
  ring_nf

theorem gap9 :
    ∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ → ℝ,
      (∀ n, c₁ n = a₁ n + b₁ n) ∧
      ¬ Summable a₁ ∧ ¬ Summable b₁ ∧ Summable c₁ ∧
      (∀ n, c₂ n = a₂ n + b₂ n) ∧
      ¬ Summable a₂ ∧ ¬ Summable b₂ ∧ ¬ Summable c₂ := by
  have hna : ¬ Summable a := by
    intro h
    exact gap1 ((summable_nat_add_iff 1).mpr h)
  have hnb : ¬ Summable b := by
    intro h
    exact gap2 ((summable_nat_add_iff 1).mpr h)
  have hsc : Summable c := by
    exact (summable_nat_add_iff 1).mp gap4
  exact ⟨a, b, c, a', b', c', fun _ => rfl,
    hna, hnb, hsc, fun _ => rfl, gap6, gap7, gap8⟩

end

end ProofGap.Exercise2706_2
