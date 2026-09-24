import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise427

noncomputable section

def original (n : ℕ) (x : ℝ) : ℝ :=
  (x ^ (n + 1) - (n + 1) * x + n) / (x - 1) ^ 2
def shifted (n : ℕ) (y : ℝ) : ℝ :=
  ((1 + y) ^ (n + 1) - (n + 1) * (1 + y) + n) / y ^ 2
def value (n : ℕ) : ℝ := (n : ℝ) * (n + 1) / 2
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 427, gap 1; formalize `y=x-1`. -/
theorem gap1 :
    Filter.Tendsto (fun x : ℝ => x - 1) (nhds 1) (nhds 0) := by
  have h :
      Filter.Tendsto (fun x : ℝ => x - 1) (nhds 1) (nhds (1 - 1)) :=
    continuousAt_id.sub continuousAt_const
  norm_num at h ⊢
  exact h

/-- Exercise 427, gap 2. -/
theorem gap2 (n : ℕ) :
    HasLimitAt (original n) 1 (value n) ↔
      HasLimitAt (shifted n) 0 (value n) := by
  unfold HasLimitAt
  have hplus :
      Filter.Tendsto (fun y : ℝ => 1 + y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) := by
    refine Filter.Tendsto.inf ?_ ?_
    · have h :
          Filter.Tendsto (fun y : ℝ => 1 + y)
            (nhds 0) (nhds (1 + 0)) :=
        continuousAt_const.add continuousAt_id
      norm_num at h ⊢
      exact h
    · apply Filter.tendsto_principal.2
      change ({0} : Set ℝ)ᶜ ⊆ {y : ℝ | 1 + y ∈ ({1} : Set ℝ)ᶜ}
      intro y hy
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
  have hminus :
      Filter.Tendsto (fun x : ℝ => x - 1)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine Filter.Tendsto.inf ?_ ?_
    · exact gap1
    · apply Filter.tendsto_principal.2
      change ({1} : Set ℝ)ᶜ ⊆ {x : ℝ | x - 1 ∈ ({0} : Set ℝ)ᶜ}
      intro x hx
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] using hx
  constructor
  · intro h
    exact (h.comp hplus).congr'
      (Filter.Eventually.of_forall fun y => by
        simp [original, shifted, sub_eq_add_neg, add_assoc])
  · intro h
    exact (h.comp hminus).congr'
      (Filter.Eventually.of_forall fun x => by
        simp [original, shifted, sub_eq_add_neg, add_assoc])

/-- Exercise 427, gap 3; replace the expansion ellipsis by its limit consequence. -/
theorem gap3 (n : ℕ) : HasLimitAt (shifted n) 0 (value n) := by
  induction n with
  | zero =>
      unfold HasLimitAt
      have hval : value 0 = 0 := by norm_num [value]
      rw [hval]
      refine (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)).congr' ?_
      filter_upwards with y
      norm_num [shifted]
  | succ n ih =>
      have hrec :
          ∀ᶠ y in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
            shifted (n + 1) y =
              (1 + y) * shifted n y + ((n + 1 : ℕ) : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := by
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
        unfold shifted
        simp only [Nat.cast_add, Nat.cast_one]
        field_simp [hy0]
        ring
      have hvalue :
          value (n + 1) = value n + ((n + 1 : ℕ) : ℝ) := by
        unfold value
        push_cast
        ring
      have hcont :
          Filter.Tendsto (fun y : ℝ => 1 + y) (nhds 0) (nhds 1) := by
        have h :
            Filter.Tendsto (fun y : ℝ => 1 + y)
              (nhds 0) (nhds (1 + 0)) :=
          continuousAt_const.add continuousAt_id
        norm_num at h ⊢
        exact h
      have hy_lim :
          Filter.Tendsto (fun y : ℝ => 1 + y)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
        Filter.Tendsto.mono_left hcont inf_le_left
      have hcalc :
          Filter.Tendsto
            (fun y : ℝ =>
              (1 + y) * shifted n y + ((n + 1 : ℕ) : ℝ))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
            (nhds (value n + ((n + 1 : ℕ) : ℝ))) := by
        simpa using (hy_lim.mul ih).add tendsto_const_nhds
      rw [← hvalue] at hcalc
      apply hcalc.congr'
      filter_upwards [hrec] with y hy
      exact hy.symm

/-- Exercise 427, gap 4. -/
theorem gap4 (n : ℕ) :
    HasLimitAt (fun _ : ℝ => value n) 0 (value n) := by
  unfold HasLimitAt
  exact tendsto_const_nhds

/-- Exercise 427, gap 5. -/
theorem gap5 (n : ℕ) : HasLimitAt (shifted n) 0 (value n) := by
  exact gap3 n

end

end ProofGap.Exercise427
