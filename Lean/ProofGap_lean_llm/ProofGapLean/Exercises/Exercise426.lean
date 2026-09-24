import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise426

noncomputable section

def original (n : ℕ) (a x : ℝ) : ℝ :=
  (x ^ n - a ^ n - n * a ^ (n - 1) * (x - a)) / (x - a) ^ 2
def shifted (n : ℕ) (a y : ℝ) : ℝ :=
  ((a + y) ^ n - a ^ n - n * a ^ (n - 1) * y) / y ^ 2
def value (n : ℕ) (a : ℝ) : ℝ :=
  ((n : ℝ) * (n - 1) / 2) * a ^ (n - 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 426, gap 1; formalize the substitution `y=x-a`. -/
theorem gap1 (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => x - a) (nhds a) (nhds 0) := by
  have h :
      Filter.Tendsto (fun x : ℝ => x - a) (nhds a) (nhds (a - a)) :=
    continuousAt_id.sub continuousAt_const
  simpa only [sub_self] using h

/-- Exercise 426, gap 2. -/
theorem gap2 (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    HasLimitAt (original n a) a (value n a) ↔
      HasLimitAt (shifted n a) 0 (value n a) := by
  unfold HasLimitAt
  have hplus :
      Filter.Tendsto (fun y : ℝ => a + y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) := by
    refine Filter.Tendsto.inf ?_ ?_
    · have h :
          Filter.Tendsto (fun y : ℝ => a + y)
            (nhds 0) (nhds (a + 0)) :=
        continuousAt_const.add continuousAt_id
      simpa only [add_zero] using h
    · apply Filter.tendsto_principal.2
      change ({0} : Set ℝ)ᶜ ⊆ {y : ℝ | a + y ∈ ({a} : Set ℝ)ᶜ}
      intro y hy
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
  have hminus :
      Filter.Tendsto (fun x : ℝ => x - a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine Filter.Tendsto.inf ?_ ?_
    · exact gap1 a
    · apply Filter.tendsto_principal.2
      change ({a} : Set ℝ)ᶜ ⊆ {x : ℝ | x - a ∈ ({0} : Set ℝ)ᶜ}
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

/-- Exercise 426, gap 3; replace the expansion ellipsis by its finite-limit consequence. -/
theorem gap3 (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    HasLimitAt (shifted n a) 0 (value n a) := by
  induction n, hn using Nat.le_induction with
  | base =>
      unfold HasLimitAt
      have hval : value 2 a = 1 := by
        norm_num [value]
      rw [hval]
      refine (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : y ≠ 0 := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
      unfold shifted
      field_simp [hy0]
      ring
  | succ n hn ih =>
      have hpow : a ^ n = a ^ (n - 1) * a := by
        calc
          a ^ n = a ^ ((n - 1) + 1) := by
            congr 1 <;> omega
          _ = a ^ (n - 1) * a := by rw [pow_succ]
      have hrec :
          ∀ᶠ y in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
            shifted (n + 1) a y =
              (a + y) * shifted n a y + (n : ℝ) * a ^ (n - 1) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := by
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
        unfold shifted
        simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
        rw [hpow]
        field_simp [hy0]
        ring
      have hpow' : a ^ (n - 1) = a ^ (n - 2) * a := by
        calc
          a ^ (n - 1) = a ^ ((n - 2) + 1) := by
            congr 1 <;> omega
          _ = a ^ (n - 2) * a := by rw [pow_succ]
      have hvalue :
          value (n + 1) a =
            a * value n a + (n : ℝ) * a ^ (n - 1) := by
        unfold value
        rw [show n + 1 - 2 = n - 1 by omega]
        rw [hpow']
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      have hcont :
          Filter.Tendsto (fun y : ℝ => a + y) (nhds 0) (nhds a) := by
        have h :
            Filter.Tendsto (fun y : ℝ => a + y)
              (nhds 0) (nhds (a + 0)) :=
          continuousAt_const.add continuousAt_id
        simpa only [add_zero] using h
      have hy_lim :
          Filter.Tendsto (fun y : ℝ => a + y)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
        exact Filter.Tendsto.mono_left hcont inf_le_left
      have hcalc :
          Filter.Tendsto
            (fun y : ℝ =>
              (a + y) * shifted n a y + (n : ℝ) * a ^ (n - 1))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
            (nhds (a * value n a + (n : ℝ) * a ^ (n - 1))) := by
        exact (hy_lim.mul ih).add tendsto_const_nhds
      rw [← hvalue] at hcalc
      apply hcalc.congr'
      filter_upwards [hrec] with y hy
      exact hy.symm

/-- Exercise 426, gap 4. -/
theorem gap4 (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    HasLimitAt (fun _ : ℝ => value n a) 0 (value n a) := by
  unfold HasLimitAt
  exact tendsto_const_nhds

/-- Exercise 426, gap 5. -/
theorem gap5 (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    HasLimitAt (shifted n a) 0 (value n a) := by
  exact gap3 n hn a

end

end ProofGap.Exercise426
