import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise650_7

noncomputable section

def higherTerms (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.Icc 2 n).sum (fun k => (n.choose k : ℝ) * x ^ (k - 1))
def remainder (n : ℕ) (x : ℝ) : ℝ :=
  (1 + x) ^ n - 1 - n * x

/-- Source: `proof_gap/exercise_650_7/1.txt`; replace the binomial ellipsis by `higherTerms`. -/
private theorem remainder_eq_mul_higherTerms (n : ℕ) (x : ℝ) :
    remainder n x = x * higherTerms n x := by
  cases n with
  | zero =>
      simp [remainder, higherTerms] <;> ring
  | succ n =>
      cases n with
      | zero =>
          simp [remainder, higherTerms] <;> ring
      | succ n =>
          unfold remainder higherTerms
          have hadd :
              (1 + x) ^ Nat.succ (Nat.succ n) =
                (Finset.range (Nat.succ (Nat.succ n) + 1)).sum
                  (fun k => ((Nat.succ (Nat.succ n)).choose k : ℝ) * x ^ k) := by
            simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
              (add_pow x (1 : ℝ) (Nat.succ (Nat.succ n)))
          have hrange :
              Finset.range (Nat.succ (Nat.succ n) + 1) =
                insert 0
                  (insert 1 (Finset.Icc 2 (Nat.succ (Nat.succ n)))) := by
            ext k
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
            omega
          have hzero :
              0 ∉ insert 1 (Finset.Icc 2 (Nat.succ (Nat.succ n))) := by
            simp
          have hone :
              1 ∉ Finset.Icc 2 (Nat.succ (Nat.succ n)) := by
            simp
          have hsum :
              (Finset.Icc 2 (Nat.succ (Nat.succ n))).sum
                  (fun k => ((Nat.succ (Nat.succ n)).choose k : ℝ) * x ^ k) =
                x * (Finset.Icc 2 (Nat.succ (Nat.succ n))).sum
                  (fun k => ((Nat.succ (Nat.succ n)).choose k : ℝ) * x ^ (k - 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            have hk1 : 1 ≤ k := by
              have hk2 := (Finset.mem_Icc.mp hk).1
              omega
            have hpow : x ^ k = x * x ^ (k - 1) := by
              calc
                x ^ k = x ^ (1 + (k - 1)) := by
                  congr 1
                  omega
                _ = x * x ^ (k - 1) := by simp [pow_add]
            rw [hpow]
            ring
          rw [hadd, hrange, Finset.sum_insert hzero,
            Finset.sum_insert hone, hsum]
          simp <;> ring

theorem gap1 (x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    remainder n x / x = higherTerms n x := by
  rw [remainder_eq_mul_higherTerms]
  simp [hx]

/-- Source: `proof_gap/exercise_650_7/2.txt`; replace the ellipsis by the complete higher-term sum. -/
theorem gap2 (n : ℕ) :
    Filter.Tendsto (higherTerms n) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt (higherTerms n) 0 := by
    classical
    unfold higherTerms
    induction Finset.Icc 2 n using Finset.induction_on with
    | empty =>
        simpa using
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0)
    | @insert k s hk ih =>
        have hterm :
            ContinuousAt
              (fun x : ℝ => (n.choose k : ℝ) * x ^ (k - 1)) 0 :=
          continuousAt_const.mul (continuousAt_id.pow (k - 1))
        simpa only [Finset.sum_insert hk] using hterm.add ih
  have hzero : higherTerms n 0 = 0 := by
    unfold higherTerms
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : k - 1 ≠ 0 := by
      have hk2 := (Finset.mem_Icc.mp hk).1
      omega
    simp [hk0]
  simpa only [hzero] using hcont.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_650_7/3.txt`. -/
theorem gap3 (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => remainder n x / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine (gap2 n).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (gap1 x n (ne_of_gt hx)).symm

/-- Source: `proof_gap/exercise_650_7/4.txt`. -/
theorem gap4 (n : ℕ) :
    Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
      (remainder n) (fun x : ℝ => x) := by
  have hzero :
      ∀ x : ℝ, (fun y : ℝ => y) x = 0 → remainder n x = 0 := by
    intro x hx
    change x = 0 at hx
    subst x
    simp [remainder]
  refine (Asymptotics.isLittleO_iff_tendsto hzero).2 ?_
  simpa [div_eq_mul_inv, mul_comm] using (gap3 n)

/-- Source: `proof_gap/exercise_650_7/5.txt`; make the little-o remainder function explicit. -/
theorem gap5 (n : ℕ) :
    ∃ r : ℝ → ℝ, Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
        r (fun x : ℝ => x) ∧
      ∀ x, (1 + x) ^ n = 1 + n * x + r x := by
  refine ⟨remainder n, gap4 n, ?_⟩
  intro x
  unfold remainder
  ring

/-- Source: `proof_gap/exercise_650_7/6.txt`. -/
theorem gap6 (n : ℕ) :
    ∃ r : ℝ → ℝ, Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
        r (fun x : ℝ => x) ∧
      ∀ x, (1 + x) ^ n = 1 + n * x + r x := by
  exact gap5 n

end

end ProofGap.Exercise650_7
