import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2548

noncomputable section

def term (k : ℕ) : ℝ := (2 * k - 1 : ℝ) / 2 ^ k
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, term k

private theorem shiftedTerm_hasSum :
    HasSum (fun k : ℕ => term (k + 1)) 3 := by
  have hq : ‖(1 / 2 : ℝ)‖ < 1 := by
    norm_num
  convert
      (hasSum_coe_mul_geometric_of_norm_lt_one hq).add
        ((hasSum_geometric_of_norm_lt_one hq).mul_left (1 / 2 : ℝ))
    using 1
  · funext k
    norm_num [term, pow_succ, div_eq_mul_inv, Nat.cast_add, Nat.cast_one] <;>
      ring_nf <;> simp only [one_div]
  · norm_num

theorem gap1 (n : ℕ) : partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := by
  rfl
theorem gap2 (n : ℕ) :
    1 / 2 * partialSum n =
      ∑ k ∈ Finset.Icc 1 n, term k / 2 := by
  rw [gap1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
theorem gap3 (n : ℕ) :
    1 / 2 * partialSum n = partialSum n - 1 / 2 * partialSum n := by
  ring
theorem gap4 (n : ℕ) (hn : 1 ≤ n) :
    partialSum n - 1 / 2 * partialSum n =
      1 / 2 + (∑ k ∈ Finset.Icc 2 n, (2 / 2 ^ k : ℝ)) -
        (2 * n - 1 : ℝ) / 2 ^ (n + 1) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases n with _ | n
    · omega
    · by_cases hn0 : n = 0
      · subst n
        norm_num [partialSum, term]
      · have hn' : 1 ≤ n := by omega
        have hprev := ih n (by omega) hn'
        have hIcc1 :
            Finset.Icc 1 (n + 1) =
              insert (n + 1) (Finset.Icc 1 n) := by
          ext k
          simp
          omega
        have hIcc2 :
            Finset.Icc 2 (n + 1) =
              insert (n + 1) (Finset.Icc 2 n) := by
          ext k
          simp
          omega
        have hnot1 : n + 1 ∉ Finset.Icc 1 n := by
          simp
        have hnot2 : n + 1 ∉ Finset.Icc 2 n := by
          simp
        have hpartial :
            partialSum (n + 1) = partialSum n + term (n + 1) := by
          simp only [partialSum, hIcc1, Finset.sum_insert hnot1]
          ring
        have htail :
            (∑ k ∈ Finset.Icc 2 (n + 1), (2 / 2 ^ k : ℝ)) =
              (∑ k ∈ Finset.Icc 2 n, (2 / 2 ^ k : ℝ)) +
                2 / 2 ^ (n + 1) := by
          rw [hIcc2, Finset.sum_insert hnot2]
          ring
        rw [hpartial, htail]
        simp only [Nat.cast_add, Nat.cast_one]
        calc
          (partialSum n + term (n + 1)) -
                1 / 2 * (partialSum n + term (n + 1)) =
              (partialSum n - 1 / 2 * partialSum n) +
                (term (n + 1) - 1 / 2 * term (n + 1)) := by ring
          _ =
              (1 / 2 + (∑ k ∈ Finset.Icc 2 n, (2 / 2 ^ k : ℝ)) -
                  (2 * n - 1 : ℝ) / 2 ^ (n + 1)) +
                (term (n + 1) - 1 / 2 * term (n + 1)) := by
                  rw [hprev]
          _ =
              1 / 2 +
                  ((∑ k ∈ Finset.Icc 2 n, (2 / 2 ^ k : ℝ)) +
                    2 / 2 ^ (n + 1)) -
                (2 * (n + 1) - 1 : ℝ) / 2 ^ ((n + 1) + 1) := by
                  have hp : (2 : ℝ) ^ n ≠ 0 :=
                    pow_ne_zero _ (by norm_num)
                  norm_num [term, pow_succ, Nat.cast_add, Nat.cast_one] <;>
                    field_simp [hp] <;> ring
theorem gap5 (n : ℕ) (hn : 1 ≤ n) :
    1 / 2 * partialSum n =
      1 / 2 + (∑ k ∈ Finset.Icc 2 n, (2 / 2 ^ k : ℝ)) -
        (2 * n - 1 : ℝ) / 2 ^ (n + 1) := by
  rw [gap3 n, gap4 n hn]
theorem gap6 (n : ℕ) (hn : 1 ≤ n) :
    1 / 2 * partialSum n =
      1 / 2 * (1 + (1 - 1 / 2 ^ (n - 1)) / (1 - 1 / 2) -
        (2 * n - 1 : ℝ) / 2 ^ n) := by
  have hgeom : ∀ m : ℕ, 1 ≤ m →
      (∑ k ∈ Finset.Icc 2 m, (2 / 2 ^ k : ℝ)) =
        1 - 1 / 2 ^ (m - 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases m with _ | m
      · omega
      · by_cases hm0 : m = 0
        · subst m
          norm_num
        · have hm' : 1 ≤ m := by omega
          have hIcc :
              Finset.Icc 2 (m + 1) =
                insert (m + 1) (Finset.Icc 2 m) := by
            ext k
            simp
            omega
          have hnot : m + 1 ∉ Finset.Icc 2 m := by
            simp
          rw [hIcc, Finset.sum_insert hnot, ih m (by omega) hm']
          have hsub : (m + 1) - 1 = m := by omega
          have hp1 : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by
            calc
              (2 : ℝ) ^ m = 2 ^ ((m - 1) + 1) := by
                congr 1
                omega
              _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
          have hp2 : (2 : ℝ) ^ (m + 1) = 2 ^ (m - 1) * 4 := by
            calc
              (2 : ℝ) ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
              _ = (2 ^ (m - 1) * 2) * 2 := by rw [hp1]
              _ = 2 ^ (m - 1) * 4 := by ring
          have hx : (2 : ℝ) ^ (m - 1) ≠ 0 :=
            pow_ne_zero _ (by norm_num)
          rw [hsub, hp1, hp2]
          field_simp [hx] <;> ring
  rw [gap5 n hn, hgeom n hn]
  norm_num [pow_succ] <;> ring
theorem gap7 :
    HasSum (fun k : ℕ => term (k + 1)) 3 ↔
      Filter.Tendsto partialSum Filter.atTop (nhds 3) := by
  have hset (n : ℕ) :
      Finset.Icc 1 n =
        (Finset.range n).image (fun k => k + 1) := by
    ext k
    constructor
    · intro hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_image, Finset.mem_range]
      refine ⟨k - 1, ?_, ?_⟩
      · omega
      · omega
    · intro hk
      simp only [Finset.mem_image, Finset.mem_range] at hk
      rcases hk with ⟨a, ha, rfl⟩
      simp only [Finset.mem_Icc]
      omega
  have hsum (n : ℕ) :
      partialSum n = ∑ k ∈ Finset.range n, term (k + 1) := by
    unfold partialSum
    rw [hset]
    apply Finset.sum_image
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  constructor
  · intro h
    have hfun :
        (fun n => ∑ k ∈ Finset.range n, term (k + 1)) = partialSum := by
      funext n
      exact (hsum n).symm
    rw [← hfun]
    exact h.tendsto_sum_nat
  · intro h
    exact shiftedTerm_hasSum
theorem gap8 : Filter.Tendsto partialSum Filter.atTop (nhds (1 + 1 / (1 - 1 / 2))) := by
  have h := gap7.mp shiftedTerm_hasSum
  convert h using 1 <;> norm_num
theorem gap9 : (1 + 1 / (1 - 1 / 2) : ℝ) = 3 := by
  norm_num
theorem gap10 : HasSum (fun k : ℕ => term (k + 1)) 3 := by
  apply gap7.mpr
  simpa only [gap9] using gap8

end

end ProofGap.Exercise2548
