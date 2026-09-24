import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2876

noncomputable section

open scoped BigOperators

def reciprocalTerm (x : ℝ) (n : ℕ) : ℝ :=
  1 / x ^ n

private theorem reciprocalTerm_hasSum (x : ℝ) (hx : 1 < |x|) :
    HasSum (fun n : ℕ => reciprocalTerm x n) (1 / (1 - 1 / x)) := by
  have hpos : 0 < |x| := lt_trans zero_lt_one hx
  have hquot : 1 / |x| < 1 := (div_lt_one hpos).2 hx
  have hnorm : ‖1 / x‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_div] using hquot
  simpa [reciprocalTerm, one_div, inv_pow] using
    (hasSum_geometric_of_norm_lt_one hnorm)

theorem gap1 :
    ∀ x : ℝ, x ≠ 0 →
      1 / (1 - x) = -(1 / x) * (1 / (1 - 1 / x)) := by
  intro x hx
  by_cases h : 1 - x = 0
  · have hx1 : x = 1 := (sub_eq_zero.mp h).symm
    subst x
    norm_num
  · have hden : 1 - 1 / x ≠ 0 := by
      intro hd
      have hi : 1 / x = 1 := (sub_eq_zero.mp hd).symm
      have hx1 : x = 1 := by
        calc
          x = x * 1 := by ring
          _ = x * (1 / x) := by rw [hi]
          _ = 1 := by field_simp [hx]
      apply h
      simp [hx1]
    have hxminus : x - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h))
    field_simp [hx, h, hden, hxminus] <;> ring

theorem gap2 :
    ∀ x : ℝ, x ≠ 0 →
      1 / (1 - x) = (1 / x) * (1 / (1 / x - 1)) := by
  intro x hx
  calc
    1 / (1 - x) = -(1 / x) * (1 / (1 - 1 / x)) := gap1 x hx
    _ = (1 / x) * (1 / (1 / x - 1)) := by
      rw [show 1 / x - 1 = -(1 - 1 / x) by ring]
      simp only [one_div, inv_neg]
      ring

theorem gap3 :
    ∀ x : ℝ, 1 < |x| →
      (1 / x) * (1 / (1 / x - 1)) =
        -(1 / x) * (∑' n : ℕ, reciprocalTerm x n) := by
  intro x hx
  rw [(reciprocalTerm_hasSum x hx).tsum_eq]
  rw [show 1 / x - 1 = -(1 - 1 / x) by ring]
  simp only [one_div, inv_neg]
  ring

theorem gap4 :
    ∀ x : ℝ, 1 < |x| →
      -(1 / x) * (∑' n : ℕ, reciprocalTerm x n) =
        -(∑' n : ℕ, reciprocalTerm x (n + 1)) := by
  intro x hx
  have hs := reciprocalTerm_hasSum x hx
  have hshift :
      HasSum (fun n : ℕ => reciprocalTerm x (n + 1))
        ((1 / x) * (1 / (1 - 1 / x))) := by
    simpa [reciprocalTerm, one_div, inv_pow, pow_succ, mul_comm,
      mul_left_comm, mul_assoc] using (hs.mul_left (1 / x))
  rw [hs.tsum_eq, hshift.tsum_eq]
  ring

theorem gap5 :
    ∀ x : ℝ, 1 < |x| →
      1 / (1 - x) = -(∑' n : ℕ, reciprocalTerm x (n + 1)) := by
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  calc
    1 / (1 - x) = (1 / x) * (1 / (1 / x - 1)) := gap2 x hx0
    _ = -(1 / x) * (∑' n : ℕ, reciprocalTerm x n) := gap3 x hx
    _ = -(∑' n : ℕ, reciprocalTerm x (n + 1)) := gap4 x hx

end

end ProofGap.Exercise2876
