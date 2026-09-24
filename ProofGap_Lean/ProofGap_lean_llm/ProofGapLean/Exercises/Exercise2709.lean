import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2709

noncomputable section

def term (n : ℕ) : ℝ :=
  Real.cos (2 * n * Real.pi / 3) / (2 : ℝ) ^ n

def residuePart (r n : ℕ) : ℝ :=
  if n % 3 = r then term n else 0

def blockTerm (k : ℕ) : ℝ :=
  term (3 * k) + term (3 * k + 1) + term (3 * k + 2)

def fullSum : ℝ :=
  ∑' n : ℕ, term n

def requestedSum : ℝ :=
  ∑' n : ℕ, term (n + 1)

private theorem summable_abs_term : Summable (fun n : ℕ => |term n|) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (1 / 2 : ℝ) ^ n)
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)) ?_
  intro n
  simp only [Real.norm_eq_abs, abs_abs, term, abs_div]
  rw [abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n),
    one_div_pow]
  exact div_le_div_of_nonneg_right
    (Real.abs_cos_le_one (2 * (n : ℝ) * Real.pi / 3))
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)

private theorem summable_term : Summable term := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => |term n|) summable_abs_term ?_
  intro n
  simpa only [Real.norm_eq_abs] using
    (le_rfl : |term n| ≤ |term n|)

theorem gap1 :
    Summable (fun n : ℕ => |term (n + 1)|) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    have h :=
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
        (1 / 2 : ℝ)
    simpa [pow_succ, mul_comm] using h
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) hg ?_
  intro n
  simp only [Real.norm_eq_abs, abs_abs, term, abs_div]
  rw [abs_of_nonneg
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1)),
    one_div_pow]
  exact div_le_div_of_nonneg_right
    (Real.abs_cos_le_one (2 * ((n + 1 : ℕ) : ℝ) * Real.pi / 3))
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1))

theorem gap2 :
    requestedSum = fullSum - 1 := by
  have h : term 0 + requestedSum = fullSum := by
    simpa [requestedSum, fullSum, add_comm] using
      (summable_term.sum_add_tsum_nat_add 1)
  have ht0 : term 0 = 1 := by
    norm_num [term]
  rw [ht0] at h
  linarith

theorem gap3 :
    fullSum =
      (∑' n : ℕ, residuePart 0 n) +
      (∑' n : ℕ, residuePart 1 n) +
      (∑' n : ℕ, residuePart 2 n) := by
  have hr (r : ℕ) : Summable (residuePart r) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => |term n|) summable_abs_term ?_
    intro n
    by_cases h : n % 3 = r
    · simp [residuePart, h, Real.norm_eq_abs]
    · simp [residuePart, h]
  calc
    fullSum = ∑' n : ℕ,
        ((residuePart 0 n + residuePart 1 n) + residuePart 2 n) := by
      unfold fullSum
      refine tsum_congr (fun n : ℕ => ?_)
      have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
      have hm : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      rcases hm with h0 | h1 | h2
      · simp [residuePart, h0]
      · simp [residuePart, h1]
      · simp [residuePart, h2]
    _ = (∑' n : ℕ, residuePart 0 n) +
        (∑' n : ℕ, residuePart 1 n) +
        (∑' n : ℕ, residuePart 2 n) := by
      have h01 := (hr 0).hasSum.add (hr 1).hasSum
      have h012 := h01.add (hr 2).hasSum
      exact h012.tsum_eq

theorem gap4 :
    fullSum =
      (1 + (1 / 2 : ℝ) * Real.cos (2 * Real.pi / 3) +
        (1 / 2 ^ 2 : ℝ) * Real.cos (Real.pi + Real.pi / 3)) *
      (∑' k : ℕ, (1 / 2 ^ 3 : ℝ) ^ k) := by
  have hs : Summable term := summable_term
  have hc : Real.cos (2 * Real.pi / 3) = (-1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_sub, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    norm_num
  have hrec (n : ℕ) :
      term (n + 2) =
        (-1 / 2 : ℝ) * term (n + 1) - (1 / 4 : ℝ) * term n := by
    let x : ℝ := 2 * (n : ℝ) * Real.pi / 3
    let a : ℝ := 2 * Real.pi / 3
    have hn0 : 2 * (n : ℝ) * Real.pi / 3 = x := by rfl
    have hn1 : 2 * ((n + 1 : ℕ) : ℝ) * Real.pi / 3 = x + a := by
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp [x, a]
      ring
    have hn2 : 2 * ((n + 2 : ℕ) : ℝ) * Real.pi / 3 = x + a + a := by
      simp only [Nat.cast_add, Nat.cast_ofNat]
      dsimp [x, a]
      ring
    have hca : Real.cos a = (-1 / 2 : ℝ) := by
      simpa [a] using hc
    have htrig :
        Real.cos (x + a + a) = -Real.cos (x + a) - Real.cos x := by
      simp only [Real.cos_add, Real.sin_add, hca]
      have hu := Real.sin_sq_add_cos_sq a
      rw [hca] at hu
      have hsqa : Real.sin a ^ 2 = (3 / 4 : ℝ) := by
        nlinarith [hu]
      ring_nf
      rw [hsqa]
      ring
    unfold term
    rw [hn2, hn1, hn0, htrig]
    simp only [pow_add]
    norm_num
    ring
  have hs1 : Summable (fun n : ℕ => term (n + 1)) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => |term (n + 1)|) gap1 ?_
    intro n
    simpa only [Real.norm_eq_abs] using
      (le_rfl : |term (n + 1)| ≤ |term (n + 1)|)
  have hsumrec :
      (∑' n : ℕ, term (n + 2)) =
        (-1 / 2 : ℝ) * (∑' n : ℕ, term (n + 1)) -
          (1 / 4 : ℝ) * (∑' n : ℕ, term n) := by
    calc
      (∑' n : ℕ, term (n + 2)) =
          ∑' n : ℕ,
            ((-1 / 2 : ℝ) * term (n + 1) - (1 / 4 : ℝ) * term n) := by
        refine tsum_congr (fun n : ℕ => hrec n)
      _ = (-1 / 2 : ℝ) * (∑' n : ℕ, term (n + 1)) -
          (1 / 4 : ℝ) * (∑' n : ℕ, term n) := by
        have hleft : HasSum
            (fun n : ℕ => (-1 / 2 : ℝ) * term (n + 1))
            ((-1 / 2 : ℝ) * (∑' n : ℕ, term (n + 1))) :=
          hs1.hasSum.mul_left (-1 / 2 : ℝ)
        have hright : HasSum
            (fun n : ℕ => (1 / 4 : ℝ) * term n)
            ((1 / 4 : ℝ) * (∑' n : ℕ, term n)) :=
          hs.hasSum.mul_left (1 / 4 : ℝ)
        exact (hleft.sub hright).tsum_eq
  have ht0 : term 0 = 1 := by
    norm_num [term]
  have ht1 : term 1 = (-1 / 4 : ℝ) := by
    norm_num [term, hc]
  have htail2 : (∑' n : ℕ, term (n + 2)) = fullSum - 3 / 4 := by
    have h : (term 0 + term 1) +
        (∑' n : ℕ, term (n + 2)) = fullSum := by
      simpa [fullSum, Finset.sum_range_succ] using
        (hs.sum_add_tsum_nat_add 2)
    rw [ht0, ht1] at h
    linarith
  have hfull : fullSum = 5 / 7 := by
    have h := hsumrec
    change (∑' n : ℕ, term (n + 2)) =
      (-1 / 2 : ℝ) * requestedSum - (1 / 4 : ℝ) * fullSum at h
    rw [htail2, gap2] at h
    linarith
  have hc2 :
      Real.cos (Real.pi + Real.pi / 3) = (-1 / 2 : ℝ) := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    norm_num
  have hg : HasSum (fun k : ℕ => (1 / 8 : ℝ) ^ k)
      ((1 - (1 / 8 : ℝ))⁻¹) :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have hgeom :
      (∑' k : ℕ, (1 / 2 ^ 3 : ℝ) ^ k) = 8 / 7 := by
    calc
      (∑' k : ℕ, (1 / 2 ^ 3 : ℝ) ^ k) =
          ∑' k : ℕ, (1 / 8 : ℝ) ^ k := by
        apply tsum_congr
        intro k
        norm_num
      _ = (1 - (1 / 8 : ℝ))⁻¹ := hg.tsum_eq
      _ = 8 / 7 := by norm_num
  rw [hfull, hc, hc2, hgeom]
  norm_num

theorem gap5 :
    (1 + (1 / 2 : ℝ) * Real.cos (2 * Real.pi / 3) +
        (1 / 2 ^ 2 : ℝ) * Real.cos (Real.pi + Real.pi / 3)) *
        (∑' k : ℕ, (1 / 2 ^ 3 : ℝ) ^ k) =
      (1 - 1 / 4 - 1 / 8 : ℝ) * (1 / (1 - 1 / 8)) := by
  have hc : Real.cos (2 * Real.pi / 3) = (-1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_sub, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    norm_num
  have hc2 :
      Real.cos (Real.pi + Real.pi / 3) = (-1 / 2 : ℝ) := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    norm_num
  have hg : HasSum (fun k : ℕ => (1 / 8 : ℝ) ^ k)
      ((1 - (1 / 8 : ℝ))⁻¹) :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have hgeom :
      (∑' k : ℕ, (1 / 2 ^ 3 : ℝ) ^ k) = 8 / 7 := by
    calc
      (∑' k : ℕ, (1 / 2 ^ 3 : ℝ) ^ k) =
          ∑' k : ℕ, (1 / 8 : ℝ) ^ k := by
        apply tsum_congr
        intro k
        norm_num
      _ = (1 - (1 / 8 : ℝ))⁻¹ := hg.tsum_eq
      _ = 8 / 7 := by norm_num
  rw [hc, hc2, hgeom]
  norm_num

theorem gap6 :
    (1 - 1 / 4 - 1 / 8 : ℝ) * (1 / (1 - 1 / 8)) = 5 / 7 := by
  norm_num

theorem gap7 :
    fullSum = 5 / 7 := by
  calc
    fullSum =
        (1 + (1 / 2 : ℝ) * Real.cos (2 * Real.pi / 3) +
          (1 / 2 ^ 2 : ℝ) * Real.cos (Real.pi + Real.pi / 3)) *
          (∑' k : ℕ, (1 / 2 ^ 3 : ℝ) ^ k) := gap4
    _ = (1 - 1 / 4 - 1 / 8 : ℝ) * (1 / (1 - 1 / 8)) := gap5
    _ = 5 / 7 := gap6

theorem gap8 :
    requestedSum = 5 / 7 - 1 := by
  rw [gap2, gap7]

theorem gap9 :
    (5 / 7 : ℝ) - 1 = -2 / 7 := by
  norm_num

theorem gap10 :
    requestedSum = -2 / 7 := by
  rw [gap8, gap9]

end

end ProofGap.Exercise2709
