import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise429

noncomputable section

def average (n : ℕ) (x a : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    (Finset.Icc 1 (n - 1)).sum (fun i => x + (i : ℝ) * a / n)
def expanded (n : ℕ) (x a : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    (((n - 1 : ℕ) : ℝ) * x +
      a / n * (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ)))
def closed (n : ℕ) (x a : ℝ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) / n * (x + a / 2)

/-- Exercise 429, gap 1; replace both summation ellipses by finite sums. -/
private theorem sum_range_natCast (n : ℕ) :
    (Finset.range n).sum (fun i => (i : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_succ]
      ring

private theorem sum_Icc_natCast (n : ℕ) :
    (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  calc
    (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ)) =
        (Finset.range n).sum (fun i => (i : ℝ)) := by
      apply Finset.sum_subset
      · intro i hi
        have hiBounds := Finset.mem_Icc.mp hi
        exact Finset.mem_range.mpr (by omega)
      · intro i hiRange hiNotIcc
        have hin : i < n := Finset.mem_range.mp hiRange
        have hi0 : i = 0 := by
          by_contra hne
          apply hiNotIcc
          exact Finset.mem_Icc.mpr
            ⟨Nat.one_le_iff_ne_zero.mpr hne, by omega⟩
        subst i
        norm_num
    _ = (n : ℝ) * ((n : ℝ) - 1) / 2 := sum_range_natCast n

private theorem average_eq_expanded (n : ℕ) (x a : ℝ) :
    average n x a = expanded n x a := by
  unfold average expanded
  apply congrArg (fun t : ℝ => (1 / (n : ℝ)) * t)
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by
    rw [Nat.card_Icc]
    omega
  have hsum :
      (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ) * a / n) =
        a / n * (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [Finset.sum_add_distrib, hsum]
  simp only [Finset.sum_const, hcard, nsmul_eq_mul]

private theorem expanded_eq_closed (n : ℕ) (x a : ℝ) :
    expanded n x a = closed n x a := by
  unfold expanded closed
  rw [sum_Icc_natCast]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [Nat.cast_sub hn1]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp [hn0]
    ring

private theorem closed_tendsto (x a : ℝ) :
    Filter.Tendsto (fun n => closed n x a) Filter.atTop
      (nhds (x + a / 2)) := by
  have hnat :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hone :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hc :
      Filter.Tendsto (fun _ : ℕ => x + a / 2) Filter.atTop
        (nhds (x + a / 2)) :=
    tendsto_const_nhds
  have hmodel :
      Filter.Tendsto
        (fun n : ℕ => (1 - (n : ℝ)⁻¹) * (x + a / 2))
        Filter.atTop (nhds (x + a / 2)) := by
    simpa using (hone.sub hinv).mul hc
  have heq :
      (fun n : ℕ => closed n x a) =ᶠ[Filter.atTop]
        (fun n : ℕ => (1 - (n : ℝ)⁻¹) * (x + a / 2)) := by
    refine Filter.eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    change
      ((n - 1 : ℕ) : ℝ) / (n : ℝ) * (x + a / 2) =
        (1 - (n : ℝ)⁻¹) * (x + a / 2)
    rw [Nat.cast_sub hn]
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
    field_simp [hn0]
    ring
  exact (Filter.tendsto_congr' heq).2 hmodel

theorem gap1 (x a : ℝ) :
    Filter.Tendsto (fun n => average n x a) Filter.atTop (nhds (x + a / 2)) ↔
      Filter.Tendsto (fun n => expanded n x a) Filter.atTop (nhds (x + a / 2)) := by
  constructor <;> intro h
  · simpa only [average_eq_expanded] using h
  · simpa only [average_eq_expanded] using h

/-- Exercise 429, gap 2. -/
theorem gap2 (x a : ℝ) :
    Filter.Tendsto (fun n => expanded n x a) Filter.atTop (nhds (x + a / 2)) ↔
      Filter.Tendsto (fun n => closed n x a) Filter.atTop (nhds (x + a / 2)) := by
  constructor <;> intro h
  · simpa only [expanded_eq_closed] using h
  · simpa only [expanded_eq_closed] using h

/-- Exercise 429, gap 3. -/
theorem gap3 (x a : ℝ) :
    Filter.Tendsto (fun n => closed n x a) Filter.atTop (nhds (x + a / 2)) := by
  exact closed_tendsto x a

/-- Exercise 429, gap 4. -/
theorem gap4 (x a : ℝ) :
    Filter.Tendsto (fun n => average n x a) Filter.atTop (nhds (x + a / 2)) := by
  apply (gap1 x a).2
  apply (gap2 x a).2
  exact gap3 x a

end

end ProofGap.Exercise429
