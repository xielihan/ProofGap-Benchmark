import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise611

noncomputable section

def binomialSeq (x : ℝ) (n : ℕ) : ℝ := (1 + x / n) ^ n
def y (x : ℝ) (n : ℕ) : ℝ := n / x
def transformed (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / y x n) (y x n * x)
def partialExp (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum (fun k => x ^ k / (k.factorial : ℝ))
def binomialExpansion (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum (fun k =>
    (n.choose k : ℝ) * (x / n) ^ k)
def truncatedBinomial (x : ℝ) (m n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum (fun k =>
    (m.choose k : ℝ) * (x / m) ^ k)
def convolution (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum (fun i =>
    (Finset.range (n + 1)).sum (fun j =>
      x ^ i / (i.factorial : ℝ) * ((-x) ^ j / (j.factorial : ℝ))))

private theorem partialExp_tendsto (x : ℝ) :
    Filter.Tendsto (partialExp x) Filter.atTop (nhds (Real.exp x)) := by
  have hs :=
    (NormedSpace.expSeries_div_hasSum_exp (x : ℝ)).tendsto_sum_nat
  have hs' := hs.comp (Filter.tendsto_add_atTop_nat 1)
  change Filter.Tendsto
    (fun n : ℕ => (Finset.range (n + 1)).sum
      (fun k => x ^ k / (k.factorial : ℝ)))
    Filter.atTop (nhds (Real.exp x))
  simpa only [Function.comp_apply, Real.exp_eq_exp_ℝ] using hs'

private theorem binomialSeq_tendsto (x : ℝ) :
    Filter.Tendsto (binomialSeq x) Filter.atTop (nhds (Real.exp x)) := by
  unfold binomialSeq
  simpa using Real.tendsto_one_add_div_pow_exp x

private theorem transformed_eventuallyEq (x : ℝ) (hx : x ≠ 0) :
    binomialSeq x =ᶠ[Filter.atTop] transformed x := by
  obtain ⟨N : ℕ, hN : |x| < N⟩ := exists_nat_gt |x|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hnabs : |x| < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast hn)
  have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt (abs_nonneg x) hnabs
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have harg :
      1 + 1 / y x n = 1 + x / (n : ℝ) := by
    unfold y
    field_simp [hx, hn0]
  have hexp : y x n * x = (n : ℝ) := by
    unfold y
    field_simp [hx]
  have hbase : 0 ≤ 1 + x / (n : ℝ) := by
    have hneg : -x ≤ |x| := neg_le_abs x
    have : -x < (n : ℝ) := hneg.trans_lt hnabs
    have : -1 < x / (n : ℝ) := by
      apply (lt_div_iff₀ hnpos).2
      nlinarith
    linarith
  unfold binomialSeq transformed
  rw [harg, hexp]
  exact (Real.rpow_natCast _ n).symm

private theorem partialExp_monotone {x : ℝ} (hx : 0 ≤ x) :
    Monotone (partialExp x) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold partialExp
  conv_rhs => rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right
    (div_nonneg (pow_nonneg hx _) (by positivity))

/-- Source: `proof_gap/exercise_611/1.txt`. -/
theorem gap1 (x : ℝ) (hx : x = 0) :
    Filter.Tendsto (binomialSeq x) Filter.atTop (nhds (Real.exp x)) := by
  exact binomialSeq_tendsto x

/-- Source: `proof_gap/exercise_611/2.txt`; define `y(n)=n/x`. -/
theorem gap2 (x : ℝ) (hx : x ≠ 0) (L : ℝ) :
    Filter.Tendsto (binomialSeq x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (transformed x) Filter.atTop (nhds L) := by
  exact ⟨fun h => h.congr' (transformed_eventuallyEq x hx),
    fun h => h.congr' (transformed_eventuallyEq x hx).symm⟩

/-- Source: `proof_gap/exercise_611/3.txt`. -/
theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (transformed x) Filter.atTop (nhds (Real.exp x)) := by
  exact (binomialSeq_tendsto x).congr' (transformed_eventuallyEq x hx)

/-- Source: `proof_gap/exercise_611/4.txt`. -/
theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (binomialSeq x) Filter.atTop (nhds (Real.exp x)) := by
  exact binomialSeq_tendsto x

/-- Source: `proof_gap/exercise_611/5.txt`. -/
theorem gap5 (x : ℝ) (hx : x = 0) :
    Filter.Tendsto (partialExp x) Filter.atTop (nhds (Real.exp x)) := by
  exact partialExp_tendsto x

/-- Source: `proof_gap/exercise_611/6.txt`; replace the coefficient ellipsis by the binomial sum. -/
theorem gap6 (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 0 < n) :
    binomialSeq x n = binomialExpansion x n := by
  unfold binomialSeq binomialExpansion
  rw [add_comm]
  simp [add_pow, mul_comm]

/-- Source: `proof_gap/exercise_611/7.txt`; compare the explicit finite sums. -/
theorem gap7 (x : ℝ) (n : ℕ) (hx : 0 < x) :
    binomialExpansion x n ≤ partialExp x n := by
  by_cases hn : n = 0
  · subst n
    norm_num [binomialExpansion, partialExp]
  · have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    unfold binomialExpansion partialExp
    apply Finset.sum_le_sum
    intro k hk
    have hchoose :
        (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) :=
      Nat.choose_le_pow_div k n
    have hpow : 0 ≤ (x / (n : ℝ)) ^ k := by positivity
    calc
      (n.choose k : ℝ) * (x / (n : ℝ)) ^ k ≤
          ((n : ℝ) ^ k / (k.factorial : ℝ)) *
            (x / (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right hchoose hpow
      _ = x ^ k / (k.factorial : ℝ) := by
        rw [div_pow]
        field_simp [hnR]

/-- Source: `proof_gap/exercise_611/8.txt`. -/
theorem gap8 (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 0 < n) :
    binomialSeq x n ≤ partialExp x n := by
  rw [gap6 x n hx hn]
  exact gap7 x n hx

/-- Source: `proof_gap/exercise_611/9.txt`; replace the truncated ellipsis by `truncatedBinomial`. -/
theorem gap9 (x : ℝ) (m n : ℕ) (hx : 0 < x) (hmn : n < m) :
    truncatedBinomial x m n < binomialSeq x m := by
  rw [gap6 x m hx (by omega)]
  let f : ℕ → ℝ := fun k => (m.choose k : ℝ) * (x / m) ^ k
  have hsplit := Finset.sum_range_add_sum_Ico f
    (show n + 1 ≤ m + 1 by omega)
  have htail :
      0 < ∑ k ∈ Finset.Ico (n + 1) (m + 1), f k := by
    apply Finset.sum_pos
    · intro k hk
      have hkm : k ≤ m := by
        have := (Finset.mem_Ico.mp hk).2
        omega
      have hchoose : 0 < (m.choose k : ℝ) := by
        exact_mod_cast Nat.choose_pos hkm
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      exact mul_pos hchoose (pow_pos (div_pos hx hmpos) _)
    · exact ⟨n + 1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  unfold truncatedBinomial binomialExpansion
  change (∑ k ∈ Finset.range (n + 1), f k) <
    ∑ k ∈ Finset.range (m + 1), f k
  linarith

/-- Source: `proof_gap/exercise_611/10.txt`. -/
theorem gap10 (x : ℝ) (n : ℕ) (hx : 0 < x) :
    partialExp x n ≤ Real.exp x := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (partialExp_tendsto x)
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact partialExp_monotone hx.le hm

/-- Source: `proof_gap/exercise_611/11.txt`. -/
theorem gap11 (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (partialExp x) Filter.atTop (nhds (Real.exp x)) := by
  exact partialExp_tendsto x

/-- Source: `proof_gap/exercise_611/12.txt`; replace the false two-term remainder identity by the exact finite Cauchy product. -/
theorem gap12 (x : ℝ) (n : ℕ) (hx : x < 0) :
    partialExp x n * partialExp (-x) n = convolution x n := by
  unfold partialExp convolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- Source: `proof_gap/exercise_611/13.txt`. -/
theorem gap13 (x : ℝ) (hx : x < 0) :
    Filter.Tendsto (fun n : ℕ => x ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp (x : ℝ)).summable
  have hz := hs.tendsto_atTop_zero
  simpa only [Real.exp_eq_exp_ℝ] using hz

/-- Source: `proof_gap/exercise_611/14.txt`. -/
theorem gap14 (x : ℝ) (hx : x < 0) :
    Filter.Tendsto (partialExp x) Filter.atTop (nhds (Real.exp x)) := by
  exact partialExp_tendsto x

/-- Source: `proof_gap/exercise_611/15.txt`. -/
theorem gap15 (x : ℝ) :
    Filter.Tendsto (binomialSeq x) Filter.atTop (nhds (Real.exp x)) ∧
      Filter.Tendsto (partialExp x) Filter.atTop (nhds (Real.exp x)) := by
  exact ⟨binomialSeq_tendsto x, partialExp_tendsto x⟩

end

end ProofGap.Exercise611
