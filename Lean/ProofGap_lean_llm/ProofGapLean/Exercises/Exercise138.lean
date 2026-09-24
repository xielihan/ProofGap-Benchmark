import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed

open Filter Topology

namespace ProofGap.Exercise138

noncomputable section

def partialSum (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, x i

def cesaro (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  partialSum x n / (n : ℝ)

def tailSum (x : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (N + 1) n, x i

private theorem Icc_eq_Ico_succ (a b : ℕ) :
    Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext i
  simp

private theorem partialSum_eq_sum_range_shift (x : ℕ → ℝ) (n : ℕ) :
    partialSum x n = ∑ i ∈ Finset.range n, x (i + 1) := by
  rw [partialSum, Icc_eq_Ico_succ,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm]

private theorem partialSum_add_tailSum (x : ℕ → ℝ) {N n : ℕ}
    (hN : N ≤ n) :
    partialSum x N + tailSum x N n = partialSum x n := by
  unfold partialSum tailSum
  rw [Icc_eq_Ico_succ, Icc_eq_Ico_succ, Icc_eq_Ico_succ]
  exact Finset.sum_Ico_consecutive x (by omega) (by omega)

/-- Source: `proof_gap/exercise_138/1.txt`; fix N and require N≤n. -/
theorem gap1 (x : ℕ → ℝ) :
    ∀ N n : ℕ, N ≤ n → 0 < n →
      cesaro x n =
        partialSum x N / (n : ℝ) +
          (partialSum x n - partialSum x N) / (n : ℝ) := by
  intro N n hN hn
  rw [cesaro]
  field_simp
  ring

/-- Source: `proof_gap/exercise_138/2.txt`; the tail ellipsis is a finite sum. -/
theorem gap2 (x : ℕ → ℝ) :
    ∀ N n : ℕ, N < n →
      partialSum x N / (n : ℝ) +
          (partialSum x n - partialSum x N) / (n : ℝ) =
        partialSum x N / (n : ℝ) +
          tailSum x N n / ((n : ℝ) - N) * (1 - (N : ℝ) / n) := by
  intro N n hN
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hden : (n : ℝ) - N ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hN.ne')
  have hdiff :
      partialSum x n - partialSum x N = tailSum x N n := by
    linarith [partialSum_add_tailSum x hN.le]
  rw [hdiff]
  field_simp [hn0, hden]
  <;> ring

/-- Source: `proof_gap/exercise_138/3.txt`. -/
theorem gap3 (x : ℕ → ℝ) :
    ∀ N n : ℕ, N < n →
      cesaro x n =
        partialSum x N / (n : ℝ) +
          tailSum x N n / ((n : ℝ) - N) * (1 - (N : ℝ) / n) := by
  intro N n hN
  calc
    cesaro x n =
        partialSum x N / (n : ℝ) +
          (partialSum x n - partialSum x N) / (n : ℝ) :=
      gap1 x N n hN.le (by omega)
    _ = partialSum x N / (n : ℝ) +
          tailSum x N n / ((n : ℝ) - N) *
            (1 - (N : ℝ) / n) :=
      gap2 x N n hN

/-- Source: `proof_gap/exercise_138/4.txt`. -/
theorem gap4 (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → |x n - a| < ε := by
  intro ε hε
  rcases (Metric.tendsto_atTop.1 hx) ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn => by
    simpa [Real.dist_eq] using hN n hn.le⟩

/-- Source: `proof_gap/exercise_138/5.txt`; N depends on ε and n>N. -/
theorem gap5 (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        tailSum x N n / ((n : ℝ) - N) ∈ Set.Ioo (a - ε) (a + ε) := by
  intro ε hε
  rcases gap4 x a hx ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hNn => ?_⟩
  have hsnonempty : (Finset.Icc (N + 1) n).Nonempty := by
    exact ⟨N + 1, by simp; omega⟩
  have hlo :
      ∑ i ∈ Finset.Icc (N + 1) n, (a - ε) <
        ∑ i ∈ Finset.Icc (N + 1) n, x i := by
    apply Finset.sum_lt_sum_of_nonempty hsnonempty
    intro i hi
    have hiN : N < i := by
      have hi' : N < i ∧ i ≤ n := by simpa using hi
      exact hi'.1
    linarith [(abs_lt.1 (hN i hiN)).1]
  have hhi :
      ∑ i ∈ Finset.Icc (N + 1) n, x i <
        ∑ i ∈ Finset.Icc (N + 1) n, (a + ε) := by
    apply Finset.sum_lt_sum_of_nonempty hsnonempty
    intro i hi
    have hiN : N < i := by
      have hi' : N < i ∧ i ≤ n := by simpa using hi
      exact hi'.1
    linarith [(abs_lt.1 (hN i hiN)).2]
  have hden : (0 : ℝ) < (n : ℝ) - N := by
    have : (N : ℝ) < n := by exact_mod_cast hNn
    linarith
  have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := by
    rw [Nat.cast_sub hNn.le]
  have hcard : (Finset.Icc (N + 1) n).card = n - N := by
    simp
  constructor
  · rw [lt_div_iff₀ hden]
    simp only [Finset.sum_const, nsmul_eq_mul] at hlo
    rw [hcard] at hlo
    rw [hcast] at hlo
    simpa [tailSum, mul_comm] using hlo
  · rw [div_lt_iff₀ hden]
    simp only [Finset.sum_const, nsmul_eq_mul] at hhi
    rw [hcard] at hhi
    rw [hcast] at hhi
    simpa [tailSum, mul_comm] using hhi

/-- Source: `proof_gap/exercise_138/6.txt`; the error depends on n and ε. -/
theorem gap6 (x : ℕ → ℝ) (a ε : ℝ) (N n : ℕ)
    (havg : tailSum x N n / ((n : ℝ) - N) ∈ Set.Ioo (a - ε) (a + ε)) :
    ∃ α : ℝ,
      tailSum x N n / ((n : ℝ) - N) = a + α ∧ |α| < ε := by
  refine ⟨tailSum x N n / ((n : ℝ) - N) - a, by ring, ?_⟩
  rcases havg with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

/-- Source: `proof_gap/exercise_138/7.txt`; α is pointwise. -/
theorem gap7 (x : ℕ → ℝ) (a α : ℝ) (N n : ℕ)
    (hN : N < n)
    (hα : tailSum x N n / ((n : ℝ) - N) = a + α) :
    cesaro x n =
      partialSum x N / (n : ℝ) + (a + α) * (1 - (N : ℝ) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hdiff :
      partialSum x n - partialSum x N = tailSum x N n := by
    linarith [partialSum_add_tailSum x hN.le]
  rw [cesaro, ← partialSum_add_tailSum x hN.le]
  have hden : (n : ℝ) - N ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hN.ne')
  have htail :
      tailSum x N n = (a + α) * ((n : ℝ) - N) :=
    (div_eq_iff hden).mp hα
  rw [htail]
  field_simp [hn0]

/-- Source: `proof_gap/exercise_138/8.txt`. -/
theorem gap8 (x : ℕ → ℝ) (a α : ℝ) (N n : ℕ)
    (hn : 0 < n)
    (hid : cesaro x n =
      partialSum x N / (n : ℝ) + (a + α) * (1 - (N : ℝ) / n)) :
    |cesaro x n - a| ≤
      |partialSum x N| / (n : ℝ) + |α| +
        (|a| + |α|) * (N : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hr0 : 0 ≤ (N : ℝ) / n := div_nonneg hNR hnR.le
  have hrewrite :
      cesaro x n - a =
        partialSum x N / (n : ℝ) + α -
          (a + α) * ((N : ℝ) / n) := by
    rw [hid]
    ring
  rw [hrewrite]
  calc
    |partialSum x N / (n : ℝ) + α -
        (a + α) * ((N : ℝ) / n)|
        ≤ |partialSum x N / (n : ℝ) + α| +
            |(a + α) * ((N : ℝ) / n)| := abs_sub _ _
    _ ≤ (|partialSum x N / (n : ℝ)| + |α|) +
            |(a + α) * ((N : ℝ) / n)| := by
          linarith [abs_add_le (partialSum x N / (n : ℝ)) α]
    _ = |partialSum x N| / (n : ℝ) + |α| +
          |a + α| * ((N : ℝ) / n) := by
        rw [abs_div, abs_of_pos hnR, abs_mul, abs_of_nonneg hr0]
    _ ≤ |partialSum x N| / (n : ℝ) + |α| +
          (|a| + |α|) * ((N : ℝ) / n) := by
        have hmul := mul_le_mul_of_nonneg_right (abs_add_le a α) hr0
        linarith
    _ = |partialSum x N| / (n : ℝ) + |α| +
          (|a| + |α|) * (N : ℝ) / n := by ring

/-- Source: `proof_gap/exercise_138/9.txt`; N' depends on ε and N. -/
theorem gap9 (x : ℕ → ℝ) (a ε : ℝ) (N : ℕ)
    (hε : 0 < ε) :
    ∃ N' : ℕ, N < N' ∧ ∀ n : ℕ, N' < n →
      |partialSum x N| / (n : ℝ) < ε ∧
      (N : ℝ) / n < ε / (|a| + ε) := by
  have hden : 0 < |a| + ε := by positivity
  have hrhs : 0 < ε / (|a| + ε) := div_pos hε hden
  have hfirst :
      Tendsto (fun n : ℕ => |partialSum x N| / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsecond :
      Tendsto (fun n : ℕ => (N : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hev1 : ∀ᶠ n : ℕ in atTop, |partialSum x N| / (n : ℝ) < ε :=
    (tendsto_order.1 hfirst).2 ε hε
  have hev2 : ∀ᶠ n : ℕ in atTop, (N : ℝ) / (n : ℝ) < ε / (|a| + ε) :=
    (tendsto_order.1 hsecond).2 _ hrhs
  rw [eventually_atTop] at hev1 hev2
  rcases hev1 with ⟨K₁, hK₁⟩
  rcases hev2 with ⟨K₂, hK₂⟩
  refine ⟨max (max K₁ K₂) N + 1, by omega, fun n hn => ?_⟩
  exact ⟨hK₁ n (by omega), hK₂ n (by omega)⟩

/-- Source: `proof_gap/exercise_138/10.txt`. -/
theorem gap10 (x : ℕ → ℝ) (a ε : ℝ)
    (hx : Tendsto x atTop (𝓝 a))
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → |cesaro x n - a| < 3 * ε := by
  rcases gap5 x a hx ε hε with ⟨N, htail⟩
  rcases gap9 x a ε N hε with ⟨N', hNN', hsmall⟩
  refine ⟨N', fun n hn => ?_⟩
  have hNn : N < n := hNN'.trans hn
  rcases gap6 x a ε N n (htail n hNn) with ⟨α, hα, hαlt⟩
  have hid := gap7 x a α N n hNn hα
  have hbound := gap8 x a α N n (by omega) hid
  rcases hsmall n hn with ⟨hfirst, hratio⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio0 : 0 ≤ (N : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg N) hnR.le
  have hden : 0 < |a| + ε := by positivity
  have hfactor : |a| + |α| ≤ |a| + ε := by
    linarith
  have hproduct :
      (|a| + |α|) * (N : ℝ) / n < ε := by
    have hle :
        (|a| + |α|) * ((N : ℝ) / n) ≤
          (|a| + ε) * ((N : ℝ) / n) :=
      mul_le_mul_of_nonneg_right hfactor hratio0
    have hlt :
        (|a| + ε) * ((N : ℝ) / n) < ε := by
      calc
        (|a| + ε) * ((N : ℝ) / n) =
            ((N : ℝ) / n) * (|a| + ε) := by ring
        _ < (ε / (|a| + ε)) * (|a| + ε) :=
          mul_lt_mul_of_pos_right hratio hden
        _ = ε := by field_simp
    exact (by simpa [mul_div_assoc] using hle.trans_lt hlt)
  linarith

/-- Source: `proof_gap/exercise_138/11.txt`; Cesàro convergence. -/
theorem gap11 (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (cesaro x) atTop (𝓝 a) := by
  have hshift :
      Tendsto (fun i : ℕ => x (i + 1)) atTop (𝓝 a) :=
    hx.comp (Filter.tendsto_add_atTop_nat 1)
  have hc := hshift.cesaro
  apply hc.congr'
  filter_upwards [Ici_mem_atTop 1] with n hn
  rw [cesaro, partialSum_eq_sum_range_shift]
  simp only [inv_mul_eq_div]

/-- Source: `proof_gap/exercise_138/12.txt`; express the common limit by Tendsto. -/
theorem gap12 (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (cesaro x) atTop (𝓝 a) ∧ Tendsto x atTop (𝓝 a) := by
  exact ⟨gap11 x a hx, hx⟩

/-- Source: `proof_gap/exercise_138/13.txt`. -/
theorem gap13 (x : ℕ → ℝ)
    (hx : ProofGap.ConvergentSeq x) :
    ProofGap.ConvergentSeq (cesaro x) := by
  rcases hx with ⟨a, ha⟩
  exact ⟨a, gap11 x a ha⟩

/-- Source: `proof_gap/exercise_138/14.txt`; the alternating example has convergent means. -/
theorem gap14 :
    ¬ ProofGap.ConvergentSeq (fun n : ℕ => (-1 : ℝ) ^ (n + 1)) ∧
      ProofGap.ConvergentSeq
        (cesaro (fun n : ℕ => (-1 : ℝ) ^ (n + 1))) := by
  let z : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 1)
  have heven : StrictMono (fun k : ℕ => 2 * k) := by
    intro i j hij
    exact (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hij
  have hodd : StrictMono (fun k : ℕ => 2 * k + 1) := by
    intro i j hij
    exact Nat.add_lt_add_right
      ((Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hij) 1
  have hzeven :
      Tendsto (z ∘ fun k : ℕ => 2 * k) atTop (𝓝 (-1)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    simp [z, Function.comp_def, pow_add, pow_mul]
  have hzodd :
      Tendsto (z ∘ fun k : ℕ => 2 * k + 1) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    simp [z, Function.comp_def, pow_add, pow_mul]
  have hz_not : ¬ ProofGap.ConvergentSeq z := by
    rintro ⟨l, hl⟩
    have hlneg := tendsto_nhds_unique
      (hl.comp heven.tendsto_atTop) hzeven
    have hlpos := tendsto_nhds_unique
      (hl.comp hodd.tendsto_atTop) hzodd
    norm_num [hlneg] at hlpos
  have hpartial (n : ℕ) :
      partialSum z n = ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i := by
    rw [partialSum_eq_sum_range_shift]
    apply Finset.sum_congr rfl
    intro i hi
    simp [z, pow_add]
  have hmean : Tendsto (cesaro z) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hone :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n : ℝ) < ε :=
      (tendsto_order.1 hone).2 ε hε
    rw [eventually_atTop] at hev
    rcases hev with ⟨K, hK⟩
    refine ⟨max K 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hnorm :
        |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i| ≤ 1 := by
      simpa [Real.norm_eq_abs] using norm_sum_neg_one_pow_le n
    rw [Real.dist_eq, sub_zero, cesaro, hpartial, abs_div,
      abs_of_pos (by exact_mod_cast hn0 : (0 : ℝ) < n)]
    exact (div_le_div_of_nonneg_right hnorm (by positivity)).trans_lt
      (hK n (by omega))
  exact ⟨by simpa [z] using hz_not, ⟨0, by simpa [z] using hmean⟩⟩

/-- Source: `proof_gap/exercise_138/15.txt`; retain the original convergent-sequence case. -/
theorem gap15 (x : ℕ → ℝ) (a : ℝ)
    (hx : Tendsto x atTop (𝓝 a)) :
    ProofGap.ConvergentSeq (cesaro x) ∧
      Tendsto (cesaro x) atTop (𝓝 a) ∧ Tendsto x atTop (𝓝 a) := by
  exact ⟨⟨a, gap11 x a hx⟩, gap11 x a hx, hx⟩

end

end ProofGap.Exercise138
