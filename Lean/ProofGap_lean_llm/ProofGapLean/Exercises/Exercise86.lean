import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace ProofGap.Exercise86

noncomputable section

def variation (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 n, |x k - x (k - 1)|

def variationTail (x : ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (n + 1) m, |x k - x (k - 1)|

def differenceTail (x : ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (n + 1) m, (x k - x (k - 1))

def HasBoundedVariation (x : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, 2 ≤ n → variation x n < c

def IsCauchy (u : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m → |u m - u n| < ε

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

def z (n : ℕ) : ℝ :=
  if Even n then -1 / (n / 2 : ℝ) else 1 / ((n + 1) / 2 : ℝ)

def omega (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ)

private theorem convergent_isCauchy {u : ℕ → ℝ} (h : Convergent u) :
    IsCauchy u := by
  rcases h with ⟨l, hl⟩
  have hc : CauchySeq u := hl.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  intro ε hε
  rcases hc ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m n hn hnm
  have hd := hN m (by omega) n (by omega)
  simpa [Real.dist_eq] using hd

private theorem isCauchy_convergent {u : ℕ → ℝ} (h : IsCauchy u) :
    Convergent u := by
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N + 1, ?_⟩
    intro m hm n hn
    by_cases hmn : m = n
    · subst m
      simpa using hε
    · rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have htail := hN n m (by omega) hlt
        simpa [Real.dist_eq, abs_sub_comm] using htail
      · have htail := hN m n (by omega) hgt
        simpa [Real.dist_eq] using htail
  exact cauchySeq_tendsto_of_complete hcauchy

private theorem variation_monotone (x : ℕ → ℝ) : Monotone (variation x) := by
  intro n m hnm
  unfold variation
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 hnm⟩
  · intro k hk hnot
    positivity

/-- Source: `proof_gap/exercise_86/1.txt`; y is the variation sequence of x. -/
theorem gap1 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x → Monotone (variation x) := by
  intro x _
  exact variation_monotone x

/-- Source: `proof_gap/exercise_86/2.txt`; y is the variation sequence of x. -/
theorem gap2 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x →
      Bornology.IsBounded (Set.range (variation x)) := by
  intro x hx
  rcases hx with ⟨c, hc⟩
  have hcpos : 0 < c := by
    have := hc 2 (by omega)
    have hnonneg : 0 ≤ variation x 2 := by
      unfold variation
      exact Finset.sum_nonneg fun k hk => abs_nonneg _
    linarith
  apply isBounded_iff_bddBelow_bddAbove.mpr
  constructor
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    unfold variation
    exact Finset.sum_nonneg fun k hk => abs_nonneg _
  · refine ⟨c, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    by_cases hn : 2 ≤ n
    · exact (hc n hn).le
    · have : variation x n = 0 := by
        unfold variation
        simp [Finset.Icc_eq_empty (by omega)]
      rw [this]
      exact hcpos.le

/-- Source: `proof_gap/exercise_86/3.txt`. -/
theorem gap3 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x → Convergent (variation x) := by
  intro x hx
  have hmono := gap1 x hx
  have hbound := (gap2 x hx).bddAbove
  have himage : variation x '' Set.Ici 0 = Set.range (variation x) := by
    ext y
    constructor
    · rintro ⟨n, _, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, Nat.zero_le n, rfl⟩
  have hbound' : BddAbove (variation x '' Set.Ici 0) := by rwa [himage]
  refine ⟨sSup (Set.range (variation x)), ?_⟩
  have ht := Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
    (k := 0) (hmono.monotoneOn (Set.Ici 0)) hbound'
  rwa [himage] at ht

/-- Source: `proof_gap/exercise_86/4.txt`. -/
theorem gap4 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x →
      IsCauchy (variation x) := by
  intro x hx
  exact convergent_isCauchy (gap3 x hx)

/-- Source: `proof_gap/exercise_86/5.txt`; remove irrelevant N and ε binders. -/
theorem gap5 :
    ∀ x : ℕ → ℝ, ∀ m n : ℕ, n < m →
      |x m - x n| = |differenceTail x n m| := by
  intro x m n hnm
  congr 1
  unfold differenceTail
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : m + 1 - (n + 1) = m - n := by omega
  rw [hlen]
  have htel := Finset.sum_range_sub (fun j : ℕ => x (n + j)) (m - n)
  convert htel.symm using 1
  · have hadd : n + (m - n) = m := by omega
    rw [hadd]
    norm_num
  · apply Finset.sum_congr rfl
    intro j hj
    congr 2 <;> omega

/-- Source: `proof_gap/exercise_86/6.txt`; remove irrelevant N and ε binders. -/
theorem gap6 :
    ∀ x : ℕ → ℝ, ∀ m n : ℕ, n < m →
      |differenceTail x n m| ≤ variationTail x n m := by
  intro x m n hnm
  unfold differenceTail variationTail
  exact Finset.abs_sum_le_sum_abs _ _

private theorem variationTail_eq_abs
    (x : ℕ → ℝ) (m n : ℕ) (hn : 1 ≤ n) (hnm : n < m) :
    variationTail x n m = |variation x m - variation x n| := by
  have hmono := variation_monotone x
  have hdiff : 0 ≤ variation x m - variation x n :=
    sub_nonneg.mpr (hmono (le_of_lt hnm))
  rw [abs_of_nonneg hdiff]
  unfold variationTail variation
  simp_rw [← Finset.Ico_add_one_right_eq_Icc]
  have hconsecutive := Finset.sum_Ico_consecutive
    (fun k => |x k - x (k - 1)|)
    (show 2 ≤ n + 1 by omega) (show n + 1 ≤ m + 1 by omega)
  linarith

/-- Source: `proof_gap/exercise_86/7.txt`; y is explicitly variation x. -/
theorem gap7 :
    ∀ x : ℕ → ℝ, ∀ m n : ℕ, 1 ≤ n → n < m →
      variationTail x n m = |variation x m - variation x n| := by
  intro x m n hn hnm
  exact variationTail_eq_abs x m n hn hnm

/-- Source: `proof_gap/exercise_86/8.txt`; the Cauchy cutoff depends on ε. -/
theorem gap8 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m →
          |variation x m - variation x n| < ε := by
  intro x hx
  exact gap4 x hx

/-- Source: `proof_gap/exercise_86/9.txt`; the Cauchy cutoff depends on ε. -/
theorem gap9 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m →
          |x m - x n| < ε := by
  intro x hx ε hε
  rcases gap8 x hx ε hε with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro m n hn hnm
  calc
    |x m - x n| = |differenceTail x n m| := gap5 x m n hnm
    _ ≤ variationTail x n m := gap6 x m n hnm
    _ = |variation x m - variation x n| :=
      variationTail_eq_abs x m n (by omega) hnm
    _ < ε := hN m n (by omega) hnm

/-- Source: `proof_gap/exercise_86/10.txt`. -/
theorem gap10 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x → IsCauchy x := by
  intro x hx
  exact gap9 x hx

/-- Source: `proof_gap/exercise_86/11.txt`. -/
theorem gap11 :
    ∀ x : ℕ → ℝ, HasBoundedVariation x → Convergent x := by
  intro x hx
  exact isCauchy_convergent (gap10 x hx)

/-- Source: `proof_gap/exercise_86/12.txt`; the alternating counterexample is explicit. -/
theorem gap12 :
    Tendsto z atTop (𝓝 0) := by
  have hmajorant :
      Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply (tendsto_zero_iff_abs_tendsto_zero z).mpr
  apply squeeze_zero'
  · filter_upwards [] with n
    exact abs_nonneg (z n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    change |z n| ≤ 2 / (n : ℝ)
    rcases Nat.even_or_odd n with heven | hodd
    · rcases heven with ⟨k, rfl⟩
      have hk : 0 < k := by omega
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      simp [z]
      have hneg : -1 / (k : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num) hkR.le
      rw [abs_of_nonpos hneg]
      field_simp
      norm_num
    · rcases hodd with ⟨k, rfl⟩
      simp [z]
      have hd1 : 0 < (2 : ℝ) * k + 1 + 1 := by positivity
      have hd2 : 0 < (2 : ℝ) * k + 1 := by positivity
      rw [abs_of_pos (div_pos (by norm_num) hd1)]
      rw [div_le_div_iff₀ hd1 hd2]
      nlinarith
  · exact hmajorant

/-- Source: `proof_gap/exercise_86/13.txt`. -/
theorem gap13 :
    ¬ Convergent omega := by
  have homega : Tendsto omega atTop atTop := by
    have hbase := Real.tendsto_sum_range_one_div_nat_succ_atTop
    apply hbase.congr'
    filter_upwards [] with n
    unfold omega
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  intro hconv
  rcases hconv with ⟨l, hl⟩
  have hhigh : ∀ᶠ n : ℕ in atTop, l + 1 ≤ omega n :=
    (tendsto_atTop.1 homega (l + 1))
  have hlow : ∀ᶠ n : ℕ in atTop, omega n < l + 1 :=
    hl.eventually (Iio_mem_nhds (by linarith))
  rcases (hhigh.and hlow).exists with ⟨n, hn1, hn2⟩
  linarith

/-- Source: `proof_gap/exercise_86/14.txt`. -/
theorem gap14 :
    Monotone omega := by
  intro n m hnm
  unfold omega
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 hnm⟩
  · intro k hk hnot
    positivity

/-- Source: `proof_gap/exercise_86/15.txt`; strictness requires n>1. -/
theorem gap15 :
    ∀ n : ℕ, 1 < n →
      variation z (2 * n) >
        ∑ k ∈ Finset.Icc 1 n, |z (2 * k) - z (2 * k - 1)| := by
  intro n hn
  let s : Finset ℕ := (Finset.Icc 1 n).image (fun k => 2 * k)
  have hsubset : s ⊆ Finset.Icc 2 (2 * n) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
    have hki := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum :
      (∑ i ∈ s, |z i - z (i - 1)|) =
        ∑ k ∈ Finset.Icc 1 n, |z (2 * k) - z (2 * k - 1)| := by
    unfold s
    rw [Finset.sum_image]
    intro a ha b hb hab
    dsimp at hab
    omega
  have hthree : 3 ∈ Finset.Icc 2 (2 * n) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hthree_not : 3 ∉ s := by
    intro h
    rcases Finset.mem_image.mp h with ⟨k, hk, hkeq⟩
    omega
  have hthree_pos : 0 < |z 3 - z (3 - 1)| := by
    norm_num [z, show ¬Even 3 by decide, show Even 2 by decide]
  have hstrict :
      (∑ i ∈ s, |z i - z (i - 1)|) <
        ∑ i ∈ Finset.Icc 2 (2 * n), |z i - z (i - 1)| :=
    Finset.sum_lt_sum_of_subset hsubset hthree hthree_not hthree_pos
      (fun i hi hnot => abs_nonneg _)
  rw [← hsum]
  unfold variation
  exact hstrict

/-- Source: `proof_gap/exercise_86/16.txt`; n>0 is restored. -/
theorem gap16 :
    ∀ n : ℕ, 0 < n →
      (∑ k ∈ Finset.Icc 1 n, |z (2 * k) - z (2 * k - 1)|) =
        2 * omega n := by
  intro n hn
  unfold omega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have heven : Even (2 * k) := by exact ⟨k, by omega⟩
  have hodd : ¬Even (2 * k - 1) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hkpos)
    simp [Nat.mul_add]
  simp [z, heven, hodd, hkpos, Nat.mul_div_cancel_left]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  rw [abs_of_nonpos]
  · field_simp
    ring
  · have : 0 < (k : ℝ)⁻¹ := inv_pos.mpr hkR
    have hneg : -1 / (k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) hkR.le
    linarith

private theorem evenJumps_le_variation (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, |z (2 * k) - z (2 * k - 1)|) ≤
      variation z (2 * n) := by
  let s : Finset ℕ := (Finset.Icc 1 n).image (fun k => 2 * k)
  have hsubset : s ⊆ Finset.Icc 2 (2 * n) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
    have hki := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum :
      (∑ i ∈ s, |z i - z (i - 1)|) =
        ∑ k ∈ Finset.Icc 1 n, |z (2 * k) - z (2 * k - 1)| := by
    unfold s
    rw [Finset.sum_image]
    intro a ha b hb hab
    dsimp at hab
    omega
  rw [← hsum]
  unfold variation
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro i hi hnot
  exact abs_nonneg _

/-- Source: `proof_gap/exercise_86/17.txt`; strictness requires n>1. -/
theorem gap17 :
    ∀ n : ℕ, 1 < n → variation z (2 * n) > 2 * omega n := by
  intro n hn
  rw [← gap16 n (by omega)]
  exact gap15 n hn

/-- Source: `proof_gap/exercise_86/18.txt`. -/
theorem gap18 :
    ¬ HasBoundedVariation z := by
  intro hz
  rcases hz with ⟨c, hc⟩
  have homega : Tendsto omega atTop atTop := by
    have hbase := Real.tendsto_sum_range_one_div_nat_succ_atTop
    apply hbase.congr'
    filter_upwards [] with n
    unfold omega
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have hlarge : ∀ᶠ n : ℕ in atTop, c / 2 + 1 ≤ omega n :=
    tendsto_atTop.1 homega (c / 2 + 1)
  rcases (hlarge.and (eventually_ge_atTop 1)).exists with ⟨n, hnlarge, hn⟩
  have hnpos : 0 < n := by omega
  have hvar := hc (2 * n) (by omega)
  have hjump : 2 * omega n ≤ variation z (2 * n) := by
    rw [← gap16 n hnpos]
    exact evenJumps_le_variation n
  nlinarith

/-- Source: `proof_gap/exercise_86/19.txt`. -/
theorem gap19 :
    (∀ x : ℕ → ℝ, HasBoundedVariation x → Convergent x) ∧
      (∃ z₀ : ℕ → ℝ, Tendsto z₀ atTop (𝓝 0) ∧
        ¬ HasBoundedVariation z₀) := by
  exact ⟨gap11, ⟨z, gap12, gap18⟩⟩

end

end ProofGap.Exercise86
