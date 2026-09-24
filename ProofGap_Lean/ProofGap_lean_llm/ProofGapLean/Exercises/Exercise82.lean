import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace ProofGap.Exercise82

noncomputable section

def x (a : ℕ → ℝ) (q : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), a i * q ^ i

def tail (a : ℕ → ℝ) (q : ℝ) (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (n + 1) m, a i * q ^ i

def absTail (a : ℕ → ℝ) (q : ℝ) (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (n + 1) m, |a i| * |q| ^ i

def geometricTail (q : ℝ) (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m - n), |q| ^ j

def IsCauchy (u : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m → |u m - u n| < ε

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/-- Exercise 82, gap 1; the tail ellipsis is a finite sum. -/
theorem gap1 (a : ℕ → ℝ) (q : ℝ) :
    ∀ m n : ℕ, n < m →
      |x a q m - x a q n| = |tail a q n m| := by
  intro m n hnm
  congr 1
  unfold x tail
  rw [← Finset.Ico_add_one_right_eq_Icc]
  exact (Finset.sum_Ico_eq_sub (fun i => a i * q ^ i) (by omega)).symm

/-- Exercise 82, gap 2; the absolute tail is explicit. -/
theorem gap2 (a : ℕ → ℝ) (q : ℝ) :
    ∀ m n : ℕ, n < m →
      |x a q m - x a q n| ≤ absTail a q n m := by
  intro m n hnm
  rw [gap1 a q m n hnm]
  unfold tail absTail
  calc
    |∑ i ∈ Finset.Icc (n + 1) m, a i * q ^ i| ≤
        ∑ i ∈ Finset.Icc (n + 1) m, |a i * q ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.Icc (n + 1) m, |a i| * |q| ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_pow]

/-- Exercise 82, gap 3; the geometric sum is explicit. -/
theorem gap3
    (a : ℕ → ℝ) (q M : ℝ)
    (ha : ∀ i : ℕ, |a i| < M)
    (hq0 : q ≠ 0) :
    ∀ m n : ℕ, n < m →
      |x a q m - x a q n| <
        M * |q| ^ (n + 1) * geometricTail q n m := by
  intro m n hnm
  have hrpos : 0 < |q| := abs_pos.mpr hq0
  have htail :
      absTail a q n m <
        M * |q| ^ (n + 1) * geometricTail q n m := by
    unfold absTail geometricTail
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : m + 1 - (n + 1) = m - n := by omega
    rw [hlen, Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨0, by simp; omega⟩
    · intro j hj
      rw [pow_add]
      have hp : 0 < |q| ^ (n + 1) * |q| ^ j :=
        mul_pos (pow_pos hrpos _) (pow_pos hrpos _)
      calc
        |a (n + 1 + j)| * (|q| ^ (n + 1) * |q| ^ j) <
            M * (|q| ^ (n + 1) * |q| ^ j) :=
          mul_lt_mul_of_pos_right (ha (n + 1 + j)) hp
        _ = (M * |q| ^ (n + 1)) * |q| ^ j := by ring
  exact (gap2 a q m n hnm).trans_lt htail

/-- Exercise 82, gap 4; q=0 is excluded from the strict bound. -/
theorem gap4
    (q M : ℝ)
    (hM : 0 < M) (hq0 : q ≠ 0) (hq : |q| < 1) :
    ∀ m n : ℕ, n < m →
      M * |q| ^ (n + 1) * geometricTail q n m <
        M * |q| ^ (n + 1) * (1 / (1 - |q|)) := by
  intro m n hnm
  have hrpos : 0 < |q| := abs_pos.mpr hq0
  have hden : 0 < 1 - |q| := sub_pos.mpr hq
  have hkpos : 0 < m - n := by omega
  have hsum :
      geometricTail q n m =
        (1 - |q| ^ (m - n)) / (1 - |q|) := by
    unfold geometricTail
    simpa using
      (geom_sum_Ico' (x := |q|) (m := 0) (n := m - n)
        (by linarith) (by omega))
  have hgeom :
      geometricTail q n m < 1 / (1 - |q|) := by
    rw [hsum, div_lt_div_iff_of_pos_right hden]
    have hp : 0 < |q| ^ (m - n) := pow_pos hrpos _
    linarith
  have hcoef : 0 < M * |q| ^ (n + 1) :=
    mul_pos hM (pow_pos hrpos _)
  exact mul_lt_mul_of_pos_left hgeom hcoef

/-- Exercise 82, gap 5. -/
theorem gap5
    (a : ℕ → ℝ) (q M : ℝ)
    (hbound : ∀ m n : ℕ, n < m →
      |x a q m - x a q n| <
        M * |q| ^ (n + 1) * geometricTail q n m)
    (hgeom : ∀ m n : ℕ, n < m →
      M * |q| ^ (n + 1) * geometricTail q n m <
        M * |q| ^ (n + 1) * (1 / (1 - |q|))) :
    ∀ m n : ℕ, n < m →
      |x a q m - x a q n| <
        M * |q| ^ (n + 1) * (1 / (1 - |q|)) := by
  intro m n hnm
  exact lt_trans (hbound m n hnm) (hgeom m n hnm)

/-- Exercise 82, gap 6; N depends on ε. -/
theorem gap6
    (q M : ℝ)
    (hM : 0 < M) (hq : |q| < 1) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        |q| ^ (n + 1) < (1 - |q|) * ε / M := by
  intro ε hε
  have hdelta : 0 < (1 - |q|) * ε / M := by
    exact div_pos (mul_pos (sub_pos.mpr hq) hε) hM
  have hp :
      Tendsto (fun n : ℕ => |q| ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg q) hq
  have hshift :
      Tendsto (fun n : ℕ => |q| ^ (n + 1)) atTop (𝓝 0) :=
    hp.comp (tendsto_add_atTop_nat 1)
  have hev :
      ∀ᶠ n : ℕ in atTop, |q| ^ (n + 1) < (1 - |q|) * ε / M :=
    hshift.eventually (Iio_mem_nhds hdelta)
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n (by omega)⟩

/-- Exercise 82, gap 7; repair the uniform-cutoff quantifier. -/
theorem gap7
    (a : ℕ → ℝ) (q M : ℝ)
    (ha : ∀ i : ℕ, |a i| < M)
    (hq0 : q ≠ 0)
    (hq : |q| < 1) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m →
        |x a q m - x a q n| < ε := by
  intro ε hε
  have hM : 0 < M := lt_of_le_of_lt (abs_nonneg (a 0)) (ha 0)
  have hbound := gap3 a q M ha hq0
  have hgeom := gap4 q M hM hq0 hq
  have hcombined := gap5 a q M hbound hgeom
  rcases gap6 q M hM hq ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m n hn hnm
  have hp := hN n hn
  have hden : 0 < 1 - |q| := sub_pos.mpr hq
  have hscaled :
      M * |q| ^ (n + 1) < (1 - |q|) * ε := by
    calc
      M * |q| ^ (n + 1) <
          M * ((1 - |q|) * ε / M) :=
        mul_lt_mul_of_pos_left hp hM
      _ = (1 - |q|) * ε := by
        field_simp [hM.ne']
  calc
    |x a q m - x a q n| <
        M * |q| ^ (n + 1) * (1 / (1 - |q|)) :=
      hcombined m n hnm
    _ = (M * |q| ^ (n + 1)) / (1 - |q|) := by ring
    _ < ((1 - |q|) * ε) / (1 - |q|) :=
      (div_lt_div_iff_of_pos_right hden).2 hscaled
    _ = ε := by field_simp [hden.ne']

/-- Exercise 82, gap 8. -/
theorem gap8 (a : ℕ → ℝ) (q : ℝ)
    (h : IsCauchy (x a q)) :
    IsCauchy (x a q) := by
  exact h

/-- Exercise 82, gap 9. -/
theorem gap9 (a : ℕ → ℝ) (q : ℝ)
    (h : IsCauchy (x a q)) :
    Convergent (x a q) := by
  have hcauchy : CauchySeq (x a q) := by
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

/-- Exercise 82, gap 10. -/
theorem gap10 (a : ℕ → ℝ) (q : ℝ)
    (h : Convergent (x a q)) :
    Convergent (x a q) := by
  exact h

end

end ProofGap.Exercise82
