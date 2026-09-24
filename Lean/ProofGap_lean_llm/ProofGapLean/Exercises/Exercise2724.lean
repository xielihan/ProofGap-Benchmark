import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2724

noncomputable section

def term (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (1 - x ^ n)

def splitTerm₁ (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (1 - x ^ (2 * n))

def splitTerm₂ (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / (1 - x ^ (2 * n))

def admissible (x : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 1 - x ^ n ≠ 0

private theorem pg_pow_le_base (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) : a ^ n ≤ a := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := by
    exact ⟨n - 1, by omega⟩
  have hpow : a ^ m ≤ 1 := pow_le_one₀ ha0 ha1
  rw [pow_succ]
  calc
    a ^ m * a ≤ 1 * a := mul_le_mul_of_nonneg_right hpow ha0
    _ = a := one_mul a

private theorem summability_aux (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |x ^ (n + 1)|) ∧
      Summable (fun n : ℕ => |x ^ (n + 1) / (1 - x ^ (n + 1))|) := by
  have hgeo : Summable (fun n : ℕ => |x| ^ n) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg x)] using hx)
  have hadd : Function.Injective (fun n : ℕ => n + 1) := by
    intro m n h
    change m + 1 = n + 1 at h
    exact Nat.add_right_cancel h
  have hshift : Summable (fun n : ℕ => |x ^ (n + 1)|) := by
    simpa [abs_pow] using hgeo.comp_injective hadd
  refine ⟨hshift, ?_⟩
  have hcpos : 0 < 1 - |x| := sub_pos.mpr hx
  have hmajor := hshift.div_const (1 - |x|)
  refine hmajor.of_norm_bounded ?_
  intro n
  have hk : 1 ≤ n + 1 := by omega
  have hpowle : |x ^ (n + 1)| ≤ |x| := by
    rw [abs_pow]
    exact pg_pow_le_base (a := |x|) (abs_nonneg x) (le_of_lt hx) hk
  have hpwlt : x ^ (n + 1) < 1 :=
    lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt hpowle hx)
  have hdpos : 0 < 1 - x ^ (n + 1) := sub_pos.mpr hpwlt
  have hden : 1 - |x| ≤ |1 - x ^ (n + 1)| := by
    rw [abs_of_pos hdpos]
    nlinarith [le_abs_self (x ^ (n + 1))]
  have hDpos : 0 < |1 - x ^ (n + 1)| :=
    abs_pos.mpr (ne_of_gt hdpos)
  have hfrac :
      |x ^ (n + 1)| / |1 - x ^ (n + 1)| ≤
        |x ^ (n + 1)| / (1 - |x|) := by
    apply (div_le_div_iff₀ hDpos hcpos).2
    exact mul_le_mul_of_nonneg_left hden (abs_nonneg _)
  have hmaj_nonneg : 0 ≤ |x ^ (n + 1)| / (1 - |x|) :=
    div_nonneg (abs_nonneg _) hcpos.le
  simpa [Real.norm_eq_abs, abs_div, abs_of_nonneg hmaj_nonneg] using hfrac

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |x ^ (n + 1)|) := by
  exact (summability_aux x hx).1

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |splitTerm₁ x (n + 1)|) := by
  have hcpos : 0 < 1 - |x| := sub_pos.mpr hx
  have hmajor := (summability_aux x hx).1.div_const (1 - |x|)
  refine hmajor.of_norm_bounded ?_
  intro n
  have hk : 1 ≤ 2 * (n + 1) := by omega
  have hpowle : |x ^ (2 * (n + 1))| ≤ |x| := by
    rw [abs_pow]
    exact pg_pow_le_base (a := |x|) (abs_nonneg x) (le_of_lt hx) hk
  have hpwlt : x ^ (2 * (n + 1)) < 1 :=
    lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt hpowle hx)
  have hdpos : 0 < 1 - x ^ (2 * (n + 1)) := sub_pos.mpr hpwlt
  have hden : 1 - |x| ≤ |1 - x ^ (2 * (n + 1))| := by
    rw [abs_of_pos hdpos]
    nlinarith [le_abs_self (x ^ (2 * (n + 1)))]
  have hDpos : 0 < |1 - x ^ (2 * (n + 1))| :=
    abs_pos.mpr (ne_of_gt hdpos)
  have hfrac :
      |x ^ (n + 1)| / |1 - x ^ (2 * (n + 1))| ≤
        |x ^ (n + 1)| / (1 - |x|) := by
    apply (div_le_div_iff₀ hDpos hcpos).2
    exact mul_le_mul_of_nonneg_left hden (abs_nonneg _)
  have hmaj_nonneg : 0 ≤ |x ^ (n + 1)| / (1 - |x|) :=
    div_nonneg (abs_nonneg _) hcpos.le
  simpa [splitTerm₁, Real.norm_eq_abs, abs_div,
    abs_of_nonneg hmaj_nonneg] using hfrac

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |splitTerm₂ x (n + 1)|) := by
  have hx2 : |x ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg x, sq_nonneg |x|]
  simpa [splitTerm₂, pow_mul] using (summability_aux (x ^ 2) hx2).2

theorem gap4 (x : ℝ) (n : ℕ) (hx : |x| < 1) (hn : 1 ≤ n) :
    term x n = splitTerm₁ x n + splitTerm₂ x n := by
  have habsn : |x ^ n| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg x) hx (by omega)
  have habs2n : |x ^ (2 * n)| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg x) hx (by omega)
  have hxn : x ^ n ≠ 1 := by
    intro h
    rw [h, abs_one] at habsn
    exact (lt_irrefl 1 habsn)
  have hx2n : x ^ (2 * n) ≠ 1 := by
    intro h
    rw [h, abs_one] at habs2n
    exact (lt_irrefl 1 habs2n)
  have hdn : 1 - x ^ n ≠ 0 := by
    intro h
    apply hxn
    linarith
  have hd2n : 1 - x ^ (2 * n) ≠ 0 := by
    intro h
    apply hx2n
    linarith
  have hpow : x ^ (2 * n) = (x ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  have hd2n' : 1 - (x ^ n) ^ 2 ≠ 0 := by
    simpa [hpow] using hd2n
  unfold term splitTerm₁ splitTerm₂
  rw [hpow]
  field_simp [hdn, hd2n'] <;> ring

theorem gap5 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  simpa only [term] using (summability_aux x hx).2

theorem gap6 (x : ℝ) (hx : |x| = 1) :
    ∃ n : ℕ, 1 ≤ n ∧ 1 - x ^ n = 0 := by
  by_cases hnonneg : 0 ≤ x
  · have hxeq : x = 1 := by
      rw [abs_of_nonneg hnonneg] at hx
      exact hx
    refine ⟨1, by norm_num, ?_⟩
    norm_num [hxeq]
  · have hxneg : x < 0 := lt_of_not_ge hnonneg
    have hxeq : x = -1 := by
      rw [abs_of_neg hxneg] at hx
      linarith
    refine ⟨2, by norm_num, ?_⟩
    norm_num [hxeq]

theorem gap7 (x : ℝ) (hx : 1 < |x|) :
    ∀ n : ℕ, 1 ≤ n →
      term x n = -1 / (1 - (1 / x) ^ n) := by
  intro n hn
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hxn0 : x ^ n ≠ 0 := pow_ne_zero n hx0
  have habsn : 1 < |x ^ n| := by
    rw [abs_pow]
    exact one_lt_pow₀ hx (by omega)
  have hxn : x ^ n ≠ 1 := by
    intro h
    rw [h, abs_one] at habsn
    exact (lt_irrefl 1 habsn)
  have hd : 1 - x ^ n ≠ 0 := by
    intro h
    apply hxn
    linarith
  have hminus : -1 + x ^ n ≠ 0 := by
    intro h
    apply hxn
    linarith
  have hdenform : 1 - 1 / x ^ n = (-1 + x ^ n) / x ^ n := by
    field_simp [hxn0]
    <;> ring
  unfold term
  rw [one_div_pow, hdenform]
  field_simp [hd, hminus, hxn0]
  <;> ring

theorem gap8 (x : ℝ) (hx : 1 < |x|) :
    Summable
      (fun n : ℕ => |(1 / x) ^ (n + 1) / (1 - (1 / x) ^ (n + 1))|) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hxabspos : 0 < |x| := abs_pos.mpr hx0
  have hrecip : |(1 / x : ℝ)| < 1 := by
    rw [abs_div, abs_one]
    exact (div_lt_one₀ hxabspos).2 hx
  simpa only [term] using (summability_aux (1 / x) hrecip).2

theorem gap9 (x : ℝ) (hx : 1 < |x|) :
    ∀ n : ℕ, 1 ≤ n →
      1 / (1 - (1 / x) ^ n) -
          (1 / x) ^ n / (1 - (1 / x) ^ n) = 1 := by
  intro n hn
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hxabspos : 0 < |x| := abs_pos.mpr hx0
  have hrecip : |(1 / x : ℝ)| < 1 := by
    rw [abs_div, abs_one]
    exact (div_lt_one₀ hxabspos).2 hx
  have hpwlt : |(1 / x) ^ n| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg (1 / x)) hrecip (by omega)
  have hpwne : (1 / x) ^ n ≠ 1 := by
    intro h
    rw [h, abs_one] at hpwlt
    exact (lt_irrefl 1 hpwlt)
  have hd : 1 - (1 / x) ^ n ≠ 0 := by
    intro h
    apply hpwne
    linarith
  field_simp [hd] <;> ring

theorem gap10 :
    ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have hzero : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) :=
    h.tendsto_atTop_zero
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at h01

theorem gap11 (x : ℝ) (hx : 1 < |x|) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hterm
  have hsmall : Summable
      (fun n : ℕ => (1 / x) ^ (n + 1) /
        (1 - (1 / x) ^ (n + 1))) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using gap8 x hx
  apply gap10
  refine (hterm.neg.sub hsmall).congr ?_
  intro n
  calc
    -term x (n + 1) -
          (1 / x) ^ (n + 1) / (1 - (1 / x) ^ (n + 1)) =
        1 / (1 - (1 / x) ^ (n + 1)) -
          (1 / x) ^ (n + 1) / (1 - (1 / x) ^ (n + 1)) := by
      rw [gap7 x hx (n + 1) (by omega)]
      ring
    _ = 1 := gap9 x hx (n + 1) (by omega)

theorem gap12 (x : ℝ) (hx : 1 < |x|) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  exact gap11 x hx

theorem gap13 :
    {x : ℝ | admissible x ∧ Summable (fun n : ℕ => term x (n + 1))} =
      {x : ℝ | |x| < 1} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hadm, hsum⟩
    by_contra hnot
    have hge : 1 ≤ |x| := le_of_not_gt hnot
    rcases eq_or_lt_of_le hge with heq | hgt
    · obtain ⟨n, hn, hz⟩ := gap6 x heq.symm
      exact (hadm n hn) hz
    · exact gap11 x hgt hsum
  · intro hx
    constructor
    · intro n hn
      have hpwlt : |x ^ n| < 1 := by
        rw [abs_pow]
        exact pow_lt_one₀ (abs_nonneg x) hx (by omega)
      intro hz
      have hpweq : x ^ n = 1 := by linarith
      rw [hpweq, abs_one] at hpwlt
      exact (lt_irrefl 1 hpwlt)
    · apply Summable.of_norm
      simpa only [Real.norm_eq_abs] using gap5 x hx

end

end ProofGap.Exercise2724
