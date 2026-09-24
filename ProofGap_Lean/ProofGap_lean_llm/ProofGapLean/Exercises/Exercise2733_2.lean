import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2733_2

noncomputable section

open Filter

def term (y : ℝ) (n : ℕ) : ℝ :=
  1 / (n + y ^ n)

private theorem Nat.ne_of_ge_one {n : ℕ} (h : 1 ≤ n) : n ≠ 0 := by omega

private theorem not_summable_one_div_natCast :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
  intro hs
  have hs' : Summable (fun n : ℕ =>
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
    exact (summable_nat_add_iff 1).2 hs
  let a : ℕ → ℝ := fun n => (1 : ℝ) / (((n + 1 : ℕ) : ℝ))
  let S : ℕ → ℝ := fun N => (Finset.range N).sum a
  let L : ℝ := tsum a
  have hsa : Summable a := by
    simpa [a] using hs'
  have hlim : Tendsto S atTop (nhds L) := by
    simpa [S, L] using hsa.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hlim) (1 / 8 : ℝ) (by norm_num)
  let K : ℕ := max N 1
  have hNK : N ≤ K := by simp [K]
  have hKpos : 0 < K := by simp [K]
  have hN2K : N ≤ 2 * K := by omega
  have hcard : (Finset.Ico K (2 * K)).card = K := by
    simp <;> omega
  have hblock :
      (1 / 2 : ℝ) ≤ (Finset.Ico K (2 * K)).sum a := by
    calc
      (1 / 2 : ℝ) =
          (Finset.Ico K (2 * K)).sum
            (fun _ : ℕ => (1 : ℝ) / (((2 * K : ℕ) : ℝ))) := by
        rw [Finset.sum_const, hcard]
        simp only [nsmul_eq_mul]
        have hcast : (((2 * K : ℕ) : ℝ)) = 2 * (K : ℝ) := by
          norm_num
        rw [hcast]
        field_simp [show (K : ℝ) ≠ 0 by positivity] <;> ring
      _ ≤ (Finset.Ico K (2 * K)).sum a := by
        apply Finset.sum_le_sum
        intro n hn
        have hnle : n + 1 ≤ 2 * K := by
          have hnlt : n < 2 * K := (Finset.mem_Ico.mp hn).2
          omega
        have hnleR : (((n + 1 : ℕ) : ℝ)) ≤ (((2 * K : ℕ) : ℝ)) := by
          exact_mod_cast hnle
        have hsmallpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
        have hbigpos : 0 < (((2 * K : ℕ) : ℝ)) := by positivity
        change (1 : ℝ) / (((2 * K : ℕ) : ℝ)) ≤
          (1 : ℝ) / (((n + 1 : ℕ) : ℝ))
        apply (div_le_div_iff₀ hbigpos hsmallpos).2
        nlinarith
  have hdisj : Disjoint (Finset.range K) (Finset.Ico K (2 * K)) := by
    rw [Finset.disjoint_left]
    intro n hnrange hnIco
    have hnlt : n < K := Finset.mem_range.mp hnrange
    have hnge : K ≤ n := (Finset.mem_Ico.mp hnIco).1
    omega
  have hunion :
      Finset.range K ∪ Finset.Ico K (2 * K) = Finset.range (2 * K) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsplit :
      S K + (Finset.Ico K (2 * K)).sum a = S (2 * K) := by
    change (Finset.range K).sum a + (Finset.Ico K (2 * K)).sum a =
      (Finset.range (2 * K)).sum a
    rw [← hunion]
    exact (Finset.sum_union hdisj).symm
  have hclose : dist (S (2 * K)) (S K) < (1 / 4 : ℝ) := by
    calc
      dist (S (2 * K)) (S K) ≤
          dist (S (2 * K)) L + dist L (S K) := dist_triangle _ _ _
      _ = dist (S (2 * K)) L + dist (S K) L := by
        rw [dist_comm L (S K)]
      _ < (1 / 8 : ℝ) + 1 / 8 :=
        add_lt_add (hN (2 * K) hN2K) (hN K hNK)
      _ = 1 / 4 := by norm_num
  have hdiff : (1 / 2 : ℝ) ≤ S (2 * K) - S K := by
    linarith [hblock, hsplit]
  have hfar : (1 / 2 : ℝ) ≤ dist (S (2 * K)) (S K) := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hdiff])]
    exact hdiff
  linarith [hclose, hfar]

theorem gap1 (y : ℝ) (hy : 1 < y) :
    ∀ n : ℕ, 1 ≤ n → |term y n| = 1 / (n + y ^ n) := by
  intro n hn
  unfold term
  rw [abs_of_pos]
  positivity

theorem gap2 (y : ℝ) (hy : 1 < y) :
    ∀ n : ℕ, 1 ≤ n → 1 / (n + y ^ n) < (1 / y) ^ n := by
  intro n hn
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hyn : 0 < y ^ n := pow_pos hy0 n
  have hden : 0 < (n : ℝ) + y ^ n := by positivity
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [one_div_pow]
  apply (div_lt_div_iff₀ hden hyn).2
  linarith

theorem gap3 (y : ℝ) (hy : 1 < y) :
    ∀ n : ℕ, 1 ≤ n → |term y n| < (1 / y) ^ n := by
  intro n hn
  rw [gap1 y hy n hn]
  exact gap2 y hy n hn

theorem gap4 (y : ℝ) (hy : 1 < y) :
    Summable (fun n : ℕ => |term y (n + 1)|) := by
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hr : ‖(1 / y : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / y)]
    exact (div_lt_one hy0).2 hy
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => le_of_lt (gap3 y hy (n + 1) (by omega)))
  exact (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hr)

theorem gap5 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ n : ℕ, 1 ≤ n → term y n / (1 / (n : ℝ)) = n / (n + y ^ n) := by
  intro n hn
  unfold term
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_ge_one hn)
  field_simp

theorem gap6 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + y ^ (n + 1)))
      atTop (nhds 1) := by
  have hy_pow : ∀ n : ℕ, 0 ≤ y ^ (n + 1) ∧ y ^ (n + 1) ≤ 1 := by
    intro n
    constructor
    · positivity
    · exact pow_le_one₀ hy0 hy1
  have hsqueeze : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤
        ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + y ^ (n + 1)) ∧
      ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + y ^ (n + 1)) ≤ 1 := by
    intro n
    rcases hy_pow n with ⟨hpow0, hpow1⟩
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    constructor
    · exact (div_le_div_iff_of_pos_left hn (by positivity) (by positivity)).2 (by linarith)
    · exact (div_le_one (by positivity)).2 (by linarith)
  have hlo : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) atTop (nhds 1) := by
    have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hrecip : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop htop
    have hdenlim : Tendsto
        (fun n : ℕ => (1 : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hrecip
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hquot : Tendsto
        ((fun _ : ℕ => (1 : ℝ)) /
          (fun n : ℕ => (1 : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)))
        atTop (nhds 1) := by
      simpa only [div_one] using
        (hone.div hdenlim (by norm_num : (1 : ℝ) ≠ 0))
    have hfrac : Tendsto
        (fun n : ℕ => (1 : ℝ) / (1 + 1 / ((n + 1 : ℕ) : ℝ)))
        atTop (nhds 1) := by
      exact hquot.congr' (Filter.Eventually.of_forall (fun n => by rfl))
    apply hfrac.congr'
    filter_upwards [] with n
    have hk0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hkp1 : (((n + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have hone : (1 + 1 / (((n + 1 : ℕ) : ℝ))) ≠ 0 := by positivity
    field_simp [hk0, hkp1, hone] <;> ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    (Filter.Eventually.of_forall (fun n => (hsqueeze n).1))
    (Filter.Eventually.of_forall (fun n => (hsqueeze n).2))

theorem gap7 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Tendsto
      (fun n : ℕ => term y (n + 1) / (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  have h := gap6 y hy0 hy1
  apply h.congr'
  filter_upwards [] with n
  exact (gap5 y hy0 hy1 (n + 1) (by omega)).symm

theorem gap8 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ¬ Summable (fun n : ℕ => term y (n + 1)) := by
  intro hs
  have hcomp : ∀ n : ℕ,
      (1 / (2 : ℝ)) * (1 / (((n + 1 : ℕ) : ℝ))) ≤ term y (n + 1) := by
    intro n
    have hpow0 : 0 ≤ y ^ (n + 1) := by positivity
    have hpow1 : y ^ (n + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have hk : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hk1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    have hk0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hk
    calc
      (1 / (2 : ℝ)) * (1 / (((n + 1 : ℕ) : ℝ))) =
          1 / (2 * (((n + 1 : ℕ) : ℝ))) := by
            field_simp [hk0] <;> ring
      _ ≤ 1 / (((n + 1 : ℕ) : ℝ) + y ^ (n + 1)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      _ = term y (n + 1) := by rfl
  have hsmall : Summable (fun n : ℕ =>
      (1 / (2 : ℝ)) * (1 / (((n + 1 : ℕ) : ℝ)))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hcomp hs
  have hharm : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    apply (hsmall.mul_left (2 : ℝ)).congr
    intro n
    ring
  exact not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hharm)

theorem gap9 :
    {y : ℝ | 0 ≤ y ∧ Summable (fun n : ℕ => |term y (n + 1)|)} =
      {y : ℝ | 1 < y} := by
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy0, hs⟩
    by_contra hnot
    have hy1 : y ≤ 1 := le_of_not_gt hnot
    have habs_eq : (fun n : ℕ => |term y (n + 1)|) = fun n : ℕ => term y (n + 1) := by
      funext n
      unfold term
      rw [abs_of_nonneg]
      positivity
    apply gap8 y hy0 hy1
    rw [← habs_eq]
    exact hs
  · intro hy
    exact ⟨le_of_lt (lt_trans (by norm_num) hy), gap4 y hy⟩

theorem gap10 :
    {y : ℝ | 0 ≤ y ∧ ¬ Summable (fun n : ℕ => term y (n + 1))} =
      {y : ℝ | 0 ≤ y ∧ y ≤ 1} := by
  set_option maxHeartbeats 1000000 in
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hy0, hns⟩
      refine ⟨hy0, ?_⟩
      by_contra hnot
      have hy : 1 < y := lt_of_not_ge hnot
      apply hns
      exact Summable.of_nonneg_of_le
        (fun n => by unfold term; positivity)
        (fun n => le_abs_self (term y (n + 1)))
        (gap4 y hy)
    · rintro ⟨hy0, hy1⟩
      exact ⟨hy0, gap8 y hy0 hy1⟩

end

end ProofGap.Exercise2733_2
