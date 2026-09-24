import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise384

noncomputable section

def f (x : ℝ) : ℝ := (1 / x) * Real.cos (1 / x)
def alternating (k : ℤ) : ℝ := if Even k then 1 else -1

def BoundedOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, |g x| ≤ M

/-- Source: `proof_gap/exercise_384/1.txt`; type the integer index explicitly. -/
private theorem cos_int_mul_pi_eq_alternating (k : ℤ) :
    Real.cos ((k : ℝ) * Real.pi) = alternating k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [alternating, if_pos hk]
    rcases hk with ⟨j, hj⟩
    let t : ℝ := (j : ℝ) * Real.pi
    have hs : Real.sin t = 0 := by
      dsimp [t]
      exact Real.sin_int_mul_pi j
    have hunit := Real.sin_sq_add_cos_sq t
    have harg : (k : ℝ) * Real.pi = t + t := by
      rw [hj]
      dsimp [t]
      norm_num [Int.cast_add, Int.cast_mul] <;> ring
    rw [harg, Real.cos_add]
    nlinarith
  · have hne : ¬Even k := by
      intro he
      rcases he with ⟨a, ha⟩
      rcases hk with ⟨b, hb⟩
      omega
    rw [alternating, if_neg hne]
    rcases hk with ⟨j, hj⟩
    let t : ℝ := (j : ℝ) * Real.pi
    have hs : Real.sin t = 0 := by
      dsimp [t]
      exact Real.sin_int_mul_pi j
    have hunit := Real.sin_sq_add_cos_sq t
    have harg : (k : ℝ) * Real.pi = (t + t) + Real.pi := by
      rw [hj]
      dsimp [t]
      norm_num [Int.cast_add, Int.cast_mul] <;> ring
    rw [harg, Real.cos_add, Real.cos_pi, Real.sin_pi]
    rw [Real.cos_add]
    nlinarith

private theorem tendsto_atTop_of_natCast_mul_le
    (c : ℝ) (hc : 0 < c) {u : ℕ → ℝ}
    (h : ∀ k : ℕ, (k : ℝ) * c ≤ u k) :
    Filter.Tendsto u Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (b / c)
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hbN : b < (N : ℝ) * c := (div_lt_iff₀ hc).mp hN
  have hNn : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  exact (le_of_lt hbN).trans
    ((mul_le_mul_of_nonneg_right hNn (le_of_lt hc)).trans (h n))

theorem gap1 : ∀ k : ℤ,
    f (2 / (((2 * k + 1 : ℤ) : ℝ) * Real.pi)) = 0 := by
  intro k
  have hkodd : (2 * k + 1 : ℤ) ≠ 0 := by omega
  have hkoddR : (((2 * k + 1 : ℤ) : ℝ)) ≠ 0 := by
    exact_mod_cast hkodd
  have hden : (((2 * k + 1 : ℤ) : ℝ) * Real.pi) ≠ 0 :=
    mul_ne_zero hkoddR (ne_of_gt Real.pi_pos)
  have hinv :
      1 / (2 / (((2 * k + 1 : ℤ) : ℝ) * Real.pi)) =
        (((2 * k + 1 : ℤ) : ℝ) * Real.pi) / 2 := by
    field_simp [hden]
  have harg :
      (((2 * k + 1 : ℤ) : ℝ) * Real.pi) / 2 =
        (k : ℝ) * Real.pi + Real.pi / 2 := by
    norm_num [Int.cast_add, Int.cast_mul] <;> ring
  unfold f
  simp only [hinv]
  rw [harg, Real.cos_add, Real.cos_pi_div_two, Real.sin_int_mul_pi]
  ring

/-- Source: `proof_gap/exercise_384/2.txt`; exclude the zero integer denominator. -/
theorem gap2 : ∀ k : ℤ, k ≠ 0 →
    f (1 / ((k : ℝ) * Real.pi)) =
      alternating k * (k : ℝ) * Real.pi := by
  intro k hk
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hden : (k : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero hkR (ne_of_gt Real.pi_pos)
  have hinv : 1 / (1 / ((k : ℝ) * Real.pi)) = (k : ℝ) * Real.pi := by
    field_simp [hden]
  unfold f
  simp only [hinv, cos_int_mul_pi_eq_alternating]
  ring

/-- Source: `proof_gap/exercise_384/3.txt`. -/
theorem gap3 :
    Filter.Tendsto
      (fun k : ℕ => 2 / (((2 * k + 1 : ℕ) : ℝ) * Real.pi))
      Filter.atTop (nhds 0) := by
  have hden :
      Filter.Tendsto
        (fun k : ℕ => (((2 * k + 1 : ℕ) : ℝ) * Real.pi))
        Filter.atTop Filter.atTop := by
    apply tendsto_atTop_of_natCast_mul_le Real.pi Real.pi_pos
    intro k
    have hk : k ≤ 2 * k + 1 := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) Real.pi_pos.le
  have hi :
      Filter.Tendsto
        (fun k : ℕ => ((((2 * k + 1 : ℕ) : ℝ) * Real.pi))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden)
  have hc :
      Filter.Tendsto (fun _ : ℕ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  simpa only [div_eq_mul_inv, mul_zero] using hc.mul hi

/-- Source: `proof_gap/exercise_384/4.txt`; use `k+1` to avoid the zero denominator. -/
theorem gap4 :
    Filter.Tendsto
      (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * Real.pi))
      Filter.atTop (nhds 0) := by
  have hden :
      Filter.Tendsto
        (fun k : ℕ => (((k + 1 : ℕ) : ℝ) * Real.pi))
        Filter.atTop Filter.atTop := by
    apply tendsto_atTop_of_natCast_mul_le Real.pi Real.pi_pos
    intro k
    have hk : k ≤ k + 1 := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) Real.pi_pos.le
  have hi :
      Filter.Tendsto
        (fun k : ℕ => ((((k + 1 : ℕ) : ℝ) * Real.pi))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden)
  simpa only [one_div] using hi

/-- Source: `proof_gap/exercise_384/5.txt`. -/
theorem gap5 :
    Filter.Tendsto
      (fun k : ℕ => |alternating (k + 1) * ((k + 1 : ℕ) : ℝ) * Real.pi|)
      Filter.atTop Filter.atTop := by
  have hden :
      Filter.Tendsto
        (fun k : ℕ => (((k + 1 : ℕ) : ℝ) * Real.pi))
        Filter.atTop Filter.atTop := by
    apply tendsto_atTop_of_natCast_mul_le Real.pi Real.pi_pos
    intro k
    have hk : k ≤ k + 1 := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) Real.pi_pos.le
  refine hden.congr' (Filter.Eventually.of_forall (fun k => ?_))
  have halt : |alternating ((k : ℤ) + 1)| = 1 := by
    unfold alternating
    split_ifs <;> norm_num
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le (k + 1)
  change ((k + 1 : ℕ) : ℝ) * Real.pi =
    |alternating ((k : ℤ) + 1) * ((k + 1 : ℕ) : ℝ) * Real.pi|
  rw [abs_mul, abs_mul, halt, abs_of_nonneg hk0,
    abs_of_pos Real.pi_pos]
  ring

/-- Source: `proof_gap/exercise_384/6.txt`; remove the point where `1/x` is undefined. -/
theorem gap6 : ∀ δ > 0,
    ¬BoundedOn f (Set.Ioo (-δ) δ \ {0}) := by
  intro δ hδ hbounded
  rcases hbounded with ⟨M, hM⟩
  have hnear :
      ∀ᶠ k : ℕ in Filter.atTop,
        1 / (((k + 1 : ℕ) : ℝ) * Real.pi) ∈ Set.Ioo (-δ) δ :=
    gap4.eventually (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ)
  have hxmem :
      ∀ᶠ k : ℕ in Filter.atTop,
        1 / (((k + 1 : ℕ) : ℝ) * Real.pi) ∈
          Set.Ioo (-δ) δ \ {0} := by
    filter_upwards [hnear] with k hk
    refine ⟨hk, ?_⟩
    simp only [Set.mem_singleton_iff]
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos k
    exact ne_of_gt (one_div_pos.mpr (mul_pos hkpos Real.pi_pos))
  have hbound :
      ∀ᶠ k : ℕ in Filter.atTop,
        |f (1 / (((k + 1 : ℕ) : ℝ) * Real.pi))| ≤ M :=
    hxmem.mono (fun k hk => hM _ hk)
  have hlarge :
      ∀ᶠ k : ℕ in Filter.atTop,
        M + 1 ≤
          |alternating (k + 1) * ((k + 1 : ℕ) : ℝ) * Real.pi| :=
    (Filter.tendsto_atTop.1 gap5) (M + 1)
  rcases (hbound.and hlarge).exists with ⟨k, hkBound, hkLarge⟩
  have hkne : (((k + 1 : ℕ) : ℤ)) ≠ 0 := by omega
  have hfk :
      f (1 / (((k + 1 : ℕ) : ℝ) * Real.pi)) =
        alternating (((k + 1 : ℕ) : ℤ)) *
          ((k + 1 : ℕ) : ℝ) * Real.pi := by
    simpa using gap2 (((k + 1 : ℕ) : ℤ)) hkne
  rw [hfk] at hkBound
  have halt : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by omega
  rw [halt] at hkBound
  linarith

/-- Source: `proof_gap/exercise_384/7.txt`. -/
theorem gap7 : ∀ k : ℕ, 0 < k →
    f (2 / (((2 * k + 1 : ℕ) : ℝ) * Real.pi)) = 0 := by
  intro k _
  simpa [Nat.cast_add, Nat.cast_mul] using gap1 (k : ℤ)

/-- Source: `proof_gap/exercise_384/8.txt`; formulate the punctured limit. -/
theorem gap8 :
    ¬Filter.Tendsto (fun x : ℝ => |f x|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) Filter.atTop := by
  intro htop
  have hx :
      Filter.Tendsto
        (fun k : ℕ => 2 / (((2 * k + 1 : ℕ) : ℝ) * Real.pi))
        Filter.atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨gap3, Filter.Eventually.of_forall (fun k => ?_)⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hkpos : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * k + 1 by omega)
    exact ne_of_gt (div_pos (by norm_num) (mul_pos hkpos Real.pi_pos))
  have hlarge :
      ∀ᶠ k : ℕ in Filter.atTop,
        (1 : ℝ) ≤
          |f (2 / (((2 * k + 1 : ℕ) : ℝ) * Real.pi))| :=
    (Filter.tendsto_atTop.1 (htop.comp hx)) 1
  rcases hlarge.exists with ⟨k, hk⟩
  have hz :
      f (2 / (((2 * k + 1 : ℕ) : ℝ) * Real.pi)) = 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using gap1 (k : ℤ)
  rw [hz] at hk
  norm_num at hk

/-- Source: `proof_gap/exercise_384/9.txt`. -/
theorem gap9 :
    (∀ δ > 0, ¬BoundedOn f (Set.Ioo (-δ) δ \ {0})) ∧
      ¬Filter.Tendsto (fun x : ℝ => |f x|)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) Filter.atTop := by
  exact ⟨gap6, gap8⟩

end

end ProofGap.Exercise384
