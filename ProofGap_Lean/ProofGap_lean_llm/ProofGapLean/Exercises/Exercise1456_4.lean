import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace ProofGap.Exercise1456_4

noncomputable section

open Filter

def rootSum (n : ℕ) (a x : ℝ) : ℝ :=
  Real.rpow (x ^ n + a ^ n) (1 / (n : ℝ))

def ratio (n : ℕ) (a x : ℝ) : ℝ := rootSum n a x / (x + a)

def IsUniqueMinimizerOn (f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ (∀ x ∈ s, f x₀ ≤ f x) ∧
    ∀ x ∈ s, f x = f x₀ → x = x₀

private lemma rpow_pow_inv (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : 0 ≤ x) :
    Real.rpow (x ^ n) (1 / (n : ℝ)) = x := by
  calc
    Real.rpow (x ^ n) (1 / (n : ℝ)) =
        Real.rpow (Real.rpow x (n : ℝ)) (1 / (n : ℝ)) := by
          exact congrArg (fun y => Real.rpow y (1 / (n : ℝ)))
            (Real.rpow_natCast x n).symm
    _ = Real.rpow x ((n : ℝ) * (1 / (n : ℝ))) := by
      exact (Real.rpow_mul hx _ _).symm
    _ = x := by
      rw [mul_one_div_cancel]
      · simp
      · exact_mod_cast hn.ne'

private lemma scale_pow_eq (n : ℕ) (hn : 0 < n) :
    (Real.rpow 2 (((n : ℝ) - 1) / n)) ^ n =
      Real.rpow 2 ((n : ℝ) - 1) := by
  calc
    (Real.rpow 2 (((n : ℝ) - 1) / n)) ^ n =
        Real.rpow (Real.rpow 2 (((n : ℝ) - 1) / n)) (n : ℝ) := by
          exact (Real.rpow_natCast _ n).symm
    _ = Real.rpow 2 ((((n : ℝ) - 1) / n) * n) := by
      exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = Real.rpow 2 ((n : ℝ) - 1) := by
      congr 1
      field_simp

private lemma rootSum_upper (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a)
    (hx : 0 < x) : rootSum n a x ≤ x + a := by
  let X : NNReal := ⟨x, hx.le⟩
  let A : NNReal := ⟨a, ha.le⟩
  have hp : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
  have h := NNReal.rpow_add_rpow_le_add X A hp
  exact_mod_cast h

private lemma rootSum_lower (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a)
    (hx : 0 < x) :
    (x + a) / Real.rpow 2 (((n : ℝ) - 1) / n) ≤ rootSum n a x := by
  let X : NNReal := ⟨x, hx.le⟩
  let A : NNReal := ⟨a, ha.le⟩
  have hp : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hnn := NNReal.rpow_add_le_mul_rpow_add_rpow X A hp
  have hnn' :
      (↑((X + A) ^ (n : ℝ)) : ℝ) ≤
        (↑((2 : NNReal) ^ ((n : ℝ) - 1) *
          (X ^ (n : ℝ) + A ^ (n : ℝ))) : ℝ) :=
    NNReal.coe_le_coe.2 hnn
  have h : (x + a) ^ n ≤
      Real.rpow 2 ((n : ℝ) - 1) * (x ^ n + a ^ n) := by
    simpa [Real.rpow_natCast] using hnn'
  unfold rootSum
  rw [show (1 / (n : ℝ)) = (n : ℝ)⁻¹ by simp]
  change (x + a) / Real.rpow 2 (((n : ℝ) - 1) / n) ≤
    (x ^ n + a ^ n) ^ (n : ℝ)⁻¹
  apply (Real.le_rpow_inv_iff_of_pos
    (div_nonneg (add_nonneg hx.le ha.le) (Real.rpow_nonneg (by norm_num) _))
    (by exact (add_pos (pow_pos hx n) (pow_pos ha n)).le)
    (by exact_mod_cast (Nat.zero_lt_of_lt hn))).2
  rw [Real.rpow_natCast, div_pow]
  change (x + a) ^ n / (Real.rpow 2 (((n : ℝ) - 1) / n)) ^ n ≤
    x ^ n + a ^ n
  rw [scale_pow_eq n (Nat.zero_lt_of_lt hn)]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

private lemma rootSum_lower_strict (n : ℕ) (a x : ℝ) (hn : 1 < n)
    (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    (x + a) / Real.rpow 2 (((n : ℝ) - 1) / n) < rootSum n a x := by
  have hs := (strictConvexOn_pow (n := n) hn).2 hx.le ha.le hxa
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hs
  have htwo : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    rw [← mul_pow_sub_one (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))]
  have hs' : (x + a) ^ n <
      (2 : ℝ) ^ (n - 1) * (x ^ n + a ^ n) := by
    rw [show (1 / 2 : ℝ) * x + 1 / 2 * a = (x + a) / 2 by ring, div_pow,
      htwo] at hs
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ (n - 1))).1 hs
    convert this using 1 <;> ring
  have hrpow2 :
      Real.rpow 2 ((n : ℝ) - 1) = (2 : ℝ) ^ (n - 1) := by
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      norm_num [Nat.cast_sub hn.le]
    rw [← hc]
    exact Real.rpow_natCast 2 (n - 1)
  have h : (x + a) ^ n <
      Real.rpow 2 ((n : ℝ) - 1) * (x ^ n + a ^ n) := by
    rwa [hrpow2]
  unfold rootSum
  rw [show (1 / (n : ℝ)) = (n : ℝ)⁻¹ by simp]
  change (x + a) / Real.rpow 2 (((n : ℝ) - 1) / n) <
    (x ^ n + a ^ n) ^ (n : ℝ)⁻¹
  apply (Real.lt_rpow_inv_iff_of_pos
    (div_nonneg (add_nonneg hx.le ha.le) (Real.rpow_nonneg (by norm_num) _))
    (by exact (add_pos (pow_pos hx n) (pow_pos ha n)).le)
    (by exact_mod_cast (Nat.zero_lt_of_lt hn))).2
  rw [Real.rpow_natCast, div_pow]
  change (x + a) ^ n / (Real.rpow 2 (((n : ℝ) - 1) / n)) ^ n <
    x ^ n + a ^ n
  rw [scale_pow_eq n (Nat.zero_lt_of_lt hn)]
  apply (div_lt_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

private lemma ratio_scale (n : ℕ) (a x : ℝ) (hn : 0 < n) (ha : 0 < a)
    (hx : 0 ≤ x) : ratio n a x = ratio n 1 (x / a) := by
  have hsum : x ^ n + a ^ n = a ^ n * ((x / a) ^ n + 1) := by
    rw [div_pow]
    field_simp [ha.ne']
  have han : 0 ≤ a ^ n := by positivity
  have hs : 0 ≤ (x / a) ^ n + 1 := by positivity
  simp only [ratio, rootSum]
  rw [hsum]
  change (a ^ n * ((x / a) ^ n + 1)) ^ (1 / (n : ℝ)) / (x + a) =
    (((x / a) ^ n + 1 ^ n) ^ (1 / (n : ℝ))) / (x / a + 1)
  rw [Real.mul_rpow han hs]
  change Real.rpow (a ^ n) (1 / (n : ℝ)) *
      Real.rpow ((x / a) ^ n + 1) (1 / (n : ℝ)) / (x + a) =
    Real.rpow ((x / a) ^ n + 1 ^ n) (1 / (n : ℝ)) / (x / a + 1)
  rw [rpow_pow_inv n a hn ha.le]
  field_simp
  <;> ring

private lemma ratio_continuousAt_zero (n : ℕ) (hn : 0 < n) :
    ContinuousAt (ratio n 1) 0 := by
  unfold ratio rootSum
  apply ContinuousAt.div
  · apply ContinuousAt.rpow_const
    · fun_prop
    · left
      simp [hn.ne']
  · fun_prop
  · norm_num

theorem gap1 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    ratio n a a = 1 / Real.rpow 2 (((n : ℝ) - 1) / n) := by
  rw [ratio_scale n a a (Nat.zero_lt_of_lt hn) ha ha.le]
  norm_num [ratio, rootSum]
  have he :
      (1 / (n : ℝ)) + (((n : ℝ) - 1) / n) = 1 := by
    field_simp
    ring
  have hmul :
      (2 : ℝ) ^ (1 / (n : ℝ)) *
        (2 : ℝ) ^ (((n : ℝ) - 1) / n) = 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), he]
    simp
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
  norm_num
  simpa [one_div] using hmul

theorem gap2 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    IsUniqueMinimizerOn (ratio n a) (Set.Ioi 0) a := by
  refine ⟨ha, ?_, ?_⟩
  · intro x hx
    rw [gap1 n a hn ha]
    have h := rootSum_lower n a x hn ha hx
    unfold ratio
    rw [le_div_iff₀ (add_pos hx ha)]
    simpa [div_eq_mul_inv, mul_comm] using h
  · intro x hx heq
    by_contra hne
    have hroot := rootSum_lower_strict n a x hn ha hx hne
    have hratio :
        1 / Real.rpow 2 (((n : ℝ) - 1) / n) < ratio n a x := by
      unfold ratio
      rw [lt_div_iff₀ (add_pos hx ha)]
      simpa [div_eq_mul_inv, mul_comm] using hroot
    rw [heq, gap1 n a hn ha] at hratio
    exact lt_irrefl _ hratio

theorem gap3 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    Tendsto (ratio n a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have ht : Tendsto (fun x : ℝ => x / a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert ((continuousAt_id.div_const a).tendsto.mono_left inf_le_left) using 1 <;> simp
  have hc := (ratio_continuousAt_zero n (Nat.zero_lt_of_lt hn)).tendsto.comp ht
  have heq : ratio n 1 0 = 1 := by
    norm_num [ratio, rootSum, (Nat.zero_lt_of_lt hn).ne']
  rw [heq] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (ratio_scale n a x (Nat.zero_lt_of_lt hn) ha hx.le).symm

theorem gap4 (n : ℕ) (a : ℝ) (hn : 1 < n) (ha : 0 < a) :
    Tendsto (ratio n a) atTop (nhds 1) := by
  have ht : Tendsto (fun x : ℝ => a / x) atTop (nhds 0) :=
    tendsto_id.const_div_atTop a
  have hc := (ratio_continuousAt_zero n (Nat.zero_lt_of_lt hn)).tendsto.comp ht
  have heq : ratio n 1 0 = 1 := by
    norm_num [ratio, rootSum, (Nat.zero_lt_of_lt hn).ne']
  rw [heq] at hc
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (calc
      ratio n a x = ratio n x a := by simp [ratio, rootSum, add_comm]
      _ = ratio n 1 (a / x) :=
        ratio_scale n x a (Nat.zero_lt_of_lt hn) hx ha.le).symm

theorem gap5 (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a) (hx : 0 < x) :
    1 / Real.rpow 2 (((n : ℝ) - 1) / n) ≤ ratio n a x := by
  have h := rootSum_lower n a x hn ha hx
  unfold ratio
  rw [le_div_iff₀ (add_pos hx ha)]
  simpa [div_eq_mul_inv, mul_comm] using h

theorem gap6 (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a) (hx : 0 < x) :
    ratio n a x ≤ 1 := by
  have h := rootSum_upper n a x hn ha hx
  unfold ratio
  exact (div_le_one (add_pos hx ha)).2 h

theorem gap7 (n : ℕ) (hn : 1 < n) :
    1 / Real.rpow 2 (((n : ℝ) - 1) / n) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / n :=
    div_nonneg (sub_nonneg.2 hnR) (by positivity)
  have hc : 1 ≤ Real.rpow 2 (((n : ℝ) - 1) / n) :=
    Real.one_le_rpow (by norm_num) he
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).2
  simpa using hc

theorem gap8 (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a) (hx : 0 < x) :
    (x + a) / Real.rpow 2 (((n : ℝ) - 1) / n) ≤ rootSum n a x := by
  exact rootSum_lower n a x hn ha hx

theorem gap9 (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a) (hx : 0 < x) :
    rootSum n a x ≤ x + a := by
  exact rootSum_upper n a x hn ha hx

theorem gap10 (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a) (hx : 0 < x) :
    (x + a) / Real.rpow 2 (((n : ℝ) - 1) / n) ≤ x + a := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hc : 1 ≤ Real.rpow 2 (((n : ℝ) - 1) / n) :=
    Real.one_le_rpow (by norm_num)
      (div_nonneg (sub_nonneg.2 hnR) (by positivity))
  exact div_le_self (add_pos hx ha).le hc

theorem gap11 (n : ℕ) (a x : ℝ) (hn : 1 < n) (ha : 0 < a) (hx : 0 < x) :
    (x + a) / Real.rpow 2 (((n : ℝ) - 1) / n) ≤ rootSum n a x ∧
      rootSum n a x ≤ x + a := by
  exact ⟨gap8 n a x hn ha hx, gap9 n a x hn ha hx⟩

end

end ProofGap.Exercise1456_4
