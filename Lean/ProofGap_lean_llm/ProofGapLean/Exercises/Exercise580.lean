import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise580

noncomputable section

def seq (n : ℕ) : ℝ :=
  (Real.cosh (Real.pi / n) / Real.cos (Real.pi / n)) ^ (n ^ 2)
def exponentialForm (n : ℕ) : ℝ :=
  ((Real.exp (Real.pi / n) + Real.exp (-Real.pi / n)) /
    (2 * Real.cos (Real.pi / n))) ^ (n ^ 2)
def scaledDifference (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (Real.exp (Real.pi / n) + Real.exp (-Real.pi / n) -
    2 * Real.cos (Real.pi / n))
def squareForm (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * ((Real.exp (Real.pi / (2 * n)) -
    Real.exp (-Real.pi / (2 * n))) ^ 2 +
    2 * (1 - Real.cos (Real.pi / n)))
def sineForm (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * ((Real.exp (Real.pi / (2 * n)) -
    Real.exp (-Real.pi / (2 * n))) ^ 2 +
    4 * Real.sin (Real.pi / (2 * n)) ^ 2)
def normalized (n : ℕ) : ℝ :=
  (((Real.exp (Real.pi / (2 * n)) - 1) / (Real.pi / (2 * n)) *
      (Real.pi / 2) +
    (Real.exp (-Real.pi / (2 * n)) - 1) / (-Real.pi / (2 * n)) *
      (Real.pi / 2)) ^ 2 +
    Real.pi ^ 2 * (Real.sin (Real.pi / (2 * n)) / (Real.pi / (2 * n))) ^ 2)

/-- Exercise 580, gap 1; exclude the zero sequence index. -/
private theorem tendsto_real_const_div_nat (c : ℝ) :
    Filter.Tendsto (fun n : ℕ => c / (n : ℝ)) Filter.atTop (nhds 0) := by
  have hcast :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0)).comp hcast
  simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv

private theorem eventually_nat_pos :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < n := by
  apply Filter.eventually_atTop.2
  exact ⟨1, fun n hn => lt_of_lt_of_le (by norm_num) hn⟩

private theorem tendsto_exp_sub_one_div_at_zero :
    Filter.Tendsto (fun x : ℝ => (Real.exp x - 1) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_exp 0).tendsto_slope_zero

private theorem tendsto_sin_div_at_zero :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

private theorem tendsto_log_one_add_div_at_zero :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero

theorem gap1 (n : ℕ) (hn : 0 < n) : seq n = exponentialForm n := by
  unfold seq exponentialForm
  congr 1
  rw [Real.cosh_eq]
  ring_nf

/-- Exercise 580, gap 2; exclude `n=0`. -/
theorem gap2 (n : ℕ) (hn : 0 < n) : scaledDifference n = squareForm n := by
  have hnR : (n : ℝ) ≠ 0 := by
    norm_num [Nat.ne_of_gt hn]
  have harg :
      Real.pi / (n : ℝ) =
        Real.pi / (2 * (n : ℝ)) + Real.pi / (2 * (n : ℝ)) := by
    field_simp [hnR]
    <;> ring
  have hneg :
      -Real.pi / (n : ℝ) =
        -Real.pi / (2 * (n : ℝ)) + -Real.pi / (2 * (n : ℝ)) := by
    field_simp [hnR]
    <;> ring
  have hprod :
      Real.exp (Real.pi / (2 * (n : ℝ))) *
          Real.exp (-Real.pi / (2 * (n : ℝ))) = 1 := by
    rw [← Real.exp_add]
    have hz :
        Real.pi / (2 * (n : ℝ)) + -Real.pi / (2 * (n : ℝ)) = 0 := by
      ring
    rw [hz, Real.exp_zero]
  unfold scaledDifference squareForm
  rw [harg, hneg, Real.exp_add, Real.exp_add]
  nlinarith [hprod]

/-- Exercise 580, gap 3; exclude `n=0`. -/
theorem gap3 (n : ℕ) (hn : 0 < n) : scaledDifference n = sineForm n := by
  have hnR : (n : ℝ) ≠ 0 := by
    norm_num [Nat.ne_of_gt hn]
  have harg :
      Real.pi / (n : ℝ) = 2 * (Real.pi / (2 * (n : ℝ))) := by
    field_simp [hnR]
    <;> ring
  have htrig :
      2 * (1 - Real.cos (Real.pi / (n : ℝ))) =
        4 * Real.sin (Real.pi / (2 * (n : ℝ))) ^ 2 := by
    rw [harg, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / (2 * (n : ℝ)))]
  rw [gap2 n hn]
  unfold squareForm sineForm
  rw [htrig]

/-- Exercise 580, gap 4; exclude `n=0`. -/
theorem gap4 (n : ℕ) (hn : 0 < n) : scaledDifference n = normalized n := by
  have hnR : (n : ℝ) ≠ 0 := by
    norm_num [Nat.ne_of_gt hn]
  rw [gap3 n hn]
  unfold sineForm normalized
  field_simp [hnR, Real.pi_ne_zero]
  <;> ring

/-- Exercise 580, gap 5. -/
theorem gap5 : Filter.Tendsto normalized Filter.atTop (nhds (2 * Real.pi ^ 2)) := by
  have hx' := tendsto_real_const_div_nat (Real.pi / 2)
  have hx :
      Filter.Tendsto
        (fun n : ℕ => Real.pi / (2 * (n : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [div_div] using hx'
  have hxpunc :
      Filter.Tendsto
        (fun n : ℕ => Real.pi / (2 * (n : ℝ)))
        Filter.atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hx, ?_⟩
    filter_upwards [eventually_nat_pos] with n hn
    have hnR : (n : ℝ) ≠ 0 := by
      norm_num [Nat.ne_of_gt hn]
    have hxne : Real.pi / (2 * (n : ℝ)) ≠ 0 :=
      div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num) hnR)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxne
  have hxm :
      Filter.Tendsto
        (fun n : ℕ => -Real.pi / (2 * (n : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [neg_div, neg_zero] using hx.neg
  have hxmin :
      Filter.Tendsto
        (fun n : ℕ => -Real.pi / (2 * (n : ℝ)))
        Filter.atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hxm, ?_⟩
    filter_upwards [eventually_nat_pos] with n hn
    have hnR : (n : ℝ) ≠ 0 := by
      norm_num [Nat.ne_of_gt hn]
    have hxmne : -Real.pi / (2 * (n : ℝ)) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr Real.pi_ne_zero)
        (mul_ne_zero (by norm_num) hnR)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmne
  have he :
      Filter.Tendsto
        (fun n : ℕ =>
          (Real.exp (Real.pi / (2 * (n : ℝ))) - 1) /
            (Real.pi / (2 * (n : ℝ))))
        Filter.atTop (nhds 1) :=
    tendsto_exp_sub_one_div_at_zero.comp hxpunc
  have hem :
      Filter.Tendsto
        (fun n : ℕ =>
          (Real.exp (-Real.pi / (2 * (n : ℝ))) - 1) /
            (-Real.pi / (2 * (n : ℝ))))
        Filter.atTop (nhds 1) :=
    tendsto_exp_sub_one_div_at_zero.comp hxmin
  have hs :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.sin (Real.pi / (2 * (n : ℝ))) /
            (Real.pi / (2 * (n : ℝ))))
        Filter.atTop (nhds 1) :=
    tendsto_sin_div_at_zero.comp hxpunc
  have hall :=
    (((he.mul_const (Real.pi / 2)).add
        (hem.mul_const (Real.pi / 2))).pow 2).add
      ((hs.pow 2).const_mul (Real.pi ^ 2))
  convert hall using 1 <;> norm_num <;> ring

/-- Exercise 580, gap 6. -/
theorem gap6 :
    Filter.Tendsto scaledDifference Filter.atTop (nhds (2 * Real.pi ^ 2)) := by
  refine gap5.congr' ?_
  filter_upwards [eventually_nat_pos] with n hn
  exact (gap4 n hn).symm

/-- Exercise 580, gap 7. -/
theorem gap7 : Filter.Tendsto seq Filter.atTop (nhds (Real.exp (Real.pi ^ 2))) := by
  let b : ℕ → ℝ := fun n =>
    (Real.exp (Real.pi / (n : ℝ)) + Real.exp (-Real.pi / (n : ℝ))) /
      (2 * Real.cos (Real.pi / (n : ℝ)))
  let u : ℕ → ℝ := fun n => b n - 1
  have hy :
      Filter.Tendsto (fun n : ℕ => Real.pi / (n : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_real_const_div_nat Real.pi
  have hep :
      Filter.Tendsto (fun n : ℕ => Real.exp (Real.pi / (n : ℝ)))
        Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hy
  have hyneg :
      Filter.Tendsto (fun n : ℕ => -Real.pi / (n : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [neg_div, neg_zero] using hy.neg
  have hem :
      Filter.Tendsto (fun n : ℕ => Real.exp (-Real.pi / (n : ℝ)))
        Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hyneg
  have hc :
      Filter.Tendsto (fun n : ℕ => Real.cos (Real.pi / (n : ℝ)))
        Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp hy
  have hden :
      Filter.Tendsto
        (fun n : ℕ => 2 * Real.cos (Real.pi / (n : ℝ)))
        Filter.atTop (nhds 2) := by
    simpa using (tendsto_const_nhds.mul hc)
  have hb : Filter.Tendsto b Filter.atTop (nhds 1) := by
    simpa [b] using
      (hep.add hem).div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hone :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hu0 : Filter.Tendsto u Filter.atTop (nhds 0) := by
    simpa [u] using hb.sub hone
  have hcospos :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 < Real.cos (Real.pi / (n : ℝ)) :=
    hc (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hq :
      Filter.Tendsto
        (fun n : ℕ =>
          scaledDifference n /
            (2 * Real.cos (Real.pi / (n : ℝ))))
        Filter.atTop (nhds (Real.pi ^ 2)) := by
    convert gap6.div hden (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> ring_nf
  have hsu :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ 2 * u n)
        Filter.atTop (nhds (Real.pi ^ 2)) := by
    refine hq.congr' ?_
    filter_upwards [hcospos] with n hncos
    have hcosne : Real.cos (Real.pi / (n : ℝ)) ≠ 0 := hncos.ne'
    dsimp [u, b]
    unfold scaledDifference
    field_simp [hcosne]
    <;> ring_nf
  have hspos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < (n : ℝ) ^ 2 * u n :=
    hsu (Ioi_mem_nhds (sq_pos_of_pos Real.pi_pos))
  have hupos : ∀ᶠ n : ℕ in Filter.atTop, 0 < u n := by
    filter_upwards [hspos] with n hn
    have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
    by_contra h
    have hu_nonpos : u n ≤ 0 := le_of_not_gt h
    nlinarith
  have hupunct :
      Filter.Tendsto u Filter.atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hu0, ?_⟩
    filter_upwards [hupos] with n hn
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hn.ne'
  have hratio :
      Filter.Tendsto
        (fun n : ℕ => Real.log (1 + u n) / u n)
        Filter.atTop (nhds 1) :=
    tendsto_log_one_add_div_at_zero.comp hupunct
  have hmul :
      Filter.Tendsto
        (fun n : ℕ =>
          (Real.log (1 + u n) / u n) * ((n : ℝ) ^ 2 * u n))
        Filter.atTop (nhds (Real.pi ^ 2)) := by
    simpa only [one_mul] using hratio.mul hsu
  have hlog :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ 2 * Real.log (b n))
        Filter.atTop (nhds (Real.pi ^ 2)) := by
    refine hmul.congr' ?_
    filter_upwards [hupos] with n hn
    have hune : u n ≠ 0 := hn.ne'
    rw [show 1 + u n = b n by simp [u]]
    field_simp [hune]
    <;> ring_nf
  have hexp :
      Filter.Tendsto
        (fun n : ℕ => Real.exp ((n : ℝ) ^ 2 * Real.log (b n)))
        Filter.atTop (nhds (Real.exp (Real.pi ^ 2))) :=
    (Real.continuous_exp.tendsto (Real.pi ^ 2)).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hupos, eventually_nat_pos] with n hun hn
  have hbpos : 0 < b n := by
    dsimp [u] at hun
    linarith
  calc
    Real.exp ((n : ℝ) ^ 2 * Real.log (b n)) =
        (Real.exp (Real.log (b n))) ^ (n ^ 2) := by
      rw [show (n : ℝ) ^ 2 = ((n ^ 2 : ℕ) : ℝ) by norm_num,
        Real.exp_nat_mul]
    _ = b n ^ (n ^ 2) := by rw [Real.exp_log hbpos]
    _ = exponentialForm n := by rfl
    _ = seq n := (gap1 n hn).symm

end

end ProofGap.Exercise580
