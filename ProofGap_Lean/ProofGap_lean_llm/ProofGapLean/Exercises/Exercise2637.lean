import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace ProofGap.Exercise2637

noncomputable section

open Filter

def ratio (n : ℕ) : ℝ :=
  Real.cosh (Real.pi / n) / Real.cos (Real.pi / n)

def term (n : ℕ) : ℝ :=
  Real.log (ratio n)

def localQuotient (x : ℝ) : ℝ :=
  (Real.cosh (Real.pi * x) - Real.cos (Real.pi * x)) / x ^ 2

private theorem ratio_gt_one (n : ℕ) (hn : 3 ≤ n) : 1 < ratio n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have htheta_pos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnpos
  have htheta_lt : Real.pi / (n : ℝ) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ hnpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos (Real.pi / (n : ℝ)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htheta_lt⟩
  unfold ratio
  rw [one_lt_div hcos]
  exact (Real.cos_le_one _).trans_lt (Real.one_lt_cosh.2 htheta_pos.ne')

private theorem secondDerivativeLimit :
    Tendsto
      (fun x : ℝ =>
        (Real.pi ^ 2 * Real.cosh (Real.pi * x) +
          Real.pi ^ 2 * Real.cos (Real.pi * x)) / 2)
      (nhds 0) (nhds (Real.pi ^ 2)) := by
  have hcont : ContinuousAt
      (fun x : ℝ =>
        (Real.pi ^ 2 * Real.cosh (Real.pi * x) +
          Real.pi ^ 2 * Real.cos (Real.pi * x)) / 2) 0 := by
    fun_prop
  simpa using hcont.tendsto

private theorem firstDerivativeLimit :
    Tendsto
      (fun x : ℝ =>
        (Real.pi * Real.sinh (Real.pi * x) +
          Real.pi * Real.sin (Real.pi * x)) / (2 * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.pi ^ 2)) := by
  apply HasDerivAt.lhopital_zero_nhds
    (f' := fun x =>
      Real.pi ^ 2 * Real.cosh (Real.pi * x) +
        Real.pi ^ 2 * Real.cos (Real.pi * x))
    (g' := fun _ => 2)
  · exact Filter.Eventually.of_forall fun x => by
      convert
        ((((hasDerivAt_id x).const_mul Real.pi).sinh.const_mul Real.pi).add
          (((hasDerivAt_id x).const_mul Real.pi).sin.const_mul Real.pi)) using 1 <;>
        simp only [id_eq] <;> ring
  · exact Filter.Eventually.of_forall fun x => by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  · simp
  · have hcont : ContinuousAt
        (fun x : ℝ =>
          Real.pi * Real.sinh (Real.pi * x) +
            Real.pi * Real.sin (Real.pi * x)) 0 := by
      fun_prop
    simpa using hcont.tendsto
  · have hcont : ContinuousAt (fun x : ℝ => 2 * x) 0 := by fun_prop
    simpa using hcont.tendsto
  · exact secondDerivativeLimit

private theorem localQuotientLimit :
    Tendsto localQuotient (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (Real.pi ^ 2)) := by
  unfold localQuotient
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun x =>
      Real.pi * Real.sinh (Real.pi * x) +
        Real.pi * Real.sin (Real.pi * x))
    (g' := fun x => 2 * x)
  · exact Filter.Eventually.of_forall fun x => by
      convert
        (((hasDerivAt_id x).const_mul Real.pi).cosh.sub
          ((hasDerivAt_id x).const_mul Real.pi).cos) using 1 <;>
        simp only [id_eq] <;> ring
  · exact Filter.Eventually.of_forall fun x => by
      convert (hasDerivAt_id x).pow 2 using 1 <;> simp only [id_eq] <;> ring
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ 0)
    exact mul_ne_zero (by norm_num) hx
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have hcont : ContinuousAt
        (fun x : ℝ => Real.cosh (Real.pi * x) - Real.cos (Real.pi * x)) 0 := by
      fun_prop
    simpa using hcont.tendsto
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have hcont : ContinuousAt (fun x : ℝ => x ^ 2) 0 := by fun_prop
    simpa using hcont.tendsto
  · exact firstDerivativeLimit

theorem gap1 (n : ℕ) (hn : 3 ≤ n) :
    term n =
      (ratio n - 1) *
        Real.log (Real.rpow (1 + (ratio n - 1)) (1 / (ratio n - 1))) := by
  have hr : 1 < ratio n := ratio_gt_one n hn
  have hrpos : 0 < 1 + (ratio n - 1) := by linarith
  have hrne : ratio n - 1 ≠ 0 := sub_ne_zero.mpr hr.ne'
  unfold term
  have hlog :
      Real.log (Real.rpow (1 + (ratio n - 1)) (1 / (ratio n - 1))) =
        (1 / (ratio n - 1)) * Real.log (1 + (ratio n - 1)) := by
    simpa only using Real.log_rpow hrpos (1 / (ratio n - 1))
  rw [hlog, show 1 + (ratio n - 1) = ratio n by ring]
  field_simp

theorem gap2 :
    Tendsto (fun n : ℕ => ratio (n + 3) - 1) atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => Real.pi / ((n + 3 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa [Nat.cast_add] using
      ((tendsto_add_atTop_iff_nat 3).2
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) Real.pi))
  have hcosh : Tendsto (fun n : ℕ => Real.cosh (Real.pi / ((n + 3 : ℕ) : ℝ)))
      atTop (nhds 1) := by
    simpa using Real.continuous_cosh.continuousAt.tendsto.comp hx
  have hcos : Tendsto (fun n : ℕ => Real.cos (Real.pi / ((n + 3 : ℕ) : ℝ)))
      atTop (nhds 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hx
  have hr : Tendsto (fun n : ℕ => ratio (n + 3)) atTop (nhds 1) := by
    unfold ratio
    simpa only [Pi.div_apply, div_one] using hcosh.div hcos one_ne_zero
  convert hr.sub_const 1 using 1 <;> norm_num

theorem gap3 :
    Tendsto localQuotient (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (Real.pi ^ 2)) ∧
    Tendsto
      (fun x : ℝ =>
        (Real.pi * Real.sinh (Real.pi * x) +
          Real.pi * Real.sin (Real.pi * x)) / (2 * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.pi ^ 2)) := by
  exact ⟨localQuotientLimit, firstDerivativeLimit⟩

theorem gap4 :
    Tendsto
      (fun x : ℝ =>
        (Real.pi * Real.sinh (Real.pi * x) +
          Real.pi * Real.sin (Real.pi * x)) / (2 * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.pi ^ 2)) ∧
    Tendsto
      (fun x : ℝ =>
        (Real.pi ^ 2 * Real.cosh (Real.pi * x) +
          Real.pi ^ 2 * Real.cos (Real.pi * x)) / 2)
      (nhds 0) (nhds (Real.pi ^ 2)) := by
  exact ⟨firstDerivativeLimit, secondDerivativeLimit⟩

theorem gap5 :
    Tendsto
      (fun x : ℝ =>
        (Real.pi ^ 2 * Real.cosh (Real.pi * x) +
          Real.pi ^ 2 * Real.cos (Real.pi * x)) / 2)
      (nhds 0) (nhds (Real.pi ^ 2)) := by
  exact secondDerivativeLimit

theorem gap6 :
    Tendsto localQuotient (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (Real.pi ^ 2)) := by
  exact localQuotientLimit

theorem gap7 :
    Tendsto
      (fun n : ℕ => term (n + 3) / (1 / ((n + 3 : ℕ) : ℝ) ^ 2))
      atTop (nhds ((1 : ℝ) * Real.pi ^ 2 * 1)) := by
  let x : ℕ → ℝ := fun n => 1 / ((n + 3 : ℕ) : ℝ)
  have hx : Tendsto x atTop (nhds 0) := by
    simpa [x, Nat.cast_add] using
      ((tendsto_add_atTop_iff_nat 3).2
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hxne : ∀ n, x n ≠ 0 := fun n => by
    dsimp [x]
    positivity
  have hxpunct : Tendsto x atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Filter.Eventually.of_forall fun n => by
      simpa using hxne n⟩
  have hlocal : Tendsto (fun n => localQuotient (x n)) atTop (nhds (Real.pi ^ 2)) :=
    gap6.comp hxpunct
  have hcos : Tendsto (fun n => Real.cos (Real.pi * x n)) atTop (nhds 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hx)
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          (ratio (n + 3) - 1) / (1 / ((n + 3 : ℕ) : ℝ) ^ 2))
        atTop (nhds (Real.pi ^ 2)) := by
    have h := hlocal.div hcos one_ne_zero
    convert h using 1
    · funext n
      have hnpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by positivity
      have htheta_pos : 0 < Real.pi / ((n + 3 : ℕ) : ℝ) :=
        div_pos Real.pi_pos hnpos
      have htheta_lt : Real.pi / ((n + 3 : ℕ) : ℝ) < Real.pi / 2 := by
        rw [div_lt_div_iff₀ hnpos (by norm_num : (0 : ℝ) < 2)]
        have hnthree : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
          exact_mod_cast (show 3 ≤ n + 3 by omega)
        nlinarith [Real.pi_pos]
      have hcospos : 0 < Real.cos (Real.pi / ((n + 3 : ℕ) : ℝ)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htheta_lt⟩
      change
        (ratio (n + 3) - 1) / (1 / ((n + 3 : ℕ) : ℝ) ^ 2) =
          localQuotient (x n) / Real.cos (Real.pi * x n)
      dsimp [x, ratio, localQuotient]
      rw [show Real.pi * (1 / (((n + 3 : ℕ) : ℝ))) =
        Real.pi / ((n + 3 : ℕ) : ℝ) by ring]
      field_simp [hcospos.ne', hnpos.ne'] <;> ring
    · ring
  have hratio : Tendsto (fun n : ℕ => ratio (n + 3)) atTop (nhds 1) := by
    convert gap2.add_const 1 using 1 <;> ring
  have hrne : ∀ n : ℕ, ratio (n + 3) ≠ 1 := fun n =>
    (ratio_gt_one (n + 3) (by omega)).ne'
  have hrpunct :
      Tendsto (fun n : ℕ => ratio (n + 3)) atTop (nhdsWithin 1 ({1} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨hratio, Filter.Eventually.of_forall fun n => by
      simpa using hrne n⟩
  have hlog :
      Tendsto (fun n : ℕ => term (n + 3) / (ratio (n + 3) - 1)) atTop (nhds 1) := by
    have h := (Real.hasDerivAt_log one_ne_zero).tendsto_slope.comp hrpunct
    simpa [Function.comp_def, slope_def_module, term, div_eq_mul_inv, mul_comm] using h
  have hproduct := hlog.mul hnormalized
  convert hproduct using 1
  · funext n
    have hr : ratio (n + 3) - 1 ≠ 0 := sub_ne_zero.mpr (hrne n)
    have hn : (1 / (((n + 3 : ℕ) : ℝ) ^ 2)) ≠ 0 := by positivity
    field_simp
  · ring

theorem gap8 :
    (1 : ℝ) * Real.pi ^ 2 * 1 = Real.pi ^ 2 := by ring

theorem gap9 :
    Tendsto
      (fun n : ℕ => term (n + 3) / (1 / ((n + 3 : ℕ) : ℝ) ^ 2))
      atTop (nhds (Real.pi ^ 2)) := by
  simpa using gap7

theorem gap10 :
    ∃ K > 0, ∃ N : ℕ, ∀ n ≥ N,
      |term n / (1 / (n : ℝ) ^ 2)| ≤ K := by
  let f : ℕ → ℝ := fun n => term n / (1 / (n : ℝ) ^ 2)
  have hf : Tendsto f atTop (nhds (Real.pi ^ 2)) := by
    apply (tendsto_add_atTop_iff_nat 3).1
    simpa [f, Nat.cast_add] using gap9
  rcases (Metric.tendsto_atTop.1 hf) 1 zero_lt_one with ⟨N, hN⟩
  refine ⟨|Real.pi ^ 2| + 1, by positivity, N, ?_⟩
  intro n hn
  have hdist := hN n hn
  rw [Real.dist_eq] at hdist
  calc
    |term n / (1 / (n : ℝ) ^ 2)| = |f n| := rfl
    _ = |(f n - Real.pi ^ 2) + Real.pi ^ 2| := by ring_nf
    _ ≤ |f n - Real.pi ^ 2| + |Real.pi ^ 2| := abs_add_le _ _
    _ ≤ |Real.pi ^ 2| + 1 := by linarith

theorem gap11 :
    ∃ K > 0, ∀ n ≥ 1, |term n| ≤ K * (1 / (n : ℝ) ^ 2) := by
  rcases gap10 with ⟨K₀, hK₀, N, hN⟩
  let K : ℝ := K₀ + ∑ n ∈ Finset.range N, |term n / (1 / (n : ℝ) ^ 2)|
  have hsum_nonneg :
      0 ≤ ∑ n ∈ Finset.range N, |term n / (1 / (n : ℝ) ^ 2)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro n hn
  have hden : 0 < 1 / (n : ℝ) ^ 2 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hratio : |term n / (1 / (n : ℝ) ^ 2)| ≤ K := by
    by_cases hlarge : N ≤ n
    · exact (hN n hlarge).trans (by dsimp [K]; linarith)
    · have hnmem : n ∈ Finset.range N := Finset.mem_range.2 (lt_of_not_ge hlarge)
      have hsingle :
          |term n / (1 / (n : ℝ) ^ 2)| ≤
            ∑ i ∈ Finset.range N, |term i / (1 / (i : ℝ) ^ 2)| :=
        Finset.single_le_sum (s := Finset.range N)
          (f := fun i => |term i / (1 / (i : ℝ) ^ 2)|)
          (fun i _ => abs_nonneg _) hnmem
      dsimp [K]
      linarith
  rw [abs_div, abs_of_pos hden] at hratio
  exact (div_le_iff₀ hden).1 hratio

theorem gap12 :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa using (summable_nat_add_iff 1).2 hp

theorem gap13 :
    Summable (fun n : ℕ => term (n + 1)) := by
  rcases gap11 with ⟨K, hK, hbound⟩
  refine Summable.of_norm_bounded (gap12.mul_left K) ?_
  intro n
  simpa [Real.norm_eq_abs] using hbound (n + 1) (by omega)

theorem gap14 :
    Summable (fun n : ℕ => term (n + 1)) := by
  exact gap13

end

end ProofGap.Exercise2637
