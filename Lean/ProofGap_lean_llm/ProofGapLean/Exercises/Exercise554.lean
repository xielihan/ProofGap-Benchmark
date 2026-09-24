import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise554

noncomputable section

def seq (a b : ℝ) (n : ℕ) : ℝ :=
  Real.rpow ((a - 1 + Real.rpow b (1 / (n : ℝ))) / a) n
def rewritten (a b : ℝ) (n : ℕ) : ℝ :=
  let d := Real.rpow b (1 / (n : ℝ)) - 1
  Real.rpow (1 + 1 / (a / d))
    ((a / d) * (d / (1 / (n : ℝ))) * (1 / a))

/-- Source: `proof_gap/exercise_554/1.txt`; require `b≠1` for the displayed substitution. -/
private theorem explicit_rpow_def_of_pos (x y : ℝ) (hx : 0 < x) :
    Real.rpow x y = Real.exp (Real.log x * y) := by
  change x ^ y = Real.exp (Real.log x * y)
  exact Real.rpow_def_of_pos hx y

private theorem exp_sub_one_div_tendsto :
    Filter.Tendsto (fun x : ℝ => (Real.exp x - 1) / x)
      (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp 0)
  have h' : Filter.Tendsto (slope Real.exp 0)
      (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
    simpa only [Real.exp_zero] using h
  have hslope :
      (fun x : ℝ => (Real.exp x - 1) / x) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
        slope Real.exp 0 := by
    apply Filter.Eventually.of_forall
    intro x
    simp [slope, Real.exp_zero, div_eq_mul_inv, mul_comm]
  exact h'.congr' hslope.symm

private theorem log_one_add_div_tendsto :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
      (hasDerivAt_id (x := (0 : ℝ))) using 1 <;> norm_num
  have hderiv : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    convert
      (Real.hasDerivAt_log (x := (1 + (0 : ℝ))) (by norm_num)).comp 0 hinner
      using 1 <;> norm_num
  have h := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hslope :
      (fun x : ℝ => Real.log (1 + x) / x) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
        slope (fun x : ℝ => Real.log (1 + x)) 0 := by
    apply Filter.Eventually.of_forall
    intro x
    simp [slope, Real.log_one, div_eq_mul_inv, mul_comm]
  exact h.congr' hslope.symm

private theorem substitution_base (a d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) :
    (a - 1 + (d + 1)) / a = 1 + 1 / (a / d) := by
  field_simp [ha, hd]
  ring

private theorem substitution_exponent (a d : ℝ) (n : ℕ)
    (ha : a ≠ 0) (hd : d ≠ 0) (hn : (n : ℝ) ≠ 0) :
    (a / d) * (d / (1 / (n : ℝ))) * (1 / a) = (n : ℝ) := by
  field_simp [ha, hd, hn]

private theorem quotient_rescale (l d a : ℝ) (ha : a ≠ 0) :
    (l / (d / a)) / a = l / d := by
  by_cases hd : d = 0
  · simp [hd]
  · field_simp [ha, hd]

private theorem quotient_product_cancel (d t l : ℝ) (hd : d ≠ 0) :
    (d / t) * (l / d) = l / t := by
  field_simp [hd]

private theorem div_one_div_eq (l x : ℝ) :
    l / (1 / x) = x * l := by
  simp [div_eq_mul_inv, mul_comm]

private theorem seq_rewritten_eventuallyEq (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hb1 : b ≠ 1) :
    seq a b =ᶠ[Filter.atTop] rewritten a b := by
  have hlog : Real.log b ≠ 0 := by
    intro h
    apply hb1
    calc
      b = Real.exp (Real.log b) := (Real.exp_log hb).symm
      _ = Real.exp 0 := by rw [h]
      _ = 1 := Real.exp_zero
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have ht0 : (1 / (n : ℝ)) ≠ 0 := one_div_ne_zero hn0
  have hd : Real.rpow b (1 / (n : ℝ)) - 1 ≠ 0 := by
    rw [explicit_rpow_def_of_pos b (1 / (n : ℝ)) hb, sub_ne_zero]
    intro he
    have hz : Real.log b * (1 / (n : ℝ)) = 0 := by
      apply Real.exp_injective
      simpa using he
    exact hlog ((mul_eq_zero.mp hz).resolve_right ht0)
  unfold seq rewritten
  dsimp
  apply congrArg₂ Real.rpow
  · simpa only [sub_add_cancel] using
      substitution_base a (Real.rpow b (1 / (n : ℝ)) - 1) ha.ne' hd
  · exact (substitution_exponent a (Real.rpow b (1 / (n : ℝ)) - 1) n
      ha.ne' hd hn0).symm

private theorem seq_one_tendsto (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (seq a 1) Filter.atTop (nhds 1) := by
  have hs : seq a 1 = fun _ : ℕ => (1 : ℝ) := by
    funext n
    unfold seq
    rw [explicit_rpow_def_of_pos 1 (1 / (n : ℝ)) (by norm_num)]
    simp only [Real.log_one, zero_mul, Real.exp_zero]
    have hbase : (a - 1 + 1) / a = 1 := by
      field_simp [ha.ne']
      ring
    rw [hbase, explicit_rpow_def_of_pos 1 (n : ℝ) (by norm_num)]
    simp
  rw [hs]
  exact tendsto_const_nhds

private theorem seq_tendsto_exp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto (seq a b) Filter.atTop
      (nhds (Real.exp ((1 / a) * Real.log b))) := by
  by_cases hb1 : b = 1
  · subst b
    simpa using seq_one_tendsto a ha
  have hlog : Real.log b ≠ 0 := by
    intro h
    apply hb1
    calc
      b = Real.exp (Real.log b) := (Real.exp_log hb).symm
      _ = Real.exp 0 := by rw [h]
      _ = 1 := Real.exp_zero
  have ht : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0))
  have htne : ∀ᶠ n : ℕ in Filter.atTop, (1 / (n : ℝ)) ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  have hconstLog : Filter.Tendsto (fun _ : ℕ => Real.log b) Filter.atTop
      (nhds (Real.log b)) := tendsto_const_nhds
  have hz : Filter.Tendsto
      (fun n : ℕ => Real.log b * (1 / (n : ℝ))) Filter.atTop (nhds 0) := by
    simpa using hconstLog.mul ht
  have hz' : Filter.Tendsto
      (fun n : ℕ => Real.log b * (1 / (n : ℝ))) Filter.atTop
      (nhdsWithin 0 ({0}ᶜ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hz, ?_⟩
    filter_upwards [htne] with n hn
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using mul_ne_zero hlog hn
  have hq1 : Filter.Tendsto
      (fun n : ℕ =>
        (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / (1 / (n : ℝ)))
      Filter.atTop (nhds (Real.log b)) := by
    have h : Filter.Tendsto
        (fun n : ℕ => Real.log b *
          ((Real.exp (Real.log b * (1 / (n : ℝ))) - 1) /
            (Real.log b * (1 / (n : ℝ)))))
        Filter.atTop (nhds (Real.log b)) := by
      simpa [Function.comp_apply] using
        hconstLog.mul (exp_sub_one_div_tendsto.comp hz')
    refine h.congr' ?_
    filter_upwards [htne] with n hn
    field_simp [hlog, hn]
  have hd : Filter.Tendsto
      (fun n : ℕ => Real.exp (Real.log b * (1 / (n : ℝ))) - 1)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.exp_zero, sub_self] using
      (Real.continuous_exp.continuousAt.tendsto.comp hz).sub
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1))
  have hx : Filter.Tendsto
      (fun n : ℕ =>
        (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a)
      Filter.atTop (nhds 0) := by
    simpa [ha.ne'] using hd.div_const a
  have hxne : ∀ᶠ n : ℕ in Filter.atTop,
      (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a ≠ 0 := by
    filter_upwards [htne] with n hn
    have hz0 : Real.log b * (1 / (n : ℝ)) ≠ 0 := mul_ne_zero hlog hn
    have hd0 : Real.exp (Real.log b * (1 / (n : ℝ))) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro he
      apply hz0
      apply Real.exp_injective
      simpa using he
    exact div_ne_zero hd0 ha.ne'
  have hx' : Filter.Tendsto
      (fun n : ℕ =>
        (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a)
      Filter.atTop (nhdsWithin 0 ({0}ᶜ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hx, ?_⟩
    filter_upwards [hxne] with n hn
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hn
  have hq2 : Filter.Tendsto
      (fun n : ℕ =>
        Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) /
          (Real.exp (Real.log b * (1 / (n : ℝ))) - 1))
      Filter.atTop (nhds (1 / a)) := by
    have h := (log_one_add_div_tendsto.comp hx').div_const a
    apply h.congr'
    filter_upwards with n
    change
      (Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) /
          ((Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a)) / a =
        Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) /
          (Real.exp (Real.log b * (1 / (n : ℝ))) - 1)
    exact quotient_rescale
      (Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a))
      (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) a ha.ne'
  have hE : Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) * Real.log
          (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a))
      Filter.atTop (nhds ((1 / a) * Real.log b)) := by
    have h := hq1.mul hq2
    have h' : Filter.Tendsto
        (fun n : ℕ =>
          (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / (1 / (n : ℝ)) *
            (Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) /
              (Real.exp (Real.log b * (1 / (n : ℝ))) - 1)))
        Filter.atTop (nhds ((1 / a) * Real.log b)) := by
      simpa [mul_comm] using h
    apply h'.congr'
    filter_upwards [htne] with n hn
    have hz0 : Real.log b * (1 / (n : ℝ)) ≠ 0 := mul_ne_zero hlog hn
    have hd0 : Real.exp (Real.log b * (1 / (n : ℝ))) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro he
      apply hz0
      apply Real.exp_injective
      simpa using he
    calc
      (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / (1 / (n : ℝ)) *
          (Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) /
            (Real.exp (Real.log b * (1 / (n : ℝ))) - 1)) =
        Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) /
          (1 / (n : ℝ)) :=
        quotient_product_cancel
          (Real.exp (Real.log b * (1 / (n : ℝ))) - 1)
          (1 / (n : ℝ))
          (Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a)) hd0
      _ = (n : ℝ) * Real.log
          (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) :=
        div_one_div_eq
          (Real.log (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a))
          (n : ℝ)
  have hbase : Filter.Tendsto
      (fun n : ℕ =>
        1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a)
      Filter.atTop (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.add hx
  have hbasepos : ∀ᶠ n : ℕ in Filter.atTop,
      0 < 1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a := by
    apply hbase.eventually
    exact isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hE
  apply hexp.congr'
  filter_upwards [hbasepos] with n hn
  simp only [Function.comp_apply]
  unfold seq
  rw [explicit_rpow_def_of_pos b (1 / (n : ℝ)) hb]
  have hbaseeq :
      (a - 1 + Real.exp (Real.log b * (1 / (n : ℝ)))) / a =
        1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a := by
    field_simp [ha.ne']
    ring
  rw [hbaseeq,
    explicit_rpow_def_of_pos
      (1 + (Real.exp (Real.log b * (1 / (n : ℝ))) - 1) / a) (n : ℝ) hn]
  congr 1
  ring

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) (L : ℝ) :
    Filter.Tendsto (seq a b) Filter.atTop (nhds L) ↔
      Filter.Tendsto (rewritten a b) Filter.atTop (nhds L) := by
  constructor
  · intro h
    exact h.congr' (seq_rewritten_eventuallyEq a b ha hb hb1)
  · intro h
    exact h.congr' (seq_rewritten_eventuallyEq a b ha hb hb1).symm

/-- Source: `proof_gap/exercise_554/2.txt`; require `b≠1` for the substitution denominator. -/
theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) :
    Filter.Tendsto (rewritten a b) Filter.atTop
      (nhds (Real.exp ((1 / a) * Real.log b))) := by
  exact (gap1 a b ha hb hb1 (Real.exp ((1 / a) * Real.log b))).mp
    (seq_tendsto_exp a b ha hb)

/-- Source: `proof_gap/exercise_554/3.txt`. -/
theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.exp ((1 / a) * Real.log b) = Real.rpow b (1 / a) := by
  rw [explicit_rpow_def_of_pos b (1 / a) hb]
  congr 1
  ring

/-- Source: `proof_gap/exercise_554/4.txt`; the final result also covers `b=1`. -/
theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto (seq a b) Filter.atTop (nhds (Real.rpow b (1 / a))) := by
  by_cases hb1 : b = 1
  · subst b
    rw [explicit_rpow_def_of_pos 1 (1 / a) (by norm_num)]
    simp only [Real.log_one, zero_mul, Real.exp_zero]
    exact seq_one_tendsto a ha
  · rw [← gap3 a b ha hb]
    exact (gap1 a b ha hb hb1 (Real.exp ((1 / a) * Real.log b))).mpr
      (gap2 a b ha hb hb1)

end

end ProofGap.Exercise554
