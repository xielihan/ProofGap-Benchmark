import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise504

noncomputable section

def cubeRoot (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def original (x : ℝ) : ℝ :=
  (1 - Real.cos x * Real.sqrt (Real.cos (2 * x)) *
    cubeRoot (Real.cos (3 * x))) / x ^ 2
def split1 (x : ℝ) : ℝ :=
  (1 - Real.cos x + Real.cos x *
    (1 - Real.sqrt (Real.cos (2 * x)) * cubeRoot (Real.cos (3 * x)))) / x ^ 2
def split2 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) +
    (1 - Real.sqrt (Real.cos (2 * x)) +
      Real.sqrt (Real.cos (2 * x)) * (1 - cubeRoot (Real.cos (3 * x)))) / x ^ 2
def split3 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) +
    (1 - Real.cos (2 * x)) /
      (x ^ 2 * (1 + Real.sqrt (Real.cos (2 * x)))) +
    (1 - Real.cos (3 * x)) /
      (x ^ 2 * (1 + cubeRoot (Real.cos (3 * x)) +
        cubeRoot (Real.cos (3 * x) ^ 2)))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 504, gap 1; remove the shadowed outer `x` and its irrelevant interval premise. -/
private theorem tendsto_mul_punctured (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto (fun x : ℝ => a * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  have hnhds : Filter.Tendsto (fun x : ℝ => a * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      (((continuousAt_const : ContinuousAt (fun _ : ℝ => a) 0).mul
        (continuousAt_id : ContinuousAt (fun x : ℝ => x) 0)).mono_left
          inf_le_left)
  refine tendsto_nhdsWithin_iff.mpr ⟨hnhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
  exact mul_ne_zero ha hx

private theorem tendsto_scaled_one_sub_cos (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto
      (fun x : ℝ => (1 - Real.cos (a * x)) / x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (a ^ 2 / 2)) := by
  have hab : a / 2 ≠ 0 := div_ne_zero ha (by norm_num)
  have harg : Filter.Tendsto (fun x : ℝ => (a / 2) * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      (((continuousAt_const : ContinuousAt (fun _ : ℝ => a / 2) 0).mul
        (continuousAt_id : ContinuousAt (fun x : ℝ => x) 0)).mono_left
          inf_le_left)
  have hsinc_at : Filter.Tendsto Real.sinc (nhds (0 : ℝ))
      (nhds (Real.sinc 0)) := Real.continuous_sinc.continuousAt
  have hsinc_zero : Real.sinc (0 : ℝ) = 1 := by
    simp [Real.sinc]
  have hsinc : Filter.Tendsto
      (fun x : ℝ => Real.sinc ((a / 2) * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    rw [← hsinc_zero]
    exact Filter.Tendsto.comp hsinc_at harg
  have hsin : Filter.Tendsto
      (fun x : ℝ => Real.sin ((a / 2) * x) / ((a / 2) * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    apply hsinc.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    have hz : (a / 2) * x ≠ 0 := mul_ne_zero hab hx
    simp [Real.sinc, hz]
  have hc : Filter.Tendsto (fun _ : ℝ => a ^ 2 / 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (a ^ 2 / 2)) :=
    tendsto_const_nhds
  have hlim := hc.mul (hsin.pow 2)
  have heq :
      (fun x : ℝ =>
        (a ^ 2 / 2) *
          (Real.sin ((a / 2) * x) / ((a / 2) * x)) ^ 2) =ᶠ[
            nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x : ℝ => (1 - Real.cos (a * x)) / x ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    have harg : a * x = 2 * ((a / 2) * x) := by ring
    have htrig :
        1 - Real.cos (a * x) =
          2 * Real.sin ((a / 2) * x) ^ 2 := by
      rw [harg, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq ((a / 2) * x)]
    rw [htrig]
    field_simp [ha, hx]
  have ht := hlim.congr' heq
  convert ht using 1 <;> ring_nf

private theorem tendsto_cos_mul (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.cos (a * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have harg : Filter.Tendsto (fun x : ℝ => a * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      (((continuousAt_const : ContinuousAt (fun _ : ℝ => a) 0).mul
        (continuousAt_id : ContinuousAt (fun x : ℝ => x) 0)).mono_left
          inf_le_left)
  have hcos : Filter.Tendsto Real.cos (nhds (0 : ℝ))
      (nhds (Real.cos 0)) := Real.continuous_cos.continuousAt
  simpa using Filter.Tendsto.comp hcos harg

private theorem cubeRoot_eq_exp {y : ℝ} (hy : 0 < y) :
    cubeRoot y = Real.exp (Real.log y * (1 / 3 : ℝ)) := by
  unfold cubeRoot
  change Real.rpow y (1 / 3 : ℝ) =
    Real.exp (Real.log y * (1 / 3 : ℝ))
  exact Real.rpow_def_of_pos hy (1 / 3 : ℝ)

private theorem tendsto_cubeRoot_one {l : Filter ℝ} {f : ℝ → ℝ}
    (hf : Filter.Tendsto f l (nhds 1)) :
    Filter.Tendsto (fun x => cubeRoot (f x)) l (nhds 1) := by
  have hlog_at : Filter.Tendsto Real.log (nhds (1 : ℝ))
      (nhds (Real.log 1)) :=
    Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hlog : Filter.Tendsto (fun x => Real.log (f x)) l (nhds 0) := by
    simpa using Filter.Tendsto.comp hlog_at hf
  have hc : Filter.Tendsto (fun _ : ℝ => (1 / 3 : ℝ)) l
      (nhds (1 / 3 : ℝ)) := tendsto_const_nhds
  have hprod : Filter.Tendsto
      (fun x => Real.log (f x) * (1 / 3 : ℝ)) l (nhds 0) := by
    simpa using hlog.mul hc
  have hexp_at : Filter.Tendsto Real.exp (nhds (0 : ℝ))
      (nhds (Real.exp 0)) := Real.continuous_exp.continuousAt
  have hexp : Filter.Tendsto
      (fun x => Real.exp (Real.log (f x) * (1 / 3 : ℝ))) l
      (nhds 1) := by
    simpa using Filter.Tendsto.comp hexp_at hprod
  have hpos : ∀ᶠ x in l, 0 < f x :=
    hf (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq :
      (fun x => Real.exp (Real.log (f x) * (1 / 3 : ℝ))) =ᶠ[l]
      (fun x => cubeRoot (f x)) := by
    filter_upwards [hpos] with x hx
    exact (cubeRoot_eq_exp hx).symm
  exact hexp.congr' heq

private theorem cubeRoot_pow_three {y : ℝ} (hy : 0 < y) :
    cubeRoot y ^ 3 = y := by
  rw [cubeRoot_eq_exp hy, ← Real.exp_nat_mul]
  convert Real.exp_log hy using 1 <;> ring_nf

private theorem tendsto_sqrt_one {l : Filter ℝ} {f : ℝ → ℝ}
    (hf : Filter.Tendsto f l (nhds 1)) :
    Filter.Tendsto (fun x => Real.sqrt (f x)) l (nhds 1) := by
  have hsqrt_at : Filter.Tendsto Real.sqrt (nhds (1 : ℝ))
      (nhds (Real.sqrt 1)) := Real.continuous_sqrt.continuousAt
  simpa using Filter.Tendsto.comp hsqrt_at hf

private theorem sqrt_quotient_limit :
    Filter.Tendsto
      (fun x : ℝ =>
        (1 - Real.sqrt (Real.cos (2 * x))) / x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hbase := tendsto_scaled_one_sub_cos 2 (by norm_num)
  have hcos := tendsto_cos_mul 2
  have hsqrt : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.cos (2 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_sqrt_one hcos
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hden : Filter.Tendsto
      (fun x : ℝ => 1 + Real.sqrt (Real.cos (2 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    convert hone.add hsqrt using 1 <;> norm_num
  have hraw : Filter.Tendsto
      (fun x : ℝ =>
        ((1 - Real.cos (2 * x)) / x ^ 2) /
          (1 + Real.sqrt (Real.cos (2 * x))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert hbase.div hden (by norm_num : (2 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hpos : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < Real.cos (2 * x) :=
    hcos (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq :
      (fun x : ℝ =>
        ((1 - Real.cos (2 * x)) / x ^ 2) /
          (1 + Real.sqrt (Real.cos (2 * x)))) =ᶠ[
            nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x : ℝ =>
        (1 - Real.sqrt (Real.cos (2 * x))) / x ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hx hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    have hsq := Real.sq_sqrt (le_of_lt hy)
    have hd : 1 + Real.sqrt (Real.cos (2 * x)) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (Real.cos (2 * x))]
    have hfactor :
        (1 - Real.sqrt (Real.cos (2 * x))) *
            (1 + Real.sqrt (Real.cos (2 * x))) =
          1 - Real.cos (2 * x) := by
      nlinarith [hsq]
    field_simp [hx, hd]
    nlinarith [hfactor]
  exact hraw.congr' heq

private theorem cube_quotient_limit :
    Filter.Tendsto
      (fun x : ℝ =>
        (1 - cubeRoot (Real.cos (3 * x))) / x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2 : ℝ)) := by
  have hbase := tendsto_scaled_one_sub_cos 3 (by norm_num)
  have hcos := tendsto_cos_mul 3
  have hroot : Filter.Tendsto
      (fun x : ℝ => cubeRoot (Real.cos (3 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_cubeRoot_one hcos
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hden : Filter.Tendsto
      (fun x : ℝ =>
        1 + cubeRoot (Real.cos (3 * x)) +
          cubeRoot (Real.cos (3 * x)) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 3) := by
    convert (hone.add hroot).add (hroot.pow 2) using 1 <;> norm_num
  have hraw : Filter.Tendsto
      (fun x : ℝ =>
        ((1 - Real.cos (3 * x)) / x ^ 2) /
          (1 + cubeRoot (Real.cos (3 * x)) +
            cubeRoot (Real.cos (3 * x)) ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2 : ℝ)) := by
    convert hbase.div hden (by norm_num : (3 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hpos : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < Real.cos (3 * x) :=
    hcos (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq :
      (fun x : ℝ =>
        ((1 - Real.cos (3 * x)) / x ^ 2) /
          (1 + cubeRoot (Real.cos (3 * x)) +
            cubeRoot (Real.cos (3 * x)) ^ 2)) =ᶠ[
            nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x : ℝ =>
        (1 - cubeRoot (Real.cos (3 * x))) / x ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hx hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    have hd :
        1 + cubeRoot (Real.cos (3 * x)) +
          cubeRoot (Real.cos (3 * x)) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg
        (cubeRoot (Real.cos (3 * x)) + (1 / 2 : ℝ))]
    have hp := cubeRoot_pow_three hy
    have hfactor :
        (1 - cubeRoot (Real.cos (3 * x))) *
            (1 + cubeRoot (Real.cos (3 * x)) +
              cubeRoot (Real.cos (3 * x)) ^ 2) =
          1 - Real.cos (3 * x) := by
      calc
        (1 - cubeRoot (Real.cos (3 * x))) *
              (1 + cubeRoot (Real.cos (3 * x)) +
                cubeRoot (Real.cos (3 * x)) ^ 2) =
            1 - cubeRoot (Real.cos (3 * x)) ^ 3 := by ring
        _ = 1 - Real.cos (3 * x) := by rw [hp]
    field_simp [hx, hd]
    nlinarith [hfactor]
  exact hraw.congr' heq

private theorem split2_pointwise (x : ℝ) :
    split2 x =
      (1 / 2 : ℝ) +
        ((1 - Real.sqrt (Real.cos (2 * x))) / x ^ 2 +
          Real.sqrt (Real.cos (2 * x)) *
            ((1 - cubeRoot (Real.cos (3 * x))) / x ^ 2)) := by
  unfold split2
  ring

private theorem original_pointwise (x : ℝ) :
    original x =
      (1 - Real.cos x) / x ^ 2 +
        Real.cos x *
          ((1 - Real.sqrt (Real.cos (2 * x))) / x ^ 2 +
            Real.sqrt (Real.cos (2 * x)) *
              ((1 - cubeRoot (Real.cos (3 * x))) / x ^ 2)) := by
  unfold original
  ring

private theorem split2_limit : HasLimitAtZero split2 3 := by
  have hhalf : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hsqrtfun : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.cos (2 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_sqrt_one (tendsto_cos_mul 2)
  have h := hhalf.add
    (sqrt_quotient_limit.add (hsqrtfun.mul cube_quotient_limit))
  have h3 : Filter.Tendsto
      (fun x : ℝ =>
        (1 / 2 : ℝ) +
          ((1 - Real.sqrt (Real.cos (2 * x))) / x ^ 2 +
            Real.sqrt (Real.cos (2 * x)) *
              ((1 - cubeRoot (Real.cos (3 * x))) / x ^ 2)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 3) := by
    convert h using 1 <;> norm_num
  exact h3.congr'
    (Filter.Eventually.of_forall (fun x => (split2_pointwise x).symm))

private theorem original_limit : HasLimitAtZero original 3 := by
  have hfirst := tendsto_scaled_one_sub_cos 1 (by norm_num)
  have hcos1 := tendsto_cos_mul 1
  have hsqrtfun : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.cos (2 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_sqrt_one (tendsto_cos_mul 2)
  have h := hfirst.add
    (hcos1.mul
      (sqrt_quotient_limit.add (hsqrtfun.mul cube_quotient_limit)))
  have h3 : Filter.Tendsto
      (fun x : ℝ =>
        (1 - Real.cos x) / x ^ 2 +
          Real.cos x *
            ((1 - Real.sqrt (Real.cos (2 * x))) / x ^ 2 +
              Real.sqrt (Real.cos (2 * x)) *
                ((1 - cubeRoot (Real.cos (3 * x))) / x ^ 2)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 3) := by
    convert h using 1 <;> norm_num
  exact h3.congr'
    (Filter.Eventually.of_forall (fun x => (original_pointwise x).symm))

private theorem split3_limit : HasLimitAtZero split3 3 := by
  have hbase2 := tendsto_scaled_one_sub_cos 2 (by norm_num)
  have hbase3 := tendsto_scaled_one_sub_cos 3 (by norm_num)
  have hcos2 := tendsto_cos_mul 2
  have hcos3 := tendsto_cos_mul 3
  have hsqrt2 : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.cos (2 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_sqrt_one hcos2
  have hroot3 : Filter.Tendsto
      (fun x : ℝ => cubeRoot (Real.cos (3 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_cubeRoot_one hcos3
  have hcos3sq : Filter.Tendsto
      (fun x : ℝ => Real.cos (3 * x) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using hcos3.pow 2
  have hroot3sq : Filter.Tendsto
      (fun x : ℝ => cubeRoot (Real.cos (3 * x) ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_cubeRoot_one hcos3sq
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hden2 : Filter.Tendsto
      (fun x : ℝ => 1 + Real.sqrt (Real.cos (2 * x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    convert hone.add hsqrt2 using 1 <;> norm_num
  have hden3 : Filter.Tendsto
      (fun x : ℝ =>
        1 + cubeRoot (Real.cos (3 * x)) +
          cubeRoot (Real.cos (3 * x) ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 3) := by
    convert (hone.add hroot3).add hroot3sq using 1 <;> norm_num
  have hraw2 : Filter.Tendsto
      (fun x : ℝ =>
        ((1 - Real.cos (2 * x)) / x ^ 2) /
          (1 + Real.sqrt (Real.cos (2 * x))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert hbase2.div hden2 (by norm_num : (2 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hraw3 : Filter.Tendsto
      (fun x : ℝ =>
        ((1 - Real.cos (3 * x)) / x ^ 2) /
          (1 + cubeRoot (Real.cos (3 * x)) +
            cubeRoot (Real.cos (3 * x) ^ 2)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2 : ℝ)) := by
    convert hbase3.div hden3 (by norm_num : (3 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hterm2 : Filter.Tendsto
      (fun x : ℝ =>
        (1 - Real.cos (2 * x)) /
          (x ^ 2 * (1 + Real.sqrt (Real.cos (2 * x)))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [div_div] using hraw2
  have hterm3 : Filter.Tendsto
      (fun x : ℝ =>
        (1 - Real.cos (3 * x)) /
          (x ^ 2 * (1 + cubeRoot (Real.cos (3 * x)) +
            cubeRoot (Real.cos (3 * x) ^ 2))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2 : ℝ)) := by
    simpa only [div_div] using hraw3
  have hhalf : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  unfold HasLimitAtZero split3
  convert (hhalf.add hterm2).add hterm3 using 1 <;> norm_num

private theorem hasLimitAtZero_iff_eq {f : ℝ → ℝ}
    (hf : HasLimitAtZero f 3) (L : ℝ) :
    HasLimitAtZero f L ↔ L = 3 := by
  constructor
  · intro h
    exact tendsto_nhds_unique h hf
  · intro h
    simpa [h] using hf

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero split1 L := by
  have h : original = split1 := by
    funext x
    unfold original split1
    ring
  rw [h]

/-- Exercise 504, gap 2; remove the shadowed outer `x`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero split2 L := by
  rw [hasLimitAtZero_iff_eq original_limit L,
    hasLimitAtZero_iff_eq split2_limit L]

/-- Exercise 504, gap 3; remove the shadowed outer `x`. -/
theorem gap3 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero split3 L := by
  rw [hasLimitAtZero_iff_eq original_limit L,
    hasLimitAtZero_iff_eq split3_limit L]

/-- Exercise 504, gap 4; remove the shadowed outer `x`. -/
theorem gap4 : HasLimitAtZero split3 3 := by
  exact split3_limit

/-- Exercise 504, gap 5; remove the shadowed outer `x`. -/
theorem gap5 : HasLimitAtZero original 3 := by
  exact original_limit

end

end ProofGap.Exercise504
