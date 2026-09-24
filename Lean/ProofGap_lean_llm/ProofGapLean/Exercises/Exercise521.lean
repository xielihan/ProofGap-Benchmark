import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise521

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.rpow (Real.cos x / Real.cos (2 * x)) (1 / x ^ 2)
def exponentialForm (x : ℝ) : ℝ :=
  Real.rpow (1 + 1 / (Real.cos (2 * x) / (Real.cos x - Real.cos (2 * x))))
    ((Real.cos (2 * x) / (Real.cos x - Real.cos (2 * x))) *
      ((Real.cos x - Real.cos (2 * x)) / (x ^ 2 * Real.cos (2 * x))))
def differenceQuotient (x : ℝ) : ℝ :=
  (Real.cos x - Real.cos (2 * x)) / x ^ 2
def polynomialForm (x : ℝ) : ℝ :=
  (Real.cos x + 1 - 2 * Real.cos x ^ 2) / x ^ 2
def factored (x : ℝ) : ℝ :=
  ((1 - Real.cos x) / x ^ 2) * (1 + 2 * Real.cos x)
def normalized (x : ℝ) : ℝ :=
  ((1 + 2 * Real.cos x) / 2) *
    (Real.sin (x / 2) / (x / 2)) ^ 2
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_521/1.txt`; localize the power rewrite to the punctured limit instead of all real `x`. -/
private theorem tendsto_log_one_plus_div_local :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [Real.log_one, div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero

private theorem tendsto_sin_div_local :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

private theorem reciprocal_product_local
    (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    1 / t = (a / b) * (b / (t * a)) := by
  field_simp [ha, hb, ht]

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero exponentialForm L := by
  unfold HasLimitAtZero
  have hcfull :
      Filter.Tendsto (fun x : ℝ => Real.cos (2 * x)) (nhds 0) (nhds 1) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.cos (2 * x)) 0 :=
      Real.continuous_cos.continuousAt.comp
        (continuousAt_const.mul continuousAt_id)
    simpa [ContinuousAt] using hcont
  have hc :
      Filter.Tendsto (fun x : ℝ => Real.cos (2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hcfull.mono_left inf_le_left
  have hcpos :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < Real.cos (2 * x) :=
    hc.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq :
      original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] exponentialForm := by
    filter_upwards [hcpos, self_mem_nhdsWithin] with x hcx hx
    have hcne : Real.cos (2 * x) ≠ 0 := ne_of_gt hcx
    have hx0 : x ≠ 0 := by simpa using hx
    by_cases hd : Real.cos x - Real.cos (2 * x) = 0
    · have he : Real.cos x = Real.cos (2 * x) := sub_eq_zero.mp hd
      simp [original, exponentialForm, he, hcne]
    · have hbase :
          Real.cos x / Real.cos (2 * x) =
            1 + 1 / (Real.cos (2 * x) /
              (Real.cos x - Real.cos (2 * x))) := by
        rw [one_div_div]
        field_simp [hcne]
        ring
      have hexponent :
          1 / x ^ 2 =
            (Real.cos (2 * x) / (Real.cos x - Real.cos (2 * x))) *
              ((Real.cos x - Real.cos (2 * x)) /
                (x ^ 2 * Real.cos (2 * x))) := by
        exact reciprocal_product_local
          (Real.cos (2 * x))
          (Real.cos x - Real.cos (2 * x))
          (x ^ 2) hcne hd (pow_ne_zero 2 hx0)
      unfold original exponentialForm
      rw [hbase, hexponent]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_521/2.txt`; exclude `x=0`. -/
theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    differenceQuotient x = polynomialForm x := by
  unfold differenceQuotient polynomialForm
  rw [Real.cos_two_mul]
  ring

/-- Source: `proof_gap/exercise_521/3.txt`; exclude `x=0`. -/
theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    polynomialForm x = factored x := by
  unfold polynomialForm factored
  field_simp [hx] <;> ring

/-- Source: `proof_gap/exercise_521/4.txt`; exclude `x=0`. -/
theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    factored x = normalized x := by
  have hcos :
      Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (x / 2) using 1 <;> ring
  have hone :
      1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  unfold factored normalized
  rw [hone]
  field_simp [hx] <;> ring

/-- Source: `proof_gap/exercise_521/5.txt`. -/
theorem gap5 : HasLimitAtZero normalized (3 / 2) := by
  unfold HasLimitAtZero
  have hhalf :
      Filter.Tendsto (fun x : ℝ => x / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : ContinuousAt (fun x : ℝ => x / 2) 0 :=
        continuousAt_id.div_const (2 : ℝ)
      have hfull :
          Filter.Tendsto (fun x : ℝ => x / 2) (nhds 0) (nhds 0) := by
        simpa [ContinuousAt] using hcont
      exact hfull.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      simpa using div_ne_zero hx0 (by norm_num : (2 : ℝ) ≠ 0)
  have hsin :
      Filter.Tendsto
        (fun x : ℝ => Real.sin (x / 2) / (x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using tendsto_sin_div_local.comp hhalf
  have hfactor :
      Filter.Tendsto
        (fun x : ℝ => (1 + 2 * Real.cos x) / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2)) := by
    have hcont :
        ContinuousAt (fun x : ℝ => (1 + 2 * Real.cos x) / 2) 0 :=
      (continuousAt_const.add
        (continuousAt_const.mul Real.continuous_cos.continuousAt)).div_const
          (2 : ℝ)
    have hfull :
        Filter.Tendsto
          (fun x : ℝ => (1 + 2 * Real.cos x) / 2)
          (nhds 0) (nhds (3 / 2)) := by
      change Filter.Tendsto
        (fun x : ℝ => (1 + 2 * Real.cos x) / 2)
        (nhds 0) (nhds ((1 + 2 * Real.cos 0) / 2)) at hcont
      norm_num at hcont
      exact hcont
    exact hfull.mono_left inf_le_left
  simpa [normalized] using hfactor.mul (hsin.pow 2)

/-- Source: `proof_gap/exercise_521/6.txt`. -/
theorem gap6 : HasLimitAtZero differenceQuotient (3 / 2) := by
  unfold HasLimitAtZero
  apply gap5.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  calc
    normalized x = factored x := (gap4 x hx0).symm
    _ = polynomialForm x := (gap3 x hx0).symm
    _ = differenceQuotient x := (gap2 x hx0).symm

/-- Source: `proof_gap/exercise_521/7.txt`. -/
theorem gap7 : HasLimitAtZero original (Real.exp (3 / 2)) := by
  apply (gap1 (Real.exp (3 / 2))).mpr
  unfold HasLimitAtZero
  have hcosfull :
      Filter.Tendsto (fun x : ℝ => Real.cos x) (nhds 0) (nhds 1) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.cos x) 0 :=
      Real.continuous_cos.continuousAt
    simpa [ContinuousAt] using hcont
  have hcos :
      Filter.Tendsto (fun x : ℝ => Real.cos x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hcosfull.mono_left inf_le_left
  have hcos2full :
      Filter.Tendsto (fun x : ℝ => Real.cos (2 * x)) (nhds 0) (nhds 1) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.cos (2 * x)) 0 :=
      Real.continuous_cos.continuousAt.comp
        (continuousAt_const.mul continuousAt_id)
    simpa [ContinuousAt] using hcont
  have hcos2 :
      Filter.Tendsto (fun x : ℝ => Real.cos (2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hcos2full.mono_left inf_le_left
  have hq :
      Filter.Tendsto differenceQuotient
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2)) := gap6
  have hdlim :
      Filter.Tendsto
        (fun x : ℝ => Real.cos x - Real.cos (2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hcos.sub hcos2
  have hu :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hdlim.div hcos2 (by norm_num : (1 : ℝ) ≠ 0)
  have hv :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.cos x - Real.cos (2 * x)) /
            (x ^ 2 * Real.cos (2 * x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2)) := by
    have ht := hq.div hcos2 (by norm_num : (1 : ℝ) ≠ 0)
    have ht' :
        Filter.Tendsto
          (differenceQuotient / fun x : ℝ => Real.cos (2 * x))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2)) := by
      simpa only [div_one] using ht
    apply ht'.congr'
    exact Filter.Eventually.of_forall (fun x => by
      change
        ((Real.cos x - Real.cos (2 * x)) / x ^ 2) /
            Real.cos (2 * x) =
          (Real.cos x - Real.cos (2 * x)) /
            (x ^ 2 * Real.cos (2 * x))
      rw [div_div])
  have hc2pos :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < Real.cos (2 * x) :=
    hcos2.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hcxpos :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < Real.cos x :=
    hcos.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hqpos :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        0 < differenceQuotient x :=
    hq.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 3 / 2))
  have hune :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        (Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x) ≠ 0 := by
    filter_upwards [hc2pos, hqpos] with x hc hqx
    have hd : Real.cos x - Real.cos (2 * x) ≠ 0 := by
      intro hd
      simp [differenceQuotient, hd] at hqx
    exact div_ne_zero hd (ne_of_gt hc)
  have huWithin :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu, by
      filter_upwards [hune] with x hx
      simpa using hx⟩
  have hlog :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log
              (1 + (Real.cos x - Real.cos (2 * x)) /
                Real.cos (2 * x)) /
            ((Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using tendsto_log_one_plus_div_local.comp huWithin
  have hprod :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log
                (1 + (Real.cos x - Real.cos (2 * x)) /
                  Real.cos (2 * x)) /
              ((Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x))) *
            ((Real.cos x - Real.cos (2 * x)) /
              (x ^ 2 * Real.cos (2 * x))))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2)) := by
    simpa only [one_mul] using hlog.mul hv
  have hexplim :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            ((Real.log
                  (1 + (Real.cos x - Real.cos (2 * x)) /
                    Real.cos (2 * x)) /
                ((Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x))) *
              ((Real.cos x - Real.cos (2 * x)) /
                (x ^ 2 * Real.cos (2 * x)))))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (Real.exp (3 / 2))) := by
    exact (Real.continuous_exp.tendsto (3 / 2)).comp hprod
  have heq :
      exponentialForm =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ =>
          Real.exp
            ((Real.log
                  (1 + (Real.cos x - Real.cos (2 * x)) /
                    Real.cos (2 * x)) /
                ((Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x))) *
              ((Real.cos x - Real.cos (2 * x)) /
                (x ^ 2 * Real.cos (2 * x))))) := by
    filter_upwards [hc2pos, hcxpos, hqpos, self_mem_nhdsWithin] with
      x hc hcx hqx hx
    have hcne : Real.cos (2 * x) ≠ 0 := ne_of_gt hc
    have hx0 : x ≠ 0 := by simpa using hx
    have hd : Real.cos x - Real.cos (2 * x) ≠ 0 := by
      intro hd
      simp [differenceQuotient, hd] at hqx
    have hbase :
        1 + 1 / (Real.cos (2 * x) /
          (Real.cos x - Real.cos (2 * x))) =
          1 + (Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x) := by
      rw [one_div_div]
    have hratio :
        1 + (Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x) =
          Real.cos x / Real.cos (2 * x) := by
      field_simp [hcne]
      ring
    have hbasepos :
        0 < 1 + 1 / (Real.cos (2 * x) /
          (Real.cos x - Real.cos (2 * x))) := by
      rw [hbase, hratio]
      exact div_pos hcx hc
    have halg (A v : ℝ) :
        A * ((Real.cos (2 * x) /
            (Real.cos x - Real.cos (2 * x))) * v) =
          (A / ((Real.cos x - Real.cos (2 * x)) /
            Real.cos (2 * x))) * v := by
      field_simp [hcne, hd]
    unfold exponentialForm
    calc
      Real.rpow
          (1 + 1 / (Real.cos (2 * x) /
            (Real.cos x - Real.cos (2 * x))))
          ((Real.cos (2 * x) / (Real.cos x - Real.cos (2 * x))) *
            ((Real.cos x - Real.cos (2 * x)) /
              (x ^ 2 * Real.cos (2 * x)))) =
        Real.exp
          (Real.log
              (1 + 1 / (Real.cos (2 * x) /
                (Real.cos x - Real.cos (2 * x)))) *
            ((Real.cos (2 * x) / (Real.cos x - Real.cos (2 * x))) *
              ((Real.cos x - Real.cos (2 * x)) /
                (x ^ 2 * Real.cos (2 * x))))) :=
          Real.rpow_def_of_pos hbasepos
            (y := (Real.cos (2 * x) /
                (Real.cos x - Real.cos (2 * x))) *
              ((Real.cos x - Real.cos (2 * x)) /
                (x ^ 2 * Real.cos (2 * x))))
      _ = Real.exp
          ((Real.log
                (1 + (Real.cos x - Real.cos (2 * x)) /
                  Real.cos (2 * x)) /
              ((Real.cos x - Real.cos (2 * x)) / Real.cos (2 * x))) *
            ((Real.cos x - Real.cos (2 * x)) /
              (x ^ 2 * Real.cos (2 * x)))) := by
        rw [hbase]
        congr 1
        exact halg _ _
  exact hexplim.congr' heq.symm

end

end ProofGap.Exercise521
