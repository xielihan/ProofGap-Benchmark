import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise569

noncomputable section

def original (a x : ℝ) : ℝ :=
  Real.log (x * Real.log a) *
    Real.log (Real.log (a * x) / Real.log (x / a))
def logPower (a x : ℝ) : ℝ :=
  Real.log (Real.rpow
    ((Real.log a + Real.log x) / (Real.log x - Real.log a))
    (Real.log x + Real.log (Real.log a)))
def exponentialForm (a x : ℝ) : ℝ :=
  let q := 2 * Real.log a / (Real.log x - Real.log a)
  Real.log (Real.rpow (1 + q)
    (((Real.log x - Real.log a) / (2 * Real.log a)) *
      (2 * Real.log a) *
      ((Real.log x + Real.log (Real.log a)) /
        (Real.log x - Real.log a))))
def HasRightLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

/-- Exercise 569, gap 1. -/
private theorem logSlopeAux :
    Filter.Tendsto (fun h : ℝ => Real.log (1 + h) / h)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm, add_comm] using
    (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto_slope_zero

private theorem originalEqLogPower (a : ℝ) (ha : 1 < a) :
    original a =ᶠ[nhdsWithin 0 (Set.Ioi 0)] logPower a := by
  have ha0 : 0 < a := by linarith
  have hc : 0 < Real.log a := Real.log_pos ha
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hnum : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      Real.log x ≤ -Real.log a - 1 :=
    (Filter.tendsto_atBot.1 hlog) (-Real.log a - 1)
  have hden : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      Real.log x ≤ Real.log a - 1 :=
    (Filter.tendsto_atBot.1 hlog) (Real.log a - 1)
  filter_upwards [self_mem_nhdsWithin, hnum, hden] with x hx hnx hdx
  have hbase : 0 <
      (Real.log a + Real.log x) / (Real.log x - Real.log a) :=
    div_pos_of_neg_of_neg (by linarith) (by linarith)
  unfold original logPower
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hc)]
  rw [Real.log_mul (ne_of_gt ha0) (ne_of_gt hx)]
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ha0)]
  change
    (Real.log x + Real.log (Real.log a)) *
        Real.log ((Real.log a + Real.log x) /
          (Real.log x - Real.log a)) =
      Real.log
        ((((Real.log a + Real.log x) /
          (Real.log x - Real.log a : ℝ)).rpow
            (Real.log x + Real.log (Real.log a) : ℝ)))
  symm
  exact Real.log_rpow hbase
    (Real.log x + Real.log (Real.log a))

private theorem logPowerEqExponential (a : ℝ) (ha : 1 < a) :
    logPower a =ᶠ[nhdsWithin 0 (Set.Ioi 0)] exponentialForm a := by
  have hc : 0 < Real.log a := Real.log_pos ha
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hden : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      Real.log x ≤ Real.log a - 1 :=
    (Filter.tendsto_atBot.1 hlog) (Real.log a - 1)
  filter_upwards [hden] with x hx
  have hd : Real.log x - Real.log a ≠ 0 := by linarith
  have hb :
      (Real.log a + Real.log x) / (Real.log x - Real.log a) =
        1 + 2 * Real.log a / (Real.log x - Real.log a) := by
    field_simp [hd]
    ring
  have he :
      ((Real.log x - Real.log a) / (2 * Real.log a)) *
          (2 * Real.log a) *
          ((Real.log x + Real.log (Real.log a)) /
            (Real.log x - Real.log a)) =
        Real.log x + Real.log (Real.log a) := by
    field_simp [hd, hc.ne']
  unfold logPower exponentialForm
  rw [hb, he]

private theorem logPowerLimit (a : ℝ) (ha : 1 < a) :
    HasRightLimitAtZero (logPower a) (Real.log (Real.rpow a 2)) := by
  have ha0 : 0 < a := by linarith
  have hc : 0 < Real.log a := Real.log_pos ha
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x) F Filter.atBot := by
    simpa [F] using Real.tendsto_log_nhdsGT_zero
  have hden : Filter.Tendsto
      (fun x : ℝ => Real.log x - Real.log a) F Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [(Filter.tendsto_atBot.1 hlog)
      (b + Real.log a)] with x hx
    linarith
  have hinv : Filter.Tendsto
      (fun x : ℝ => (Real.log x - Real.log a)⁻¹) F (nhds 0) :=
    tendsto_inv_atBot_zero.comp hden
  have hconst : Filter.Tendsto
      (fun _ : ℝ => 2 * Real.log a) F (nhds (2 * Real.log a)) :=
    tendsto_const_nhds
  have hq : Filter.Tendsto
      (fun x : ℝ => 2 * Real.log a / (Real.log x - Real.log a))
      F (nhds 0) := by
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hden_ne : ∀ᶠ x in F, Real.log x - Real.log a ≠ 0 := by
    filter_upwards [(Filter.tendsto_atBot.1 hden) (-1)] with x hx
    linarith
  have hqne : ∀ᶠ x in F,
      2 * Real.log a / (Real.log x - Real.log a) ≠ 0 := by
    filter_upwards [hden_ne] with x hx
    exact div_ne_zero (mul_ne_zero (by norm_num) hc.ne') hx
  have hq_near : Filter.Tendsto
      (fun x : ℝ => 2 * Real.log a / (Real.log x - Real.log a))
      F (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hq, ?_⟩
    filter_upwards [hqne] with x hx
    simpa using hx
  have hratio : Filter.Tendsto
      (fun x : ℝ =>
        Real.log (1 + 2 * Real.log a / (Real.log x - Real.log a)) /
          (2 * Real.log a / (Real.log x - Real.log a)))
      F (nhds 1) :=
    logSlopeAux.comp hq_near
  have hsmall : Filter.Tendsto
      (fun x : ℝ =>
        (Real.log a + Real.log (Real.log a)) *
          (Real.log x - Real.log a)⁻¹)
      F (nhds 0) := by
    have hk : Filter.Tendsto
        (fun _ : ℝ => Real.log a + Real.log (Real.log a)) F
        (nhds (Real.log a + Real.log (Real.log a))) :=
      tendsto_const_nhds
    simpa using hk.mul hinv
  have hone : Filter.Tendsto
      (fun x : ℝ =>
        1 + (Real.log a + Real.log (Real.log a)) *
          (Real.log x - Real.log a)⁻¹)
      F (nhds 1) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ => (1 : ℝ)) F (nhds 1)).add hsmall)
  have hscaled : Filter.Tendsto
      (fun x : ℝ =>
        (2 * Real.log a) *
          (1 + (Real.log a + Real.log (Real.log a)) *
            (Real.log x - Real.log a)⁻¹))
      F (nhds (2 * Real.log a)) := by
    simpa using hconst.mul hone
  have hpq : Filter.Tendsto
      (fun x : ℝ =>
        (Real.log x + Real.log (Real.log a)) *
          (2 * Real.log a / (Real.log x - Real.log a)))
      F (nhds (2 * Real.log a)) := by
    apply hscaled.congr'
    filter_upwards [hden_ne] with x hx
    field_simp [hx]
    ring
  have hproduct : Filter.Tendsto
      (fun x : ℝ =>
        ((Real.log x + Real.log (Real.log a)) *
          (2 * Real.log a / (Real.log x - Real.log a))) *
        (Real.log (1 + 2 * Real.log a /
            (Real.log x - Real.log a)) /
          (2 * Real.log a / (Real.log x - Real.log a))))
      F (nhds (2 * Real.log a)) := by
    simpa using hpq.mul hratio
  have hsimple : Filter.Tendsto
      (fun x : ℝ =>
        (Real.log x + Real.log (Real.log a)) *
          Real.log (1 + 2 * Real.log a /
            (Real.log x - Real.log a)))
      F (nhds (2 * Real.log a)) := by
    apply hproduct.congr'
    filter_upwards [hqne, hden_ne] with x hqx hdx
    field_simp [hqx, hdx, hc.ne']
  have hq_gt : ∀ᶠ x in F,
      -1 < 2 * Real.log a / (Real.log x - Real.log a) := by
    have hm : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) :=
      isOpen_Ioi.mem_nhds (by norm_num)
    exact hq.eventually hm
  have hform : logPower a =ᶠ[F]
      (fun x : ℝ =>
        (Real.log x + Real.log (Real.log a)) *
          Real.log (1 + 2 * Real.log a /
            (Real.log x - Real.log a))) := by
    filter_upwards [hden_ne, hq_gt] with x hdx hqx
    have hb :
        (Real.log a + Real.log x) / (Real.log x - Real.log a) =
          1 + 2 * Real.log a / (Real.log x - Real.log a) := by
      field_simp [hdx]
      ring
    have hbpos :
        0 < 1 + 2 * Real.log a / (Real.log x - Real.log a) := by
      linarith
    unfold logPower
    rw [hb]
    change
      Real.log
          ((1 + 2 * Real.log a /
              (Real.log x - Real.log a) : ℝ).rpow
            (Real.log x + Real.log (Real.log a) : ℝ)) =
        (Real.log x + Real.log (Real.log a)) *
          Real.log (1 + 2 * Real.log a /
            (Real.log x - Real.log a))
    exact Real.log_rpow hbpos
      (Real.log x + Real.log (Real.log a))
  have hlim : Filter.Tendsto (logPower a) F (nhds (2 * Real.log a)) :=
    hsimple.congr' hform.symm
  have htarget : Real.log (Real.rpow a 2) = 2 * Real.log a := by
    exact Real.log_rpow ha0 2
  unfold HasRightLimitAtZero
  change Filter.Tendsto (logPower a) F (nhds (Real.log (Real.rpow a 2)))
  rw [htarget]
  exact hlim

theorem gap1 (a : ℝ) (ha : 1 < a) (L : ℝ) :
    HasRightLimitAtZero (original a) L ↔ HasRightLimitAtZero (logPower a) L := by
  unfold HasRightLimitAtZero
  constructor
  · intro h
    exact h.congr' (originalEqLogPower a ha)
  · intro h
    exact h.congr' (originalEqLogPower a ha).symm

/-- Exercise 569, gap 2. -/
theorem gap2 (a : ℝ) (ha : 1 < a) (L : ℝ) :
    HasRightLimitAtZero (logPower a) L ↔
      HasRightLimitAtZero (exponentialForm a) L := by
  unfold HasRightLimitAtZero
  constructor
  · intro h
    exact h.congr' (logPowerEqExponential a ha)
  · intro h
    exact h.congr' (logPowerEqExponential a ha).symm

/-- Exercise 569, gap 3. -/
theorem gap3 (a : ℝ) (ha : 1 < a) :
    HasRightLimitAtZero (exponentialForm a) (Real.log (Real.rpow a 2)) := by
  have h := logPowerLimit a ha
  unfold HasRightLimitAtZero at h ⊢
  exact h.congr' (logPowerEqExponential a ha)

/-- Exercise 569, gap 4. -/
theorem gap4 (a : ℝ) (ha : 1 < a) :
    HasRightLimitAtZero (logPower a) (Real.log (Real.rpow a 2)) := by
  exact (gap2 a ha (Real.log (Real.rpow a 2))).mpr (gap3 a ha)

end

end ProofGap.Exercise569
