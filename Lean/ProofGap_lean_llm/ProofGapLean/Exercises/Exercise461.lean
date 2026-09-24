import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic

namespace ProofGap.Exercise461

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def p (x : ℝ) : ℝ := x ^ 3 + x ^ 2 + 1
def q (x : ℝ) : ℝ := x ^ 3 - x ^ 2 + 1
def original (x : ℝ) : ℝ := cbrt (p x) - cbrt (q x)
def rationalized (x : ℝ) : ℝ :=
  (2 * x ^ 2) /
    (cbrt ((p x) ^ 2) + cbrt (p x * q x) + cbrt ((q x) ^ 2))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_461/1.txt`; use the difference-of-cubes identity. -/
private def normalizedP (t : ℝ) : ℝ := 1 + t + t ^ 3

private def normalizedQ (t : ℝ) : ℝ := 1 - t + t ^ 3

private def scaledForm (t : ℝ) : ℝ :=
  2 /
    ((cbrt (normalizedP t)) ^ 2 +
      cbrt (normalizedP t) * cbrt (normalizedQ t) +
      (cbrt (normalizedQ t)) ^ 2)

private theorem cbrt_mul_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    cbrt (u * v) = cbrt u * cbrt v := by
  unfold cbrt
  exact Real.mul_rpow hu hv

private theorem cbrt_cube_pos {x : ℝ} (hx : 0 < x) :
    (cbrt x) ^ 3 = x := by
  unfold cbrt
  calc
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
      exact (Real.rpow_natCast (Real.rpow x (1 / 3 : ℝ)) 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul (le_of_lt hx) (1 / 3 : ℝ) (3 : ℝ)).symm
    _ = x := by norm_num

private theorem cbrt_pow_three_pos {x : ℝ} (hx : 0 < x) :
    cbrt (x ^ 3) = x := by
  unfold cbrt
  calc
    Real.rpow (x ^ 3) (1 / 3 : ℝ) =
        Real.rpow (Real.rpow x (3 : ℝ)) (1 / 3 : ℝ) := by
      exact congrArg (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
        (Real.rpow_natCast x 3).symm
    _ = Real.rpow x ((3 : ℝ) * (1 / 3 : ℝ)) := by
      exact (Real.rpow_mul (le_of_lt hx) (3 : ℝ) (1 / 3 : ℝ)).symm
    _ = x := by norm_num

private theorem cbrt_tendsto_one :
    Filter.Tendsto cbrt (nhds (1 : ℝ)) (nhds (1 : ℝ)) := by
  have hcont :
      ContinuousAt
        (fun x : ℝ => Real.exp (Real.log x * (1 / 3 : ℝ))) 1 := by
    have hlog : ContinuousAt Real.log (1 : ℝ) :=
      Real.continuousAt_log (by norm_num)
    simpa only [Function.comp_apply] using
      Real.continuous_exp.continuousAt.comp
        (hlog.mul continuousAt_const)
  have ht :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log x * (1 / 3 : ℝ)))
        (nhds 1) (nhds 1) := by
    simpa only [ContinuousAt, Real.log_one, zero_mul, Real.exp_zero] using hcont
  have heq :
      cbrt =ᶠ[nhds (1 : ℝ)]
        (fun x : ℝ => Real.exp (Real.log x * (1 / 3 : ℝ))) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    unfold cbrt
    change Real.rpow x (1 / 3 : ℝ) =
      Real.exp (Real.log x * (1 / 3 : ℝ))
    exact Real.rpow_def_of_pos hx (1 / 3 : ℝ)
  exact ht.congr' heq.symm

private theorem scaledForm_tendsto :
    Filter.Tendsto scaledForm (nhds 0) (nhds (2 / 3 : ℝ)) := by
  have hPcont : ContinuousAt normalizedP 0 := by
    unfold normalizedP
    fun_prop
  have hQcont : ContinuousAt normalizedQ 0 := by
    unfold normalizedQ
    fun_prop
  have hP :
      Filter.Tendsto normalizedP (nhds 0) (nhds (1 : ℝ)) := by
    convert hPcont.tendsto using 1 <;> norm_num [normalizedP]
  have hQ :
      Filter.Tendsto normalizedQ (nhds 0) (nhds (1 : ℝ)) := by
    convert hQcont.tendsto using 1 <;> norm_num [normalizedQ]
  have hcP :
      Filter.Tendsto (fun t : ℝ => cbrt (normalizedP t))
        (nhds 0) (nhds 1) :=
    cbrt_tendsto_one.comp hP
  have hcQ :
      Filter.Tendsto (fun t : ℝ => cbrt (normalizedQ t))
        (nhds 0) (nhds 1) :=
    cbrt_tendsto_one.comp hQ
  have hd :
      Filter.Tendsto
        (fun t : ℝ =>
          (cbrt (normalizedP t)) ^ 2 +
            cbrt (normalizedP t) * cbrt (normalizedQ t) +
            (cbrt (normalizedQ t)) ^ 2)
        (nhds 0) (nhds (3 : ℝ)) := by
    convert ((hcP.pow 2).add (hcP.mul hcQ)).add (hcQ.pow 2) using 1 <;>
      norm_num
  have hnum :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) (nhds 0) (nhds 2) :=
    tendsto_const_nhds
  have hquot :
      Filter.Tendsto
        (fun t : ℝ =>
          (2 : ℝ) /
            ((cbrt (normalizedP t)) ^ 2 +
              cbrt (normalizedP t) * cbrt (normalizedQ t) +
              (cbrt (normalizedQ t)) ^ 2))
        (nhds 0) (nhds ((2 : ℝ) / 3)) :=
    hnum.div hd (by norm_num)
  simpa [scaledForm] using hquot

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rationalized L := by
  have heq : original =ᶠ[Filter.atTop] rationalized := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hp : 0 < p x := by
      unfold p
      nlinarith [pow_pos hxpos 3, sq_nonneg x]
    have hq : 0 < q x := by
      have hxminus : 0 ≤ x - 1 := by linarith
      have hnonneg : 0 ≤ x ^ 2 * (x - 1) :=
        mul_nonneg (sq_nonneg x) hxminus
      unfold q
      nlinarith
    have hpp : cbrt ((p x) ^ 2) = (cbrt (p x)) ^ 2 := by
      simpa [pow_two] using
        cbrt_mul_nonneg (le_of_lt hp) (le_of_lt hp)
    have hpq : cbrt (p x * q x) = cbrt (p x) * cbrt (q x) :=
      cbrt_mul_nonneg (le_of_lt hp) (le_of_lt hq)
    have hqq : cbrt ((q x) ^ 2) = (cbrt (q x)) ^ 2 := by
      simpa [pow_two] using
        cbrt_mul_nonneg (le_of_lt hq) (le_of_lt hq)
    have hpcube : (cbrt (p x)) ^ 3 = p x :=
      cbrt_cube_pos hp
    have hqcube : (cbrt (q x)) ^ 3 = q x :=
      cbrt_cube_pos hq
    have hcp : 0 < cbrt (p x) := by
      unfold cbrt
      exact Real.rpow_pos_of_pos hp _
    have hcq : 0 ≤ cbrt (q x) := by
      unfold cbrt
      exact Real.rpow_nonneg (le_of_lt hq) _
    have hcp2 : 0 < (cbrt (p x)) ^ 2 := pow_pos hcp 2
    have hcpq : 0 ≤ cbrt (p x) * cbrt (q x) :=
      mul_nonneg (le_of_lt hcp) hcq
    have hcq2 : 0 ≤ (cbrt (q x)) ^ 2 := sq_nonneg _
    have hdenpos :
        0 < (cbrt (p x)) ^ 2 + cbrt (p x) * cbrt (q x) +
          (cbrt (q x)) ^ 2 := by
      linarith
    have hdiff :
        (cbrt (p x) - cbrt (q x)) *
            ((cbrt (p x)) ^ 2 + cbrt (p x) * cbrt (q x) +
              (cbrt (q x)) ^ 2) =
          2 * x ^ 2 := by
      calc
        _ = (cbrt (p x)) ^ 3 - (cbrt (q x)) ^ 3 := by ring
        _ = p x - q x := by rw [hpcube, hqcube]
        _ = 2 * x ^ 2 := by unfold p q; ring
    unfold original rationalized
    rw [hpp, hpq, hqq]
    exact (eq_div_iff (ne_of_gt hdenpos)).2 hdiff
  unfold HasLimitAtPosInfinity
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_461/2.txt`. -/
theorem gap2 : HasLimitAtPosInfinity rationalized (2 / 3) := by
  have heq :
      rationalized =ᶠ[Filter.atTop] (fun x : ℝ => scaledForm x⁻¹) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hinv_nonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
    have hinv_le : x⁻¹ ≤ 1 := by
      have hm : 0 ≤ (x - 1) * x⁻¹ :=
        mul_nonneg (by linarith) hinv_nonneg
      have hc : x⁻¹ * x = 1 := inv_mul_cancel₀ hxne
      nlinarith
    have hinv_cube_nonneg : 0 ≤ (x⁻¹) ^ 3 :=
      pow_nonneg hinv_nonneg 3
    have hPpos : 0 < normalizedP x⁻¹ := by
      unfold normalizedP
      nlinarith
    have hQnonneg : 0 ≤ normalizedQ x⁻¹ := by
      unfold normalizedQ
      nlinarith
    have hp_id : p x = x ^ 3 * normalizedP x⁻¹ := by
      unfold p normalizedP
      field_simp [hxne] <;> ring
    have hq_id : q x = x ^ 3 * normalizedQ x⁻¹ := by
      unfold q normalizedQ
      field_simp [hxne] <;> ring
    have hp : 0 < p x := by
      unfold p
      nlinarith [pow_pos hxpos 3, sq_nonneg x]
    have hq : 0 < q x := by
      have hxminus : 0 ≤ x - 1 := by linarith
      have hnonneg : 0 ≤ x ^ 2 * (x - 1) :=
        mul_nonneg (sq_nonneg x) hxminus
      unfold q
      nlinarith
    have hxcube_nonneg : 0 ≤ x ^ 3 :=
      le_of_lt (pow_pos hxpos 3)
    have hcp :
        cbrt (p x) = x * cbrt (normalizedP x⁻¹) := by
      rw [hp_id,
        cbrt_mul_nonneg hxcube_nonneg (le_of_lt hPpos),
        cbrt_pow_three_pos hxpos]
    have hcq :
        cbrt (q x) = x * cbrt (normalizedQ x⁻¹) := by
      rw [hq_id,
        cbrt_mul_nonneg hxcube_nonneg hQnonneg,
        cbrt_pow_three_pos hxpos]
    have hpp : cbrt ((p x) ^ 2) = (cbrt (p x)) ^ 2 := by
      simpa [pow_two] using
        cbrt_mul_nonneg (le_of_lt hp) (le_of_lt hp)
    have hpq : cbrt (p x * q x) = cbrt (p x) * cbrt (q x) :=
      cbrt_mul_nonneg (le_of_lt hp) (le_of_lt hq)
    have hqq : cbrt ((q x) ^ 2) = (cbrt (q x)) ^ 2 := by
      simpa [pow_two] using
        cbrt_mul_nonneg (le_of_lt hq) (le_of_lt hq)
    have hrootPpos : 0 < cbrt (normalizedP x⁻¹) := by
      unfold cbrt
      exact Real.rpow_pos_of_pos hPpos _
    have hrootQnonneg : 0 ≤ cbrt (normalizedQ x⁻¹) := by
      unfold cbrt
      exact Real.rpow_nonneg hQnonneg _
    have hrootP2 : 0 < (cbrt (normalizedP x⁻¹)) ^ 2 :=
      pow_pos hrootPpos 2
    have hrootPQ :
        0 ≤ cbrt (normalizedP x⁻¹) * cbrt (normalizedQ x⁻¹) :=
      mul_nonneg (le_of_lt hrootPpos) hrootQnonneg
    have hrootQ2 : 0 ≤ (cbrt (normalizedQ x⁻¹)) ^ 2 := sq_nonneg _
    have hSpos :
        0 < (cbrt (normalizedP x⁻¹)) ^ 2 +
            cbrt (normalizedP x⁻¹) * cbrt (normalizedQ x⁻¹) +
            (cbrt (normalizedQ x⁻¹)) ^ 2 := by
      linarith
    have hden :
        (x * cbrt (normalizedP x⁻¹)) ^ 2 +
              (x * cbrt (normalizedP x⁻¹)) *
                (x * cbrt (normalizedQ x⁻¹)) +
              (x * cbrt (normalizedQ x⁻¹)) ^ 2 =
            x ^ 2 *
              ((cbrt (normalizedP x⁻¹)) ^ 2 +
                cbrt (normalizedP x⁻¹) * cbrt (normalizedQ x⁻¹) +
                (cbrt (normalizedQ x⁻¹)) ^ 2) := by
      ring
    unfold rationalized scaledForm
    rw [hpp, hpq, hqq, hcp, hcq, hden]
    apply
      (div_eq_div_iff
        (mul_ne_zero (pow_ne_zero 2 hxne) (ne_of_gt hSpos))
        (ne_of_gt hSpos)).2
    ring
  unfold HasLimitAtPosInfinity
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hlim := scaledForm_tendsto.comp hinv
  exact hlim.congr' heq.symm

end

end ProofGap.Exercise461
