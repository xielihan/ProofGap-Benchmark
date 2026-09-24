import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise510

noncomputable section

def base (x : ℝ) : ℝ := Real.tan (Real.pi / 8 + x)
def exponent (x : ℝ) : ℝ := Real.tan (2 * x)
def f (x : ℝ) : ℝ := Real.rpow (base x) (exponent x)
def rightFilter : Filter ℝ := nhdsWithin (Real.pi / 4) (Set.Ioi (Real.pi / 4))

/-- Source: `proof_gap/exercise_510/1.txt`; localize the false global bound to the required right neighborhood. -/
theorem gap1 :
    ∃ δ > 0, ∀ x : ℝ, Real.pi / 4 < x → x < Real.pi / 4 + δ →
      1 < base x := by
  refine ⟨Real.pi / 8, by nlinarith [Real.pi_pos], ?_⟩
  intro x hx hxδ
  have hleft : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hright : Real.pi / 8 + x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have htan := Real.strictMonoOn_tan hleft hright (by nlinarith [Real.pi_pos])
  simpa only [base, Real.tan_pi_div_four] using htan

/-- Source: `proof_gap/exercise_510/2.txt`; replace the meaningless global “less than infinity” by local boundedness. -/
theorem gap2 :
    ∃ δ > 0, ∃ M : ℝ, ∀ x : ℝ,
      Real.pi / 4 < x → x < Real.pi / 4 + δ → base x < M := by
  refine ⟨Real.pi / 16, by nlinarith [Real.pi_pos], Real.tan (7 * Real.pi / 16), ?_⟩
  intro x hx hxδ
  have hleft : Real.pi / 8 + x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hright : 7 * Real.pi / 16 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have htan := Real.strictMonoOn_tan hleft hright (by nlinarith [Real.pi_pos])
  simpa only [base] using htan

/-- Source: `proof_gap/exercise_510/3.txt`; a concrete real upper comparison. -/
theorem gap3 : (1 : ℝ) < 2 := by
  exact one_lt_two

/-- Source: `proof_gap/exercise_510/4.txt`. -/
theorem gap4 : Filter.Tendsto exponent rightFilter Filter.atBot := by
  have hcont :
      ContinuousAt (fun x : ℝ => Real.pi - 2 * x) (Real.pi / 4) :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hval : Real.pi - 2 * (Real.pi / 4) = Real.pi / 2 := by
    ring
  have hmap_nhds :
      Filter.Tendsto (fun x : ℝ => Real.pi - 2 * x) (nhds (Real.pi / 4))
        (nhds (Real.pi / 2)) := by
    simpa only [ContinuousAt, hval] using hcont
  have hmap :
      Filter.Tendsto (fun x : ℝ => Real.pi - 2 * x) rightFilter
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · apply hmap_nhds.mono_left
      unfold rightFilter
      exact inf_le_left
    · have hr : ∀ᶠ x : ℝ in rightFilter, x ∈ Set.Ioi (Real.pi / 4) := by
        unfold rightFilter
        exact self_mem_nhdsWithin
      filter_upwards [hr] with x hx
      change Real.pi - 2 * x < Real.pi / 2
      change Real.pi / 4 < x at hx
      nlinarith
  have ht :
      Filter.Tendsto (fun x : ℝ => Real.tan (Real.pi - 2 * x))
        rightFilter Filter.atTop :=
    Real.tendsto_tan_pi_div_two.comp hmap
  refine Filter.tendsto_atBot.2 ?_
  intro A
  have hA :
      ∀ᶠ x in rightFilter, -A ≤ Real.tan (Real.pi - 2 * x) :=
    (Filter.tendsto_atTop.1 ht) (-A)
  filter_upwards [hA] with x hx
  have heq : exponent x = -Real.tan (Real.pi - 2 * x) := by
    unfold exponent
    rw [show Real.pi - 2 * x = -(2 * x) + Real.pi by ring,
      Real.tan_add_pi, Real.tan_neg]
    ring
  rw [heq]
  linarith

/-- Source: `proof_gap/exercise_510/5.txt`; interpret the variable power by `Real.rpow`. -/
theorem gap5 : Filter.Tendsto f rightFilter (nhds 0) := by
  have hleft : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hright : Real.pi / 8 + Real.pi / 4 ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hb : 1 < base (Real.pi / 4) := by
    have htan := Real.strictMonoOn_tan hleft hright (by nlinarith [Real.pi_pos])
    simpa only [base, Real.tan_pi_div_four] using htan
  have hbpos : 0 < base (Real.pi / 4) := lt_trans zero_lt_one hb
  have hcos : Real.cos (Real.pi / 8 + Real.pi / 4) ≠ 0 := by
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo hright)
  have hinner :
      ContinuousAt (fun x : ℝ => Real.pi / 8 + x) (Real.pi / 4) :=
    continuousAt_const.add continuousAt_id
  have hsin :
      ContinuousAt (fun x : ℝ => Real.sin (Real.pi / 8 + x)) (Real.pi / 4) := by
    simpa only [Function.comp_apply] using
      Real.continuous_sin.continuousAt.comp hinner
  have hcos_cont :
      ContinuousAt (fun x : ℝ => Real.cos (Real.pi / 8 + x)) (Real.pi / 4) := by
    simpa only [Function.comp_apply] using
      Real.continuous_cos.continuousAt.comp hinner
  have hbase_eq :
      base =
        (fun x : ℝ => Real.sin (Real.pi / 8 + x)) /
          (fun x : ℝ => Real.cos (Real.pi / 8 + x)) := by
    funext x
    change Real.tan (Real.pi / 8 + x) =
      Real.sin (Real.pi / 8 + x) / Real.cos (Real.pi / 8 + x)
    exact Real.tan_eq_sin_div_cos (Real.pi / 8 + x)
  have hbase_cont : ContinuousAt base (Real.pi / 4) := by
    rw [hbase_eq]
    exact hsin.div hcos_cont hcos
  have hbase_tend :
      Filter.Tendsto base rightFilter (nhds (base (Real.pi / 4))) := by
    apply hbase_cont.mono_left
    unfold rightFilter
    exact inf_le_left
  have hlog_at :
      Filter.Tendsto Real.log (nhds (base (Real.pi / 4)))
        (nhds (Real.log (base (Real.pi / 4)))) :=
    Real.continuousAt_log (ne_of_gt hbpos)
  have hlog_tend :
      Filter.Tendsto (fun x => Real.log (base x)) rightFilter
        (nhds (Real.log (base (Real.pi / 4)))) :=
    hlog_at.comp hbase_tend
  have hc : 0 < Real.log (base (Real.pi / 4)) := Real.log_pos hb
  have hd : 0 < Real.log (base (Real.pi / 4)) / 2 := half_pos hc
  have hlog_lower :
      ∀ᶠ x in rightFilter,
        Real.log (base (Real.pi / 4)) / 2 < Real.log (base x) :=
    hlog_tend.eventually (Ioi_mem_nhds (by nlinarith [hc]))
  have hbase_pos : ∀ᶠ x in rightFilter, 0 < base x :=
    hbase_tend.eventually (Ioi_mem_nhds hbpos)
  have hprod :
      Filter.Tendsto (fun x => Real.log (base x) * exponent x)
        rightFilter Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro A
    have hevent :
        ∀ᶠ x in rightFilter,
          exponent x ≤ min 0 (A / (Real.log (base (Real.pi / 4)) / 2)) :=
      (Filter.tendsto_atBot.1 gap4)
        (min 0 (A / (Real.log (base (Real.pi / 4)) / 2)))
    filter_upwards [hlog_lower, hevent] with x hl he
    have he0 : exponent x ≤ 0 := le_trans he (min_le_left _ _)
    have heA : exponent x ≤ A / (Real.log (base (Real.pi / 4)) / 2) :=
      le_trans he (min_le_right _ _)
    have hp :
        Real.log (base x) * exponent x ≤
          (Real.log (base (Real.pi / 4)) / 2) * exponent x :=
      mul_le_mul_of_nonpos_right (le_of_lt hl) he0
    have hA :
        (Real.log (base (Real.pi / 4)) / 2) * exponent x ≤ A := by
      simpa only [mul_comm] using (le_div_iff₀ hd).1 heA
    exact hp.trans hA
  have hzero :
      Filter.Tendsto
        (fun x => Real.exp (Real.log (base x) * exponent x))
        rightFilter (nhds 0) := by
    simpa only [Function.comp_apply] using Real.tendsto_exp_atBot.comp hprod
  apply hzero.congr'
  filter_upwards [hbase_pos] with x hx
  change Real.exp (Real.log (base x) * exponent x) =
    Real.rpow (base x) (exponent x)
  exact (Real.rpow_def_of_pos hx (exponent x)).symm

end

end ProofGap.Exercise510
