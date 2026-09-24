import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise650_4

noncomputable section

def power (ε x : ℝ) : ℝ := Real.rpow x ε

/-- Exercise 650_4, gap 1; require `x>0` and `ε>0` for the reciprocal power. -/
private theorem log_isLittleO_reciprocal_power (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
      Real.log (fun x => 1 / power ε x) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (x⁻¹))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Real.tendsto_log_atTop.comp hinv
  have hmul :
      Filter.Tendsto (fun x : ℝ => Real.log (x⁻¹) * ε)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.tendsto_atTop.1 hlog (b / ε)] with x hx
    have hε0 : ε ≠ 0 := ne_of_gt hε
    calc
      b = (b / ε) * ε := by field_simp [hε0]
      _ ≤ Real.log (x⁻¹) * ε :=
        mul_le_mul_of_nonneg_right hx (le_of_lt hε)
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (Real.log (x⁻¹) * ε))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Real.tendsto_exp_atTop.comp hmul
  have hrpow :
      Filter.Tendsto (fun x : ℝ => Real.rpow (x⁻¹) ε)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    refine hexp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    change Real.exp (Real.log (x⁻¹) * ε) = x⁻¹ ^ ε
    exact (Real.rpow_def_of_pos (inv_pos.mpr hx) ε).symm
  have hcomp :
      Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
        (fun x : ℝ => Real.log (Real.rpow (x⁻¹) ε))
        (fun x : ℝ => Real.rpow (x⁻¹) ε) := by
    simpa only [Function.comp_apply, id_eq] using
      Real.isLittleO_log_id_atTop.comp_tendsto hrpow
  have hscaled := hcomp.const_mul_left ((-ε)⁻¹)
  apply hscaled.congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hε0 : ε ≠ 0 := ne_of_gt hε
    have hinvdef :
        Real.rpow (x⁻¹) ε = Real.exp (Real.log (x⁻¹) * ε) := by
      change x⁻¹ ^ ε = Real.exp (Real.log (x⁻¹) * ε)
      exact Real.rpow_def_of_pos (inv_pos.mpr hx) ε
    rw [hinvdef, Real.log_exp, Real.log_inv]
    field_simp [hε0] <;> ring
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxdef :
        Real.rpow x ε = Real.exp (Real.log x * ε) := by
      change x ^ ε = Real.exp (Real.log x * ε)
      exact Real.rpow_def_of_pos hx ε
    calc
      Real.rpow (x⁻¹) ε
          = Real.exp (Real.log (x⁻¹) * ε) := by
              change x⁻¹ ^ ε = Real.exp (Real.log (x⁻¹) * ε)
              exact Real.rpow_def_of_pos (inv_pos.mpr hx) ε
      _ = Real.exp (-(Real.log x * ε)) := by
            rw [Real.log_inv]
            simp only [neg_mul]
      _ = (Real.exp (Real.log x * ε))⁻¹ := Real.exp_neg _
      _ = (Real.rpow x ε)⁻¹ :=
            congrArg (fun z : ℝ => z⁻¹) hxdef.symm
      _ = 1 / power ε x := by
            simp only [power, one_div]

theorem gap1 (ε x : ℝ) (hε : 0 < ε) (hx : 0 < x) :
    Real.log x / (1 / power ε x) = power ε x * Real.log x := by
  simpa [div_eq_mul_inv, mul_comm]

/-- Exercise 650_4, gap 2. -/
theorem gap2 (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun x => power ε x * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hratio :
      Filter.Tendsto (fun x => Real.log x / (1 / power ε x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (log_isLittleO_reciprocal_power ε hε).tendsto_div_nhds_zero
  refine hratio.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact gap1 ε x hε hx

/-- Exercise 650_4, gap 3. -/
theorem gap3 (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun x => Real.log x / (1 / power ε x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact (log_isLittleO_reciprocal_power ε hε).tendsto_div_nhds_zero

/-- Exercise 650_4, gap 4. -/
theorem gap4 (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
      Real.log (fun x => 1 / power ε x) := by
  exact log_isLittleO_reciprocal_power ε hε

/-- Exercise 650_4, gap 5. -/
theorem gap5 (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
      Real.log (fun x => 1 / power ε x) := by
  exact gap4 ε hε

end

end ProofGap.Exercise650_4
