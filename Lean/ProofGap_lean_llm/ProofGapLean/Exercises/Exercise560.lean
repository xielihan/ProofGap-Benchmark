import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise560

noncomputable section

def original (a x : ℝ) : ℝ :=
  (Real.rpow a (Real.rpow a x) - Real.rpow a (Real.rpow x a)) /
    (Real.rpow a x - Real.rpow x a)
def factored (a x : ℝ) : ℝ :=
  Real.rpow a (Real.rpow x a) *
    ((Real.rpow a (Real.rpow a x - Real.rpow x a) - 1) /
      (Real.rpow a x - Real.rpow x a))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 560, gap 1. -/
private theorem original_eq_factored (a : ℝ) (ha : 0 < a) :
    original a = factored a := by
  funext x
  unfold original factored
  have hrpow_sub (u v : ℝ) :
      Real.rpow a u = Real.rpow a v * Real.rpow a (u - v) := by
    have hu : Real.rpow a u = Real.exp (Real.log a * u) :=
      Real.rpow_def_of_pos ha u
    have hv : Real.rpow a v = Real.exp (Real.log a * v) :=
      Real.rpow_def_of_pos ha v
    have huv : Real.rpow a (u - v) =
        Real.exp (Real.log a * (u - v)) :=
      Real.rpow_def_of_pos ha (u - v)
    rw [hu, hv, huv, ← Real.exp_add]
    congr 1
    ring
  rw [hrpow_sub (Real.rpow a x) (Real.rpow x a)]
  ring

private theorem rpow_sub_ne_zero_eventually (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ,
      Real.rpow a x - Real.rpow x a ≠ 0 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hxpos : ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, 0 < x := by
    exact
      (show ∀ᶠ x : ℝ in nhds a, 0 < x from
        isOpen_Ioi.mem_nhds ha).filter_mono inf_le_left
  have hxne : ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, x ≠ a := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (self_mem_nhdsWithin :
        ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, x ∈ ({a} : Set ℝ)ᶜ)
  have hdivne :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, x / a ≠ 1 := by
    filter_upwards [hxne] with x hx
    intro h
    exact hx ((div_eq_one_iff_eq ha0).mp h)
  have hdivcont :
      Filter.Tendsto (fun x : ℝ => x / a) (nhds a) (nhds 1) := by
    have hcont : ContinuousAt (fun x : ℝ => x / a) a :=
      continuousAt_id.div_const a
    simpa only [ContinuousAt, div_self ha0] using hcont
  have hdiv :
      Filter.Tendsto (fun x : ℝ => x / a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hdivcont.mono_left inf_le_left, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hdivne
  by_cases hla : Real.log a = 1
  · filter_upwards [hxpos, hxne, hdivne] with x hx hxna hyne
    intro hz
    have heq : Real.rpow a x = Real.rpow x a := sub_eq_zero.mp hz
    have hlogs : x * Real.log a = a * Real.log x := by
      calc
        x * Real.log a = Real.log (Real.rpow a x) :=
          (Real.log_rpow ha x).symm
        _ = Real.log (Real.rpow x a) := congrArg Real.log heq
        _ = a * Real.log x := Real.log_rpow hx a
    have hypos : 0 < x / a := div_pos hx ha
    have hstrict := Real.log_lt_sub_one_of_pos hypos hyne
    rw [Real.log_div (ne_of_gt hx) ha0, hla] at hstrict
    have hscaled := mul_lt_mul_of_pos_left hstrict ha
    field_simp [ha0] at hscaled
    simp [hla] at hlogs
    nlinarith
  · have hslope :=
      (Real.hasDerivAt_log (by exact one_ne_zero)).tendsto_slope
    have hone : (1 : ℝ)⁻¹ = 1 := by norm_num
    rw [hone] at hslope
    have hq :
        Filter.Tendsto
          (fun x : ℝ => slope Real.log 1 (x / a))
          (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) :=
      hslope.comp hdiv
    have hmem : ({Real.log a} : Set ℝ)ᶜ ∈ nhds (1 : ℝ) :=
      isOpen_compl_singleton.mem_nhds (by
        simpa using (Ne.symm hla))
    have hqne :
        ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ,
          slope Real.log 1 (x / a) ≠ Real.log a := by
      have he := hq hmem
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using he
    filter_upwards [hxpos, hxne, hdivne, hqne] with x hx hxna hyne hne
    intro hz
    have heq : Real.rpow a x = Real.rpow x a := sub_eq_zero.mp hz
    have hlogs : x * Real.log a = a * Real.log x := by
      calc
        x * Real.log a = Real.log (Real.rpow a x) :=
          (Real.log_rpow ha x).symm
        _ = Real.log (Real.rpow x a) := congrArg Real.log heq
        _ = a * Real.log x := Real.log_rpow hx a
    apply hne
    have hquot :
        (Real.log (x / a) - Real.log 1) / (x / a - 1) =
          Real.log a := by
      rw [Real.log_one, sub_zero, Real.log_div (ne_of_gt hx) ha0]
      have hnum :
          Real.log x - Real.log a =
            (x - a) * Real.log a / a := by
        field_simp [ha0]
        nlinarith [hlogs]
      have hden : x / a - 1 = (x - a) / a := by
        field_simp [ha0]
      rw [hnum, hden]
      field_simp [ha0, sub_ne_zero.mpr hxna]
    simpa [slope, div_eq_mul_inv, mul_comm] using hquot

theorem gap1 (a : ℝ) (ha : 0 < a) (L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (factored a) a L := by
  unfold HasLimitAt
  rw [original_eq_factored a ha]

/-- Exercise 560, gap 2. -/
theorem gap2 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (factored a) a
      (Real.rpow a (Real.rpow a a) * Real.log a) := by
  let g : ℝ → ℝ := fun x =>
    Real.rpow a x - Real.rpow x a
  let m : ℝ → ℝ := fun x =>
    Real.exp (Real.log a * x) - Real.exp (Real.log x * a)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hleftArg : ContinuousAt (fun x : ℝ => Real.log a * x) a :=
    continuousAt_const.mul continuousAt_id
  have hrightArg : ContinuousAt (fun x : ℝ => Real.log x * a) a :=
    (Real.continuousAt_log ha0).mul continuousAt_const
  have hm : ContinuousAt m a := by
    dsimp [m]
    exact
      (Real.continuous_exp.continuousAt.comp hleftArg).sub
        (Real.continuous_exp.continuousAt.comp hrightArg)
  have hma : m a = 0 := by
    simp [m]
  have hmt : Filter.Tendsto m (nhds a) (nhds 0) := by
    rw [← hma]
    exact hm
  have hgm : g =ᶠ[nhds a] m := by
    filter_upwards [isOpen_Ioi.mem_nhds ha] with x hx
    simp [g, m, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hx]
  have hgn : Filter.Tendsto g (nhds a) (nhds 0) :=
    hmt.congr' hgm.symm
  have hg : Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hgn.mono_left inf_le_left, ?_⟩
    simpa [g, Set.mem_compl_iff, Set.mem_singleton_iff] using
      rpow_sub_ne_zero_eventually a ha
  have hexpslope := (Real.hasDerivAt_exp 0).tendsto_slope
  rw [Real.exp_zero] at hexpslope
  have hslope :
      Filter.Tendsto
        (fun y : ℝ => (Real.rpow a y - 1) / y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.log a)) := by
    let c : ℝ := Real.log a
    by_cases hc : c = 0
    · simpa [c, hc, Real.rpow_def_of_pos ha] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => 0)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0))
    · have hlin0 :
          Filter.Tendsto (fun y : ℝ => c * y) (nhds 0) (nhds 0) := by
        have hcont : ContinuousAt (fun y : ℝ => c * y) 0 :=
          continuousAt_const.mul continuousAt_id
        simpa only [ContinuousAt, mul_zero] using hcont
      have hlin :
          Filter.Tendsto (fun y : ℝ => c * y)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hlin0.mono_left inf_le_left, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          mul_ne_zero hc hy0
      have ht :
          Filter.Tendsto
            (fun y : ℝ => c * slope Real.exp 0 (c * y))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (c * 1)) := by
        simpa using
          (tendsto_const_nhds.mul (hexpslope.comp hlin))
      have hevent :
          (fun y : ℝ => (Real.rpow a y - 1) / y) =ᶠ[
            nhdsWithin 0 ({0} : Set ℝ)ᶜ]
          (fun y : ℝ => c * slope Real.exp 0 (c * y)) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
        have hrpow : Real.rpow a y = Real.exp (c * y) := by
          dsimp [c]
          exact Real.rpow_def_of_pos ha y
        have hquot :
            (Real.rpow a y - 1) / y =
              c * ((Real.exp (c * y) - Real.exp 0) / (c * y - 0)) := by
          rw [hrpow]
          simp only [Real.exp_zero, sub_zero]
          field_simp [hc, hy0] <;> ring
        simpa [slope, div_eq_mul_inv, mul_comm] using hquot
      simpa [c] using ht.congr' hevent.symm
  let p : ℝ → ℝ := fun x =>
    Real.exp (Real.log a * Real.exp (Real.log x * a))
  have hpInner :
      ContinuousAt (fun x : ℝ => Real.exp (Real.log x * a)) a :=
    Real.continuous_exp.continuousAt.comp hrightArg
  have hpOuterArg :
      ContinuousAt
        (fun x : ℝ => Real.log a * Real.exp (Real.log x * a)) a :=
    continuousAt_const.mul hpInner
  have hpcont : ContinuousAt p a := by
    dsimp [p]
    exact Real.continuous_exp.continuousAt.comp hpOuterArg
  have hpa : p a = Real.rpow a (Real.rpow a a) := by
    simp [p, Real.rpow_def_of_pos ha]
  have hpt : Filter.Tendsto p (nhds a)
      (nhds (Real.rpow a (Real.rpow a a))) := by
    rw [← hpa]
    exact hpcont
  have hpm : (fun x => Real.rpow a (Real.rpow x a)) =ᶠ[nhds a] p := by
    filter_upwards [isOpen_Ioi.mem_nhds ha] with x hx
    simp [p, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hx]
  have hp : Filter.Tendsto
      (fun x => Real.rpow a (Real.rpow x a))
      (nhdsWithin a ({a} : Set ℝ)ᶜ)
      (nhds (Real.rpow a (Real.rpow a a))) :=
    (hpt.congr' hpm.symm).mono_left inf_le_left
  simpa [factored, g] using hp.mul (hslope.comp hg)

/-- Exercise 560, gap 3. -/
theorem gap3 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (original a) a
      (Real.rpow a (Real.rpow a a) * Real.log a) := by
  exact (gap1 a ha _).mpr (gap2 a ha)

end

end ProofGap.Exercise560
