import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise963

noncomputable section

def rootForm (x : ℝ) : ℝ := Real.rpow x (1 / x)
def y (x : ℝ) : ℝ := rootForm x
def exponentialForm (x : ℝ) : ℝ :=
  Real.exp ((1 / x) * Real.log x)
def derivativeFormula (x : ℝ) : ℝ :=
  Real.rpow x (1 / x - 2) * (1 - Real.log x)

def IsMaximumPointOn (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) : Prop :=
  x ∈ s ∧ ∀ z ∈ s, f z ≤ f x

def IsMinimumPointOn (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) : Prop :=
  x ∈ s ∧ ∀ z ∈ s, f x ≤ f z

theorem gap1 (x : ℝ) (hx : 0 < x) : y x = rootForm x := by
  rfl

theorem gap2 (x : ℝ) (hx : 0 < x) :
    rootForm x = exponentialForm x := by
  simpa [rootForm, exponentialForm, Real.rpow_def_of_pos hx, mul_comm]

theorem gap3 (x : ℝ) (hx : 0 < x) :
    y x = exponentialForm x := by
  rw [gap1 x hx, gap2 x hx]

theorem gap4 (x : ℝ) (hx : 0 < x) :
    deriv y x = deriv exponentialForm x := by
  have hlocal : y =ᶠ[nhds x] exponentialForm := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact gap3 z (show 0 < z from hz)
  exact hlocal.deriv_eq

theorem gap5 (x : ℝ) (hx : 0 < x) :
    HasDerivAt exponentialForm (derivativeFormula x) x := by
  have hrecip :
      HasDerivAt (fun z : ℝ => 1 / z) (-1 / x ^ 2) x := by
    simpa only [Pi.div_apply, id_eq, zero_mul, one_mul, zero_sub] using
      ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx.ne')
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log hx.ne'
  have hinner :
      HasDerivAt (fun z : ℝ => (1 / z) * Real.log z)
        ((1 - Real.log x) / x ^ 2) x := by
    convert hrecip.mul hlog using 1 <;>
      field_simp [hx.ne'] <;> ring
  have hout :
      HasDerivAt exponentialForm
        (Real.exp ((1 / x) * Real.log x) *
          ((1 - Real.log x) / x ^ 2)) x := by
    simpa only [exponentialForm] using hinner.exp
  convert hout using 1
  unfold derivativeFormula
  have hrpow :
      Real.rpow x (1 / x - 2) =
        Real.exp (Real.log x * (1 / x - 2)) := by
    exact Real.rpow_def_of_pos hx _
  have hfactor :
      Real.exp (Real.log x * (1 / x - 2)) =
        Real.exp ((1 / x) * Real.log x) / x ^ 2 := by
    rw [show Real.log x * (1 / x - 2) =
        (1 / x) * Real.log x - (Real.log x + Real.log x) by ring]
    rw [Real.exp_sub, Real.exp_add, Real.exp_log hx]
    ring
  rw [hrpow, hfactor]
  ring

theorem gap6 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (derivativeFormula x) x := by
  have hlocal : y =ᶠ[nhds x] exponentialForm := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact gap3 z (show 0 < z from hz)
  rw [hlocal.hasDerivAt_iff]
  exact gap5 x hx

theorem gap7 (x : ℝ) (hx : 0 < x) :
    deriv y x = 0 ↔ 1 - Real.log x = 0 := by
  rw [(gap6 x hx).deriv]
  change
    Real.rpow x (1 / x - 2) * (1 - Real.log x) = 0 ↔
      1 - Real.log x = 0
  constructor
  · intro h
    have hpow : Real.rpow x (1 / x - 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hx _)
    exact (mul_eq_zero.mp h).resolve_left hpow
  · intro h
    exact mul_eq_zero_of_right _ h

theorem gap8 (x : ℝ) (hx : 0 < x) :
    deriv y x = 0 ↔ x = Real.exp 1 := by
  rw [gap7 x hx]
  constructor
  · intro h
    have hlog : Real.log x = 1 := by linarith
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ = Real.exp 1 := congrArg Real.exp hlog
  · intro h
    rw [h, Real.log_exp]
    norm_num

theorem gap9 (x : ℝ) (hx : 0 < x) :
    x ∈ ({Real.exp 1} : Set ℝ) ↔ deriv y x = 0 := by
  simpa only [Set.mem_singleton_iff] using (gap8 x hx).symm

theorem gap10 (x : ℝ) (hx0 : 0 < x) (hxe : x < Real.exp 1) :
    0 < deriv y x := by
  have hlog : Real.log x < 1 := by
    have h := Real.strictMonoOn_log hx0 (Real.exp_pos 1) hxe
    simpa using h
  rw [(gap6 x hx0).deriv]
  exact mul_pos (Real.rpow_pos_of_pos hx0 _) (sub_pos.mpr hlog)

theorem gap11 :
    StrictMonoOn y (Set.Ioo 0 (Real.exp 1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (Real.exp 1))
  · intro x hx
    exact (gap6 x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.exp 1) := interior_subset hx
    exact gap10 x hx'.1 hx'.2

theorem gap12 (x : ℝ) (hx : Real.exp 1 < x) :
    deriv y x < 0 := by
  have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
  have hlog : 1 < Real.log x := by
    have h := Real.strictMonoOn_log (Real.exp_pos 1) hx0 hx
    simpa using h
  rw [(gap6 x hx0).deriv]
  exact mul_neg_of_pos_of_neg
    (Real.rpow_pos_of_pos hx0 _) (sub_neg.mpr hlog)

theorem gap13 :
    StrictAntiOn y (Set.Ioi (Real.exp 1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (Real.exp 1))
  · intro x hx
    have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
    exact (gap6 x hx0).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioi (Real.exp 1) := interior_subset hx
    exact gap12 x (show Real.exp 1 < x from hx')

theorem gap14 :
    IsMaximumPointOn y (Set.Ioi 0) (Real.exp 1) := by
  refine ⟨Real.exp_pos 1, ?_⟩
  intro z hz
  have hz0 : 0 < z := hz
  rw [gap3 z hz0, gap3 (Real.exp 1) (Real.exp_pos 1)]
  unfold exponentialForm
  apply Real.exp_le_exp.mpr
  have ht : 0 < z / Real.exp 1 :=
    div_pos hz0 (Real.exp_pos 1)
  have hbound := Real.log_le_sub_one_of_pos ht
  rw [Real.log_div hz0.ne' (Real.exp_pos 1).ne', Real.log_exp] at hbound
  have hlogz : Real.log z ≤ z / Real.exp 1 := by
    linarith
  calc
    (1 / z) * Real.log z ≤ (1 / z) * (z / Real.exp 1) :=
      mul_le_mul_of_nonneg_left hlogz (le_of_lt (one_div_pos.mpr hz0))
    _ = 1 / Real.exp 1 := by
      field_simp [hz0.ne', (Real.exp_pos 1).ne']
    _ = (1 / Real.exp 1) * Real.log (Real.exp 1) := by
      rw [Real.log_exp]
      ring

theorem gap15 :
    y (Real.exp 1) = rootForm (Real.exp 1) := by
  exact gap1 (Real.exp 1) (Real.exp_pos 1)

theorem gap16 :
    ¬ ∃ x : ℝ, IsMinimumPointOn y (Set.Ioi 0) x := by
  rintro ⟨x, hx0, hmin⟩
  have hxpos : 0 < x := hx0
  by_cases hxe : x < Real.exp 1
  · have hz0 : 0 < x / 2 :=
      div_pos hxpos (by norm_num)
    have hzlt : x / 2 < x := by linarith
    have hze : x / 2 < Real.exp 1 := lt_trans hzlt hxe
    have hstrict : y (x / 2) < y x :=
      gap11 ⟨hz0, hze⟩ ⟨hxpos, hxe⟩ hzlt
    exact (not_lt_of_ge (hmin (x / 2) hz0)) hstrict
  · have hexp_le : Real.exp 1 ≤ x := le_of_not_gt hxe
    have hone_exp : 1 < Real.exp 1 := by
      have h := Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
      simpa using h
    have hx1 : 1 < x := lt_of_lt_of_le hone_exp hexp_le
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hyx : 1 < y x := by
      rw [gap3 x hxpos]
      unfold exponentialForm
      have hinner : 0 < (1 / x) * Real.log x :=
        mul_pos (one_div_pos.mpr hxpos) hlog
      have h := Real.exp_lt_exp.mpr hinner
      simpa using h
    have hyone : y 1 = 1 := by
      simp [y, rootForm]
    have hmin_one := hmin 1 (show (0 : ℝ) < 1 by norm_num)
    rw [hyone] at hmin_one
    exact (not_lt_of_ge hmin_one) hyx

end

end ProofGap.Exercise963
