import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1006

open Filter

noncomputable section

def f (x : ℝ) : ℝ := abs (Real.log (abs x))
def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

def rawDerivative (x : ℝ) : ℝ :=
  abs (Real.log (abs x)) / Real.log (abs x) * (1 / abs x) * (abs x / x)

def finalDerivative (x : ℝ) : ℝ :=
  (1 / x) * (abs (Real.log (abs x)) / Real.log (abs x))

def logQuotient (h : ℝ) : ℝ :=
  abs (Real.log (abs (1 + h))) / h

def powerModel (h : ℝ) : ℝ :=
  abs (Real.log (Real.rpow (1 + h) (1 / h)))

private theorem deriv_sides {g : ℝ → ℝ} {g' a : ℝ}
    (hg : HasDerivAt g g' a) :
    HasLeftDerivAt g g' a ∧ HasRightDerivAt g g' a := by
  have ht : Tendsto (dq g a) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds g') := by
    simpa [dq, div_eq_mul_inv, mul_comm] using
      (hasDerivAt_iff_tendsto_slope_zero.mp hg)
  constructor
  · exact ht.mono_left (nhdsWithin_mono 0 (by
      intro h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_lt hh))
  · exact ht.mono_left (nhdsWithin_mono 0 (by
      intro h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hh))

private theorem raw_eq_final (x : ℝ) (hx1 : |x| ≠ 1) :
    rawDerivative x = finalDerivative x := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [rawDerivative, finalDerivative]
  · have hax : 0 < |x| := abs_pos.mpr hx0
    have hlog : Real.log |x| ≠ 0 := by
      rcases lt_or_gt_of_ne hx1 with hlt | hgt
      · exact (Real.log_neg hax hlt).ne
      · exact (Real.log_pos hgt).ne'
    unfold rawDerivative finalDerivative
    field_simp [hx0, abs_ne_zero.mpr hx0, hlog] <;> ring

private theorem hasDerivAt_f_final (x : ℝ) (hx0 : x ≠ 0) (hx1 : |x| ≠ 1) :
    HasDerivAt f (finalDerivative x) x := by
  have hax : 0 < |x| := abs_pos.mpr hx0
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · have hlogabs : Real.log |x| < 0 := Real.log_neg hax hlt
    have hlog : Real.log x < 0 := by
      simpa only [Real.log_abs] using hlogabs
    have hev : ∀ᶠ y : ℝ in nhds x, Real.log y < 0 :=
      (Real.hasDerivAt_log hx0).continuousAt (Iio_mem_nhds hlog)
    have heq : f =ᶠ[nhds x] (fun y : ℝ => -Real.log y) := by
      filter_upwards [hev] with y hy
      simp [f, Real.log_abs, abs_of_neg hy]
    have hdf : HasDerivAt f (-x⁻¹) x :=
      (Real.hasDerivAt_log hx0).neg.congr_of_eventuallyEq heq
    have hfinal : finalDerivative x = -x⁻¹ := by
      unfold finalDerivative
      rw [Real.log_abs, abs_of_neg hlog]
      field_simp [hx0, hlog.ne] <;> ring
    rw [hfinal]
    exact hdf
  · have hlogabs : 0 < Real.log |x| := Real.log_pos hgt
    have hlog : 0 < Real.log x := by
      simpa only [Real.log_abs] using hlogabs
    have hev : ∀ᶠ y : ℝ in nhds x, 0 < Real.log y :=
      (Real.hasDerivAt_log hx0).continuousAt (Ioi_mem_nhds hlog)
    have heq : f =ᶠ[nhds x] Real.log := by
      filter_upwards [hev] with y hy
      simp [f, Real.log_abs, abs_of_pos hy]
    have hdf : HasDerivAt f (1 / x) x := by
      simpa [one_div] using
        (Real.hasDerivAt_log hx0).congr_of_eventuallyEq heq
    have hfinal : finalDerivative x = 1 / x := by
      unfold finalDerivative
      rw [Real.log_abs, abs_of_pos hlog]
      field_simp [hx0, hlog.ne'] <;> ring
    rw [hfinal]
    exact hdf

private theorem powerModel_eventually_eq :
    powerModel =ᶠ[nhdsWithin 0 (Set.Iio 0)]
      (fun h : ℝ => Real.log (1 + h) / h) := by
  have hm : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) :=
    Ioi_mem_nhds (by norm_num)
  have hnear : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Iio 0), -1 < h := by
    exact (show nhdsWithin (0 : ℝ) (Set.Iio 0) ≤ nhds (0 : ℝ) from inf_le_left) hm
  filter_upwards [hnear, self_mem_nhdsWithin] with h hlower hupper
  change h < 0 at hupper
  have hb : 0 < 1 + h := by linarith
  have hlog : Real.log (1 + h) < 0 :=
    Real.log_neg hb (by linarith)
  have hinv : 1 / h < 0 := div_neg_of_pos_of_neg zero_lt_one hupper
  have hprod : 0 < Real.log (1 + h) * (1 / h) :=
    mul_pos_of_neg_of_neg hlog hinv
  change |Real.log ((1 + h) ^ (1 / h : ℝ))| = Real.log (1 + h) / h
  rw [Real.rpow_def_of_pos hb, Real.log_exp, abs_of_pos hprod] <;> ring

private theorem logQuotient_eventually_eq :
    logQuotient =ᶠ[nhdsWithin 0 (Set.Iio 0)]
      (fun h : ℝ => -(Real.log (1 + h) / h)) := by
  have hm : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) :=
    Ioi_mem_nhds (by norm_num)
  have hnear : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Iio 0), -1 < h := by
    exact (show nhdsWithin (0 : ℝ) (Set.Iio 0) ≤ nhds (0 : ℝ) from inf_le_left) hm
  filter_upwards [hnear, self_mem_nhdsWithin] with h hlower hupper
  change h < 0 at hupper
  have hb : 0 < 1 + h := by linarith
  have hlog : Real.log (1 + h) < 0 :=
    Real.log_neg hb (by linarith)
  rw [logQuotient, abs_of_pos hb, abs_of_neg hlog]
  ring

theorem gap1 (x : ℝ) (hx0 : x ≠ 0) (hx1 : |x| ≠ 1) :
    HasLeftDerivAt f (finalDerivative x) x ∧
      HasRightDerivAt f (finalDerivative x) x := by
  exact deriv_sides (hasDerivAt_f_final x hx0 hx1)

theorem gap2 (x : ℝ) (hx0 : x ≠ 0) (hx1 : |x| ≠ 1) :
    HasRightDerivAt f (rawDerivative x) x := by
  rw [raw_eq_final x hx1]
  exact (gap1 x hx0 hx1).2

theorem gap3 (x : ℝ) (hx1 : |x| ≠ 1) :
    rawDerivative x = finalDerivative x := by
  exact raw_eq_final x hx1

theorem gap4 (x : ℝ) (hx0 : x ≠ 0) (hx1 : |x| ≠ 1) :
    HasLeftDerivAt f (finalDerivative x) x := by
  exact (gap1 x hx0 hx1).1

theorem gap5 (x : ℝ) (hx0 : 0 < |x|) (hx1 : |x| < 1) :
    HasLeftDerivAt f (-1 / x) x ∧
      HasRightDerivAt f (-1 / x) x := by
  have hx : x ≠ 0 := abs_pos.mp hx0
  have hlog : Real.log |x| < 0 := Real.log_neg hx0 hx1
  have hlogx : Real.log x < 0 := by
    simpa only [Real.log_abs] using hlog
  have heq : finalDerivative x = -1 / x := by
    unfold finalDerivative
    rw [Real.log_abs, abs_of_neg hlogx]
    field_simp [hx, hlogx.ne] <;> ring
  rw [← heq]
  exact gap1 x hx (ne_of_lt hx1)

theorem gap6 (x : ℝ) (hx0 : 0 < |x|) (hx1 : |x| < 1) :
    HasRightDerivAt f (-1 / x) x := by
  exact (gap5 x hx0 hx1).2

theorem gap7 (x : ℝ) (hx0 : 0 < |x|) (hx1 : |x| < 1) :
    HasLeftDerivAt f (-1 / x) x := by
  exact (gap5 x hx0 hx1).1

theorem gap8 (x : ℝ) (hx : 1 < |x|) :
    HasLeftDerivAt f (1 / x) x ∧
      HasRightDerivAt f (1 / x) x := by
  have hx0 : x ≠ 0 := abs_pos.mp (lt_trans zero_lt_one hx)
  have hlog : 0 < Real.log |x| := Real.log_pos hx
  have hlogx : 0 < Real.log x := by
    simpa only [Real.log_abs] using hlog
  have heq : finalDerivative x = 1 / x := by
    unfold finalDerivative
    rw [Real.log_abs, abs_of_pos hlogx]
    field_simp [hx0, hlogx.ne'] <;> ring
  rw [← heq]
  exact gap1 x hx0 (ne_of_gt hx)

theorem gap9 (x : ℝ) (hx : 1 < |x|) :
    HasRightDerivAt f (1 / x) x := by
  exact (gap8 x hx).2

theorem gap10 (x : ℝ) (hx : 1 < |x|) :
    HasLeftDerivAt f (1 / x) x := by
  exact (gap8 x hx).1

theorem gap11 (L : ℝ) :
    Tendsto (dq f 1) (nhdsWithin 0 (Set.Iio 0)) (nhds L) ↔
      Tendsto logQuotient (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  have heq : dq f 1 = logQuotient := by
    funext h
    simp [dq, f, logQuotient]
  rw [heq]

theorem gap12 (L : ℝ) :
    Tendsto logQuotient (nhdsWithin 0 (Set.Iio 0)) (nhds (-L)) ↔
      Tendsto powerModel (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  let r : ℝ → ℝ := fun h => Real.log (1 + h) / h
  have hp : powerModel =ᶠ[nhdsWithin 0 (Set.Iio 0)] r := by
    simpa [r] using powerModel_eventually_eq
  have hq : logQuotient =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun h => -r h) := by
    simpa [r] using logQuotient_eventually_eq
  constructor
  · intro h
    have hn : Tendsto (fun h => -r h) (nhdsWithin 0 (Set.Iio 0)) (nhds (-L)) :=
      h.congr' hq
    have hr : Tendsto r (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
      simpa using hn.neg
    exact hr.congr' hp.symm
  · intro h
    have hr : Tendsto r (nhdsWithin 0 (Set.Iio 0)) (nhds L) :=
      h.congr' hp
    have hn : Tendsto (fun h => -r h) (nhdsWithin 0 (Set.Iio 0)) (nhds (-L)) := by
      simpa using hr.neg
    exact hn.congr' hq.symm

theorem gap13 :
    Tendsto powerModel (nhdsWithin 0 (Set.Iio 0))
      (nhds (Real.log (Real.exp 1))) := by
  have hd : HasDerivAt Real.log 1 1 := by
    simpa using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have ht : Tendsto (dq Real.log 1) (nhdsWithin 0 (Set.Iio 0)) (nhds 1) :=
    (deriv_sides hd).1
  have heq : dq Real.log 1 = (fun h : ℝ => Real.log (1 + h) / h) := by
    funext h
    simp [dq]
  have hr : Tendsto (fun h : ℝ => Real.log (1 + h) / h)
      (nhdsWithin 0 (Set.Iio 0)) (nhds 1) := by
    rw [← heq]
    exact ht
  have hp := hr.congr' powerModel_eventually_eq.symm
  simpa using hp

theorem gap14 :
    -Real.log (Real.exp 1) = (-1 : ℝ) := by
  simp

theorem gap15 :
    HasLeftDerivAt f (-1) 1 := by
  have hp := gap13
  have hq := (gap12 (Real.log (Real.exp 1))).mpr hp
  have hd := (gap11 (-Real.log (Real.exp 1))).mpr hq
  simpa [HasLeftDerivAt] using hd

theorem gap16 :
    HasLeftDerivAt f (-1) (-1) := by
  have hd : HasDerivAt Real.log (-1) (-1) := by
    simpa using (Real.hasDerivAt_log (by norm_num : (-1 : ℝ) ≠ 0))
  have ht : HasLeftDerivAt Real.log (-1) (-1) := (deriv_sides hd).1
  have heq : dq f (-1) =ᶠ[nhdsWithin 0 (Set.Iio 0)] dq Real.log (-1) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change h < 0 at hh
    have hy : -1 + h < 0 := by linarith
    have ha : 1 < |-1 + h| := by
      rw [abs_of_neg hy]
      linarith
    have hl : 0 < Real.log |-1 + h| := Real.log_pos ha
    have hlx : 0 < Real.log (-1 + h) := by
      simpa only [Real.log_abs] using hl
    simp [dq, f, Real.log_abs, abs_of_pos hlx]
  exact ht.congr' heq.symm

theorem gap17 :
    HasRightDerivAt f 1 1 := by
  have hd : HasDerivAt Real.log 1 1 := by
    simpa using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have ht : HasRightDerivAt Real.log 1 1 := (deriv_sides hd).2
  have heq : dq f 1 =ᶠ[nhdsWithin 0 (Set.Ioi 0)] dq Real.log 1 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    have hb : 1 < 1 + h := by linarith
    have hl : 0 < Real.log (1 + h) := Real.log_pos hb
    simp [dq, f, abs_of_pos (lt_trans zero_lt_one hb), abs_of_pos hl]
  exact ht.congr' heq.symm

theorem gap18 :
    HasRightDerivAt f 1 (-1) := by
  have hd : HasDerivAt (fun y : ℝ => -Real.log y) 1 (-1) := by
    simpa using (Real.hasDerivAt_log (by norm_num : (-1 : ℝ) ≠ 0)).neg
  have ht : HasRightDerivAt (fun y : ℝ => -Real.log y) 1 (-1) :=
    (deriv_sides hd).2
  have hm : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
    Iio_mem_nhds (by norm_num)
  have hupper : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < 1 := by
    exact (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left) hm
  have heq : dq f (-1) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      dq (fun y : ℝ => -Real.log y) (-1) := by
    filter_upwards [self_mem_nhdsWithin, hupper] with h hh hu
    change 0 < h at hh
    have hy : -1 + h < 0 := by linarith
    have ha0 : 0 < |-1 + h| := abs_pos.mpr (ne_of_lt hy)
    have ha1 : |-1 + h| < 1 := by
      rw [abs_of_neg hy]
      linarith
    have hl : Real.log |-1 + h| < 0 := Real.log_neg ha0 ha1
    have hlx : Real.log (-1 + h) < 0 := by
      simpa only [Real.log_abs] using hl
    simp [dq, f, Real.log_abs, abs_of_neg hlx]
  exact ht.congr' heq.symm

end

end ProofGap.Exercise1006
