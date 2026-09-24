import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1007

open Filter

noncomputable section

def f (x : ℝ) : ℝ := Real.arcsin (2 * x / (1 + x ^ 2))
def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

def rawDerivative (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) *
    ((2 * (1 + x ^ 2) - 4 * x ^ 2) / (1 + x ^ 2) ^ 2)

def middleDerivative (x : ℝ) : ℝ :=
  2 * (1 - x ^ 2) / ((1 + x ^ 2) * Real.sqrt ((1 - x ^ 2) ^ 2))

def finalDerivative (x : ℝ) : ℝ :=
  2 / (1 + x ^ 2) * Real.sign (1 - x ^ 2)

def cuspModel (h : ℝ) : ℝ :=
  (Real.arcsin (2 * (1 + h) / (1 + (1 + h) ^ 2)) - Real.arcsin 1) / h

private theorem one_sided_of_derivative {g : ℝ → ℝ} {g' a : ℝ}
    (hg : HasDerivAt g g' a) :
    HasLeftDerivAt g g' a ∧ HasRightDerivAt g g' a := by
  have ht : Tendsto (dq g a)
      (nhdsWithin (0 : ℝ) (Set.compl {0})) (nhds g') := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at hg
    simpa [dq, div_eq_mul_inv, mul_comm] using hg
  constructor
  · apply ht.mono_left
    apply nhdsWithin_mono
    intro h hh
    exact ne_of_lt hh
  · apply ht.mono_left
    apply nhdsWithin_mono
    intro h hh
    exact ne_of_gt hh

private theorem left_derivative_of_local_eq {g m : ℝ → ℝ} {g' a : ℝ}
    (hm : HasDerivAt m g' a)
    (heq : ∀ᶠ h in nhdsWithin 0 (Set.Iio 0), g (a + h) = m (a + h))
    (hbase : g a = m a) : HasLeftDerivAt g g' a := by
  have ht := (one_sided_of_derivative hm).1
  have hdq : dq g a =ᶠ[nhdsWithin 0 (Set.Iio 0)] dq m a := by
    filter_upwards [heq] with h hh
    simp only [dq]
    rw [hh, hbase]
  exact (tendsto_congr' hdq).2 ht

private theorem right_derivative_of_local_eq {g m : ℝ → ℝ} {g' a : ℝ}
    (hm : HasDerivAt m g' a)
    (heq : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), g (a + h) = m (a + h))
    (hbase : g a = m a) : HasRightDerivAt g g' a := by
  have ht := (one_sided_of_derivative hm).2
  have hdq : dq g a =ᶠ[nhdsWithin 0 (Set.Ioi 0)] dq m a := by
    filter_upwards [heq] with h hh
    simp only [dq]
    rw [hh, hbase]
  exact (tendsto_congr' hdq).2 ht

private theorem square_ne_one {x : ℝ} (hx : |x| ≠ 1) : x ^ 2 ≠ 1 := by
  have hx1 : x ≠ 1 := by
    intro h
    apply hx
    simp [h]
  have hxm1 : x ≠ -1 := by
    intro h
    apply hx
    simp [h]
  intro hsq
  have hfac : (x - 1) * (x + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · apply hx1
    linarith
  · apply hxm1
    linarith

private theorem rational_square_identity (x : ℝ) :
    1 - (2 * x / (1 + x ^ 2)) ^ 2 =
      (1 - x ^ 2) ^ 2 / (1 + x ^ 2) ^ 2 := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hd] <;> ring_nf

private theorem inverse_sqrt_identity (x : ℝ) :
    Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) =
      Real.sqrt ((1 - x ^ 2) ^ 2) / (1 + x ^ 2) := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hl : 0 ≤ 1 - (2 * x / (1 + x ^ 2)) ^ 2 := by
    rw [rational_square_identity]
    positivity
  have hs : 0 ≤ Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) :=
    Real.sqrt_nonneg _
  have ht : 0 ≤ Real.sqrt ((1 - x ^ 2) ^ 2) / (1 + x ^ 2) :=
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt hd)
  have hsq :
      Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) ^ 2 =
        (Real.sqrt ((1 - x ^ 2) ^ 2) / (1 + x ^ 2)) ^ 2 := by
    calc
      Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) ^ 2 =
          1 - (2 * x / (1 + x ^ 2)) ^ 2 := Real.sq_sqrt hl
      _ = (1 - x ^ 2) ^ 2 / (1 + x ^ 2) ^ 2 := rational_square_identity x
      _ = (Real.sqrt ((1 - x ^ 2) ^ 2) / (1 + x ^ 2)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (sq_nonneg (1 - x ^ 2))]
  nlinarith [sq_nonneg
    (Real.sqrt (1 - (2 * x / (1 + x ^ 2)) ^ 2) +
      Real.sqrt ((1 - x ^ 2) ^ 2) / (1 + x ^ 2))]

private theorem has_derivative_raw (x : ℝ) (hx : |x| ≠ 1) :
    HasDerivAt f (rawDerivative x) x := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hd0 : 1 + x ^ 2 ≠ 0 := ne_of_gt hd
  have hsquare : x ^ 2 ≠ 1 := square_ne_one hx
  have ha : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hsquare)
  have hp : 0 < 1 - (2 * x / (1 + x ^ 2)) ^ 2 := by
    rw [rational_square_identity]
    exact div_pos (sq_pos_of_ne_zero ha) (by positivity)
  have hbounds : 2 * x / (1 + x ^ 2) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith
  have hne_neg : 2 * x / (1 + x ^ 2) ≠ (-1 : ℝ) := ne_of_gt hbounds.1
  have hne_pos : 2 * x / (1 + x ^ 2) ≠ (1 : ℝ) := ne_of_lt hbounds.2
  have hn : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hden : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      norm_num <;> ring
  have hq0 : HasDerivAt (fun y : ℝ => 2 * y / (1 + y ^ 2))
      ((2 * (1 + x ^ 2) - (2 * x) * (2 * x)) / (1 + x ^ 2) ^ 2) x :=
    hn.div hden hd0
  have hq : HasDerivAt (fun y : ℝ => 2 * y / (1 + y ^ 2))
      ((2 * (1 + x ^ 2) - 4 * x ^ 2) / (1 + x ^ 2) ^ 2) x := by
    convert hq0 using 1 <;> ring
  simpa [f, rawDerivative, one_div] using
    (Real.hasDerivAt_arcsin hne_neg hne_pos).comp x hq

private theorem raw_eq_middle (x : ℝ) (hx : |x| ≠ 1) :
    rawDerivative x = middleDerivative x := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hsquare : x ^ 2 ≠ 1 := square_ne_one hx
  have ha : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hsquare)
  have hs : 0 < Real.sqrt ((1 - x ^ 2) ^ 2) :=
    Real.sqrt_pos.2 (sq_pos_of_ne_zero ha)
  rw [rawDerivative, middleDerivative, inverse_sqrt_identity x]
  field_simp [ne_of_gt hd, ne_of_gt hs] <;> ring

private theorem middle_eq_final (x : ℝ) (hx : |x| ≠ 1) :
    middleDerivative x = finalDerivative x := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hsquare : x ^ 2 ≠ 1 := square_ne_one hx
  have ha : 1 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hsquare)
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · rw [middleDerivative, finalDerivative, Real.sqrt_sq_eq_abs,
      abs_of_neg hneg, Real.sign_of_neg hneg]
    field_simp [hd] <;> ring
  · rw [middleDerivative, finalDerivative, Real.sqrt_sq_eq_abs,
      abs_of_pos hpos, Real.sign_of_pos hpos]
    field_simp [hd] <;> ring

private theorem has_derivative_final (x : ℝ) (hx : |x| ≠ 1) :
    HasDerivAt f (finalDerivative x) x := by
  convert has_derivative_raw x hx using 1
  exact ((raw_eq_middle x hx).trans (middle_eq_final x hx)).symm

private theorem sin_two_arctan (x : ℝ) :
    Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hp : 0 < 1 + x ^ 2 := by positivity
  have hs : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hp)
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  calc
    2 * (x / Real.sqrt (1 + x ^ 2)) *
        (1 / Real.sqrt (1 + x ^ 2)) =
        2 * x / Real.sqrt (1 + x ^ 2) ^ 2 := by
      field_simp [hs] <;> ring
    _ = 2 * x / (1 + x ^ 2) := by
      rw [Real.sq_sqrt (le_of_lt hp)]

private theorem inverse_inside (x : ℝ) (hl : -1 ≤ x) (hu : x ≤ 1) :
    Real.arcsin (2 * x / (1 + x ^ 2)) = 2 * Real.arctan x := by
  have hlo : -(Real.pi / 4) ≤ Real.arctan x := by
    calc
      -(Real.pi / 4) = Real.arctan (-1) := by
        simp [Real.arctan_one]
      _ ≤ Real.arctan x := Real.arctan_mono hl
  have hhi : Real.arctan x ≤ Real.pi / 4 := by
    calc
      Real.arctan x ≤ Real.arctan 1 := Real.arctan_mono hu
      _ = Real.pi / 4 := Real.arctan_one
  rw [← sin_two_arctan x]
  exact Real.arcsin_sin (by nlinarith) (by nlinarith)

private theorem inverse_outer_positive (x : ℝ) (hx : 1 ≤ x) :
    Real.arcsin (2 * x / (1 + x ^ 2)) =
      Real.pi - 2 * Real.arctan x := by
  have hlo : Real.pi / 4 ≤ Real.arctan x := by
    calc
      Real.pi / 4 = Real.arctan 1 := Real.arctan_one.symm
      _ ≤ Real.arctan x := Real.arctan_mono hx
  have hhi := Real.arctan_lt_pi_div_two x
  have hlower : -(Real.pi / 2) ≤ Real.pi - 2 * Real.arctan x := by
    nlinarith [Real.pi_pos]
  have hupper : Real.pi - 2 * Real.arctan x ≤ Real.pi / 2 := by
    nlinarith
  have hsin : Real.sin (Real.pi - 2 * Real.arctan x) =
      2 * x / (1 + x ^ 2) := by
    rw [Real.sin_pi_sub]
    exact sin_two_arctan x
  rw [← hsin]
  exact Real.arcsin_sin hlower hupper

private theorem inverse_outer_negative (x : ℝ) (hx : x ≤ -1) :
    Real.arcsin (2 * x / (1 + x ^ 2)) =
      -Real.pi - 2 * Real.arctan x := by
  have hp := inverse_outer_positive (-x) (by linarith)
  have harg : 2 * (-x) / (1 + (-x) ^ 2) =
      -(2 * x / (1 + x ^ 2)) := by ring
  rw [harg] at hp
  calc
    Real.arcsin (2 * x / (1 + x ^ 2)) =
        -Real.arcsin (-(2 * x / (1 + x ^ 2))) := by
          rw [Real.arcsin_neg]
          simp
    _ = -(Real.pi - 2 * Real.arctan (-x)) := congrArg Neg.neg hp
    _ = -Real.pi - 2 * Real.arctan x := by
      rw [Real.arctan_neg]
      ring

theorem gap1 (x : ℝ) (hx : |x| ≠ 1) :
    HasLeftDerivAt f (finalDerivative x) x ∧
      HasRightDerivAt f (finalDerivative x) x := by
  exact one_sided_of_derivative (has_derivative_final x hx)

theorem gap2 (x : ℝ) (hx : |x| ≠ 1) :
    HasRightDerivAt f (rawDerivative x) x := by
  exact (one_sided_of_derivative (has_derivative_raw x hx)).2

theorem gap3 (x : ℝ) (hx : |x| ≠ 1) :
    rawDerivative x = middleDerivative x := by
  exact raw_eq_middle x hx

theorem gap4 (x : ℝ) (hx : |x| ≠ 1) :
    middleDerivative x = finalDerivative x := by
  exact middle_eq_final x hx

theorem gap5 (x : ℝ) (hx : |x| ≠ 1) :
    HasLeftDerivAt f (finalDerivative x) x := by
  exact (one_sided_of_derivative (has_derivative_final x hx)).1

theorem gap6 (L : ℝ) :
    Tendsto (dq f 1) (nhdsWithin 0 (Set.Iio 0)) (nhds L) ↔
      Tendsto cuspModel (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  have hf1 : f 1 = Real.arcsin 1 := by
    norm_num [f]
  have heq : dq f 1 = cuspModel := by
    funext h
    unfold dq cuspModel
    rw [hf1]
    rfl
  rw [heq]

theorem gap7 :
    Tendsto cuspModel (nhdsWithin 0 (Set.Iio 0)) (nhds 1) := by
  let m : ℝ → ℝ := fun x => 2 * Real.arctan x
  have hm : HasDerivAt m 1 1 := by
    dsimp [m]
    convert (Real.hasDerivAt_arctan 1).const_mul 2 using 1 <;> norm_num
  have ht := (one_sided_of_derivative hm).1
  have hone : Real.arcsin 1 = 2 * Real.arctan 1 := by
    rw [Real.arcsin_one, Real.arctan_one]
    ring
  have hnear : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Iio 0), -1 < h := by
    exact
      (show nhdsWithin (0 : ℝ) (Set.Iio 0) ≤ nhds (0 : ℝ) from inf_le_left)
        (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))
  have heq : cuspModel =ᶠ[nhdsWithin 0 (Set.Iio 0)] dq m 1 := by
    filter_upwards [self_mem_nhdsWithin, hnear] with h hh hlow
    change h < 0 at hh
    have hf := inverse_inside (1 + h) (by linarith) (by linarith)
    simpa only [cuspModel, dq, m, hf, hone]
  exact (tendsto_congr' heq).2 ht

theorem gap8 :
    HasLeftDerivAt f 1 1 := by
  unfold HasLeftDerivAt
  exact (gap6 1).2 gap7

theorem gap9 :
    HasLeftDerivAt f (-1) (-1) := by
  let m : ℝ → ℝ := fun x => -Real.pi - 2 * Real.arctan x
  have ha : HasDerivAt (fun x : ℝ => 2 * Real.arctan x) 1 (-1) := by
    convert (Real.hasDerivAt_arctan (-1)).const_mul 2 using 1 <;> norm_num
  have hc : HasDerivAt (fun _ : ℝ => -Real.pi) 0 (-1) :=
    hasDerivAt_const (-1) (-Real.pi)
  have hm : HasDerivAt m (-1) (-1) := by
    simpa [m] using hc.sub ha
  have heq : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Iio 0),
      f ((-1) + h) = m ((-1) + h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change h < 0 at hh
    simpa only [f, m] using
      inverse_outer_negative ((-1 : ℝ) + h) (by linarith)
  have hbase : f (-1) = m (-1) := by
    simpa only [f, m] using inverse_outer_negative (-1 : ℝ) (by norm_num)
  exact left_derivative_of_local_eq (g := f) (m := m) (a := (-1 : ℝ)) hm heq hbase

theorem gap10 :
    HasRightDerivAt f (-1) 1 := by
  let m : ℝ → ℝ := fun x => Real.pi - 2 * Real.arctan x
  have ha : HasDerivAt (fun x : ℝ => 2 * Real.arctan x) 1 1 := by
    convert (Real.hasDerivAt_arctan 1).const_mul 2 using 1 <;> norm_num
  have hc : HasDerivAt (fun _ : ℝ => Real.pi) 0 1 :=
    hasDerivAt_const 1 Real.pi
  have hm : HasDerivAt m (-1) 1 := by
    simpa [m] using hc.sub ha
  have heq : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      f (1 + h) = m (1 + h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    simpa only [f, m] using inverse_outer_positive (1 + h) (by linarith)
  have hbase : f 1 = m 1 := by
    simpa only [f, m] using inverse_outer_positive (1 : ℝ) (by norm_num)
  exact right_derivative_of_local_eq (g := f) (m := m) (a := (1 : ℝ)) hm heq hbase

theorem gap11 :
    HasRightDerivAt f 1 (-1) := by
  let m : ℝ → ℝ := fun x => 2 * Real.arctan x
  have hm : HasDerivAt m 1 (-1) := by
    dsimp [m]
    convert (Real.hasDerivAt_arctan (-1)).const_mul 2 using 1 <;> norm_num
  have hnear : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < 1 := by
    exact
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left)
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have heq : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      f ((-1) + h) = m ((-1) + h) := by
    filter_upwards [self_mem_nhdsWithin, hnear] with h hh hu
    change 0 < h at hh
    have hf := inverse_inside ((-1 : ℝ) + h) (by linarith) (by linarith)
    simpa only [f, m] using hf
  have hbase : f (-1) = m (-1) := by
    simpa only [f, m] using
      inverse_inside (-1 : ℝ) (by norm_num) (by norm_num)
  exact right_derivative_of_local_eq (g := f) (m := m) (a := (-1 : ℝ)) hm heq hbase

end

end ProofGap.Exercise1007
