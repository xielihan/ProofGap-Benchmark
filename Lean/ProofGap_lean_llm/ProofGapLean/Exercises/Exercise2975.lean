import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2975

noncomputable section

open scoped Interval

def principal (x : ℝ) : ℝ :=
  x - 2 * Real.pi *
    (Int.floor ((x + Real.pi) / (2 * Real.pi)) : ℝ)

def extension (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  let r := principal x
  if 0 < r ∧ r < Real.pi / 2 then f r
  else if Real.pi / 2 < r ∧ r < Real.pi then -f (Real.pi - r)
  else if -Real.pi / 2 < r ∧ r < 0 then f (-r)
  else if -Real.pi < r ∧ r < -Real.pi / 2 then -f (Real.pi + r)
  else 0

def OnRightHalf (f g : ℝ → ℝ) : Prop :=
  ∀ x, Real.pi / 2 < x → x < Real.pi →
    g x = -f (Real.pi - x)

def ExtendsBase (f F : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → x < Real.pi / 2 → F x = f x

def HasRequiredSymmetry (F : ℝ → ℝ) : Prop :=
  (∀ x, -Real.pi < x → x < Real.pi → F (-x) = F x) ∧
    (∀ x, -Real.pi < x → x < Real.pi →
      F (Real.pi - x) = -F x)

def evenModeIntegral (f g : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∫ x in 0..Real.pi / 2,
      f x * Real.cos (2 * (n : ℝ) * x)) +
    ∫ x in Real.pi / 2..Real.pi,
      g x * Real.cos (2 * (n : ℝ) * x)

def transformedEvenModeIntegral (f g : ℝ → ℝ) (n : ℕ) : ℝ :=
  -(∫ y in Real.pi..Real.pi / 2,
      f (Real.pi - y) * Real.cos (2 * (n : ℝ) * y)) +
    ∫ x in Real.pi / 2..Real.pi,
      g x * Real.cos (2 * (n : ℝ) * x)

def combinedEvenModeIntegral (f g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Real.pi / 2..Real.pi,
    (f (Real.pi - x) + g x) * Real.cos (2 * (n : ℝ) * x)

private theorem principal_eq_self {x : ℝ}
    (hlower : -Real.pi < x) (hupper : x < Real.pi) :
    principal x = x := by
  have htwo_pi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfloor :
      Int.floor ((x + Real.pi) / (2 * Real.pi)) = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · exact div_nonneg (by linarith) htwo_pi.le
    · exact (div_lt_one htwo_pi).mpr (by linarith)
  rw [principal, hfloor]
  norm_num

private theorem principal_pi_sub_of_pos {x : ℝ}
    (hx : 0 < x) (hupper : x < Real.pi) :
    principal (Real.pi - x) = Real.pi - x :=
  principal_eq_self (by linarith [Real.pi_pos]) (by linarith)

private theorem principal_pi_sub_of_nonpos {x : ℝ}
    (hlower : -Real.pi < x) (hx : x ≤ 0) :
    principal (Real.pi - x) = -Real.pi - x := by
  have htwo_pi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfloor :
      Int.floor (((Real.pi - x) + Real.pi) / (2 * Real.pi)) = 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · rw [le_div_iff₀ htwo_pi]
      norm_num
      linarith
    · rw [div_lt_iff₀ htwo_pi]
      norm_num
      linarith [Real.pi_pos]
  rw [principal, hfloor]
  norm_num
  ring

private theorem extension_of_principal_base (f : ℝ → ℝ) {z r : ℝ}
    (hr : principal z = r) (hzero : 0 < r) (hhalf : r < Real.pi / 2) :
    extension f z = f r := by
  simp [extension, hr, hzero, hhalf]

private theorem extension_of_principal_right (f : ℝ → ℝ) {z r : ℝ}
    (hr : principal z = r) (hhalf : Real.pi / 2 < r) (hpi : r < Real.pi) :
    extension f z = -f (Real.pi - r) := by
  have hnotbase : ¬(0 < r ∧ r < Real.pi / 2) := by
    intro h
    linarith
  simp [extension, hr, hnotbase, hhalf, hpi]

private theorem extension_of_principal_negbase (f : ℝ → ℝ) {z r : ℝ}
    (hr : principal z = r) (hneghalf : -Real.pi / 2 < r) (hzero : r < 0) :
    extension f z = f (-r) := by
  have hnotbase : ¬(0 < r ∧ r < Real.pi / 2) := by
    intro h
    linarith
  have hnotright : ¬(Real.pi / 2 < r ∧ r < Real.pi) := by
    intro h
    linarith [Real.pi_pos]
  simp [extension, hr, hnotbase, hnotright, hneghalf, hzero]

private theorem extension_of_principal_negleft (f : ℝ → ℝ) {z r : ℝ}
    (hr : principal z = r) (hnegpi : -Real.pi < r)
    (hneghalf : r < -Real.pi / 2) :
    extension f z = -f (Real.pi + r) := by
  have hnotbase : ¬(0 < r ∧ r < Real.pi / 2) := by
    intro h
    linarith [Real.pi_pos]
  have hnotright : ¬(Real.pi / 2 < r ∧ r < Real.pi) := by
    intro h
    linarith [Real.pi_pos]
  have hnotnegbase : ¬(-Real.pi / 2 < r ∧ r < 0) := by
    intro h
    linarith
  simp [extension, hr, hnotbase, hnotright, hnotnegbase, hnegpi, hneghalf]

private theorem extension_of_principal_zero (f : ℝ → ℝ) {z : ℝ}
    (hr : principal z = 0) : extension f z = 0 := by
  simp only [extension, hr]
  split_ifs <;> simp_all <;> linarith [Real.pi_pos]

private theorem extension_of_principal_half (f : ℝ → ℝ) {z : ℝ}
    (hr : principal z = Real.pi / 2) : extension f z = 0 := by
  simp only [extension, hr]
  split_ifs <;> simp_all <;> linarith [Real.pi_pos]

private theorem extension_of_principal_neghalf (f : ℝ → ℝ) {z : ℝ}
    (hr : principal z = -Real.pi / 2) : extension f z = 0 := by
  simp only [extension, hr]
  split_ifs <;> simp_all <;> linarith [Real.pi_pos]

private theorem extension_of_principal_negpi (f : ℝ → ℝ) {z : ℝ}
    (hr : principal z = -Real.pi) : extension f z = 0 := by
  simp only [extension, hr]
  split_ifs <;> simp_all <;> linarith [Real.pi_pos]

private theorem intervalIntegral_congr_Ioo {u v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h : ∀ x, a < x → x < b → u x = v x) :
    (∫ x in a..b, u x) = ∫ x in a..b, v x := by
  apply intervalIntegral.integral_congr_ae
  refine (MeasureTheory.Measure.ae_ne MeasureTheory.volume b).mono ?_
  intro x hxb hx
  rw [Set.uIoc_of_le hab] at hx
  exact h x hx.1 (lt_of_le_of_ne hx.2 hxb)

private theorem even_cos_reflect (n : ℕ) (x : ℝ) :
    Real.cos (2 * (n : ℝ) * (Real.pi - x)) =
      Real.cos (2 * (n : ℝ) * x) := by
  calc
    Real.cos (2 * (n : ℝ) * (Real.pi - x)) =
        Real.cos ((n : ℝ) * (2 * Real.pi) - 2 * (n : ℝ) * x) := by
      congr 1
      ring
    _ = Real.cos (2 * (n : ℝ) * x) :=
      Real.cos_nat_mul_two_pi_sub (2 * (n : ℝ) * x) n

private theorem left_evenModeIntegral_reflect (f : ℝ → ℝ) (n : ℕ) :
    (∫ x in 0..Real.pi / 2,
        f x * Real.cos (2 * (n : ℝ) * x)) =
      ∫ x in Real.pi / 2..Real.pi,
        f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x) := by
  let u : ℝ → ℝ := fun x => f x * Real.cos (2 * (n : ℝ) * x)
  calc
    (∫ x in 0..Real.pi / 2,
        f x * Real.cos (2 * (n : ℝ) * x)) =
        ∫ x in Real.pi / 2..Real.pi, u (Real.pi - x) := by
      symm
      convert intervalIntegral.integral_comp_sub_left
        (f := u) (a := Real.pi / 2) (b := Real.pi) Real.pi using 1 <;>
        simp [u] <;> ring
    _ = ∫ x in Real.pi / 2..Real.pi,
        f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [u]
      rw [even_cos_reflect]

theorem gap1 (f F : ℝ → ℝ) (hF : ∀ x, F x = extension f x) :
    ∀ x, -Real.pi < x → x < Real.pi →
      F (-x) = F x := by
  intro x hlower hupper
  rw [hF (-x), hF x]
  have hpx : principal x = x := principal_eq_self hlower hupper
  have hpneg : principal (-x) = -x :=
    principal_eq_self (by linarith) (by linarith)
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · rcases lt_trichotomy x (-Real.pi / 2) with hxleft | hxhalf | hxbase
    · rw [extension_of_principal_right f hpneg (by linarith) (by linarith),
        extension_of_principal_negleft f hpx hlower hxleft]
      congr 2
      ring
    · have hnegx : -x = Real.pi / 2 := by linarith
      rw [extension_of_principal_half f (hpneg.trans hnegx),
        extension_of_principal_neghalf f (hpx.trans hxhalf)]
    · rw [extension_of_principal_base f hpneg (by linarith) (by linarith),
        extension_of_principal_negbase f hpx hxbase hxneg]
  · have hxzero' : x = 0 := hxzero
    have hnegzero : -x = 0 := by linarith
    rw [extension_of_principal_zero f (hpneg.trans hnegzero),
      extension_of_principal_zero f (hpx.trans hxzero')]
  · rcases lt_trichotomy x (Real.pi / 2) with hxbase | hxhalf | hxright
    · rw [extension_of_principal_negbase f hpneg (by linarith) (by linarith),
        extension_of_principal_base f hpx hxpos hxbase]
      simp
    · have hnegx : -x = -Real.pi / 2 := by linarith
      rw [extension_of_principal_neghalf f (hpneg.trans hnegx),
        extension_of_principal_half f (hpx.trans hxhalf)]
    · rw [extension_of_principal_negleft f hpneg (by linarith) (by linarith),
        extension_of_principal_right f hpx hxright hupper]
      congr 2

theorem gap2 (f g : ℝ → ℝ) (hg : OnRightHalf f g) :
    ∀ n : ℕ, evenModeIntegral f g n = 0 := by
  intro n
  have hpi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hright :
      (∫ x in Real.pi / 2..Real.pi,
          g x * Real.cos (2 * (n : ℝ) * x)) =
        -(∫ x in Real.pi / 2..Real.pi,
          f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x)) := by
    calc
      (∫ x in Real.pi / 2..Real.pi,
          g x * Real.cos (2 * (n : ℝ) * x)) =
          ∫ x in Real.pi / 2..Real.pi,
            -(f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x)) := by
        apply intervalIntegral_congr_Ioo hpi
        intro x hxhalf hxpi
        rw [hg x hxhalf hxpi]
        ring
      _ = -(∫ x in Real.pi / 2..Real.pi,
          f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x)) := by
        rw [intervalIntegral.integral_neg]
  rw [evenModeIntegral, left_evenModeIntegral_reflect, hright]
  ring

theorem gap3 (f g : ℝ → ℝ) (hg : OnRightHalf f g) :
    ∀ n : ℕ, transformedEvenModeIntegral f g n = 0 := by
  intro n
  have hpi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hright :
      (∫ x in Real.pi / 2..Real.pi,
          g x * Real.cos (2 * (n : ℝ) * x)) =
        -(∫ x in Real.pi / 2..Real.pi,
          f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x)) := by
    calc
      (∫ x in Real.pi / 2..Real.pi,
          g x * Real.cos (2 * (n : ℝ) * x)) =
          ∫ x in Real.pi / 2..Real.pi,
            -(f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x)) := by
        apply intervalIntegral_congr_Ioo hpi
        intro x hxhalf hxpi
        rw [hg x hxhalf hxpi]
        ring
      _ = -(∫ x in Real.pi / 2..Real.pi,
          f (Real.pi - x) * Real.cos (2 * (n : ℝ) * x)) := by
        rw [intervalIntegral.integral_neg]
  rw [transformedEvenModeIntegral, intervalIntegral.integral_symm, hright]
  ring

theorem gap4 (f g : ℝ → ℝ) (hg : OnRightHalf f g) :
    ∀ n : ℕ, combinedEvenModeIntegral f g n = 0 := by
  intro n
  rw [combinedEvenModeIntegral]
  have hpi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  calc
    (∫ x in Real.pi / 2..Real.pi,
        (f (Real.pi - x) + g x) * Real.cos (2 * (n : ℝ) * x)) =
        ∫ x in Real.pi / 2..Real.pi, 0 := by
      apply intervalIntegral_congr_Ioo hpi
      intro x hxhalf hxpi
      rw [hg x hxhalf hxpi]
      ring
    _ = 0 := intervalIntegral.integral_zero

theorem gap5 (f g : ℝ → ℝ) :
    ∀ n : ℕ,
      (∀ x, Real.pi / 2 < x → x < Real.pi →
        f (Real.pi - x) + g x = 0) →
      combinedEvenModeIntegral f g n = 0 := by
  intro n h
  rw [combinedEvenModeIntegral]
  have hpi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  calc
    (∫ x in Real.pi / 2..Real.pi,
        (f (Real.pi - x) + g x) * Real.cos (2 * (n : ℝ) * x)) =
        ∫ x in Real.pi / 2..Real.pi, 0 := by
      apply intervalIntegral_congr_Ioo hpi
      intro x hxhalf hxpi
      rw [h x hxhalf hxpi]
      ring
    _ = 0 := intervalIntegral.integral_zero

theorem gap6 (f g : ℝ → ℝ) :
    OnRightHalf f g →
      ∀ x, Real.pi / 2 < x → x < Real.pi →
        f (Real.pi - x) + g x = 0 := by
  intro h x hxhalf hxpi
  rw [h x hxhalf hxpi]
  ring

theorem gap7 (f g : ℝ → ℝ) :
    ∀ n : ℕ, OnRightHalf f g →
      combinedEvenModeIntegral f g n = 0 := by
  intro n h
  exact gap4 f g h n

theorem gap8 (f F : ℝ → ℝ) (hF : ∀ x, F x = extension f x) :
    ∀ x, -Real.pi < x → x < Real.pi →
      F x = extension f x := by
  intro x hlower hupper
  exact hF x

private theorem extension_pi_sub_eq_neg (f : ℝ → ℝ) {x : ℝ}
    (hlower : -Real.pi < x) (hupper : x < Real.pi) :
    extension f (Real.pi - x) = -extension f x := by
  have hpx : principal x = x := principal_eq_self hlower hupper
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hpy : principal (Real.pi - x) = -Real.pi - x :=
      principal_pi_sub_of_nonpos hlower hxneg.le
    rcases lt_trichotomy x (-Real.pi / 2) with hxleft | hxhalf | hxbase
    · rw [extension_of_principal_negbase f hpy (by linarith) (by linarith),
        extension_of_principal_negleft f hpx hlower hxleft]
      congr 1
      ring
    · have hry : -Real.pi - x = -Real.pi / 2 := by linarith
      rw [extension_of_principal_neghalf f (hpy.trans hry),
        extension_of_principal_neghalf f (hpx.trans hxhalf)]
      simp
    · rw [extension_of_principal_negleft f hpy (by linarith) (by linarith),
        extension_of_principal_negbase f hpx hxbase hxneg]
      congr 2
      ring
  · have hpy : principal (Real.pi - x) = -Real.pi - x :=
      principal_pi_sub_of_nonpos hlower hxzero.le
    have hrx : x = 0 := hxzero
    have hry : -Real.pi - x = -Real.pi := by linarith
    rw [extension_of_principal_negpi f (hpy.trans hry),
      extension_of_principal_zero f (hpx.trans hrx)]
    simp
  · have hpy : principal (Real.pi - x) = Real.pi - x :=
      principal_pi_sub_of_pos hxpos hupper
    rcases lt_trichotomy x (Real.pi / 2) with hxbase | hxhalf | hxright
    · rw [extension_of_principal_right f hpy (by linarith) (by linarith),
        extension_of_principal_base f hpx hxpos hxbase]
      congr 2
      ring
    · have hry : Real.pi - x = Real.pi / 2 := by linarith
      rw [extension_of_principal_half f (hpy.trans hry),
        extension_of_principal_half f (hpx.trans hxhalf)]
      simp
    · rw [extension_of_principal_base f hpy (by linarith) (by linarith),
        extension_of_principal_right f hpx hxright hupper]
      simp

theorem gap9 (f F : ℝ → ℝ) (hF : ∀ x, F x = extension f x) :
    ExtendsBase f F ∧ HasRequiredSymmetry F := by
  constructor
  · intro x hxzero hxhalf
    rw [hF x]
    apply extension_of_principal_base f
    · exact principal_eq_self (by linarith [Real.pi_pos]) (by linarith)
    · exact hxzero
    · exact hxhalf
  · constructor
    · exact gap1 f F hF
    · intro x hlower hupper
      rw [hF (Real.pi - x), hF x]
      exact extension_pi_sub_eq_neg f hlower hupper

theorem gap10 (f F : ℝ → ℝ) (hF : ∀ x, F x = extension f x) :
    ExtendsBase f F ∧ HasRequiredSymmetry F := by
  exact gap9 f F hF

end

end ProofGap.Exercise2975
