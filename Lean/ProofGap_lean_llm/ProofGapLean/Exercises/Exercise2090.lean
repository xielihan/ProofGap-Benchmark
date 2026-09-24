import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2090
noncomputable section

def U : Set ℝ := Set.Iio 0
def f (x : ℝ) :=
  1 / (Real.sqrt (1 + Real.exp x) + Real.sqrt (1 - Real.exp x))
def fplus (x : ℝ) := 1 / Real.sqrt (1 + Real.exp x)
def fminus (x : ℝ) := 1 / Real.sqrt (1 - Real.exp x)
def rationalized (x : ℝ) :=
  Real.exp (-x) * (Real.sqrt (1 + Real.exp x) - Real.sqrt (1 - Real.exp x))
def baseTerm (x : ℝ) :=
  -Real.exp (-x) / 2 *
    (Real.sqrt (1 + Real.exp x) - Real.sqrt (1 - Real.exp x))
def primitive (x : ℝ) :=
  baseTerm x + (1 / 4 : ℝ) *
    Real.log (((Real.sqrt (1 + Real.exp x) - 1) *
      (1 - Real.sqrt (1 - Real.exp x))) /
      ((Real.sqrt (1 + Real.exp x) + 1) *
        (1 + Real.sqrt (1 - Real.exp x))))
def plusX (t : ℝ) := Real.log (t ^ 2 - 1)
def minusX (t : ℝ) := Real.log (1 - t ^ 2)
def Tplus : Set ℝ := Set.Ioo 1 (Real.sqrt 2)
def Tminus : Set ℝ := Set.Ioo 0 1
def Family (V : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ V, HasDerivAt F (g x) x}
def Scaled (V : Set ℝ) (c : ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family V g, ∃ C, ∀ x ∈ V, F x = c * G x + C}
def Pullback (φ : ℝ → ℝ) (V : Set ℝ) (A : Set (ℝ → ℝ)) :=
  {G : ℝ → ℝ | ∃ F ∈ A, ∀ t ∈ V, G t = F (φ t)}
def Step3 := {F : ℝ → ℝ |
  ∃ G ∈ Family U (fun x => fplus x + fminus x), ∃ C, ∀ x ∈ U,
  F x = baseTerm x + G x / 4 + C}
def Split := {F : ℝ → ℝ |
  ∃ A ∈ Family U fplus, ∃ B ∈ Family U fminus, ∃ C, ∀ x ∈ U,
  F x = baseTerm x + A x / 4 + B x / 4 + C}
def PlusTranslates := {G : ℝ → ℝ | ∃ C, ∀ t ∈ Tplus,
  G t = Real.log ((t - 1) / (t + 1)) + C}
def MinusTranslates := {G : ℝ → ℝ | ∃ C, ∀ t ∈ Tminus,
  G t = -Real.log ((1 + t) / (1 - t)) + C}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}

private def plusPrimitive (x : ℝ) :=
  Real.log (Real.sqrt (1 + Real.exp x) - 1) -
    Real.log (Real.sqrt (1 + Real.exp x) + 1)

private def minusPrimitive (x : ℝ) :=
  Real.log (1 - Real.sqrt (1 - Real.exp x)) -
    Real.log (1 + Real.sqrt (1 - Real.exp x))

private theorem hasDerivAt_congr_on_open {V : Set ℝ} (hV : IsOpen V)
    {F H : ℝ → ℝ} {x d : ℝ} (hx : x ∈ V) (hEq : ∀ y ∈ V, F y = H y)
    (hH : HasDerivAt H d x) : HasDerivAt F d x := by
  apply hH.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hx] with y hy
  exact hEq y hy

private theorem family_eq_scaled_of_eq {V : Set ℝ} {g h : ℝ → ℝ} {c : ℝ}
    (hV : IsOpen V) (hc : c ≠ 0) (hgh : ∀ x ∈ V, g x = c * h x) :
    Family V g = Scaled V c h := by
  ext F
  constructor
  · intro hF
    refine ⟨(fun x => F x / c), ?_, 0, ?_⟩
    · intro x hx
      convert (hF x hx).div_const c using 1
      rw [hgh x hx]
      field_simp [hc] <;> ring
    · intro x hx
      field_simp [hc] <;> ring
  · rintro ⟨G, hG, C, hEq⟩
    intro x hx
    have hd : HasDerivAt (fun y => c * G y + C) (g x) x := by
      convert ((hG x hx).const_mul c).add_const C using 1
      exact hgh x hx
    exact hasDerivAt_congr_on_open hV hx (fun y hy => hEq y hy) hd

private theorem family_eq_shifted_of_deriv {V : Set ℝ} {g h k b : ℝ → ℝ} {c : ℝ}
    (hV : IsOpen V) (hc : c ≠ 0) (hb : ∀ x ∈ V, HasDerivAt b (k x) x)
    (hrel : ∀ x ∈ V, g x = k x + c * h x) :
    Family V g =
      {F : ℝ → ℝ | ∃ G ∈ Family V h, ∃ C, ∀ x ∈ V, F x = b x + c * G x + C} := by
  ext F
  constructor
  · intro hF
    refine ⟨(fun x => (F x - b x) / c), ?_, 0, ?_⟩
    · intro x hx
      convert ((hF x hx).sub (hb x hx)).div_const c using 1
      rw [hrel x hx]
      field_simp [hc] <;> ring
    · intro x hx
      field_simp [hc] <;> ring
  · rintro ⟨G, hG, C, hEq⟩
    intro x hx
    have hd : HasDerivAt (fun y => b y + c * G y + C) (g x) x := by
      convert ((hb x hx).add ((hG x hx).const_mul c)).add_const C using 1
      exact hrel x hx
    exact hasDerivAt_congr_on_open hV hx (fun y hy => hEq y hy) hd

private theorem family_Ioo_translates {a b : ℝ} {p g : ℝ → ℝ} (hab : a < b)
    (hp : ∀ x ∈ Set.Ioo a b, HasDerivAt p (g x) x) :
    Family (Set.Ioo a b) g =
      {F : ℝ → ℝ | ∃ C, ∀ x ∈ Set.Ioo a b, F x = p x + C} := by
  ext F
  constructor
  · intro hF
    let m := (a + b) / 2
    have hm : m ∈ Set.Ioo a b := by
      dsimp [m]
      constructor <;> linarith
    let q := fun x => F x - p x
    have hdiff : DifferentiableOn ℝ q (Set.Ioo a b) := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ Set.Ioo a b, deriv q x = 0 := by
      intro x hx
      simpa [q] using ((hF x hx).sub (hp x hx)).deriv
    refine ⟨q m, ?_⟩
    intro x hx
    have he : q x = q m :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hx hm
    dsimp [q] at he ⊢
    linarith
  · rintro ⟨C, hEq⟩
    intro x hx
    exact hasDerivAt_congr_on_open isOpen_Ioo hx (fun y hy => hEq y hy)
      ((hp x hx).add_const C)

private theorem family_Iio_translates {b : ℝ} {p g : ℝ → ℝ} (hm : -1 < b)
    (hp : ∀ x ∈ Set.Iio b, HasDerivAt p (g x) x) :
    Family (Set.Iio b) g =
      {F : ℝ → ℝ | ∃ C, ∀ x ∈ Set.Iio b, F x = p x + C} := by
  ext F
  constructor
  · intro hF
    let q := fun x => F x - p x
    have hdiff : DifferentiableOn ℝ q (Set.Iio b) := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ Set.Iio b, deriv q x = 0 := by
      intro x hx
      simpa [q] using ((hF x hx).sub (hp x hx)).deriv
    refine ⟨q (-1), ?_⟩
    intro x hx
    have he : q x = q (-1) :=
      isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio hdiff hzero hx hm
    dsimp [q] at he ⊢
    linarith
  · rintro ⟨C, hEq⟩
    intro x hx
    exact hasDerivAt_congr_on_open isOpen_Iio hx (fun y hy => hEq y hy)
      ((hp x hx).add_const C)

private theorem plus_chart_bounds (t : ℝ) (ht : t ∈ Tplus) :
    0 < t ^ 2 - 1 ∧ t ^ 2 - 1 < 1 := by
  change 1 < t ∧ t < Real.sqrt 2 at ht
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hlo : 0 < (t - 1) * (t + 1) :=
    mul_pos (sub_pos.mpr ht.1) (by linarith)
  have hhi : 0 < (Real.sqrt 2 - t) * (Real.sqrt 2 + t) :=
    mul_pos (sub_pos.mpr ht.2) (by linarith)
  constructor <;> nlinarith

private theorem minus_chart_bounds (t : ℝ) (ht : t ∈ Tminus) :
    0 < 1 - t ^ 2 ∧ 1 - t ^ 2 < 1 := by
  change 0 < t ∧ t < 1 at ht
  have hlo : 0 < (1 - t) * (1 + t) :=
    mul_pos (sub_pos.mpr ht.2) (by linarith)
  have ht2 : 0 < t * t := mul_pos ht.1 ht.1
  constructor <;> nlinarith

private theorem f_eq_half_rationalized (x : ℝ) (hx : x ∈ U) :
    f x = (1 / 2 : ℝ) * rationalized x := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have hm : 0 ≤ 1 - Real.exp x :=
    le_of_lt (sub_pos.mpr (Real.exp_lt_one_iff.mpr hx))
  have hp : 0 ≤ 1 + Real.exp x := by positivity
  have ha := Real.sq_sqrt hp
  have hb := Real.sq_sqrt hm
  have hsum : Real.sqrt (1 + Real.exp x) + Real.sqrt (1 - Real.exp x) ≠ 0 := by
    positivity
  simp only [f, rationalized]
  rw [div_eq_iff hsum, Real.exp_neg]
  field_simp [Real.exp_ne_zero] <;> nlinarith [ha, hb]

private theorem plus_primitive_derivative (x : ℝ) (hx : x ∈ U) :
    HasDerivAt plusPrimitive (fplus x) x := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have hp : 0 < 1 + Real.exp x := by positivity
  have hs : 0 < Real.sqrt (1 + Real.exp x) := Real.sqrt_pos.2 hp
  have hs0 : Real.sqrt (1 + Real.exp x) ≠ 0 := ne_of_gt hs
  have hs2 := Real.sq_sqrt (le_of_lt hp)
  have hs1 : 1 < Real.sqrt (1 + Real.exp x) := by nlinarith
  have hm1 : Real.sqrt (1 + Real.exp x) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hs1)
  have hp1 : Real.sqrt (1 + Real.exp x) + 1 ≠ 0 := by positivity
  have ha : HasDerivAt (fun y : ℝ => Real.sqrt (1 + Real.exp y))
      (Real.exp x / (2 * Real.sqrt (1 + Real.exp x))) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x 1).add (Real.hasDerivAt_exp x)))
  have hnum := (ha.sub_const 1).log hm1
  have hden := (ha.add_const 1).log hp1
  have hl : HasDerivAt
      (fun y : ℝ =>
        Real.log (Real.sqrt (1 + Real.exp y) - 1) -
          Real.log (Real.sqrt (1 + Real.exp y) + 1))
      (Real.exp x / (2 * Real.sqrt (1 + Real.exp x)) /
          (Real.sqrt (1 + Real.exp x) - 1) -
        Real.exp x / (2 * Real.sqrt (1 + Real.exp x)) /
          (Real.sqrt (1 + Real.exp x) + 1)) x := by
    simpa using (hnum.sub hden)
  have hcoef :
      Real.exp x / (2 * Real.sqrt (1 + Real.exp x)) /
          (Real.sqrt (1 + Real.exp x) - 1) -
        Real.exp x / (2 * Real.sqrt (1 + Real.exp x)) /
          (Real.sqrt (1 + Real.exp x) + 1) =
      1 / Real.sqrt (1 + Real.exp x) := by
    field_simp [hs0, hm1, hp1]
    nlinarith [hs2]
  unfold plusPrimitive fplus
  rw [← hcoef]
  exact hl

private theorem minus_primitive_derivative (x : ℝ) (hx : x ∈ U) :
    HasDerivAt minusPrimitive (fminus x) x := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have he1 : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  have hp : 0 < 1 - Real.exp x := sub_pos.mpr he1
  have hs : 0 < Real.sqrt (1 - Real.exp x) := Real.sqrt_pos.2 hp
  have hs0 : Real.sqrt (1 - Real.exp x) ≠ 0 := ne_of_gt hs
  have hs2 := Real.sq_sqrt (le_of_lt hp)
  have hs1 : Real.sqrt (1 - Real.exp x) < 1 := by nlinarith
  have hm1 : 1 - Real.sqrt (1 - Real.exp x) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hs1)
  have hp1 : 1 + Real.sqrt (1 - Real.exp x) ≠ 0 := by positivity
  have ha : HasDerivAt (fun y : ℝ => Real.sqrt (1 - Real.exp y))
      (-Real.exp x / (2 * Real.sqrt (1 - Real.exp x))) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x 1).sub (Real.hasDerivAt_exp x)))
  have hleft := ((hasDerivAt_const x 1).sub ha).log hm1
  have hright := ((hasDerivAt_const x 1).add ha).log hp1
  have hcoef :
      Real.exp x / (2 * Real.sqrt (1 - Real.exp x)) /
          (1 - Real.sqrt (1 - Real.exp x)) -
        (-Real.exp x / (2 * Real.sqrt (1 - Real.exp x))) /
          (1 + Real.sqrt (1 - Real.exp x)) =
      1 / Real.sqrt (1 - Real.exp x) := by
    field_simp [hs0, hp1, hm1]
    nlinarith [hs2]
  unfold minusPrimitive fminus
  rw [← hcoef]
  convert (hleft.sub hright) using 1 <;> simp <;> ring

private theorem plus_primitive_family : plusPrimitive ∈ Family U fplus :=
  plus_primitive_derivative

private theorem minus_primitive_family : minusPrimitive ∈ Family U fminus :=
  minus_primitive_derivative

private theorem base_derivative (x : ℝ) (hx : x ∈ U) :
    HasDerivAt baseTerm (f x - (1 / 4 : ℝ) * (fplus x + fminus x)) x := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have he0 : Real.exp x ≠ 0 := ne_of_gt he
  have he1 : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  have hp : 0 < 1 + Real.exp x := by positivity
  have hm : 0 < 1 - Real.exp x := sub_pos.mpr he1
  have hsp : 0 < Real.sqrt (1 + Real.exp x) := Real.sqrt_pos.2 hp
  have hsm : 0 < Real.sqrt (1 - Real.exp x) := Real.sqrt_pos.2 hm
  have hsp0 : Real.sqrt (1 + Real.exp x) ≠ 0 := ne_of_gt hsp
  have hsm0 : Real.sqrt (1 - Real.exp x) ≠ 0 := ne_of_gt hsm
  have hsp2 := Real.sq_sqrt (le_of_lt hp)
  have hsm2 := Real.sq_sqrt (le_of_lt hm)
  have hsum : Real.sqrt (1 + Real.exp x) + Real.sqrt (1 - Real.exp x) ≠ 0 := by
    positivity
  have ha : HasDerivAt (fun y : ℝ => Real.sqrt (1 + Real.exp y))
      (Real.exp x / (2 * Real.sqrt (1 + Real.exp x))) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x 1).add (Real.hasDerivAt_exp x)))
  have hb : HasDerivAt (fun y : ℝ => Real.sqrt (1 - Real.exp y))
      (-Real.exp x / (2 * Real.sqrt (1 - Real.exp x))) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((Real.hasDerivAt_sqrt (ne_of_gt hm)).comp x
        ((hasDerivAt_const x 1).sub (Real.hasDerivAt_exp x)))
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hn : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using (Real.hasDerivAt_exp (-x)).comp x hneg
  have hd : HasDerivAt baseTerm
      (Real.exp (-x) / 2 *
          (Real.sqrt (1 + Real.exp x) - Real.sqrt (1 - Real.exp x)) +
        (-Real.exp (-x)) / 2 *
          (Real.exp x / (2 * Real.sqrt (1 + Real.exp x)) +
            Real.exp x / (2 * Real.sqrt (1 - Real.exp x)))) x := by
    unfold baseTerm
    convert ((hn.neg.div_const 2).mul (ha.sub hb)) using 1 <;> simp <;> ring
  have hfirst :
      Real.exp (-x) / 2 *
          (Real.sqrt (1 + Real.exp x) - Real.sqrt (1 - Real.exp x)) =
        1 / (Real.sqrt (1 + Real.exp x) + Real.sqrt (1 - Real.exp x)) := by
    rw [Real.exp_neg]
    field_simp [he0, hsum]
    nlinarith [hsp2, hsm2]
  have hsecond :
      (-Real.exp (-x)) / 2 *
          (Real.exp x / (2 * Real.sqrt (1 + Real.exp x)) +
            Real.exp x / (2 * Real.sqrt (1 - Real.exp x))) =
        -(1 / 4 : ℝ) *
          (1 / Real.sqrt (1 + Real.exp x) +
            1 / Real.sqrt (1 - Real.exp x)) := by
    rw [Real.exp_neg]
    field_simp [he0, hsp0, hsm0] <;> ring
  have hcoef :
      Real.exp (-x) / 2 *
          (Real.sqrt (1 + Real.exp x) - Real.sqrt (1 - Real.exp x)) +
        (-Real.exp (-x)) / 2 *
          (Real.exp x / (2 * Real.sqrt (1 + Real.exp x)) +
            Real.exp x / (2 * Real.sqrt (1 - Real.exp x))) =
      f x - (1 / 4 : ℝ) * (fplus x + fminus x) := by
    rw [hfirst, hsecond]
    unfold f fplus fminus
    ring
  rw [← hcoef]
  exact hd

private theorem plus_chart_derivative (t : ℝ) (ht : t ∈ Set.Ioo 1 (Real.sqrt 2)) :
    HasDerivAt (fun s => Real.log ((s - 1) / (s + 1)))
      (2 * (1 / (t ^ 2 - 1))) t := by
  have ht1 : 1 < t := ht.1
  have hn : t - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  have hd : t + 1 ≠ 0 := ne_of_gt (by linarith)
  have hp : t ^ 2 - 1 ≠ 0 := by
    have hlo : 0 < (t - 1) * (t + 1) :=
      mul_pos (sub_pos.mpr ht1) (by linarith)
    nlinarith
  have hnum : HasDerivAt (fun s : ℝ => s - 1) 1 t := by
    simpa using (hasDerivAt_id t).sub_const 1
  have hden : HasDerivAt (fun s : ℝ => s + 1) 1 t := by
    simpa using (hasDerivAt_id t).add_const 1
  have hq0 := hnum.div hden hd
  have hq : HasDerivAt (fun s : ℝ => (s - 1) / (s + 1))
      (2 / (t + 1) ^ 2) t := by
    convert hq0 using 1 <;> ring_nf
  have hratio : (t - 1) / (t + 1) ≠ 0 := div_ne_zero hn hd
  have hl := hq.log hratio
  have hcoef :
      (2 / (t + 1) ^ 2) / ((t - 1) / (t + 1)) =
        2 * (1 / (t ^ 2 - 1)) := by
    field_simp [hn, hd, hp, hratio] <;> ring
  rw [← hcoef]
  exact hl

private theorem minus_chart_derivative (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    HasDerivAt (fun s => -Real.log ((1 + s) / (1 - s)))
      (-2 * (1 / (1 - t ^ 2))) t := by
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have hn : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hd : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  have hp : 1 - t ^ 2 ≠ 0 := by
    have hlo : 0 < (1 - t) * (1 + t) :=
      mul_pos (sub_pos.mpr ht1) (by linarith)
    nlinarith
  have hnum : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
    simpa using (hasDerivAt_const t 1).add (hasDerivAt_id t)
  have hden : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_const t 1).sub (hasDerivAt_id t)
  have hq0 := hnum.div hden hd
  have hq : HasDerivAt (fun s : ℝ => (1 + s) / (1 - s))
      (2 / (1 - t) ^ 2) t := by
    convert hq0 using 1 <;> ring_nf
  have hratio : (1 + t) / (1 - t) ≠ 0 := div_ne_zero hn hd
  have hl := (hq.log hratio).neg
  have hcoef :
      -((2 / (1 - t) ^ 2) / ((1 + t) / (1 - t))) =
        -2 * (1 / (1 - t ^ 2)) := by
    field_simp [hn, hd, hp, hratio] <;> ring
  rw [← hcoef]
  exact hl

private theorem primitive_decomposition (x : ℝ) (hx : x ∈ U) :
    primitive x = baseTerm x + (1 / 4 : ℝ) *
      (plusPrimitive x + minusPrimitive x) := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have he1 : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  have hp : 0 < 1 + Real.exp x := by positivity
  have hm : 0 < 1 - Real.exp x := sub_pos.mpr he1
  have ap : 1 < Real.sqrt (1 + Real.exp x) := by
    have hsq := Real.sq_sqrt (le_of_lt hp)
    have hn := Real.sqrt_nonneg (1 + Real.exp x)
    nlinarith
  have bm : Real.sqrt (1 - Real.exp x) < 1 := by
    have hsq := Real.sq_sqrt (le_of_lt hm)
    have hn := Real.sqrt_nonneg (1 - Real.exp x)
    nlinarith
  have h1 : Real.sqrt (1 + Real.exp x) - 1 ≠ 0 := by nlinarith
  have h2 : Real.sqrt (1 + Real.exp x) + 1 ≠ 0 := by positivity
  have h3 : 1 - Real.sqrt (1 - Real.exp x) ≠ 0 := by nlinarith
  have h4 : 1 + Real.sqrt (1 - Real.exp x) ≠ 0 := by positivity
  unfold primitive plusPrimitive minusPrimitive
  rw [Real.log_div (mul_ne_zero h1 h3) (mul_ne_zero h2 h4)]
  rw [Real.log_mul h1 h3, Real.log_mul h2 h4]
  ring

theorem gap1 : Family U f = Scaled U (1 / 2) rationalized := by
  apply family_eq_scaled_of_eq isOpen_Iio (by norm_num)
  intro x hx
  exact f_eq_half_rationalized x hx
theorem gap2 : Family U f =
    Scaled U (-1 / 2)
      (fun x => (Real.sqrt (1 + Real.exp x) - Real.sqrt (1 - Real.exp x)) *
        deriv (fun y => Real.exp (-y)) x) := by
  apply family_eq_scaled_of_eq isOpen_Iio (by norm_num)
  intro x hx
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hd : deriv (fun y : ℝ => Real.exp (-y)) x = -Real.exp (-x) := by
    simpa using (((Real.hasDerivAt_exp (-x)).comp x hneg).deriv)
  rw [hd, f_eq_half_rationalized x hx]
  simp only [rationalized]
  ring
theorem gap3 : Family U f = Step3 := by
  have h := family_eq_shifted_of_deriv
    (V := U) (g := f) (h := fun x => fplus x + fminus x)
    (k := fun x => f x - (1 / 4 : ℝ) * (fplus x + fminus x))
    (b := baseTerm) (c := (1 / 4 : ℝ))
    isOpen_Iio (by norm_num) base_derivative
    (by
      intro x hx
      ring)
  simpa [Step3, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
theorem gap4 : Family U f = Split := by
  rw [gap3]
  ext F
  constructor
  · intro hF
    rcases hF with ⟨G, hG, C, hEq⟩
    refine ⟨plusPrimitive, plus_primitive_family, (fun x => G x - plusPrimitive x), ?_, C, ?_⟩
    · intro x hx
      simpa [fplus, fminus] using (hG x hx).sub (plus_primitive_derivative x hx)
    · intro x hx
      rw [hEq x hx]
      ring
  · intro hF
    rcases hF with ⟨A, hA, B, hB, C, hEq⟩
    refine ⟨(fun x => A x + B x), ?_, C, ?_⟩
    · intro x hx
      exact (hA x hx).add (hB x hx)
    · intro x hx
      rw [hEq x hx]
      ring
theorem gap5 : ∀ t ∈ Tplus,
    Real.sqrt (1 + Real.exp (plusX t)) = t ∧ plusX t = Real.log (t ^ 2 - 1) := by
  intro t ht
  have hb := plus_chart_bounds t ht
  constructor
  · rw [plusX, Real.exp_log hb.1]
    have heq : 1 + (t ^ 2 - 1) = t ^ 2 := by ring
    rw [heq, Real.sqrt_sq_eq_abs]
    have ht' : 1 < t := by
      change 1 < t ∧ t < Real.sqrt 2 at ht
      exact ht.1
    rw [abs_of_pos (by linarith)]
  · rfl
theorem gap6 : ∀ t ∈ Tplus,
    HasDerivAt plusX (2 * t / (t ^ 2 - 1)) t := by
  intro t ht
  have hb := plus_chart_bounds t ht
  have hi : HasDerivAt (fun s : ℝ => s ^ 2 - 1) (2 * t) t := by
    simpa [pow_two, mul_comm] using ((hasDerivAt_id t).pow 2).sub_const 1
  have hl := hi.log (ne_of_gt hb.1)
  simpa [plusX] using hl
theorem gap7 :
    Pullback plusX Tplus (Family U fplus) =
      Family Tplus (fun t => fplus (plusX t) * deriv plusX t) := by
  have hmap : ∀ t ∈ Tplus, plusX t ∈ U := by
    intro t ht
    have hb := plus_chart_bounds t ht
    exact Real.log_neg hb.1 hb.2
  have hsource : Family U fplus =
      {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = plusPrimitive x + C} := by
    simpa [U] using
      (family_Iio_translates (b := (0 : ℝ)) (p := plusPrimitive) (g := fplus)
        (by norm_num) plus_primitive_derivative)
  have hright : Family Tplus (fun t => fplus (plusX t) * deriv plusX t) =
      {G : ℝ → ℝ | ∃ C, ∀ t ∈ Tplus, G t = plusPrimitive (plusX t) + C} := by
    apply family_Ioo_translates (p := fun t => plusPrimitive (plusX t))
    · exact Real.one_lt_sqrt_two
    · intro t ht
      have hc := (plus_primitive_derivative (plusX t) (hmap t ht)).comp t (gap6 t ht)
      have hd := (gap6 t ht).deriv
      simpa [Function.comp_def, hd] using hc
  rw [hright]
  ext G
  constructor
  · rintro ⟨F, hF, hGF⟩
    rw [hsource] at hF
    rcases hF with ⟨C, hFC⟩
    exact ⟨C, fun t ht => (hGF t ht).trans (hFC (plusX t) (hmap t ht))⟩
  · rintro ⟨C, hGC⟩
    refine ⟨(fun x => plusPrimitive x + C), ?_, ?_⟩
    · rw [hsource]
      exact ⟨C, fun x hx => rfl⟩
    · intro t ht
      exact hGC t ht
theorem gap8 :
    Pullback plusX Tplus (Family U fplus) =
      Scaled Tplus 2 (fun t => 1 / (t ^ 2 - 1)) := by
  rw [gap7]
  apply family_eq_scaled_of_eq isOpen_Ioo (by norm_num)
  intro t ht
  have hs := (gap5 t ht).1
  have hd := (gap6 t ht).deriv
  have hb := plus_chart_bounds t ht
  have ht' : 1 < t := by
    change 1 < t ∧ t < Real.sqrt 2 at ht
    exact ht.1
  have ht0 : t ≠ 0 := by linarith
  rw [hd]
  simp only [fplus, hs]
  field_simp [ht0, ne_of_gt hb.1] <;> ring
theorem gap9 :
    Scaled Tplus 2 (fun t => 1 / (t ^ 2 - 1)) = PlusTranslates := by
  calc
    Scaled Tplus 2 (fun t => 1 / (t ^ 2 - 1)) =
        Family Tplus (fun t => 2 * (1 / (t ^ 2 - 1))) :=
      (family_eq_scaled_of_eq isOpen_Ioo (by norm_num) (fun t ht => rfl)).symm
    _ = PlusTranslates := by
      simpa [Tplus, PlusTranslates] using
        (family_Ioo_translates (a := (1 : ℝ)) (b := Real.sqrt 2)
          (p := fun t => Real.log ((t - 1) / (t + 1)))
          (g := fun t => 2 * (1 / (t ^ 2 - 1)))
          Real.one_lt_sqrt_two plus_chart_derivative)
theorem gap10 : PlusTranslates =
    {G : ℝ → ℝ | ∃ C, ∀ t ∈ Tplus,
      G t = Real.log ((Real.sqrt (1 + Real.exp (plusX t)) - 1) /
        (Real.sqrt (1 + Real.exp (plusX t)) + 1)) + C} := by
  ext G
  constructor
  · rintro ⟨C, hG⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hG t ht, (gap5 t ht).1]
  · rintro ⟨C, hG⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hG t ht, (gap5 t ht).1]
theorem gap11 :
    Pullback plusX Tplus (Family U fplus) = PlusTranslates := by
  exact gap8.trans gap9
theorem gap12 : ∀ t ∈ Tminus,
    Real.sqrt (1 - Real.exp (minusX t)) = t ∧ minusX t = Real.log (1 - t ^ 2) := by
  intro t ht
  have hb := minus_chart_bounds t ht
  constructor
  · rw [minusX, Real.exp_log hb.1]
    have heq : 1 - (1 - t ^ 2) = t ^ 2 := by ring
    rw [heq, Real.sqrt_sq_eq_abs]
    have ht' : 0 < t := by
      change 0 < t ∧ t < 1 at ht
      exact ht.1
    rw [abs_of_pos ht']
  · rfl
theorem gap13 : ∀ t ∈ Tminus,
    HasDerivAt minusX (-2 * t / (1 - t ^ 2)) t := by
  intro t ht
  have hb := minus_chart_bounds t ht
  have hi : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-2 * t) t := by
    simpa [pow_two, mul_comm] using
      (hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2)
  have hl := hi.log (ne_of_gt hb.1)
  simpa [minusX] using hl
theorem gap14 :
    Pullback minusX Tminus (Family U fminus) =
      Family Tminus (fun t => fminus (minusX t) * deriv minusX t) := by
  have hmap : ∀ t ∈ Tminus, minusX t ∈ U := by
    intro t ht
    have hb := minus_chart_bounds t ht
    exact Real.log_neg hb.1 hb.2
  have hsource : Family U fminus =
      {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = minusPrimitive x + C} := by
    simpa [U] using
      (family_Iio_translates (b := (0 : ℝ)) (p := minusPrimitive) (g := fminus)
        (by norm_num) minus_primitive_derivative)
  have hright : Family Tminus (fun t => fminus (minusX t) * deriv minusX t) =
      {G : ℝ → ℝ | ∃ C, ∀ t ∈ Tminus, G t = minusPrimitive (minusX t) + C} := by
    apply family_Ioo_translates (p := fun t => minusPrimitive (minusX t))
    · norm_num
    · intro t ht
      have hc := (minus_primitive_derivative (minusX t) (hmap t ht)).comp t (gap13 t ht)
      have hd := (gap13 t ht).deriv
      simpa [Function.comp_def, hd] using hc
  rw [hright]
  ext G
  constructor
  · rintro ⟨F, hF, hGF⟩
    rw [hsource] at hF
    rcases hF with ⟨C, hFC⟩
    exact ⟨C, fun t ht => (hGF t ht).trans (hFC (minusX t) (hmap t ht))⟩
  · rintro ⟨C, hGC⟩
    refine ⟨(fun x => minusPrimitive x + C), ?_, ?_⟩
    · rw [hsource]
      exact ⟨C, fun x hx => rfl⟩
    · intro t ht
      exact hGC t ht
theorem gap15 :
    Pullback minusX Tminus (Family U fminus) =
      Scaled Tminus (-2) (fun t => 1 / (1 - t ^ 2)) := by
  rw [gap14]
  apply family_eq_scaled_of_eq isOpen_Ioo (by norm_num)
  intro t ht
  have hs := (gap12 t ht).1
  have hd := (gap13 t ht).deriv
  have hb := minus_chart_bounds t ht
  have ht' : 0 < t := by
    change 0 < t ∧ t < 1 at ht
    exact ht.1
  have ht0 : t ≠ 0 := ne_of_gt ht'
  rw [hd]
  simp only [fminus, hs]
  field_simp [ht0, ne_of_gt hb.1] <;> ring
theorem gap16 :
    Scaled Tminus (-2) (fun t => 1 / (1 - t ^ 2)) =
      MinusTranslates := by
  calc
    Scaled Tminus (-2) (fun t => 1 / (1 - t ^ 2)) =
        Family Tminus (fun t => -2 * (1 / (1 - t ^ 2))) :=
      (family_eq_scaled_of_eq isOpen_Ioo (by norm_num) (fun t ht => rfl)).symm
    _ = MinusTranslates := by
      simpa [Tminus, MinusTranslates] using
        (family_Ioo_translates (a := (0 : ℝ)) (b := 1)
          (p := fun t => -Real.log ((1 + t) / (1 - t)))
          (g := fun t => -2 * (1 / (1 - t ^ 2)))
          (by norm_num) minus_chart_derivative)
theorem gap17 : MinusTranslates =
    {G : ℝ → ℝ | ∃ C, ∀ t ∈ Tminus,
      G t = -Real.log ((1 + Real.sqrt (1 - Real.exp (minusX t))) /
        (1 - Real.sqrt (1 - Real.exp (minusX t)))) + C} := by
  ext G
  constructor
  · rintro ⟨C, hG⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hG t ht, (gap12 t ht).1]
  · rintro ⟨C, hG⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hG t ht, (gap12 t ht).1]
theorem gap18 :
    Pullback minusX Tminus (Family U fminus) = MinusTranslates := by
  exact gap15.trans gap16
theorem gap19 : Family U f = Translates primitive := by
  have hp : ∀ x ∈ U, HasDerivAt primitive (f x) x := by
    intro x hx
    have hd := (base_derivative x hx).add
      (((plus_primitive_derivative x hx).add (minus_primitive_derivative x hx)).const_mul
        (1 / 4 : ℝ))
    have hc := hasDerivAt_congr_on_open isOpen_Iio hx
      (fun y hy => primitive_decomposition y hy) hd
    convert hc using 1 <;> ring
  simpa [U, Translates] using
    (family_Iio_translates (b := (0 : ℝ)) (p := primitive) (g := f)
      (by norm_num) hp)

end
end ProofGap.Exercise2090
