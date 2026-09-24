import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1787

noncomputable section

def xOf (a t : ℝ) : ℝ := a * Real.sinh t
def tOf (a x : ℝ) : ℝ :=
  Real.log ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a)
def integrand (a x : ℝ) : ℝ := x ^ 2 / Real.sqrt (a ^ 2 + x ^ 2)
def anglePrimitive (a t : ℝ) : ℝ :=
  a ^ 2 * ((1 / 4 : ℝ) * Real.sinh (2 * t) - t / 2)
def primitive (a x : ℝ) : ℝ :=
  x / 2 * Real.sqrt (a ^ 2 + x ^ 2) -
    a ^ 2 / 2 * Real.log (x + Real.sqrt (a ^ 2 + x ^ 2))
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem primitive_hasDerivAt (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (primitive a) (integrand a x) x := by
  have ha2 : 0 < a ^ 2 := by nlinarith
  have hu : 0 < a ^ 2 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (a ^ 2 + x ^ 2) := Real.sqrt_pos.2 hu
  have hsq :
      Real.sqrt (a ^ 2 + x ^ 2) ^ 2 = a ^ 2 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hu)
  have hquad :
      HasDerivAt (fun y : ℝ => a ^ 2 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (a ^ 2)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (a ^ 2 + y ^ 2))
        (x / Real.sqrt (a ^ 2 + x ^ 2)) x := by
    have hcomp := (Real.hasDerivAt_sqrt hu.ne').comp x hquad
    convert hcomp using 1 <;>
      field_simp [ne_of_gt hs] <;> ring
  have hxs : 0 < x + Real.sqrt (a ^ 2 + x ^ 2) := by
    by_cases hx : x ≤ 0
    · nlinarith
    · have hxpos : 0 < x := lt_of_not_ge hx
      by_contra hn
      have hsle : Real.sqrt (a ^ 2 + x ^ 2) ≤ x := by linarith
      have hsqle := mul_self_le_mul_self (le_of_lt hs) hsle
      nlinarith [hsqle]
  have hlog :
      HasDerivAt
        (fun y : ℝ => Real.log (y + Real.sqrt (a ^ 2 + y ^ 2)))
        (1 / Real.sqrt (a ^ 2 + x ^ 2)) x := by
    have hsum := (hasDerivAt_id x).add hsqrt
    have hcomp := (Real.hasDerivAt_log (ne_of_gt hxs)).comp x hsum
    convert hcomp using 1 <;>
      field_simp [ne_of_gt hs, ne_of_gt hxs] <;> ring
  have hresult :
      HasDerivAt (primitive a)
        ((1 / 2 : ℝ) * Real.sqrt (a ^ 2 + x ^ 2) +
          (x / 2) * (x / Real.sqrt (a ^ 2 + x ^ 2)) -
          (a ^ 2 / 2) * (1 / Real.sqrt (a ^ 2 + x ^ 2))) x := by
    unfold primitive
    convert
      (((hasDerivAt_id x).div_const 2).mul hsqrt).sub
        (hlog.const_mul (a ^ 2 / 2)) using 1 <;> ring
  convert hresult using 1
  unfold integrand
  field_simp [ne_of_gt hs]
  nlinarith [hsq]

theorem gap1 (a t : ℝ) (ha : 0 < a) :
    integrand a (xOf a t) =
      a * Real.sinh t ^ 2 / Real.cosh t := by
  unfold integrand xOf
  have hbase : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hrad :
      a ^ 2 + (a * Real.sinh t) ^ 2 =
        (a * Real.cosh t) ^ 2 := by
    calc
      a ^ 2 + (a * Real.sinh t) ^ 2 =
          a ^ 2 * (1 + Real.sinh t ^ 2) := by ring
      _ = a ^ 2 * Real.cosh t ^ 2 := by rw [hbase]
      _ = (a * Real.cosh t) ^ 2 := by ring
  rw [hrad, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos ha (Real.cosh_pos t))]
  field_simp [ne_of_gt ha, ne_of_gt (Real.cosh_pos t)] <;> ring

theorem gap2 (a t : ℝ) :
    deriv (xOf a) t = a * Real.cosh t := by
  have h :
      HasDerivAt (fun y : ℝ => a * Real.sinh y)
        (a * Real.cosh t) t :=
    (Real.hasDerivAt_sinh t).const_mul a
  change deriv (fun y : ℝ => a * Real.sinh y) t = a * Real.cosh t
  exact h.deriv

theorem gap3 (a t : ℝ) (ha : 0 < a) :
    integrand a (xOf a t) * deriv (xOf a) t =
      a ^ 2 * Real.sinh t ^ 2 := by
  rw [gap1 a t ha, gap2 a t]
  field_simp [ne_of_gt (Real.cosh_pos t)] <;> ring

theorem gap4 (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (anglePrimitive a)
      (integrand a (xOf a t) * deriv (xOf a) t) t := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hsinhD :
      HasDerivAt (fun y : ℝ => Real.sinh (2 * y))
        (Real.cosh (2 * t) * 2) t :=
    (Real.hasDerivAt_sinh (2 * t)).comp t hlin
  have hcore :=
    (hsinhD.const_mul (1 / 4 : ℝ)).sub
      ((hasDerivAt_id t).div_const 2)
  have hang0 := hcore.const_mul (a ^ 2)
  have hang :
      HasDerivAt (anglePrimitive a)
        (a ^ 2 *
          ((1 / 4 : ℝ) * (Real.cosh (2 * t) * 2) - 1 / 2)) t := by
    unfold anglePrimitive
    convert hang0 using 1 <;> ring
  have htwo :
      Real.cosh (2 * t) =
        Real.cosh t * Real.cosh t + Real.sinh t * Real.sinh t := by
    rw [show 2 * t = t + t by ring, Real.cosh_add]
  have hval :
      a ^ 2 *
          ((1 / 4 : ℝ) * (Real.cosh (2 * t) * 2) - 1 / 2) =
        a ^ 2 * Real.sinh t ^ 2 := by
    nlinarith [htwo, Real.cosh_sq_sub_sinh_sq t]
  rw [gap3 a t ha]
  simpa only [hval] using hang

theorem gap5 (a x : ℝ) (ha : 0 < a) :
    anglePrimitive a (tOf a x) =
      primitive a x + a ^ 2 / 2 * Real.log a := by
  have ha2 : 0 < a ^ 2 := by nlinarith
  have hu : 0 < a ^ 2 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (a ^ 2 + x ^ 2) := Real.sqrt_pos.2 hu
  have hsq :
      Real.sqrt (a ^ 2 + x ^ 2) ^ 2 = a ^ 2 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hu)
  have hsx : 0 < Real.sqrt (a ^ 2 + x ^ 2) - x := by
    by_cases hx : x ≤ 0
    · nlinarith
    · have hxpos : 0 < x := lt_of_not_ge hx
      by_contra hn
      have hsle : Real.sqrt (a ^ 2 + x ^ 2) ≤ x := by linarith
      have hsqle :=
        mul_self_le_mul_self (le_of_lt hs) hsle
      nlinarith [hsqle]
  have hprod :
      (Real.sqrt (a ^ 2 + x ^ 2) - x) *
          (Real.sqrt (a ^ 2 + x ^ 2) + x) = a ^ 2 := by
    nlinarith [hsq]
  have hp :
      0 < (Real.sqrt (a ^ 2 + x ^ 2) - x) *
          (Real.sqrt (a ^ 2 + x ^ 2) + x) := by
    rw [hprod]
    exact ha2
  have hxs : 0 < x + Real.sqrt (a ^ 2 + x ^ 2) := by
    rcases (mul_pos_iff.mp hp) with h | h
    · nlinarith [h.2]
    · nlinarith [hsx, h.1]
  have hq : 0 < (x + Real.sqrt (a ^ 2 + x ^ 2)) / a :=
    div_pos hxs ha
  have hinv :
      ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a)⁻¹ =
        (Real.sqrt (a ^ 2 + x ^ 2) - x) / a := by
    field_simp [ne_of_gt ha, ne_of_gt hxs] <;> nlinarith [hsq]
  have hexp :
      Real.exp
          (Real.log ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a)) =
        (x + Real.sqrt (a ^ 2 + x ^ 2)) / a :=
    Real.exp_log hq
  have hexpneg :
      Real.exp
          (-Real.log ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a)) =
        ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a)⁻¹ := by
    rw [Real.exp_neg, hexp]
  have hsinh :
      Real.sinh
          (Real.log ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a)) =
        x / a := by
    rw [Real.sinh_eq, hexp, hexpneg, hinv]
    field_simp [ne_of_gt ha] <;> ring
  have hcosh :
      Real.cosh
          (Real.log ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a)) =
        Real.sqrt (a ^ 2 + x ^ 2) / a := by
    rw [Real.cosh_eq, hexp, hexpneg, hinv]
    field_simp [ne_of_gt ha] <;> ring
  have hlog :
      Real.log ((x + Real.sqrt (a ^ 2 + x ^ 2)) / a) =
        Real.log (x + Real.sqrt (a ^ 2 + x ^ 2)) - Real.log a := by
    exact Real.log_div (ne_of_gt hxs) (ne_of_gt ha)
  unfold anglePrimitive tOf primitive
  rw [Real.sinh_two_mul, hsinh, hcosh, hlog]
  field_simp [ne_of_gt ha] <;> ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    Family (integrand a) = Translates (primitive a) := by
  ext F
  constructor
  · intro hF
    change IsAntiderivative F (integrand a) at hF
    let G : ℝ → ℝ := fun x => F x - primitive a x
    have hG : ∀ x, HasDerivAt G 0 x := by
      intro x
      dsimp [G]
      convert (hF x).sub (primitive_hasDerivAt a x ha) using 1 <;> ring
    have hGdiff : Differentiable ℝ G := fun x => (hG x).differentiableAt
    have hGderiv : ∀ x, deriv G x = 0 := fun x => (hG x).deriv
    refine ⟨G 0, ?_⟩
    intro x
    have hx0 : G x = G 0 :=
      is_const_of_deriv_eq_zero hGdiff hGderiv x 0
    dsimp [G] at hx0 ⊢
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivative F (integrand a)
    have hfun : F = fun x => primitive a x + C := funext hC
    subst F
    intro x
    simpa only [Pi.add_apply, add_zero] using
      (primitive_hasDerivAt a x ha).add (hasDerivAt_const x C)

end

end ProofGap.Exercise1787
