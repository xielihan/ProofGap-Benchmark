import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2089
noncomputable section

def radicand (x : ℝ) := Real.exp (2 * x) + 4 * Real.exp x - 1
def f (x : ℝ) := Real.sqrt (radicand x)
def primitive (x : ℝ) :=
  Real.sqrt (radicand x) +
    2 * Real.log (Real.exp x + 2 + Real.sqrt (radicand x)) -
    Real.arcsin ((2 * Real.exp x - 1) / (Real.sqrt 5 * Real.exp x))
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Split (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ A ∈ Family U (fun x =>
    (2 * Real.exp (2 * x) + 4 * Real.exp x) / (2 * Real.sqrt (radicand x))),
  ∃ B ∈ Family U (fun x => Real.exp x / Real.sqrt (radicand x)),
  ∃ C ∈ Family U (fun x => 1 / Real.sqrt (radicand x)),
  ∃ C₀, ∀ x ∈ U, F x = A x + 2 * B x - C x + C₀}
def Substitutions (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ A ∈ Family U (fun x => deriv radicand x / (2 * Real.sqrt (radicand x))),
  ∃ B ∈ Family U (fun x => deriv (fun y => Real.exp y + 2) x /
    Real.sqrt ((Real.exp x + 2) ^ 2 - 5)),
  ∃ C ∈ Family U (fun x => deriv (fun y => Real.exp (-y) - 2) x /
    Real.sqrt (5 - (Real.exp (-x) - 2) ^ 2)),
  ∃ C₀, ∀ x ∈ U, F x = A x + 2 * B x + C x + C₀}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, 0 < radicand x

private def logPart (x : ℝ) :=
  Real.log (Real.exp x + 2 + Real.sqrt (radicand x))

private def asinPart (x : ℝ) :=
  Real.arcsin ((2 * Real.exp x - 1) / (Real.sqrt 5 * Real.exp x))

private theorem exp_two_mul (x : ℝ) :
    Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  ring

private theorem radicand_div_sqrt (x : ℝ) (hx : 0 < radicand x) :
    radicand x / Real.sqrt (radicand x) = Real.sqrt (radicand x) := by
  apply (div_eq_iff (Real.sqrt_pos.2 hx).ne').2
  simpa [pow_two] using (Real.sq_sqrt hx.le).symm

private theorem hasDerivAt_radicand (x : ℝ) :
    HasDerivAt radicand (2 * Real.exp (2 * x) + 4 * Real.exp x) x := by
  have htwo : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 2
  have hfirst : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * x)) x := by
    have h := (Real.hasDerivAt_exp (2 * x)).comp x htwo
    simpa only [Function.comp_def, mul_comm] using h
  have hsecond : HasDerivAt (fun y : ℝ => 4 * Real.exp y)
      (4 * Real.exp x) x :=
    (Real.hasDerivAt_exp x).const_mul 4
  simpa only [radicand] using (hfirst.add hsecond).sub_const 1

private theorem hasDerivAt_f (x : ℝ) (hx : 0 < radicand x) :
    HasDerivAt f
      ((2 * Real.exp (2 * x) + 4 * Real.exp x) /
        (2 * Real.sqrt (radicand x))) x := by
  have h := (Real.hasDerivAt_sqrt hx.ne').comp x (hasDerivAt_radicand x)
  simpa [f, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

private theorem hasDerivAt_logPart (x : ℝ) (hx : 0 < radicand x) :
    HasDerivAt logPart (Real.exp x / Real.sqrt (radicand x)) x := by
  let s := Real.sqrt (radicand x)
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hq : 0 < Real.exp x + 2 + s := by
    nlinarith [Real.exp_pos x]
  have hinner :
      HasDerivAt (fun y => Real.exp y + 2 + Real.sqrt (radicand y))
        (Real.exp x +
          (2 * Real.exp (2 * x) + 4 * Real.exp x) / (2 * s)) x := by
    simpa [f, s] using
      ((Real.hasDerivAt_exp x).add_const 2).add (hasDerivAt_f x hx)
  have hlog := (Real.hasDerivAt_log hq.ne').comp x hinner
  have hcoef :
      (Real.exp x + 2 + s)⁻¹ *
          (Real.exp x +
            (2 * Real.exp (2 * x) + 4 * Real.exp x) / (2 * s)) =
        Real.exp x / s := by
    rw [exp_two_mul]
    field_simp [hs.ne', hq.ne']
    ring
  simpa [logPart, s, hcoef] using hlog

private theorem hasDerivAt_zpart (x : ℝ) :
    HasDerivAt
      (fun y => (2 * Real.exp y - 1) / (Real.sqrt 5 * Real.exp y))
      (1 / (Real.sqrt 5 * Real.exp x)) x := by
  have ha : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have ht : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hnum := ((Real.hasDerivAt_exp x).const_mul 2).sub_const 1
  have hden := (Real.hasDerivAt_exp x).const_mul (Real.sqrt 5)
  have h := hnum.div hden (mul_ne_zero ha.ne' ht)
  convert h using 1
  field_simp [ha.ne', ht]
  ring

private theorem asin_data (x : ℝ) (hx : 0 < radicand x) :
    let z := (2 * Real.exp x - 1) / (Real.sqrt 5 * Real.exp x)
    z ∈ Set.Ioo (-1) 1 ∧
      Real.sqrt (1 - z ^ 2) =
        Real.sqrt (radicand x) / (Real.sqrt 5 * Real.exp x) := by
  let t := Real.exp x
  let a := Real.sqrt 5
  let s := Real.sqrt (radicand x)
  let z := (2 * t - 1) / (a * t)
  have ht : 0 < t := Real.exp_pos x
  have ha : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have ha_sq : a ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs_sq : s ^ 2 = radicand x := Real.sq_sqrt hx.le
  have hrad : radicand x = t ^ 2 + 4 * t - 1 := by
    dsimp [t]
    rw [radicand, exp_two_mul]
  have hr : 0 < t ^ 2 + 4 * t - 1 := by
    nlinarith [hx, hrad]
  have hat_sq : (a * t) ^ 2 = 5 * t ^ 2 := by
    rw [mul_pow, ha_sq]
  have hsqdiff : 0 < (a * t) ^ 2 - (2 * t - 1) ^ 2 := by
    nlinarith
  have hlower : -(a * t) < 2 * t - 1 := by
    nlinarith [sq_nonneg (a * t + (2 * t - 1))]
  have hupper : 2 * t - 1 < a * t := by
    nlinarith [sq_nonneg (a * t - (2 * t - 1))]
  have hz : z ∈ Set.Ioo (-1) 1 := by
    constructor
    · change (-1 : ℝ) < (2 * t - 1) / (a * t)
      apply (lt_div_iff₀ (mul_pos ha ht)).2
      simpa using hlower
    · change (2 * t - 1) / (a * t) < (1 : ℝ)
      apply (div_lt_iff₀ (mul_pos ha ht)).2
      simpa using hupper
  have hw : 0 < 1 - z ^ 2 := by
    nlinarith [hz.1, hz.2, sq_nonneg (z + 1), sq_nonneg (1 - z)]
  have hratio_sq : (s / (a * t)) ^ 2 = 1 - z ^ 2 := by
    dsimp [z]
    field_simp [ha.ne', ht.ne']
    nlinarith [hs_sq, ha_sq, hrad]
  have hroot : Real.sqrt (1 - z ^ 2) = s / (a * t) := by
    have hsqrt_sq := Real.sq_sqrt hw.le
    have hratio : 0 < s / (a * t) := div_pos hs (mul_pos ha ht)
    nlinarith [Real.sqrt_nonneg (1 - z ^ 2),
      sq_nonneg (Real.sqrt (1 - z ^ 2) + s / (a * t))]
  simpa [z, t, a, s] using And.intro hz hroot

private theorem hasDerivAt_asinPart (x : ℝ) (hx : 0 < radicand x) :
    HasDerivAt asinPart (1 / Real.sqrt (radicand x)) x := by
  let z := (2 * Real.exp x - 1) / (Real.sqrt 5 * Real.exp x)
  rcases asin_data x hx with ⟨hz, hroot⟩
  have h :=
    (Real.hasDerivAt_arcsin hz.1.ne' hz.2.ne).comp x (hasDerivAt_zpart x)
  have hs : 0 < Real.sqrt (radicand x) := Real.sqrt_pos.2 hx
  have ha : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have ht : 0 < Real.exp x := Real.exp_pos x
  convert h using 1
  · rw [hroot] <;>
      field_simp [hs.ne', ha.ne', ht.ne'] <;>
      ring

private theorem split_coeff_forward (x : ℝ) (hx : 0 < radicand x) :
    f x - 2 * (Real.exp x / Real.sqrt (radicand x)) +
        1 / Real.sqrt (radicand x) =
      (2 * Real.exp (2 * x) + 4 * Real.exp x) /
        (2 * Real.sqrt (radicand x)) := by
  have hs := Real.sqrt_pos.2 hx
  have hs_sq := Real.sq_sqrt hx.le
  rw [f]
  field_simp [hs.ne']
  rw [hs_sq]
  simp only [radicand]
  rw [exp_two_mul]
  ring

private theorem split_coeff_reverse (x : ℝ) (hx : 0 < radicand x) :
    (2 * Real.exp (2 * x) + 4 * Real.exp x) /
          (2 * Real.sqrt (radicand x)) +
        2 * (Real.exp x / Real.sqrt (radicand x)) -
        1 / Real.sqrt (radicand x) = f x := by
  linarith [split_coeff_forward x hx]

private theorem hasDerivAt_adjusted (F : ℝ → ℝ) (x : ℝ)
    (hx : 0 < radicand x) (hF : HasDerivAt F (f x) x) :
    HasDerivAt (fun y => F y - 2 * logPart y + asinPart y)
      ((2 * Real.exp (2 * x) + 4 * Real.exp x) /
        (2 * Real.sqrt (radicand x))) x := by
  have h := (hF.sub ((hasDerivAt_logPart x hx).const_mul 2)).add
    (hasDerivAt_asinPart x hx)
  have h' : HasDerivAt (fun y => F y - 2 * logPart y + asinPart y)
      (f x - 2 * (Real.exp x / Real.sqrt (radicand x)) +
        1 / Real.sqrt (radicand x)) x := by
    simpa only [Pi.sub_apply, Pi.add_apply] using h
  rw [split_coeff_forward x hx] at h'
  exact h'

private theorem hasDerivAt_splitSum (x : ℝ) (hx : 0 < radicand x)
    {A B C : ℝ → ℝ}
    (hA : HasDerivAt A
      ((2 * Real.exp (2 * x) + 4 * Real.exp x) /
        (2 * Real.sqrt (radicand x))) x)
    (hB : HasDerivAt B (Real.exp x / Real.sqrt (radicand x)) x)
    (hC : HasDerivAt C (1 / Real.sqrt (radicand x)) x) :
    HasDerivAt (fun y => A y + 2 * B y - C y) (f x) x := by
  have h := (hA.add (hB.const_mul 2)).sub hC
  have h' : HasDerivAt (fun y => A y + 2 * B y - C y)
      ((2 * Real.exp (2 * x) + 4 * Real.exp x) /
          (2 * Real.sqrt (radicand x)) +
        2 * (Real.exp x / Real.sqrt (radicand x)) -
        1 / Real.sqrt (radicand x)) x := by
    simpa only [Pi.add_apply, Pi.sub_apply] using h
  rw [split_coeff_reverse x hx] at h'
  exact h'

private theorem substitutionA_eq (x : ℝ) (_hx : 0 < radicand x) :
    deriv radicand x / (2 * Real.sqrt (radicand x)) =
      (2 * Real.exp (2 * x) + 4 * Real.exp x) /
        (2 * Real.sqrt (radicand x)) := by
  rw [(hasDerivAt_radicand x).deriv]

private theorem substitutionB_eq (x : ℝ) :
    deriv (fun y => Real.exp y + 2) x /
        Real.sqrt ((Real.exp x + 2) ^ 2 - 5) =
      Real.exp x / Real.sqrt (radicand x) := by
  have hd : deriv (fun y => Real.exp y + 2) x = Real.exp x :=
    ((Real.hasDerivAt_exp x).add_const 2).deriv
  have hr : (Real.exp x + 2) ^ 2 - 5 = radicand x := by
    rw [radicand, exp_two_mul]
    ring
  rw [hd, hr]

private theorem substitutionC_root (x : ℝ) (hx : 0 < radicand x) :
    Real.sqrt (5 - (Real.exp (-x) - 2) ^ 2) =
      Real.exp (-x) * Real.sqrt (radicand x) := by
  have hu : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have hs : 0 < Real.sqrt (radicand x) := Real.sqrt_pos.2 hx
  have hid :
      5 - (Real.exp (-x) - 2) ^ 2 =
        (Real.exp (-x)) ^ 2 * radicand x := by
    rw [Real.exp_neg]
    have ht : Real.exp x ≠ 0 := Real.exp_ne_zero x
    field_simp [ht]
    rw [radicand, exp_two_mul]
    ring
  have hi : 0 < 5 - (Real.exp (-x) - 2) ^ 2 := by
    rw [hid]
    exact mul_pos (sq_pos_of_pos hu) hx
  have hleft := Real.sq_sqrt hi.le
  have hright :
      (Real.exp (-x) * Real.sqrt (radicand x)) ^ 2 =
        5 - (Real.exp (-x) - 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx.le, ← hid]
  have hprod : 0 < Real.exp (-x) * Real.sqrt (radicand x) := mul_pos hu hs
  nlinarith [Real.sqrt_nonneg (5 - (Real.exp (-x) - 2) ^ 2), hprod.le,
    sq_nonneg (Real.sqrt (5 - (Real.exp (-x) - 2) ^ 2) +
      Real.exp (-x) * Real.sqrt (radicand x))]

private theorem substitutionC_eq (x : ℝ) (hx : 0 < radicand x) :
    deriv (fun y => Real.exp (-y) - 2) x /
        Real.sqrt (5 - (Real.exp (-x) - 2) ^ 2) =
      -(1 / Real.sqrt (radicand x)) := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x :=
    (hasDerivAt_id x).neg
  have hd : deriv (fun y => Real.exp (-y) - 2) x = -Real.exp (-x) := by
    simpa using (((Real.hasDerivAt_exp (-x)).comp x hneg).sub_const 2).deriv
  rw [hd, substitutionC_root x hx]
  have hu : Real.exp (-x) ≠ 0 := Real.exp_ne_zero (-x)
  have hs : Real.sqrt (radicand x) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  field_simp [hu, hs]

private theorem family_eq_translates {U : Set ℝ} {g p : ℝ → ℝ}
    (hopen : IsOpen U) (hconn : IsPreconnected U)
    (hp : p ∈ Family U g) : Family U g = Translates U p := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (g x) x at hF
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - p x₀, ?_⟩
      intro x hx
      have hdiff : DifferentiableOn ℝ (fun y => F y - p y) U := by
        intro y hy
        exact ((hF y hy).sub (hp y hy)).differentiableAt.differentiableWithinAt
      have hzero : ∀ y ∈ U, deriv (fun z => F z - p z) y = 0 := by
        intro y hy
        simpa using ((hF y hy).sub (hp y hy)).deriv
      have heq := hopen.is_const_of_deriv_eq_zero hconn hdiff hzero hx hx₀
      change F x - p x = F x₀ - p x₀ at heq
      change F x = p x + (F x₀ - p x₀)
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hEq⟩
    change ∀ x ∈ U, HasDerivAt F (g x) x
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y => C + p y) :=
      Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => by
        change F y = C + p y
        rw [hEq y hy]
        ring)
    exact ((hp x hx).const_add C).congr_of_eventuallyEq heq

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U f = Family U (fun x => radicand x / Real.sqrt (radicand x)) := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    have heq := radicand_div_sqrt x (hU.2.2 x hx)
    simpa [f, heq] using hF x hx
  · intro hF x hx
    have heq := radicand_div_sqrt x (hU.2.2 x hx)
    simpa [f, heq] using hF x hx
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U f = Split U := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (f x) x at hF
    change F ∈ Split U
    refine ⟨fun y => F y - 2 * logPart y + asinPart y, ?_, logPart, ?_, asinPart, ?_, 0, ?_⟩
    · intro x hx
      exact hasDerivAt_adjusted F x (hU.2.2 x hx) (hF x hx)
    · intro x hx
      exact hasDerivAt_logPart x (hU.2.2 x hx)
    · intro x hx
      exact hasDerivAt_asinPart x (hU.2.2 x hx)
    · intro x hx
      ring
  · intro hF
    change F ∈ Split U at hF
    change ∀ x ∈ U, HasDerivAt F (f x) x
    rcases hF with ⟨A, hA, B, hB, C, hC, C₀, hEq⟩
    intro x hx
    have hder :=
      (hasDerivAt_splitSum x (hU.2.2 x hx)
        (hA x hx) (hB x hx) (hC x hx)).const_add C₀
    have heq : F =ᶠ[nhds x] (fun y => C₀ + (A y + 2 * B y - C y)) :=
      Filter.mem_of_superset (hU.1.mem_nhds hx) (fun y hy => by
        change F y = C₀ + (A y + 2 * B y - C y)
        rw [hEq y hy]
        ring)
    exact hder.congr_of_eventuallyEq heq
theorem gap3 (U : Set ℝ) (hU : Regular U) :
    Family U f = Substitutions U := by
  rw [gap2 U hU]
  ext F
  constructor
  · rintro ⟨A, hA, B, hB, C, hC, C₀, hEq⟩
    refine ⟨A, ?_, B, ?_, fun y => -C y, ?_, C₀, ?_⟩
    · intro x hx
      change HasDerivAt A
        (deriv radicand x / (2 * Real.sqrt (radicand x))) x
      rw [substitutionA_eq x (hU.2.2 x hx)]
      exact hA x hx
    · intro x hx
      change HasDerivAt B
        (deriv (fun y => Real.exp y + 2) x /
          Real.sqrt ((Real.exp x + 2) ^ 2 - 5)) x
      rw [substitutionB_eq x]
      exact hB x hx
    · intro x hx
      change HasDerivAt (fun y => -C y)
        (deriv (fun y => Real.exp (-y) - 2) x /
          Real.sqrt (5 - (Real.exp (-x) - 2) ^ 2)) x
      rw [substitutionC_eq x (hU.2.2 x hx)]
      simpa only [Pi.neg_apply] using (hC x hx).neg
    · intro x hx
      simpa only [Pi.neg_apply, sub_eq_add_neg] using hEq x hx
  · rintro ⟨A, hA, B, hB, C, hC, C₀, hEq⟩
    refine ⟨A, ?_, B, ?_, fun y => -C y, ?_, C₀, ?_⟩
    · intro x hx
      have h := hA x hx
      change HasDerivAt A
        (deriv radicand x / (2 * Real.sqrt (radicand x))) x at h
      rw [substitutionA_eq x (hU.2.2 x hx)] at h
      exact h
    · intro x hx
      have h := hB x hx
      change HasDerivAt B
        (deriv (fun y => Real.exp y + 2) x /
          Real.sqrt ((Real.exp x + 2) ^ 2 - 5)) x at h
      rw [substitutionB_eq x] at h
      exact h
    · intro x hx
      have hneg := (hC x hx).neg
      change HasDerivAt (fun y => -C y)
        (-(deriv (fun y => Real.exp (-y) - 2) x /
          Real.sqrt (5 - (Real.exp (-x) - 2) ^ 2))) x at hneg
      rw [substitutionC_eq x (hU.2.2 x hx)] at hneg
      simpa only [neg_neg] using hneg
    · intro x hx
      simpa only [Pi.neg_apply, sub_neg_eq_add] using hEq x hx
theorem gap4 (U : Set ℝ) (hU : Regular U) :
    Family U f = Translates U primitive := by
  have hp : primitive ∈ Family U f := by
    rw [gap2 U hU]
    refine ⟨f, ?_, logPart, ?_, asinPart, ?_, 0, ?_⟩
    · intro x hx
      exact hasDerivAt_f x (hU.2.2 x hx)
    · intro x hx
      exact hasDerivAt_logPart x (hU.2.2 x hx)
    · intro x hx
      exact hasDerivAt_asinPart x (hU.2.2 x hx)
    · intro x hx
      simp only [primitive, f, logPart, asinPart, add_zero]
  exact family_eq_translates hU.1 hU.2.1 hp

end
end ProofGap.Exercise2089
