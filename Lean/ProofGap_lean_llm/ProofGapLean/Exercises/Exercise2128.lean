import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2128
noncomputable section

def sqrtThree : ℝ := Real.sqrt 3
def integrand (x : ℝ) := 1 / (1 + x ^ 4 + x ^ 8)
def qPlusOne (x : ℝ) := x ^ 2 + x + 1
def qMinusOne (x : ℝ) := x ^ 2 - x + 1
def qPlusSqrt (x : ℝ) := x ^ 2 + x * sqrtThree + 1
def qMinusSqrt (x : ℝ) := x ^ 2 - x * sqrtThree + 1
def logDiffPlus (x : ℝ) := (2 * x + sqrtThree) / qPlusSqrt x
def logDiffMinus (x : ℝ) := (2 * x - sqrtThree) / qMinusSqrt x
def primitiveExpanded (x : ℝ) :=
  1 / (2 * sqrtThree) *
      (Real.arctan ((2 * x + 1) / sqrtThree) +
        Real.arctan ((2 * x - 1) / sqrtThree)) +
    1 / (4 * sqrtThree) *
      (Real.log (qPlusSqrt x) - Real.log (qMinusSqrt x))
def primitiveCompact (x : ℝ) :=
  -(1 / (2 * sqrtThree)) *
      Real.arctan ((1 - x ^ 2) / (x * sqrtThree)) +
    1 / (4 * sqrtThree) * Real.log (qPlusSqrt x / qMinusSqrt x)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def CombinationFamily :=
  {F : ℝ → ℝ |
    ∃ A ∈ Family (fun x => 1 / qPlusOne x),
    ∃ B ∈ Family (fun x => 1 / qMinusOne x),
    ∃ C ∈ Family logDiffPlus,
    ∃ D ∈ Family logDiffMinus,
    ∀ x, F x =
      (1 / 4 : ℝ) * A x + (1 / 4 : ℝ) * B x +
      1 / (4 * sqrtThree) * C x - 1 / (4 * sqrtThree) * D x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}
def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Iio 0 ∨ U = Set.Ioi 0
def FamilyOn (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def TranslatesOn (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem sqrtThree_pos : 0 < sqrtThree := by
  unfold sqrtThree
  positivity

private theorem sqrtThree_ne : sqrtThree ≠ 0 := ne_of_gt sqrtThree_pos

private theorem sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  unfold sqrtThree
  exact Real.sq_sqrt (by norm_num)

private theorem qPlusOne_pos (x : ℝ) : 0 < qPlusOne x := by
  unfold qPlusOne
  nlinarith [sq_nonneg (x + 1 / 2)]

private theorem qMinusOne_pos (x : ℝ) : 0 < qMinusOne x := by
  unfold qMinusOne
  nlinarith [sq_nonneg (x - 1 / 2)]

private theorem qPlusSqrt_pos (x : ℝ) : 0 < qPlusSqrt x := by
  unfold qPlusSqrt
  nlinarith [sqrtThree_sq, sq_nonneg (2 * x + sqrtThree)]

private theorem qMinusSqrt_pos (x : ℝ) : 0 < qMinusSqrt x := by
  unfold qMinusSqrt
  nlinarith [sqrtThree_sq, sq_nonneg (2 * x - sqrtThree)]

private theorem qPlusOne_ne (x : ℝ) : qPlusOne x ≠ 0 := ne_of_gt (qPlusOne_pos x)
private theorem qMinusOne_ne (x : ℝ) : qMinusOne x ≠ 0 := ne_of_gt (qMinusOne_pos x)
private theorem qPlusSqrt_ne (x : ℝ) : qPlusSqrt x ≠ 0 := ne_of_gt (qPlusSqrt_pos x)
private theorem qMinusSqrt_ne (x : ℝ) : qMinusSqrt x ≠ 0 := ne_of_gt (qMinusSqrt_pos x)

private theorem polyMinus_ne (x : ℝ) : x ^ 4 - x ^ 2 + 1 ≠ 0 := by
  have h : 0 < x ^ 4 - x ^ 2 + 1 := by
    nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
  exact ne_of_gt h

private theorem twoFactorPartialFraction
    (A B t : ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hnum : (t + 1) * B - (t - 1) * A = 2) :
    1 / (A * B) =
      (1 / 2 : ℝ) * ((t + 1) / A - (t - 1) / B) := by
  field_simp [hA, hB] <;> nlinarith

private def plusPrimitive (x : ℝ) :=
  2 / sqrtThree * Real.arctan ((2 * x + 1) / sqrtThree)

private def minusPrimitive (x : ℝ) :=
  2 / sqrtThree * Real.arctan ((2 * x - 1) / sqrtThree)

private def plusLogPrimitive (x : ℝ) := Real.log (qPlusSqrt x)
private def minusLogPrimitive (x : ℝ) := Real.log (qMinusSqrt x)

private theorem hasDerivAt_qPlusSqrt (x : ℝ) :
    HasDerivAt qPlusSqrt (2 * x + sqrtThree) x := by
  unfold qPlusSqrt
  convert (((hasDerivAt_id x).pow 2).add
    ((hasDerivAt_id x).mul_const sqrtThree)).add_const 1 using 1 <;>
    simp <;> ring

private theorem hasDerivAt_qMinusSqrt (x : ℝ) :
    HasDerivAt qMinusSqrt (2 * x - sqrtThree) x := by
  unfold qMinusSqrt
  convert (((hasDerivAt_id x).pow 2).sub
    ((hasDerivAt_id x).mul_const sqrtThree)).add_const 1 using 1 <;>
    simp <;> ring

private theorem hasDerivAt_plusPrimitive (x : ℝ) :
    HasDerivAt plusPrimitive (1 / qPlusOne x) x := by
  have haff : HasDerivAt (fun y : ℝ => (2 * y + 1) / sqrtThree)
      (2 / sqrtThree) x := by
    convert ((((hasDerivAt_id x).const_mul 2).add_const 1).div_const
      sqrtThree) using 1 <;> simp <;> ring
  have h := (Real.hasDerivAt_arctan _).comp x haff
  have hden :
      1 + ((2 * x + 1) / sqrtThree) ^ 2 =
        4 * qPlusOne x / sqrtThree ^ 2 := by
    field_simp [sqrtThree_ne]
    unfold qPlusOne
    nlinarith [sqrtThree_sq]
  unfold plusPrimitive
  convert h.const_mul (2 / sqrtThree) using 1
  rw [hden]
  field_simp [sqrtThree_ne, qPlusOne_ne x]
  ring

private theorem hasDerivAt_minusPrimitive (x : ℝ) :
    HasDerivAt minusPrimitive (1 / qMinusOne x) x := by
  have haff : HasDerivAt (fun y : ℝ => (2 * y - 1) / sqrtThree)
      (2 / sqrtThree) x := by
    convert ((((hasDerivAt_id x).const_mul 2).sub_const 1).div_const
      sqrtThree) using 1 <;> simp <;> ring
  have h := (Real.hasDerivAt_arctan _).comp x haff
  have hden :
      1 + ((2 * x - 1) / sqrtThree) ^ 2 =
        4 * qMinusOne x / sqrtThree ^ 2 := by
    field_simp [sqrtThree_ne]
    unfold qMinusOne
    nlinarith [sqrtThree_sq]
  unfold minusPrimitive
  convert h.const_mul (2 / sqrtThree) using 1
  rw [hden]
  field_simp [sqrtThree_ne, qMinusOne_ne x]
  ring

private theorem hasDerivAt_logPlus (x : ℝ) :
    HasDerivAt plusLogPrimitive (logDiffPlus x) x := by
  unfold plusLogPrimitive logDiffPlus
  convert (Real.hasDerivAt_log (qPlusSqrt_ne x)).comp x
    (hasDerivAt_qPlusSqrt x) using 1
  field_simp [qPlusSqrt_ne x]

private theorem hasDerivAt_logMinus (x : ℝ) :
    HasDerivAt minusLogPrimitive (logDiffMinus x) x := by
  unfold minusLogPrimitive logDiffMinus
  convert (Real.hasDerivAt_log (qMinusSqrt_ne x)).comp x
    (hasDerivAt_qMinusSqrt x) using 1
  field_simp [qMinusSqrt_ne x]

private theorem primitiveExpanded_eq_components (x : ℝ) :
    primitiveExpanded x =
      (1 / 4 : ℝ) * plusPrimitive x +
      (1 / 4 : ℝ) * minusPrimitive x +
      1 / (4 * sqrtThree) * plusLogPrimitive x -
      1 / (4 * sqrtThree) * minusLogPrimitive x := by
  unfold primitiveExpanded plusPrimitive minusPrimitive
    plusLogPrimitive minusLogPrimitive
  field_simp [sqrtThree_ne]
  ring

private theorem hasDerivAt_compactArctan (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ =>
        -(1 / (2 * sqrtThree)) *
          Real.arctan ((1 - y ^ 2) / (y * sqrtThree)))
      ((1 / 2 : ℝ) *
        ((x ^ 2 + 1) / (x ^ 4 + x ^ 2 + 1))) x := by
  have hnum : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
      using 1 <;> simp <;> ring
  have hden : HasDerivAt (fun y : ℝ => y * sqrtThree) sqrtThree x := by
    convert (hasDerivAt_id x).mul_const sqrtThree using 1 <;>
      simp <;> ring
  have hquot := hnum.div hden (mul_ne_zero hx sqrtThree_ne)
  have hatan := (Real.hasDerivAt_arctan _).comp x hquot
  simp only [Pi.div_apply] at hatan
  have hpoly : x ^ 4 + x ^ 2 + 1 ≠ 0 := by positivity
  have harg : 1 + ((1 - x ^ 2) / (x * sqrtThree)) ^ 2 ≠ 0 := by positivity
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hnorm :
      x ^ 2 * sqrtThree ^ 2 + (1 - x ^ 2) ^ 2 ≠ 0 := by
    apply ne_of_gt
    rw [sqrtThree_sq]
    nlinarith [sq_nonneg (1 - x ^ 2)]
  convert hatan.const_mul (-(1 / (2 * sqrtThree))) using 1
  field_simp [hx, sqrtThree_ne, hpoly, harg, hnorm]
  nlinarith [sqrtThree_sq]

theorem gap1 (x : ℝ) :
    1 + x ^ 4 + x ^ 8 = (x ^ 4 + 1) ^ 2 - x ^ 4 := by
  ring
theorem gap2 (x : ℝ) :
    (x ^ 4 + 1) ^ 2 - x ^ 4 =
      (x ^ 4 + x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) := by
  ring
theorem gap3 (x : ℝ) :
    1 + x ^ 4 + x ^ 8 =
      (x ^ 4 + x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) := by
  rw [gap1, gap2]
theorem gap4 (x : ℝ) :
    x ^ 4 + x ^ 2 + 1 = (x ^ 2 + 1) ^ 2 - x ^ 2 := by
  ring
theorem gap5 (x : ℝ) :
    (x ^ 2 + 1) ^ 2 - x ^ 2 = qPlusOne x * qMinusOne x := by
  unfold qPlusOne qMinusOne
  ring
theorem gap6 (x : ℝ) :
    x ^ 4 + x ^ 2 + 1 = qPlusOne x * qMinusOne x := by
  rw [gap4, gap5]
theorem gap7 (x : ℝ) :
    x ^ 4 - x ^ 2 + 1 = (x ^ 2 + 1) ^ 2 - 3 * x ^ 2 := by
  ring
theorem gap8 (x : ℝ) :
    (x ^ 2 + 1) ^ 2 - 3 * x ^ 2 = qPlusSqrt x * qMinusSqrt x := by
  unfold qPlusSqrt qMinusSqrt
  nlinarith [sqrtThree_sq]
theorem gap9 (x : ℝ) :
    x ^ 4 - x ^ 2 + 1 = qPlusSqrt x * qMinusSqrt x := by
  rw [gap7, gap8]
theorem gap10 (x : ℝ) :
    integrand x =
      (1 / 2 : ℝ) *
        ((x ^ 2 + 1) / (x ^ 4 + x ^ 2 + 1) -
          (x ^ 2 - 1) / (x ^ 4 - x ^ 2 + 1)) := by
  have hA : x ^ 4 + x ^ 2 + 1 ≠ 0 := by positivity
  have hB : x ^ 4 - x ^ 2 + 1 ≠ 0 := polyMinus_ne x
  unfold integrand
  rw [gap3]
  exact twoFactorPartialFraction
    (x ^ 4 + x ^ 2 + 1)
    (x ^ 4 - x ^ 2 + 1)
    (x ^ 2) hA hB (by ring)
theorem gap11 (x : ℝ) :
    (x ^ 2 + 1) / (x ^ 4 + x ^ 2 + 1) =
      (1 / 2 : ℝ) * (1 / qPlusOne x + 1 / qMinusOne x) := by
  rw [gap6]
  field_simp [qPlusOne_ne x, qMinusOne_ne x]
  unfold qPlusOne qMinusOne
  ring
theorem gap12 (x : ℝ) :
    (x ^ 2 - 1) / (x ^ 4 - x ^ 2 + 1) =
      ((-(1 / sqrtThree) * x - (1 / 2 : ℝ)) / qPlusSqrt x) +
      (((1 / sqrtThree) * x - (1 / 2 : ℝ)) / qMinusSqrt x) := by
  rw [gap9]
  field_simp [qPlusSqrt_ne x, qMinusSqrt_ne x, sqrtThree_ne]
  unfold qPlusSqrt qMinusSqrt
  nlinarith [sqrtThree_sq]
theorem gap13 : Family integrand = CombinationFamily := by
  have hdecomp : ∀ x : ℝ,
      integrand x =
        (1 / 4 : ℝ) * (1 / qPlusOne x) +
        (1 / 4 : ℝ) * (1 / qMinusOne x) +
        1 / (4 * sqrtThree) * logDiffPlus x -
        1 / (4 * sqrtThree) * logDiffMinus x := by
    intro x
    rw [gap10 x, gap11 x, gap12 x]
    unfold logDiffPlus logDiffMinus
    field_simp [sqrtThree_ne, qPlusOne_ne x, qMinusOne_ne x,
      qPlusSqrt_ne x, qMinusSqrt_ne x] <;> ring
  have hprim : ∀ x : ℝ, HasDerivAt primitiveExpanded (integrand x) x := by
    intro x
    have h :=
      ((((hasDerivAt_plusPrimitive x).const_mul (1 / 4 : ℝ)).add
        ((hasDerivAt_minusPrimitive x).const_mul (1 / 4 : ℝ))).add
        ((hasDerivAt_logPlus x).const_mul (1 / (4 * sqrtThree)))).sub
        ((hasDerivAt_logMinus x).const_mul (1 / (4 * sqrtThree)))
    have heq : primitiveExpanded = fun y =>
        (1 / 4 : ℝ) * plusPrimitive y +
        (1 / 4 : ℝ) * minusPrimitive y +
        1 / (4 * sqrtThree) * plusLogPrimitive y -
        1 / (4 * sqrtThree) * minusLogPrimitive y := by
      funext y
      exact primitiveExpanded_eq_components y
    rw [heq]
    convert h using 1
    exact hdecomp x
  apply Set.Subset.antisymm
  · intro F hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    let g : ℝ → ℝ := fun x => F x - primitiveExpanded x
    have hg : ∀ x, HasDerivAt g 0 x := by
      intro x
      dsimp [g]
      convert (hF x).sub (hprim x) using 1 <;> ring
    have hdiff : Differentiable ℝ g := fun x => (hg x).differentiableAt
    have hderiv : ∀ x, deriv g x = 0 := fun x => (hg x).deriv
    unfold CombinationFamily
    refine ⟨fun x => plusPrimitive x + 4 * g 0, ?_,
      fun x => minusPrimitive x, ?_,
      fun x => plusLogPrimitive x, ?_,
      fun x => minusLogPrimitive x, ?_, ?_⟩
    · intro x
      exact (hasDerivAt_plusPrimitive x).add_const (4 * g 0)
    · exact hasDerivAt_minusPrimitive
    · exact hasDerivAt_logPlus
    · exact hasDerivAt_logMinus
    · intro x
      have hc : g x = g 0 :=
        is_const_of_deriv_eq_zero hdiff hderiv x 0
      have hFx : F x = primitiveExpanded x + g 0 := by
        dsimp [g] at hc
        linarith
      rw [hFx, primitiveExpanded_eq_components]
      ring
  · intro F hF
    unfold CombinationFamily at hF
    rcases hF with ⟨A, hA, B, hB, C, hC, D, hD, hF⟩
    have heq : F = fun x =>
        (1 / 4 : ℝ) * A x + (1 / 4 : ℝ) * B x +
        1 / (4 * sqrtThree) * C x -
        1 / (4 * sqrtThree) * D x := funext hF
    rw [heq]
    intro x
    have h :=
      ((((hA x).const_mul (1 / 4 : ℝ)).add
        ((hB x).const_mul (1 / 4 : ℝ))).add
        ((hC x).const_mul (1 / (4 * sqrtThree)))).sub
        ((hD x).const_mul (1 / (4 * sqrtThree)))
    convert h using 1
    exact hdecomp x
theorem gap14 : Family integrand = Translates primitiveExpanded := by
  have hdecomp : ∀ x : ℝ,
      integrand x =
        (1 / 4 : ℝ) * (1 / qPlusOne x) +
        (1 / 4 : ℝ) * (1 / qMinusOne x) +
        1 / (4 * sqrtThree) * logDiffPlus x -
        1 / (4 * sqrtThree) * logDiffMinus x := by
    intro x
    rw [gap10 x, gap11 x, gap12 x]
    unfold logDiffPlus logDiffMinus
    field_simp [sqrtThree_ne, qPlusOne_ne x, qMinusOne_ne x,
      qPlusSqrt_ne x, qMinusSqrt_ne x] <;> ring
  have hprim : ∀ x : ℝ, HasDerivAt primitiveExpanded (integrand x) x := by
    intro x
    have h :=
      ((((hasDerivAt_plusPrimitive x).const_mul (1 / 4 : ℝ)).add
        ((hasDerivAt_minusPrimitive x).const_mul (1 / 4 : ℝ))).add
        ((hasDerivAt_logPlus x).const_mul (1 / (4 * sqrtThree)))).sub
        ((hasDerivAt_logMinus x).const_mul (1 / (4 * sqrtThree)))
    have heq : primitiveExpanded = fun y =>
        (1 / 4 : ℝ) * plusPrimitive y +
        (1 / 4 : ℝ) * minusPrimitive y +
        1 / (4 * sqrtThree) * plusLogPrimitive y -
        1 / (4 * sqrtThree) * minusLogPrimitive y := by
      funext y
      exact primitiveExpanded_eq_components y
    rw [heq]
    convert h using 1
    exact hdecomp x
  ext F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ C : ℝ, ∀ x, F x = primitiveExpanded x + C
  constructor
  · intro hF
    let g : ℝ → ℝ := fun x => F x - primitiveExpanded x
    have hg : ∀ x, HasDerivAt g 0 x := by
      intro x
      dsimp [g]
      convert (hF x).sub (hprim x) using 1 <;> ring
    have hdiff : Differentiable ℝ g := fun x => (hg x).differentiableAt
    have hderiv : ∀ x, deriv g x = 0 := fun x => (hg x).deriv
    refine ⟨g 0, ?_⟩
    intro x
    have hc : g x = g 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    dsimp [g] at hc ⊢
    linarith
  · rintro ⟨C, hF⟩
    have heq : F = fun x => primitiveExpanded x + C := funext hF
    rw [heq]
    intro x
    exact (hprim x).add_const C
theorem gap15 (U : Set ℝ) (hU : AdmissibleBranch U) :
    FamilyOn U integrand = TranslatesOn U primitiveCompact := by
  have hp : ∀ x : ℝ, x ≠ 0 → HasDerivAt primitiveCompact (integrand x) x := by
    intro x hx
    have hlogs :=
      ((hasDerivAt_logPlus x).sub (hasDerivAt_logMinus x)).const_mul
        (1 / (4 * sqrtThree))
    have hsum := (hasDerivAt_compactArctan x hx).add hlogs
    have hfun : primitiveCompact = fun y =>
        -(1 / (2 * sqrtThree)) *
            Real.arctan ((1 - y ^ 2) / (y * sqrtThree)) +
          1 / (4 * sqrtThree) *
            (plusLogPrimitive - minusLogPrimitive) y := by
      funext y
      unfold primitiveCompact
      rw [Real.log_div (qPlusSqrt_ne y) (qMinusSqrt_ne y)]
      simp [plusLogPrimitive, minusLogPrimitive]
    have hcoef : integrand x =
        (1 / 2 : ℝ) *
            ((x ^ 2 + 1) / (x ^ 4 + x ^ 2 + 1)) +
          1 / (4 * sqrtThree) *
            (logDiffPlus x - logDiffMinus x) := by
      rw [gap10 x, gap12 x]
      unfold logDiffPlus logDiffMinus
      have hpoly : x ^ 4 + x ^ 2 + 1 ≠ 0 := by positivity
      field_simp [sqrtThree_ne, qPlusSqrt_ne x,
        qMinusSqrt_ne x, hpoly] <;> ring
    rw [hfun, hcoef]
    exact hsum
  ext F
  change (∀ x ∈ U, HasDerivAt F (integrand x) x) ↔
    ∃ C : ℝ, ∀ x ∈ U, F x = primitiveCompact x + C
  rcases hU with rfl | rfl
  · constructor
    · intro hF
      let g : ℝ → ℝ := fun y => F y - primitiveCompact y
      have hg : ∀ x ∈ Set.Iio (0 : ℝ), HasDerivAt g 0 x := by
        intro x hx
        dsimp [g]
        convert (hF x hx).sub (hp x (ne_of_lt hx)) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ g (Set.Iio 0) := by
        intro x hx
        exact (hg x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ Set.Iio (0 : ℝ), deriv g x = 0 := by
        intro x hx
        exact (hg x hx).deriv
      refine ⟨g (-1), ?_⟩
      intro x hx
      have hc : g x = g (-1) :=
        isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
          hdiff hderiv hx (by norm_num)
      dsimp [g] at hc ⊢
      linarith
    · rintro ⟨C, hF⟩ x hx
      have hbase := (hp x (ne_of_lt hx)).add_const C
      apply hbase.congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      exact hF y hy
  · constructor
    · intro hF
      let g : ℝ → ℝ := fun y => F y - primitiveCompact y
      have hg : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt g 0 x := by
        intro x hx
        dsimp [g]
        convert (hF x hx).sub (hp x (ne_of_gt hx)) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ g (Set.Ioi 0) := by
        intro x hx
        exact (hg x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), deriv g x = 0 := by
        intro x hx
        exact (hg x hx).deriv
      refine ⟨g 1, ?_⟩
      intro x hx
      have hc : g x = g 1 :=
        isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
          hdiff hderiv hx (by norm_num)
      dsimp [g] at hc ⊢
      linarith
    · rintro ⟨C, hF⟩ x hx
      have hbase := (hp x (ne_of_gt hx)).add_const C
      apply hbase.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact hF y hy

end
end ProofGap.Exercise2128
