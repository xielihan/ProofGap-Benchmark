import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3365_3

noncomputable section

def identityFunction (x : ℝ) : ℝ :=
  x

def negIdentityFunction (x : ℝ) : ℝ :=
  -x

def IsDifferentiableSquareRootChoice (y : ℝ → ℝ) : Prop :=
  Differentiable ℝ y ∧ ∀ x, x ^ 2 = y x ^ 2

def differentiableSquareRootChoices : Set (ℝ → ℝ) :=
  {y | IsDifferentiableSquareRootChoice y}

private lemma square_root_deriv_relation
    {y : ℝ → ℝ} (hy : Differentiable ℝ y)
    (hsq : ∀ x, x ^ 2 = y x ^ 2) (x : ℝ) :
    x = y x * deriv y x := by
  have hxderiv : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
    · funext z
      simp [pow_two]
    · dsimp [id]
      ring
  have hyderiv :
      HasDerivAt (fun z : ℝ => y z ^ 2) (2 * y x * deriv y x) x := by
    convert (hy x).hasDerivAt.mul (hy x).hasDerivAt using 1
    · funext z
      simp [pow_two]
    · ring
  have hfun : (fun z : ℝ => z ^ 2) = fun z : ℝ => y z ^ 2 := by
    funext z
    exact hsq z
  rw [hfun] at hxderiv
  have hxval := hxderiv.deriv
  have hyval := hyderiv.deriv
  nlinarith

private lemma square_root_quotient_deriv_zero
    {y : ℝ → ℝ} (hy : Differentiable ℝ y)
    (hsq : ∀ x, x ^ 2 = y x ^ 2) {x : ℝ} (hx : x ≠ 0) :
    deriv (fun z : ℝ => y z / z) x = 0 := by
  have hyx : y x ≠ 0 := by
    intro hyx0
    apply hx
    have h := hsq x
    rw [hyx0] at h
    norm_num at h
    nlinarith [sq_nonneg x]
  have hd : deriv y x = x / y x := by
    apply (eq_div_iff hyx).2
    simpa [mul_comm] using (square_root_deriv_relation hy hsq x).symm
  have hxy : deriv y x * x = y x := by
    rw [hd]
    calc
      (x / y x) * x = (x * x) / y x := by ring
      _ = y x := by
        apply (div_eq_iff hyx).2
        nlinarith [hsq x]
  have hquot :
      HasDerivAt (fun z : ℝ => y z / z)
        ((deriv y x * x - y x * 1) / x ^ 2) x :=
    (hy x).hasDerivAt.div (hasDerivAt_id x) hx
  have hquot0 : HasDerivAt (fun z : ℝ => y z / z) 0 x := by
    simpa [hxy] using hquot
  exact hquot0.deriv

private lemma square_root_quotient_eq_pos
    {y : ℝ → ℝ} (hy : Differentiable ℝ y)
    (hsq : ∀ x, x ^ 2 = y x ^ 2) {x z : ℝ}
    (hx : 0 < x) (hz : 0 < z) :
    y x / x = y z / z := by
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun t ht =>
      ((hy t).div differentiableAt_id (ne_of_gt ht)).differentiableWithinAt)
    (fun t ht => square_root_quotient_deriv_zero hy hsq (ne_of_gt ht))
    hx hz

private lemma square_root_quotient_eq_neg
    {y : ℝ → ℝ} (hy : Differentiable ℝ y)
    (hsq : ∀ x, x ^ 2 = y x ^ 2) {x z : ℝ}
    (hx : x < 0) (hz : z < 0) :
    y x / x = y z / z := by
  exact isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
    (fun t ht =>
      ((hy t).div differentiableAt_id (ne_of_lt ht)).differentiableWithinAt)
    (fun t ht => square_root_quotient_deriv_zero hy hsq (ne_of_lt ht))
    hx hz

private theorem classify_differentiable_square_root
    {y : ℝ → ℝ} (hy : Differentiable ℝ y)
    (hsq : ∀ x, x ^ 2 = y x ^ 2) :
    y = negIdentityFunction ∨ y = identityFunction := by
  have hyzero : y 0 = 0 := by
    nlinarith [hsq 0]
  have hpos : ∀ x : ℝ, 0 < x → y x = y 1 * x := by
    intro x hx
    have hq := square_root_quotient_eq_pos hy hsq hx zero_lt_one
    calc
      y x = (y x / x) * x := by
        field_simp [ne_of_gt hx]
      _ = (y 1 / 1) * x := by rw [hq]
      _ = y 1 * x := by norm_num
  have hneg : ∀ x : ℝ, x < 0 → y x = (-y (-1)) * x := by
    intro x hx
    have hq := square_root_quotient_eq_neg hy hsq hx (by norm_num : (-1 : ℝ) < 0)
    calc
      y x = (y x / x) * x := by
        field_simp [ne_of_lt hx]
      _ = (y (-1) / (-1)) * x := by rw [hq]
      _ = (-y (-1)) * x := by ring
  have hEqPos : Set.EqOn y (fun x : ℝ => y 1 * x) (Set.Ici 0) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [hyzero]
    · exact hpos x (lt_of_le_of_ne hx (Ne.symm hx0))
  have hEqNeg : Set.EqOn y (fun x : ℝ => (-y (-1)) * x) (Set.Iic 0) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [hyzero]
    · exact hneg x (lt_of_le_of_ne hx hx0)
  have hlinPos :
      HasDerivWithinAt (fun x : ℝ => y 1 * x) (y 1) (Set.Ici 0) 0 := by
    simpa using ((hasDerivAt_id 0).const_mul (y 1)).hasDerivWithinAt
  have hlinNeg :
      HasDerivWithinAt (fun x : ℝ => (-y (-1)) * x) (-y (-1)) (Set.Iic 0) 0 := by
    simpa using ((hasDerivAt_id 0).const_mul (-y (-1))).hasDerivWithinAt
  have hyPos : HasDerivWithinAt y (y 1) (Set.Ici 0) 0 := by
    exact hlinPos.congr hEqPos (hEqPos (by simp))
  have hyNeg : HasDerivWithinAt y (-y (-1)) (Set.Iic 0) 0 := by
    exact hlinNeg.congr hEqNeg (hEqNeg (by simp))
  have huniqPos : UniqueDiffWithinAt ℝ (Set.Ici (0 : ℝ)) 0 :=
    (uniqueDiffOn_Ici (0 : ℝ)) 0 (by simp)
  have huniqNeg : UniqueDiffWithinAt ℝ (Set.Iic (0 : ℝ)) 0 :=
    (uniqueDiffOn_Iic (0 : ℝ)) 0 (by simp)
  have hfullPos : HasDerivWithinAt y (deriv y 0) (Set.Ici 0) 0 :=
    (hy 0).hasDerivAt.hasDerivWithinAt
  have hfullNeg : HasDerivWithinAt y (deriv y 0) (Set.Iic 0) 0 :=
    (hy 0).hasDerivAt.hasDerivWithinAt
  have hdPosFull := hfullPos.derivWithin huniqPos
  have hdPosLinear := hyPos.derivWithin huniqPos
  have hdNegFull := hfullNeg.derivWithin huniqNeg
  have hdNegLinear := hyNeg.derivWithin huniqNeg
  have hcoef : y 1 = -y (-1) := by
    linarith
  have hall : ∀ x : ℝ, y x = y 1 * x := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [hneg x hx, ← hcoef]
    · subst x
      simp [hyzero]
    · exact hpos x hx
  have hfactor : (y 1 - 1) * (y 1 + 1) = 0 := by
    nlinarith [hsq 1]
  rcases mul_eq_zero.mp hfactor with hone | hnegone
  · right
    have hyone : y 1 = 1 := by linarith
    funext x
    rw [hall x, hyone]
    simp [identityFunction]
  · left
    have hynegone : y 1 = -1 := by linarith
    funext x
    rw [hall x, hynegone]
    simp [negIdentityFunction]

theorem gap1 :
    differentiableSquareRootChoices =
      {negIdentityFunction, identityFunction} := by
  ext y
  simp only [differentiableSquareRootChoices, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hsq⟩
    exact classify_differentiable_square_root hy hsq
  · intro hy
    rcases hy with rfl | rfl
    · constructor
      · simpa only [negIdentityFunction] using
          (differentiable_id.neg : Differentiable ℝ (fun x : ℝ => -x))
      · intro x
        simp [negIdentityFunction]
    · constructor
      · simpa only [identityFunction] using
          (differentiable_id : Differentiable ℝ (fun x : ℝ => x))
      · intro x
        simp [identityFunction]

theorem gap2 :
    differentiableSquareRootChoices.ncard = 2 := by
  rw [gap1]
  have hne : negIdentityFunction ≠ identityFunction := by
    intro h
    have h1 := congrFun h 1
    norm_num [negIdentityFunction, identityFunction] at h1
  simp [hne]

end

end ProofGap.Exercise3365_3
