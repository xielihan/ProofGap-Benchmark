import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2109
noncomputable section

def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Ioi 1 ∨ U = Set.Iio (-1)
def integrand (x : ℝ) := x * Real.arccos (1 / x)
def squareDifferential (x : ℝ) :=
  Real.arccos (1 / x) * deriv (fun y : ℝ => y ^ 2) x
def residual (x : ℝ) := |x| / Real.sqrt (x ^ 2 - 1)
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) * x ^ 2 * Real.arccos (1 / x) -
    (1 / 2 : ℝ) * SignType.sign x * Real.sqrt (x ^ 2 - 1)

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def HalfFamily (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U f, ∀ x ∈ U, F x = (1 / 2 : ℝ) * A x}
def ByPartsFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U residual, ∀ x ∈ U,
    F x = (1 / 2 : ℝ) * x ^ 2 * Real.arccos (1 / x) - (1 / 2 : ℝ) * A x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem admissible_open {U : Set ℝ} (hU : AdmissibleBranch U) : IsOpen U := by
  rcases hU with hU | hU
  · simpa [hU] using isOpen_Ioi
  · simpa [hU] using isOpen_Iio

private theorem hasDerivAt_of_eqOn_open {U : Set ℝ} {f g : ℝ → ℝ}
    {f' x : ℝ} (hU : IsOpen U) (hx : x ∈ U) (hg : HasDerivAt g f' x)
    (hfg : ∀ y ∈ U, f y = g y) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hfg y hy

private theorem squareDifferential_eq_integrand (x : ℝ) :
    squareDifferential x = 2 * integrand x := by
  have hsq : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
    simpa using (((hasDerivAt_id x).pow 2).deriv)
  rw [squareDifferential, integrand, hsq]
  ring

private theorem admissible_radicand_pos {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : 0 < x ^ 2 - 1 := by
  rcases hU with hU | hU
  · rw [hU] at hx
    change 1 < x at hx
    nlinarith [sq_nonneg (x - 1)]
  · rw [hU] at hx
    change x < -1 at hx
    nlinarith [sq_nonneg (x + 1)]

private theorem sqrt_one_sub_inv_sq {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) :
    Real.sqrt (1 - (1 / x) ^ 2) = Real.sqrt (x ^ 2 - 1) / |x| := by
  have hrad : 0 < x ^ 2 - 1 := admissible_radicand_pos hU hx
  have hx0 : x ≠ 0 := by nlinarith [sq_nonneg x]
  have hfrac : 1 - (1 / x) ^ 2 = (x ^ 2 - 1) / x ^ 2 := by
    field_simp [hx0] <;> ring
  have hleft : 0 ≤ 1 - (1 / x) ^ 2 := by
    rw [hfrac]
    exact div_nonneg (le_of_lt hrad) (sq_nonneg x)
  have hsquares :
      (Real.sqrt (1 - (1 / x) ^ 2) * |x|) ^ 2 =
        (Real.sqrt (x ^ 2 - 1)) ^ 2 := by
    calc
      (Real.sqrt (1 - (1 / x) ^ 2) * |x|) ^ 2 =
          (1 - (1 / x) ^ 2) * x ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hleft, sq_abs]
      _ = x ^ 2 - 1 := by
        field_simp [hx0] <;> ring
      _ = (Real.sqrt (x ^ 2 - 1)) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hrad)]
  have hprod :
      Real.sqrt (1 - (1 / x) ^ 2) * |x| = Real.sqrt (x ^ 2 - 1) := by
    have ha : 0 ≤ Real.sqrt (1 - (1 / x) ^ 2) * |x| :=
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have hb : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
    nlinarith
  exact (eq_div_iff (abs_ne_zero.mpr hx0)).2 hprod

private theorem hasDerivAt_arccos_inv {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun y : ℝ => Real.arccos (1 / y))
      (|x| / (x ^ 2 * Real.sqrt (x ^ 2 - 1))) x := by
  have hrad : 0 < x ^ 2 - 1 := admissible_radicand_pos hU hx
  have hx0 : x ≠ 0 := by nlinarith [sq_nonneg x]
  have hz1 : (1 / x : ℝ) ≠ 1 := by
    intro h
    have heq : (1 : ℝ) = x := by
      calc
        (1 : ℝ) = (1 / x) * x := by field_simp [hx0]
        _ = 1 * x := by rw [h]
        _ = x := by ring
    nlinarith
  have hzn1 : (1 / x : ℝ) ≠ -1 := by
    intro h
    have heq : (1 : ℝ) = -x := by
      calc
        (1 : ℝ) = (1 / x) * x := by field_simp [hx0]
        _ = (-1) * x := by rw [h]
        _ = -x := by ring
    nlinarith
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    simpa only [one_div, id_eq] using (hasDerivAt_id x).inv hx0
  have hcomp := (Real.hasDerivAt_arccos hzn1 hz1).comp x hinv
  convert hcomp using 1
  rw [sqrt_one_sub_inv_sq hU hx]
  field_simp [hx0, abs_ne_zero.mpr hx0, Real.sqrt_ne_zero'.mpr hrad] <;> ring

private theorem hasDerivAt_mainTerm {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun y : ℝ => y ^ 2 * Real.arccos (1 / y))
      (squareDifferential x + residual x) x := by
  have hrad : 0 < x ^ 2 - 1 := admissible_radicand_pos hU hx
  have hx0 : x ≠ 0 := by nlinarith [sq_nonneg x]
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num <;> ring
  have hprod := hsquare.mul (hasDerivAt_arccos_inv hU hx)
  convert hprod using 1
  rw [squareDifferential_eq_integrand]
  unfold integrand residual
  field_simp [hx0, Real.sqrt_ne_zero'.mpr hrad] <;> ring

private theorem hasDerivAt_sqrt_radicand {x : ℝ} (hrad : 0 < x ^ 2 - 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
      (x / Real.sqrt (x ^ 2 - 1)) x := by
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num <;> ring
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    simpa using hsquare.sub_const 1
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner
  convert h using 1
  field_simp [Real.sqrt_ne_zero'.mpr hrad] <;> ring

private theorem hasDerivAt_primitive {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : HasDerivAt primitive (integrand x) x := by
  rcases hU with hU | hU
  · subst U
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hrad : 0 < x ^ 2 - 1 := admissible_radicand_pos (Or.inl rfl) hx
    have hp := (hasDerivAt_mainTerm (Or.inl rfl) hx).const_mul (1 / 2 : ℝ)
    have hs := (hasDerivAt_sqrt_radicand hrad).const_mul (1 / 2 : ℝ)
    have hd : HasDerivAt
        (fun y : ℝ => (1 / 2 : ℝ) * (y ^ 2 * Real.arccos (1 / y)) -
          (1 / 2 : ℝ) * Real.sqrt (y ^ 2 - 1))
        (integrand x) x := by
      convert hp.sub hs using 1
      rw [squareDifferential_eq_integrand]
      simp [residual, abs_of_pos hx0] <;> ring
    apply hasDerivAt_of_eqOn_open isOpen_Ioi hx hd
    intro y hy
    have hy0 : 0 < y := lt_trans zero_lt_one hy
    simp [primitive, SignType.sign, hy0] <;> ring
  · subst U
    have hx0 : x < 0 := lt_trans hx (by norm_num)
    have hrad : 0 < x ^ 2 - 1 := admissible_radicand_pos (Or.inr rfl) hx
    have hp := (hasDerivAt_mainTerm (Or.inr rfl) hx).const_mul (1 / 2 : ℝ)
    have hs := (hasDerivAt_sqrt_radicand hrad).const_mul (1 / 2 : ℝ)
    have hd : HasDerivAt
        (fun y : ℝ => (1 / 2 : ℝ) * (y ^ 2 * Real.arccos (1 / y)) +
          (1 / 2 : ℝ) * Real.sqrt (y ^ 2 - 1))
        (integrand x) x := by
      convert hp.add hs using 1
      rw [squareDifferential_eq_integrand]
      simp [residual, abs_of_neg hx0] <;> ring
    apply hasDerivAt_of_eqOn_open isOpen_Iio hx hd
    intro y hy
    have hy0 : y < 0 := lt_trans hy (by norm_num)
    have hny : ¬0 < y := not_lt_of_ge (le_of_lt hy0)
    simp [primitive, SignType.sign, hny, hy0] <;> ring

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = HalfFamily U squareDifferential := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ U, HasDerivAt F (integrand x) x) ↔
      ∃ A, (∀ x ∈ U, HasDerivAt A (squareDifferential x) x) ∧
        ∀ x ∈ U, F x = (1 / 2 : ℝ) * A x
  constructor
  · intro hF
    refine ⟨fun y => 2 * F y, ?_, ?_⟩
    · intro x hx
      simpa [squareDifferential_eq_integrand] using (hF x hx).const_mul 2
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have hd : HasDerivAt (fun y => (1 / 2 : ℝ) * A y) (integrand x) x := by
      convert (hA x hx).const_mul (1 / 2 : ℝ) using 1
      rw [squareDifferential_eq_integrand]
      ring
    exact hasDerivAt_of_eqOn_open (admissible_open hU) hx hd hFA
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) :
    HalfFamily U squareDifferential = ByPartsFamily U := by
  apply Set.ext
  intro F
  change
    (∃ A, (∀ x ∈ U, HasDerivAt A (squareDifferential x) x) ∧
      ∀ x ∈ U, F x = (1 / 2 : ℝ) * A x) ↔
    ∃ A, (∀ x ∈ U, HasDerivAt A (residual x) x) ∧
      ∀ x ∈ U,
        F x = (1 / 2 : ℝ) * x ^ 2 * Real.arccos (1 / x) -
          (1 / 2 : ℝ) * A x
  constructor
  · rintro ⟨A, hA, hFA⟩
    refine ⟨fun y => y ^ 2 * Real.arccos (1 / y) - A y, ?_, ?_⟩
    · intro x hx
      simpa using (hasDerivAt_mainTerm hU hx).sub (hA x hx)
    · intro x hx
      rw [hFA x hx]
      ring
  · rintro ⟨A, hA, hFA⟩
    refine ⟨fun y => y ^ 2 * Real.arccos (1 / y) - A y, ?_, ?_⟩
    · intro x hx
      simpa using (hasDerivAt_mainTerm hU hx).sub (hA x hx)
    · intro x hx
      rw [hFA x hx]
      ring
theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = ByPartsFamily U := by
  exact (gap1 U hU).trans (gap2 U hU)
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ U, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ U, F x = primitive x + C
  constructor
  · intro hF
    rcases hU with hU | hU
    · subst U
      let D : ℝ → ℝ := fun y => F y - primitive y
      have hD : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt D 0 x := by
        intro x hx
        simpa [D] using (hF x hx).sub (hasDerivAt_primitive (Or.inl rfl) hx)
      have hdiff : DifferentiableOn ℝ D (Set.Ioi (1 : ℝ)) := by
        intro x hx
        exact (hD x hx).differentiableAt.differentiableWithinAt
      have hzero : ∀ x ∈ Set.Ioi (1 : ℝ), deriv D x = 0 := by
        intro x hx
        exact (hD x hx).deriv
      refine ⟨D 2, ?_⟩
      intro x hx
      have hc := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hzero hx (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num)
      dsimp [D] at hc ⊢
      linarith
    · subst U
      let D : ℝ → ℝ := fun y => F y - primitive y
      have hD : ∀ x ∈ Set.Iio (-1 : ℝ), HasDerivAt D 0 x := by
        intro x hx
        simpa [D] using (hF x hx).sub (hasDerivAt_primitive (Or.inr rfl) hx)
      have hdiff : DifferentiableOn ℝ D (Set.Iio (-1 : ℝ)) := by
        intro x hx
        exact (hD x hx).differentiableAt.differentiableWithinAt
      have hzero : ∀ x ∈ Set.Iio (-1 : ℝ), deriv D x = 0 := by
        intro x hx
        exact (hD x hx).deriv
      refine ⟨D (-2), ?_⟩
      intro x hx
      have hc := isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
        hdiff hzero hx (show (-2 : ℝ) ∈ Set.Iio (-1) by norm_num)
      dsimp [D] at hc ⊢
      linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hd : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (hasDerivAt_primitive hU hx).add_const C
    exact hasDerivAt_of_eqOn_open (admissible_open hU) hx hd hFC

end
end ProofGap.Exercise2109
