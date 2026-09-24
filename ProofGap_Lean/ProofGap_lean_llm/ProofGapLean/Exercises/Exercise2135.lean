import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2135
noncomputable section

def domain : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) := 1 / (x * Real.sqrt (1 + x ^ 3 + x ^ 6))
def normalized (x : ℝ) :=
  1 / (x ^ 4 * Real.sqrt (x ^ (-6 : ℤ) + x ^ (-3 : ℤ) + 1))
def u (x : ℝ) := x ^ (-3 : ℤ) + (1 / 2 : ℝ)
def uDifferential (x : ℝ) :=
  deriv u x / Real.sqrt (u x ^ 2 + (3 / 4 : ℝ))
def primitiveU (x : ℝ) :=
  -(1 / 3 : ℝ) *
    Real.log |x ^ (-3 : ℤ) + (1 / 2 : ℝ) +
      Real.sqrt (x ^ (-6 : ℤ) + x ^ (-3 : ℤ) + 1)|
def primitive (x : ℝ) :=
  -(1 / 3 : ℝ) *
    Real.log |(2 + x ^ 3 + 2 * Real.sqrt (x ^ 6 + x ^ 3 + 1)) / x ^ 3|

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def MinusThirdFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family uDifferential,
    ∀ x ∈ domain, F x = -(1 / 3 : ℝ) * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private lemma normalized_eq_integrand (x : ℝ) (hx : 0 < x) :
    normalized x = integrand x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hrad :
      x ^ (-6 : ℤ) + x ^ (-3 : ℤ) + 1 =
        (1 + x ^ 3 + x ^ 6) / x ^ 6 := by
    simp [zpow_neg]
    field_simp [hx0] <;> ring
  have hsqrtpow : Real.sqrt (x ^ 6) = x ^ 3 := by
    have hp : x ^ 6 = (x ^ 3) ^ 2 := by ring
    rw [hp, Real.sqrt_sq (le_of_lt (pow_pos hx 3))]
  simp only [normalized, integrand]
  rw [hrad, Real.sqrt_div (by positivity), hsqrtpow]
  field_simp [hx0] <;> ring

private lemma hasDerivAt_u (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt u (-3 / x ^ 4) x := by
  have h := (((hasDerivAt_id x).pow 3).inv (pow_ne_zero 3 hx)).add_const (1 / 2 : ℝ)
  convert h using 1 <;>
    simp [u, zpow_neg] <;>
    field_simp [hx] <;>
    ring

private lemma radicand_eq (x : ℝ) :
    x ^ (-6 : ℤ) + x ^ (-3 : ℤ) + 1 =
      u x ^ 2 + (3 / 4 : ℝ) := by
  by_cases hx : x = 0
  · subst x
    norm_num [u, zpow_neg]
  · unfold u
    simp [zpow_neg]
    field_simp [hx] <;> ring

private lemma uDifferential_eq (x : ℝ) (hx : 0 < x) :
    uDifferential x = -3 * normalized x := by
  rw [uDifferential, (hasDerivAt_u x (ne_of_gt hx)).deriv]
  rw [← radicand_eq x]
  simp only [normalized]
  ring

private lemma hasDerivAt_of_eq_on_Ioi
    {F G : ℝ → ℝ} {x d : ℝ} (hx : 0 < x)
    (hFG : ∀ y ∈ domain, F y = G y) (hG : HasDerivAt G d x) :
    HasDerivAt F d x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact hFG y hy

private def auxiliaryW (x : ℝ) :=
  u x + Real.sqrt (u x ^ 2 + (3 / 4 : ℝ))

private lemma auxiliaryW_pos (x : ℝ) : 0 < auxiliaryW x := by
  have hbase : 0 < u x ^ 2 + (3 / 4 : ℝ) := by
    nlinarith [sq_nonneg (u x)]
  have hspos : 0 < Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) :=
    Real.sqrt_pos.2 hbase
  have hs_sq :
      Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) ^ 2 =
        u x ^ 2 + (3 / 4 : ℝ) :=
    Real.sq_sqrt (le_of_lt hbase)
  by_cases hq : 0 < u x
  · unfold auxiliaryW
    linarith
  · have hden : 0 < Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) - u x := by
      linarith
    have hp :
        0 < (u x + Real.sqrt (u x ^ 2 + (3 / 4 : ℝ))) *
          (Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) - u x) := by
      nlinarith
    unfold auxiliaryW
    exact pos_of_mul_pos_left hp (le_of_lt hden)

private lemma hasDerivAt_log_auxiliaryW (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => Real.log |auxiliaryW y|)
      ((-3 / x ^ 4) / Real.sqrt (u x ^ 2 + (3 / 4 : ℝ))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hu := hasDerivAt_u x hx0
  have hbase : 0 < u x ^ 2 + (3 / 4 : ℝ) := by
    nlinarith [sq_nonneg (u x)]
  have hspos : 0 < Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) :=
    Real.sqrt_pos.2 hbase
  have hinner := (hu.pow 2).add_const (3 / 4 : ℝ)
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hbase)).comp x hinner
  have hw : HasDerivAt auxiliaryW
      ((-3 / x ^ 4) +
        (Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)))⁻¹ / 2 *
          ((-3 / x ^ 4) * 2 * u x)) x := by
    convert hu.add hsqrt using 1 <;>
      simp [auxiliaryW, Function.comp_def] <;>
      ring
  have hwpos := auxiliaryW_pos x
  have hw0 : auxiliaryW x ≠ 0 := ne_of_gt hwpos
  have hs0 : Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) ≠ 0 := ne_of_gt hspos
  have hraw := (Real.hasDerivAt_log hw0).comp x hw
  have hstep :
      (-3 / x ^ 4) +
          (Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)))⁻¹ / 2 *
            ((-3 / x ^ 4) * 2 * u x) =
        auxiliaryW x *
          ((-3 / x ^ 4) /
            Real.sqrt (u x ^ 2 + (3 / 4 : ℝ))) := by
    unfold auxiliaryW
    field_simp [hs0, hx0] <;> ring
  have hderiv :
      (auxiliaryW x)⁻¹ *
          ((-3 / x ^ 4) +
            (Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)))⁻¹ / 2 *
              ((-3 / x ^ 4) * 2 * u x)) =
        (-3 / x ^ 4) / Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) := by
    rw [hstep]
    calc
      (auxiliaryW x)⁻¹ *
          (auxiliaryW x *
            ((-3 / x ^ 4) /
              Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)))) =
        ((auxiliaryW x)⁻¹ * auxiliaryW x) *
          ((-3 / x ^ 4) /
            Real.sqrt (u x ^ 2 + (3 / 4 : ℝ))) := by
        ring
      _ = (-3 / x ^ 4) / Real.sqrt (u x ^ 2 + (3 / 4 : ℝ)) := by
        simp [hw0]
  have hlog : HasDerivAt (Real.log ∘ auxiliaryW)
      ((-3 / x ^ 4) / Real.sqrt (u x ^ 2 + (3 / 4 : ℝ))) x :=
    hderiv ▸ hraw
  have heq :
      (fun y => Real.log |auxiliaryW y|) = Real.log ∘ auxiliaryW := by
    funext y
    simp [Function.comp_apply, abs_of_pos (auxiliaryW_pos y)]
  exact (heq.symm ▸ hlog)

private lemma primitiveU_eq_log_auxiliaryW (x : ℝ) :
    primitiveU x = -(1 / 3 : ℝ) * Real.log |auxiliaryW x| := by
  unfold primitiveU
  rw [radicand_eq x]
  rfl

private lemma primitiveU_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt primitiveU (normalized x) x := by
  have heq : primitiveU = fun y => -(1 / 3 : ℝ) * Real.log |auxiliaryW y| := by
    funext y
    exact primitiveU_eq_log_auxiliaryW y
  rw [heq]
  have h := (hasDerivAt_log_auxiliaryW x hx).const_mul (-(1 / 3 : ℝ))
  convert h using 1
  rw [← radicand_eq x]
  simp only [normalized]
  ring

private lemma primitive_argument_eq (x : ℝ) (hx : 0 < x) :
    (2 + x ^ 3 + 2 * Real.sqrt (x ^ 6 + x ^ 3 + 1)) / x ^ 3 =
      2 * auxiliaryW x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hrad :
      x ^ (-6 : ℤ) + x ^ (-3 : ℤ) + 1 =
        (x ^ 6 + x ^ 3 + 1) / x ^ 6 := by
    simp [zpow_neg]
    field_simp [hx0] <;> ring
  have hsqrtpow : Real.sqrt (x ^ 6) = x ^ 3 := by
    have hp : x ^ 6 = (x ^ 3) ^ 2 := by ring
    rw [hp, Real.sqrt_sq (le_of_lt (pow_pos hx 3))]
  have hroot :
      Real.sqrt (x ^ (-6 : ℤ) + x ^ (-3 : ℤ) + 1) =
        Real.sqrt (x ^ 6 + x ^ 3 + 1) / x ^ 3 := by
    rw [hrad, Real.sqrt_div (by positivity), hsqrtpow]
  unfold auxiliaryW
  rw [← radicand_eq x, hroot]
  unfold u
  simp [zpow_neg]
  field_simp [hx0] <;> ring

private lemma primitiveU_eq_primitive (x : ℝ) (hx : 0 < x) :
    primitiveU x = primitive x + (1 / 3 : ℝ) * Real.log 2 := by
  have hwpos := auxiliaryW_pos x
  have harg := primitive_argument_eq x hx
  rw [primitiveU_eq_log_auxiliaryW x]
  unfold primitive
  rw [harg, abs_of_pos hwpos,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hwpos)]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hwpos)]
  ring

theorem gap1 : Family integrand = Family normalized := by
  ext F
  constructor
  · intro hF
    intro x hx
    change 0 < x at hx
    simpa [normalized_eq_integrand x hx] using hF x hx
  · intro hF
    intro x hx
    change 0 < x at hx
    simpa [normalized_eq_integrand x hx] using hF x hx
theorem gap2 : Family normalized = MinusThirdFamily := by
  ext F
  simp only [Family, MinusThirdFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun x => -3 * F x, ?_, ?_⟩
    · intro x hx
      change 0 < x at hx
      have h := (hF x hx).const_mul (-3)
      simpa [uDifferential_eq x hx] using h
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    change 0 < x at hx
    have h := (hA x hx).const_mul (-(1 / 3 : ℝ))
    have hs : HasDerivAt (fun y => -(1 / 3 : ℝ) * A y) (normalized x) x := by
      convert h using 1
      rw [uDifferential_eq x hx]
      ring
    exact hasDerivAt_of_eq_on_Ioi hx hFA hs
theorem gap3 : Family integrand = MinusThirdFamily := by
  rw [gap1, gap2]
theorem gap4 : Family integrand = Translates primitiveU := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 1 - primitiveU 1, ?_⟩
    intro x hx
    change 0 < x at hx
    let H : ℝ → ℝ := fun z => F z - primitiveU z
    have hdiff : DifferentiableOn ℝ H (Set.Ioi (0 : ℝ)) := by
      intro y hy
      have hF' := hF y hy
      have hP := primitiveU_hasDerivAt y hy
      exact (hF'.sub hP).differentiableAt.differentiableWithinAt
    have hderiv : Set.EqOn (deriv H) 0 (Set.Ioi (0 : ℝ)) := by
      intro y hy
      have hF' := hF y hy
      have hP := primitiveU_hasDerivAt y hy
      have hd : HasDerivAt (fun z => F z - primitiveU z) 0 y := by
        convert hF'.sub hP using 1
        rw [normalized_eq_integrand y hy]
        ring
      simpa [H] using hd.deriv
    have hopen : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have hpre : IsPreconnected (Set.Ioi (0 : ℝ)) := isPreconnected_Ioi
    have hc := hopen.is_const_of_deriv_eq_zero hpre hdiff hderiv hx
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    change 0 < x at hx
    have hp := (primitiveU_hasDerivAt x hx).add_const C
    have hpI : HasDerivAt (fun y => primitiveU y + C) (integrand x) x := by
      convert hp using 1
      exact (normalized_eq_integrand x hx).symm
    exact hasDerivAt_of_eq_on_Ioi hx hC hpI
theorem gap5 : Translates primitiveU = Translates primitive := by
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 3 : ℝ) * Real.log 2 + C, ?_⟩
    intro x hx
    change 0 < x at hx
    rw [hC x hx, primitiveU_eq_primitive x hx]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - (1 / 3 : ℝ) * Real.log 2, ?_⟩
    intro x hx
    change 0 < x at hx
    rw [hC x hx, primitiveU_eq_primitive x hx]
    ring
theorem gap6 : Family integrand = Translates primitive := by
  rw [gap4, gap5]

end
end ProofGap.Exercise2135
