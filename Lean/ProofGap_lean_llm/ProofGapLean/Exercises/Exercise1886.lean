import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1886

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x ^ 6 + 1)
def qPlus (x : ℝ) : ℝ := x ^ 2 + x * Real.sqrt 3 + 1
def qMinus (x : ℝ) : ℝ := x ^ 2 - x * Real.sqrt 3 + 1
def primitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.arctan x +
    (1 / 6 : ℝ) * Real.arctan (x ^ 3) +
    1 / (4 * Real.sqrt 3) * Real.log (qPlus x / qMinus x)
def primitiveAlt (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.arctan x +
    (1 / 6 : ℝ) * Real.arctan ((x ^ 2 - 1) / x) +
    1 / (4 * Real.sqrt 3) * Real.log (qPlus x / qMinus x)
def altDomain : Set ℝ := {x | x ≠ 0}
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem qPlus_pos (x : ℝ) : 0 < qPlus x := by
  unfold qPlus
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := sqrt_three_sq
  nlinarith [sq_nonneg (2 * x + Real.sqrt 3)]

private theorem qMinus_pos (x : ℝ) : 0 < qMinus x := by
  unfold qMinus
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := sqrt_three_sq
  nlinarith [sq_nonneg (2 * x - Real.sqrt 3)]

private theorem quartic_pos (x : ℝ) : 0 < x ^ 4 - x ^ 2 + 1 := by
  nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]

private theorem qPlus_mul_qMinus (x : ℝ) :
    qPlus x * qMinus x = x ^ 4 - x ^ 2 + 1 := by
  unfold qPlus qMinus
  calc
    (x ^ 2 + x * Real.sqrt 3 + 1) *
        (x ^ 2 - x * Real.sqrt 3 + 1) =
      (x ^ 2 + 1) ^ 2 - x ^ 2 * (Real.sqrt 3) ^ 2 := by ring
    _ = x ^ 4 - x ^ 2 + 1 := by rw [sqrt_three_sq]; ring

private theorem log_numerator (x : ℝ) :
    (2 * x + Real.sqrt 3) * qMinus x -
        qPlus x * (2 * x - Real.sqrt 3) =
      2 * Real.sqrt 3 * (1 - x ^ 2) := by
  unfold qPlus qMinus
  ring

private theorem quadratic_numerator (x : ℝ) :
    ((Real.sqrt 3 / 6) * x + 1 / 3) * qMinus x +
        (-(Real.sqrt 3 / 6) * x + 1 / 3) * qPlus x =
      (2 - x ^ 2) / 3 := by
  unfold qPlus qMinus
  field_simp
  ring_nf
  rw [sqrt_three_sq]
  ring

private theorem hasDerivAt_qPlus (x : ℝ) :
    HasDerivAt qPlus (2 * x + Real.sqrt 3) x := by
  unfold qPlus
  convert
    (((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_id x).mul_const (Real.sqrt 3))).add_const 1 using 1 <;>
    simp <;> ring

private theorem hasDerivAt_qMinus (x : ℝ) :
    HasDerivAt qMinus (2 * x - Real.sqrt 3) x := by
  unfold qMinus
  convert
    (((hasDerivAt_id x).pow 2).sub
      ((hasDerivAt_id x).mul_const (Real.sqrt 3))).add_const 1 using 1 <;>
    simp <;> ring

private theorem log_term_derivative_value (x : ℝ) :
    1 / (4 * Real.sqrt 3) *
        ((qPlus x / qMinus x)⁻¹ *
          (((2 * x + Real.sqrt 3) * qMinus x -
              qPlus x * (2 * x - Real.sqrt 3)) / qMinus x ^ 2)) =
      -(x ^ 2 - 1) / (2 * (x ^ 4 - x ^ 2 + 1)) := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have hq : x ^ 4 - x ^ 2 + 1 ≠ 0 := ne_of_gt (quartic_pos x)
  calc
    1 / (4 * Real.sqrt 3) *
          ((qPlus x / qMinus x)⁻¹ *
            (((2 * x + Real.sqrt 3) * qMinus x -
                qPlus x * (2 * x - Real.sqrt 3)) / qMinus x ^ 2)) =
        ((2 * x + Real.sqrt 3) * qMinus x -
            qPlus x * (2 * x - Real.sqrt 3)) /
          (4 * Real.sqrt 3 * (qPlus x * qMinus x)) := by
      field_simp [hs3, hqp, hqm]
    _ = -(x ^ 2 - 1) / (2 * (x ^ 4 - x ^ 2 + 1)) := by
      rw [log_numerator, qPlus_mul_qMinus]
      field_simp [hs3, hq]
      ring

private theorem normalized_log_term_derivative_value (x : ℝ) :
    (Real.sqrt 3)⁻¹ * 4⁻¹ *
        (qMinus x / qPlus x *
          (((2 * x + Real.sqrt 3) * qMinus x -
              qPlus x * (2 * x - Real.sqrt 3)) / qMinus x ^ 2)) =
      -(x ^ 2 - 1) / (2 * (x ^ 4 - x ^ 2 + 1)) := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have hq : x ^ 4 - x ^ 2 + 1 ≠ 0 := ne_of_gt (quartic_pos x)
  calc
    (Real.sqrt 3)⁻¹ * 4⁻¹ *
          (qMinus x / qPlus x *
            (((2 * x + Real.sqrt 3) * qMinus x -
                qPlus x * (2 * x - Real.sqrt 3)) / qMinus x ^ 2)) =
        ((2 * x + Real.sqrt 3) * qMinus x -
            qPlus x * (2 * x - Real.sqrt 3)) /
          (4 * Real.sqrt 3 * (qPlus x * qMinus x)) := by
      field_simp [hs3, hqp, hqm]
    _ = -(x ^ 2 - 1) / (2 * (x ^ 4 - x ^ 2 + 1)) := by
      rw [log_numerator, qPlus_mul_qMinus]
      field_simp [hs3, hq]
      ring

private theorem quadratic_fraction_sum (x : ℝ) :
    ((Real.sqrt 3 / 6) * x + 1 / 3) / qPlus x +
        (-(Real.sqrt 3 / 6) * x + 1 / 3) / qMinus x =
      (2 - x ^ 2) / (3 * (x ^ 4 - x ^ 2 + 1)) := by
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have hq : x ^ 4 - x ^ 2 + 1 ≠ 0 := ne_of_gt (quartic_pos x)
  calc
    ((Real.sqrt 3 / 6) * x + 1 / 3) / qPlus x +
          (-(Real.sqrt 3 / 6) * x + 1 / 3) / qMinus x =
        (((Real.sqrt 3 / 6) * x + 1 / 3) * qMinus x +
          (-(Real.sqrt 3 / 6) * x + 1 / 3) * qPlus x) /
            (qPlus x * qMinus x) := by
      field_simp [hqp, hqm]
    _ = (2 - x ^ 2) / (3 * (x ^ 4 - x ^ 2 + 1)) := by
      rw [quadratic_numerator, qPlus_mul_qMinus]
      field_simp [hq]

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have ha1 : 1 + x ^ 2 ≠ 0 := by positivity
  have ha3 : 1 + (x ^ 3) ^ 2 ≠ 0 := by positivity
  have hi : x ^ 6 + 1 ≠ 0 := by positivity
  have hratio := (hasDerivAt_qPlus x).div (hasDerivAt_qMinus x) hqm
  have hlog := (Real.hasDerivAt_log (div_ne_zero hqp hqm)).comp x hratio
  have hcube := (hasDerivAt_id x).pow 3
  have hatan := Real.hasDerivAt_arctan x
  have hatanCube := (Real.hasDerivAt_arctan (x ^ 3)).comp x hcube
  have h :=
    ((hatan.const_mul (1 / 2 : ℝ)).add
      (hatanCube.const_mul (1 / 6 : ℝ))).add
      (hlog.const_mul (1 / (4 * Real.sqrt 3)))
  convert h using 1
  simp
  rw [normalized_log_term_derivative_value]
  unfold integrand
  have hq' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    nlinarith [quartic_pos x]
  rw [show x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 by ring]
  field_simp [ha1, ha3, hi, hq']
  ring

private theorem hasDerivAt_primitiveAlt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt primitiveAlt (integrand x) x := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have ha1 : 1 + x ^ 2 ≠ 0 := by positivity
  have hargDen : 1 + ((x ^ 2 - 1) / x) ^ 2 ≠ 0 := by positivity
  have hi : x ^ 6 + 1 ≠ 0 := by positivity
  have hratio := (hasDerivAt_qPlus x).div (hasDerivAt_qMinus x) hqm
  have hlog := (Real.hasDerivAt_log (div_ne_zero hqp hqm)).comp x hratio
  have hnum := ((hasDerivAt_id x).pow 2).sub_const 1
  have harg := hnum.div (hasDerivAt_id x) hx
  have hatanArg := (Real.hasDerivAt_arctan _).comp x harg
  have hatan := Real.hasDerivAt_arctan x
  have h :=
    ((hatan.const_mul (1 / 3 : ℝ)).add
      (hatanArg.const_mul (1 / 6 : ℝ))).add
      (hlog.const_mul (1 / (4 * Real.sqrt 3)))
  convert h using 1
  simp
  rw [normalized_log_term_derivative_value]
  unfold integrand
  have hq' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    nlinarith [quartic_pos x]
  rw [show x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 by ring]
  field_simp [hx, ha1, hargDen, hi, hq']
  ring

private theorem family_eq_translates_of_hasDeriv
    (P f : ℝ → ℝ) (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hP : ∀ x ∈ s, HasDerivAt P (f x) x) :
    Family f s = Translates P s := by
  ext F
  change IsAntiderivativeOn F f s ↔ ∃ C, ∀ x ∈ s, F x = P x + C
  constructor
  · intro hF
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hz : ∀ x ∈ s, HasDerivAt (fun y => F y - P y) 0 x := by
        intro x hx
        convert (hF x hx).sub (hP x hx) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ (fun y => F y - P y) s := by
        intro x hx
        exact (hz x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s, deriv (fun y => F y - P y) x = 0 := by
        intro x hx
        exact (hz x hx).deriv
      refine ⟨F x0 - P x0, ?_⟩
      intro x hx
      have heq : F x - P x = F x0 - P x0 :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv
          (x := x) (y := x0) hx hx0
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => P y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hP x hx).add_const C).congr_of_eventuallyEq heq

theorem gap1 (x : ℝ) :
    integrand x =
      1 / (3 * (x ^ 2 + 1)) +
        ((Real.sqrt 3 / 6) * x + 1 / 3) / qPlus x +
        (-(Real.sqrt 3 / 6) * x + 1 / 3) / qMinus x := by
  have hx2 : x ^ 2 + 1 ≠ 0 := by positivity
  have hi : x ^ 6 + 1 ≠ 0 := by positivity
  rw [show
    1 / (3 * (x ^ 2 + 1)) +
          ((Real.sqrt 3 / 6) * x + 1 / 3) / qPlus x +
          (-(Real.sqrt 3 / 6) * x + 1 / 3) / qMinus x =
      1 / (3 * (x ^ 2 + 1)) +
        (((Real.sqrt 3 / 6) * x + 1 / 3) / qPlus x +
          (-(Real.sqrt 3 / 6) * x + 1 / 3) / qMinus x) by ring]
  rw [quadratic_fraction_sum]
  unfold integrand
  have hq' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    nlinarith [quartic_pos x]
  rw [show x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 by ring]
  field_simp [hx2, hi, hq']
  ring

theorem gap2 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  apply family_eq_translates_of_hasDeriv primitive integrand Set.univ
      isOpen_univ isPreconnected_univ
  intro x hx
  exact hasDerivAt_primitive x

theorem gap3 (x : ℝ) :
    integrand x =
      (1 / 2 : ℝ) * ((x ^ 4 + 1) / (x ^ 6 + 1)) -
        (1 / 2 : ℝ) * ((x ^ 4 - 1) / (x ^ 6 + 1)) := by
  have hi : x ^ 6 + 1 ≠ 0 := by positivity
  unfold integrand
  field_simp [hi]
  ring

theorem gap4 (x : ℝ) :
    integrand x =
      (1 / 2 : ℝ) * (x ^ 2 / (x ^ 6 + 1)) +
        (1 / 2 : ℝ) * (1 / (1 + x ^ 2)) -
        (1 / 2 : ℝ) * ((x ^ 2 - 1) / (x ^ 4 - x ^ 2 + 1)) := by
  have hi : x ^ 6 + 1 ≠ 0 := by positivity
  have hx2 : 1 + x ^ 2 ≠ 0 := by positivity
  have hq' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    nlinarith [quartic_pos x]
  unfold integrand
  rw [show x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 by ring]
  field_simp [hi, hx2, hq']
  ring

theorem gap5 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  exact hasDerivAt_primitive x

theorem gap6 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  exact gap2

theorem gap7 (x : ℝ) :
    integrand x =
      1 / (3 * (x ^ 2 + 1)) -
        (x ^ 2 - 2) / (3 * (x ^ 4 - x ^ 2 + 1)) := by
  have hi : x ^ 6 + 1 ≠ 0 := by positivity
  have hx2 : x ^ 2 + 1 ≠ 0 := by positivity
  have hq' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    nlinarith [quartic_pos x]
  unfold integrand
  rw [show x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 by ring]
  field_simp [hi, hx2, hq']
  ring

theorem gap8 (x : ℝ) :
    integrand x =
      (1 / 3 : ℝ) * (1 / (x ^ 2 + 1)) -
        (1 / 6 : ℝ) * ((x ^ 2 + 1) / (x ^ 4 - x ^ 2 + 1)) -
        (1 / 6 : ℝ) * ((x ^ 2 - 1) / (x ^ 4 - x ^ 2 + 1)) +
        (1 / 3 : ℝ) * (2 / (x ^ 4 - x ^ 2 + 1)) := by
  have hi : x ^ 6 + 1 ≠ 0 := by positivity
  have hx2 : x ^ 2 + 1 ≠ 0 := by positivity
  have hq' : 1 - x ^ 2 + x ^ 4 ≠ 0 := by
    nlinarith [quartic_pos x]
  unfold integrand
  rw [show x ^ 4 - x ^ 2 + 1 = 1 - x ^ 2 + x ^ 4 by ring]
  field_simp [hi, hx2, hq']
  ring

theorem gap9 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ altDomain) :
    Family integrand s = Translates primitiveAlt s := by
  apply family_eq_translates_of_hasDeriv primitiveAlt integrand s hopen hs
  intro x hx
  exact hasDerivAt_primitiveAlt x (hdom hx)

end

end ProofGap.Exercise1886
