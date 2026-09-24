import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2062
noncomputable section

def radicand (x : ℝ) := 2 + Real.sin (2 * x)
def integrand (x : ℝ) := Real.sin x / Real.sqrt (radicand x)
def cosMode (x : ℝ) :=
  Real.cos x / Real.sqrt (3 - (Real.sin x - Real.cos x) ^ 2)
def differenceMode (x : ℝ) :=
  deriv (fun y => Real.sin y - Real.cos y) x /
    Real.sqrt (3 - (Real.sin x - Real.cos x) ^ 2)
def logTerm (x : ℝ) :=
  Real.log (Real.sin x + Real.cos x + Real.sqrt (radicand x))
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) * Real.arcsin ((Real.sin x - Real.cos x) / Real.sqrt 3) -
    (1 / 2 : ℝ) * logTerm x
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def Step5 :=
  {F : ℝ → ℝ | ∃ G ∈ Family cosMode, ∃ C, ∀ x, F x = G x - logTerm x + C}
def Step6 :=
  {F : ℝ → ℝ | ∃ G ∈ Family integrand, ∃ H ∈ Family differenceMode,
    ∃ C, ∀ x, F x = -G x + H x - logTerm x + C}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private lemma radicand_eq_add_sq (x : ℝ) :
    radicand x = 1 + (Real.sin x + Real.cos x) ^ 2 := by
  unfold radicand
  rw [Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma radicand_eq_difference (x : ℝ) :
    radicand x = 3 - (Real.sin x - Real.cos x) ^ 2 := by
  rw [radicand_eq_add_sq]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma radicand_pos (x : ℝ) : 0 < radicand x := by
  rw [radicand_eq_add_sq]
  nlinarith [sq_nonneg (Real.sin x + Real.cos x)]

private lemma sqrt_radicand_pos (x : ℝ) :
    0 < Real.sqrt (radicand x) :=
  Real.sqrt_pos.2 (radicand_pos x)

private lemma hasDerivAt_sum (x : ℝ) :
    HasDerivAt (fun y => Real.sin y + Real.cos y)
      (Real.cos x - Real.sin x) x := by
  convert (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x) using 1 <;> ring

private lemma hasDerivAt_difference (x : ℝ) :
    HasDerivAt (fun y => Real.sin y - Real.cos y)
      (Real.sin x + Real.cos x) x := by
  convert (Real.hasDerivAt_sin x).sub (Real.hasDerivAt_cos x) using 1 <;> ring

private lemma hasDerivAt_radicand (x : ℝ) :
    HasDerivAt radicand (2 * Real.cos (2 * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have hsin := (Real.hasDerivAt_sin (2 * x)).comp x hinner
  convert hsin.const_add 2 using 1 <;> simp [radicand, mul_comm]

private lemma hasDerivAt_sqrt_radicand (x : ℝ) :
    HasDerivAt (fun y => Real.sqrt (radicand y))
      (Real.cos (2 * x) / Real.sqrt (radicand x)) x := by
  have h := (Real.hasDerivAt_sqrt (ne_of_gt (radicand_pos x))).comp x
    (hasDerivAt_radicand x)
  convert h using 1
  field_simp [ne_of_gt (sqrt_radicand_pos x)] <;> ring

private lemma cos_two_factor (x : ℝ) :
    Real.cos (2 * x) =
      (Real.sin x + Real.cos x) * (Real.cos x - Real.sin x) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma log_argument_pos (x : ℝ) :
    0 < Real.sin x + Real.cos x + Real.sqrt (radicand x) := by
  let u := Real.sin x + Real.cos x
  let q := Real.sqrt (radicand x)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = radicand x := Real.sq_sqrt (le_of_lt (radicand_pos x))
  have hr : radicand x = 1 + u ^ 2 := by
    dsimp [u]
    exact radicand_eq_add_sq x
  by_contra hn
  have hle : q ≤ -u := by
    dsimp [u, q] at hn ⊢
    linarith
  have hneg : 0 ≤ -u := le_trans hq hle
  have hm : q * q ≤ (-u) * (-u) := mul_le_mul hle hle hq hneg
  nlinarith

private lemma hasDerivAt_logTerm (x : ℝ) :
    HasDerivAt logTerm
      ((Real.cos x - Real.sin x) / Real.sqrt (radicand x)) x := by
  have harg := (hasDerivAt_sum x).add (hasDerivAt_sqrt_radicand x)
  have h := (Real.hasDerivAt_log (ne_of_gt (log_argument_pos x))).comp x harg
  unfold logTerm
  convert h using 1
  rw [cos_two_factor]
  field_simp [ne_of_gt (sqrt_radicand_pos x), ne_of_gt (log_argument_pos x)]
  <;> ring

private lemma integrand_add_log_deriv_eq_cosMode (x : ℝ) :
    integrand x +
      (Real.cos x - Real.sin x) / Real.sqrt (radicand x) = cosMode x := by
  unfold integrand cosMode
  rw [← radicand_eq_difference x]
  ring

private lemma cosMode_sub_log_deriv_eq_integrand (x : ℝ) :
    cosMode x -
      (Real.cos x - Real.sin x) / Real.sqrt (radicand x) = integrand x := by
  unfold integrand cosMode
  rw [← radicand_eq_difference x]
  ring

private lemma differenceMode_eq (x : ℝ) :
    differenceMode x =
      (Real.sin x + Real.cos x) / Real.sqrt (radicand x) := by
  unfold differenceMode
  rw [(hasDerivAt_difference x).deriv]
  rw [← radicand_eq_difference x]

private lemma two_integrand_add_log_deriv_eq_differenceMode (x : ℝ) :
    2 * integrand x +
      (Real.cos x - Real.sin x) / Real.sqrt (radicand x) = differenceMode x := by
  rw [differenceMode_eq]
  unfold integrand
  ring

private lemma neg_integrand_add_differenceMode_sub_log_deriv_eq_integrand (x : ℝ) :
    -integrand x + differenceMode x -
      (Real.cos x - Real.sin x) / Real.sqrt (radicand x) = integrand x := by
  rw [differenceMode_eq]
  unfold integrand
  ring

private lemma difference_sq_lt_three (x : ℝ) :
    (Real.sin x - Real.cos x) ^ 2 < 3 := by
  have h := radicand_pos x
  rw [radicand_eq_difference] at h
  linarith

private lemma scaled_difference_mem_Ioo (x : ℝ) :
    (Real.sin x - Real.cos x) / Real.sqrt 3 ∈ Set.Ioo (-1 : ℝ) 1 := by
  let v := Real.sin x - Real.cos x
  let q := Real.sqrt (3 : ℝ)
  have hq : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq2 : q ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hv2 : v ^ 2 < 3 := by
    dsimp [v]
    exact difference_sq_lt_three x
  have hvup : v < q := by
    by_contra hn
    have hle : q ≤ v := le_of_not_gt hn
    have hv0 : 0 ≤ v := le_trans (le_of_lt hq) hle
    have hm : q * q ≤ v * v :=
      mul_le_mul hle hle (le_of_lt hq) hv0
    nlinarith
  have hvlow : -q < v := by
    by_contra hn
    have hle : v ≤ -q := le_of_not_gt hn
    have hcomp : q ≤ -v := by linarith
    have hnv0 : 0 ≤ -v := le_trans (le_of_lt hq) hcomp
    have hm : q * q ≤ (-v) * (-v) :=
      mul_le_mul hcomp hcomp (le_of_lt hq) hnv0
    nlinarith
  constructor
  · apply (lt_div_iff₀ hq).2
    dsimp [v, q] at hvlow ⊢
    linarith
  · apply (div_lt_iff₀ hq).2
    dsimp [v, q] at hvup ⊢
    linarith

private lemma sqrt_one_sub_scaled_sq (x : ℝ) :
    Real.sqrt
        (1 - ((Real.sin x - Real.cos x) / Real.sqrt 3) ^ 2) =
      Real.sqrt (radicand x) / Real.sqrt 3 := by
  let v := Real.sin x - Real.cos x
  let q := Real.sqrt (3 : ℝ)
  have hq : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq2 : q ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hinside : 1 - (v / q) ^ 2 = radicand x / 3 := by
    rw [radicand_eq_difference]
    dsimp [v]
    field_simp [ne_of_gt hq]
    nlinarith
  have hi : 0 ≤ 1 - (v / q) ^ 2 := by
    rw [hinside]
    exact div_nonneg (le_of_lt (radicand_pos x)) (by norm_num)
  have ha2 := Real.sq_sqrt hi
  have hb2 : (Real.sqrt (radicand x) / q) ^ 2 = radicand x / 3 := by
    have hr2 := Real.sq_sqrt (le_of_lt (radicand_pos x))
    field_simp [ne_of_gt hq]
    nlinarith
  have ha0 : 0 ≤ Real.sqrt (1 - (v / q) ^ 2) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ Real.sqrt (radicand x) / q :=
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt hq)
  dsimp [v, q] at hinside ha2 hb2 ha0 hb0 ⊢
  nlinarith

private lemma hasDerivAt_arcsin_part (x : ℝ) :
    HasDerivAt
      (fun y => Real.arcsin
        ((Real.sin y - Real.cos y) / Real.sqrt 3))
      ((Real.sin x + Real.cos x) / Real.sqrt (radicand x)) x := by
  have hinner := (hasDerivAt_difference x).div_const (Real.sqrt 3)
  have hz := scaled_difference_mem_Ioo x
  have h := (Real.hasDerivAt_arcsin
    (ne_of_gt hz.1) (ne_of_lt hz.2)).comp x hinner
  convert h using 1
  rw [sqrt_one_sub_scaled_sq]
  field_simp [ne_of_gt (sqrt_radicand_pos x),
    ne_of_gt (Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num))]
  <;> ring

private lemma hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h := ((hasDerivAt_arcsin_part x).const_mul (1 / 2 : ℝ)).sub
    ((hasDerivAt_logTerm x).const_mul (1 / 2 : ℝ))
  unfold primitive
  convert h using 1
  unfold integrand
  ring

theorem gap1 : ∀ x, 2 + Real.sin (2 * x) =
    1 + (Real.sin x + Real.cos x) ^ 2 := by
  exact radicand_eq_add_sq
theorem gap2 : ∀ x, 1 + (Real.sin x + Real.cos x) ^ 2 =
    3 - (Real.sin x - Real.cos x) ^ 2 := by
  intro x
  rw [← radicand_eq_add_sq x]
  exact radicand_eq_difference x
theorem gap3 : ∀ x, 2 + Real.sin (2 * x) =
    3 - (Real.sin x - Real.cos x) ^ 2 := by
  exact radicand_eq_difference
theorem gap4 : Family integrand =
    Family (fun x => (Real.cos x - (Real.cos x - Real.sin x)) /
      Real.sqrt (1 + (Real.sin x + Real.cos x) ^ 2)) := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∀ x, HasDerivAt F
      ((Real.cos x - (Real.cos x - Real.sin x)) /
        Real.sqrt (1 + (Real.sin x + Real.cos x) ^ 2)) x
  constructor
  · intro h x
    simpa [integrand, radicand_eq_add_sq x] using h x
  · intro h x
    simpa [integrand, radicand_eq_add_sq x] using h x
theorem gap5 : Family integrand = Step5 := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ G, (∀ x, HasDerivAt G (cosMode x) x) ∧
      ∃ C, ∀ x, F x = G x - logTerm x + C
  constructor
  · intro hF
    refine ⟨fun x => F x + logTerm x, ?_, 0, ?_⟩
    · intro x
      have hx := (hF x).add (hasDerivAt_logTerm x)
      convert hx using 1
      exact (integrand_add_log_deriv_eq_cosMode x).symm
    · intro x
      ring
  · rintro ⟨G, hG, C, hEq⟩
    have hfun : F = fun x => G x - logTerm x + C := funext hEq
    rw [hfun]
    intro x
    have hx := ((hG x).sub (hasDerivAt_logTerm x)).add_const C
    convert hx using 1
    exact (cosMode_sub_log_deriv_eq_integrand x).symm
theorem gap6 : Family integrand = Step6 := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ G, (∀ x, HasDerivAt G (integrand x) x) ∧
      ∃ H, (∀ x, HasDerivAt H (differenceMode x) x) ∧
        ∃ C, ∀ x, F x = -G x + H x - logTerm x + C
  constructor
  · intro hF
    refine ⟨F, hF, fun x => 2 * F x + logTerm x, ?_, 0, ?_⟩
    · intro x
      have hx := ((hF x).const_mul 2).add (hasDerivAt_logTerm x)
      convert hx using 1
      exact (two_integrand_add_log_deriv_eq_differenceMode x).symm
    · intro x
      ring
  · rintro ⟨G, hG, H, hH, C, hEq⟩
    have hfun : F = fun x => -G x + H x - logTerm x + C := funext hEq
    rw [hfun]
    intro x
    have hx := (((hG x).neg.add (hH x)).sub
      (hasDerivAt_logTerm x)).add_const C
    convert hx using 1
    exact (neg_integrand_add_differenceMode_sub_log_deriv_eq_integrand x).symm
theorem gap7 : Family integrand = Translates primitive := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      dsimp [D]
      convert (hF x).sub (hasDerivAt_primitive x) using 1 <;> ring
    have hdiff : Differentiable ℝ D := fun x => (hD x).differentiableAt
    have hderiv : ∀ x, deriv D x = 0 := fun x => (hD x).deriv
    refine ⟨D 0, ?_⟩
    intro x
    have hc : D x = D 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    dsimp [D] at hc ⊢
    linarith
  · rintro ⟨C, hEq⟩
    have hfun : F = fun x => primitive x + C := funext hEq
    rw [hfun]
    intro x
    simpa using (hasDerivAt_primitive x).add_const C

end
end ProofGap.Exercise2062
