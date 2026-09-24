import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2122
noncomputable section

def domain : Set ℝ := Set.Ioi 0
def tanh (x : ℝ) := Real.sinh x / Real.cosh x
def integrand (x : ℝ) := Real.sqrt (tanh x)
def exponentialForm (x : ℝ) :=
  Real.sqrt ((Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)))
def quotientForm (x : ℝ) :=
  (Real.exp x - Real.exp (-x)) /
    Real.sqrt (Real.exp (2 * x) - Real.exp (-2 * x))
def firstTerm (x : ℝ) :=
  Real.exp (2 * x) / Real.sqrt (Real.exp (4 * x) - 1)
def secondTerm (x : ℝ) :=
  Real.exp (-2 * x) / Real.sqrt (1 - Real.exp (-4 * x))
def uDifferential (x : ℝ) :=
  deriv (fun y : ℝ => Real.exp (2 * y)) x /
    Real.sqrt ((Real.exp (2 * x)) ^ 2 - 1)
def vDifferential (x : ℝ) :=
  deriv (fun y : ℝ => Real.exp (-2 * y)) x /
    Real.sqrt (1 - (Real.exp (-2 * x)) ^ 2)
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) *
      Real.log (Real.exp (2 * x) + Real.sqrt (Real.exp (4 * x) - 1)) +
    (1 / 2 : ℝ) * Real.arcsin (Real.exp (-2 * x))

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def DifferenceFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family firstTerm, ∃ B ∈ Family secondTerm,
    ∀ x ∈ domain, F x = A x - B x}
def HalfSumFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family uDifferential, ∃ B ∈ Family vDifferential,
    ∀ x ∈ domain, F x = (1 / 2 : ℝ) * A x + (1 / 2 : ℝ) * B x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem family_congr_on {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ domain, f x = g x) : Family f = Family g := by
  ext F
  constructor <;> intro hF <;> intro x <;> intro hx
  · simpa [hfg x hx] using hF x hx
  · simpa [hfg x hx] using hF x hx

private theorem integrand_exponential (x : ℝ) (hx : x ∈ domain) :
    integrand x = exponentialForm x := by
  unfold integrand exponentialForm tanh
  congr 1
  have hsum : Real.exp x + Real.exp (-x) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos x) (Real.exp_pos (-x)))
  rw [Real.sinh_eq, Real.cosh_eq]
  field_simp [hsum] <;> ring

private theorem exponential_quotient (x : ℝ) (hx : x ∈ domain) :
    exponentialForm x = quotientForm x := by
  have hx0 : 0 < x := hx
  let ep := Real.exp x
  let em := Real.exp (-x)
  let d := Real.sqrt (Real.exp (2 * x) - Real.exp (-2 * x))
  have hep : 0 < ep := Real.exp_pos x
  have hem : 0 < em := Real.exp_pos (-x)
  have hsub : 0 < ep - em := by
    dsimp [ep, em]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hsum : 0 < ep + em := add_pos hep hem
  have he2 : Real.exp (2 * x) = ep ^ 2 := by
    dsimp [ep]
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring
  have hem2 : Real.exp (-2 * x) = em ^ 2 := by
    dsimp [em]
    rw [show -2 * x = -x + -x by ring, Real.exp_add]
    ring
  have hdarg : 0 < Real.exp (2 * x) - Real.exp (-2 * x) := by
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hd : 0 < d := Real.sqrt_pos.2 hdarg
  have hd_sq : d ^ 2 = Real.exp (2 * x) - Real.exp (-2 * x) :=
    Real.sq_sqrt (le_of_lt hdarg)
  have hdiff : ep ^ 2 - em ^ 2 ≠ 0 := by
    rw [← he2, ← hem2]
    exact ne_of_gt hdarg
  have hrad : 0 ≤ (ep - em) / (ep + em) :=
    div_nonneg (le_of_lt hsub) (le_of_lt hsum)
  have hratio : (ep - em) / (ep + em) = ((ep - em) / d) ^ 2 := by
    rw [div_pow, hd_sq, he2, hem2]
    field_simp [ne_of_gt hsum, hdiff] <;> ring
  unfold exponentialForm quotientForm
  change Real.sqrt ((ep - em) / (ep + em)) = (ep - em) / d
  have hright : 0 ≤ (ep - em) / d :=
    div_nonneg (le_of_lt hsub) (le_of_lt hd)
  rw [hratio, Real.sqrt_sq_eq_abs, abs_of_nonneg hright]

private theorem quotient_first_second (x : ℝ) (hx : x ∈ domain) :
    quotientForm x = firstTerm x - secondTerm x := by
  have hx0 : 0 < x := hx
  let ep := Real.exp x
  let em := Real.exp (-x)
  let d := Real.sqrt (Real.exp (2 * x) - Real.exp (-2 * x))
  let p := Real.sqrt (Real.exp (4 * x) - 1)
  let m := Real.sqrt (1 - Real.exp (-4 * x))
  have hep : 0 < ep := Real.exp_pos x
  have hem : 0 < em := Real.exp_pos (-x)
  have hemul : ep * em = 1 := by
    dsimp [ep, em]
    rw [← Real.exp_add]
    norm_num
  have he2 : Real.exp (2 * x) = ep ^ 2 := by
    dsimp [ep]
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring
  have hem2 : Real.exp (-2 * x) = em ^ 2 := by
    dsimp [em]
    rw [show -2 * x = -x + -x by ring, Real.exp_add]
    ring
  have he4 : Real.exp (4 * x) = ep ^ 4 := by
    dsimp [ep]
    rw [show 4 * x = x + x + x + x by ring]
    simp only [Real.exp_add]
    ring
  have hem4 : Real.exp (-4 * x) = em ^ 4 := by
    dsimp [em]
    rw [show -4 * x = -x + -x + -x + -x by ring]
    simp only [Real.exp_add]
    ring
  have hdarg : 0 < Real.exp (2 * x) - Real.exp (-2 * x) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hparg : 0 < Real.exp (4 * x) - 1 := by
    rw [← Real.exp_zero]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hmarg : 0 < 1 - Real.exp (-4 * x) := by
    rw [← Real.exp_zero]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hd : 0 < d := Real.sqrt_pos.2 hdarg
  have hp : 0 < p := Real.sqrt_pos.2 hparg
  have hm : 0 < m := Real.sqrt_pos.2 hmarg
  have hd_sq : d ^ 2 = Real.exp (2 * x) - Real.exp (-2 * x) :=
    Real.sq_sqrt (le_of_lt hdarg)
  have hp_sq : p ^ 2 = Real.exp (4 * x) - 1 :=
    Real.sq_sqrt (le_of_lt hparg)
  have hm_sq : m ^ 2 = 1 - Real.exp (-4 * x) :=
    Real.sq_sqrt (le_of_lt hmarg)
  have hemul_sq : ep ^ 2 * em ^ 2 = 1 := by
    calc
      ep ^ 2 * em ^ 2 = (ep * em) ^ 2 := by ring
      _ = 1 := by rw [hemul]; norm_num
  have hpd_sq : p ^ 2 = (ep * d) ^ 2 := by
    calc
      p ^ 2 = Real.exp (4 * x) - 1 := hp_sq
      _ = ep ^ 4 - 1 := by rw [he4]
      _ = (ep * d) ^ 2 := by
        rw [mul_pow, hd_sq, he2, hem2]
        nlinarith [hemul_sq]
  have hmd_sq : m ^ 2 = (em * d) ^ 2 := by
    calc
      m ^ 2 = 1 - Real.exp (-4 * x) := hm_sq
      _ = 1 - em ^ 4 := by rw [hem4]
      _ = (em * d) ^ 2 := by
        rw [mul_pow, hd_sq, he2, hem2]
        nlinarith [hemul_sq]
  have hpd : p = ep * d := by
    nlinarith [mul_pos hep hd]
  have hmd : m = em * d := by
    nlinarith [mul_pos hem hd]
  unfold quotientForm firstTerm secondTerm
  change (ep - em) / d = Real.exp (2 * x) / p - Real.exp (-2 * x) / m
  rw [he2, hem2, hpd, hmd]
  field_simp [ne_of_gt hep, ne_of_gt hem, ne_of_gt hd] <;> ring

private theorem uDifferential_firstTerm (x : ℝ) (hx : x ∈ domain) :
    uDifferential x = 2 * firstTerm x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have hexp := (Real.hasDerivAt_exp (2 * x)).comp x hlin
  have hderiv0 := hexp.deriv
  change deriv (fun y : ℝ => Real.exp (2 * y)) x =
    Real.exp (2 * x) * 2 at hderiv0
  have hderiv : deriv (fun y : ℝ => Real.exp (2 * y)) x =
      2 * Real.exp (2 * x) := by
    calc
      deriv (fun y : ℝ => Real.exp (2 * y)) x =
          Real.exp (2 * x) * 2 := hderiv0
      _ = 2 * Real.exp (2 * x) := by ring
  have heq : Real.exp (4 * x) = (Real.exp (2 * x)) ^ 2 := by
    rw [show 4 * x = 2 * x + 2 * x by ring, Real.exp_add]
    ring
  unfold uDifferential firstTerm
  rw [hderiv, heq]
  ring

private theorem vDifferential_secondTerm (x : ℝ) (hx : x ∈ domain) :
    vDifferential x = -2 * secondTerm x := by
  have hlin : HasDerivAt (fun y : ℝ => -2 * y) (-2) x := by
    convert (hasDerivAt_id x).const_mul (-2) using 1 <;> ring
  have hexp := (Real.hasDerivAt_exp (-2 * x)).comp x hlin
  have hderiv : deriv (fun y : ℝ => Real.exp (-2 * y)) x =
      -2 * Real.exp (-2 * x) := by
    convert hexp.deriv using 1 <;> ring
  have heq : Real.exp (-4 * x) = (Real.exp (-2 * x)) ^ 2 := by
    rw [show -4 * x = -2 * x + -2 * x by ring, Real.exp_add]
    ring
  unfold vDifferential secondTerm
  rw [hderiv, heq]
  ring

private theorem integrand_half_components (x : ℝ) (hx : x ∈ domain) :
    integrand x = (1 / 2 : ℝ) * uDifferential x +
      (1 / 2 : ℝ) * vDifferential x := by
  rw [integrand_exponential x hx, exponential_quotient x hx,
    quotient_first_second x hx, uDifferential_firstTerm x hx,
    vDifferential_secondTerm x hx]
  ring

private theorem arc_member (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y : ℝ => Real.arcsin (Real.exp (-2 * y)))
      (vDifferential x) x := by
  have hx0 : 0 < x := hx
  have harg : Real.exp (-2 * x) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [Real.exp_pos (-2 * x)]
    · rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
  have hlin : HasDerivAt (fun y : ℝ => -2 * y) (-2) x := by
    convert (hasDerivAt_id x).const_mul (-2) using 1 <;> ring
  have hi₀ := (Real.hasDerivAt_exp (-2 * x)).comp x hlin
  have hi : HasDerivAt (fun y : ℝ => Real.exp (-2 * y))
      (deriv (fun y : ℝ => Real.exp (-2 * y)) x) x :=
    hi₀.differentiableAt.hasDerivAt
  have h := (Real.hasDerivAt_arcsin
    (ne_of_gt harg.1) (ne_of_lt harg.2)).comp x hi
  convert h using 1
  simp only [vDifferential, div_eq_mul_inv]
  ring

private def logPart (x : ℝ) : ℝ :=
  Real.log (Real.exp (2 * x) +
    Real.sqrt ((Real.exp (2 * x)) ^ 2 - 1))

private theorem log_part_member (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt logPart (uDifferential x) x := by
  have hx0 : 0 < x := hx
  let a : ℝ → ℝ := fun y => Real.exp (2 * y)
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have ha₀raw := (Real.hasDerivAt_exp (2 * x)).comp x hlin
  change HasDerivAt (fun y : ℝ => Real.exp (2 * y))
    (Real.exp (2 * x) * 2) x at ha₀raw
  have ha₀ : HasDerivAt a (2 * a x) x := by
    dsimp [a]
    convert ha₀raw using 1 <;> ring
  have haderiv : deriv a x = 2 * a x := ha₀.deriv
  have ha : HasDerivAt a (deriv a x) x :=
    ha₀.differentiableAt.hasDerivAt
  have ha1 : 1 < a x := by
    dsimp [a]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hspos : 0 < (a x) ^ 2 - 1 := by nlinarith
  have hs := (ha.pow 2).sub_const 1
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hspos)).comp x hs
  have hsum := ha.add hsqrt
  have hroot : 0 < Real.sqrt ((a x) ^ 2 - 1) := Real.sqrt_pos.2 hspos
  have hsumpos : 0 < a x + Real.sqrt ((a x) ^ 2 - 1) :=
    add_pos (lt_trans zero_lt_one ha1) hroot
  have hlog := (Real.hasDerivAt_log (ne_of_gt hsumpos)).comp x hsum
  have hroot_ne : Real.sqrt ((a x) ^ 2 - 1) ≠ 0 := ne_of_gt hroot
  have hsum_ne : a x + Real.sqrt ((a x) ^ 2 - 1) ≠ 0 := ne_of_gt hsumpos
  convert hlog using 1
  unfold uDifferential
  change deriv a x / Real.sqrt ((a x) ^ 2 - 1) = _
  rw [haderiv]
  norm_num
  field_simp [hroot_ne, hsum_ne] <;> ring

private theorem family_eq_translates {f p : ℝ → ℝ}
    (hp : p ∈ Family f) : Family f = Translates p := by
  ext F
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y => F y - p y
    have hdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      simpa [H] using ((hF x hx).sub (hp x hx)).deriv
    refine ⟨H 1, ?_⟩
    intro x hx
    have hc : H x = H 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hzero hx (show (1 : ℝ) ∈ domain by norm_num [domain])
    dsimp [H] at hc ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have h := (hp x hx).const_add C
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simpa [add_comm] using hC y hy

theorem gap1 : Family integrand = Family exponentialForm := by
  exact family_congr_on integrand_exponential
theorem gap2 : Family exponentialForm = Family quotientForm := by
  exact family_congr_on exponential_quotient
theorem gap3 : Family quotientForm = DifferenceFamily := by
  ext F
  constructor
  · intro hF
    let B₀ : ℝ → ℝ := fun y => -(1 / 2 : ℝ) * Real.arcsin (Real.exp (-2 * y))
    have hB₀ : B₀ ∈ Family secondTerm := by
      intro x hx
      have h := (arc_member x hx).const_mul (-(1 / 2 : ℝ))
      convert h using 1
      rw [vDifferential_secondTerm x hx]
      ring
    refine ⟨fun y => F y + B₀ y, ?_, B₀, hB₀, ?_⟩
    · intro x hx
      have h := (hF x hx).add (hB₀ x hx)
      convert h using 1
      rw [quotient_first_second x hx]
      ring
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, hF⟩
    intro x hx
    have h := (hA x hx).sub (hB x hx)
    have hAB : HasDerivAt (fun y => A y - B y)
        (firstTerm x - secondTerm x) x := h
    have hFB : HasDerivAt (fun y => F y)
        (firstTerm x - secondTerm x) x := by
      apply hAB.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [hF y hy]
    convert hFB using 1
    exact quotient_first_second x hx
theorem gap4 : Family integrand = DifferenceFamily := by
  calc
    Family integrand = Family exponentialForm := gap1
    _ = Family quotientForm := gap2
    _ = DifferenceFamily := gap3
theorem gap5 : Family integrand = HalfSumFamily := by
  ext F
  constructor
  · intro hF
    let V₀ : ℝ → ℝ := fun y => Real.arcsin (Real.exp (-2 * y))
    have hV₀ : V₀ ∈ Family vDifferential := arc_member
    refine ⟨fun y => 2 * F y - V₀ y, ?_, V₀, hV₀, ?_⟩
    · intro x hx
      have h := ((hF x hx).const_mul 2).sub (hV₀ x hx)
      convert h using 1
      have hi := integrand_half_components x hx
      linarith
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, hF⟩
    intro x hx
    have h := ((hA x hx).const_mul (1 / 2 : ℝ)).add
      ((hB x hx).const_mul (1 / 2 : ℝ))
    have hlocal : (fun y => (1 / 2 : ℝ) * A y + (1 / 2 : ℝ) * B y) =ᶠ[nhds x] F := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (hF y hy).symm
    have hF' := h.congr_of_eventuallyEq hlocal.symm
    convert hF' using 1
    exact integrand_half_components x hx
theorem gap6 : HalfSumFamily = Translates primitive := by
  rw [← gap5]
  apply family_eq_translates
  intro x hx
  have hlog := (log_part_member x hx).const_mul (1 / 2 : ℝ)
  have harc := (arc_member x hx).const_mul (1 / 2 : ℝ)
  have hsum := hlog.add harc
  convert hsum using 1
  · funext y
    unfold primitive logPart
    congr 2
    rw [show 4 * y = 2 * y + 2 * y by ring, Real.exp_add]
    ring
  · exact integrand_half_components x hx
theorem gap7 : Family integrand = Translates primitive := by
  calc
    Family integrand = HalfSumFamily := gap5
    _ = Translates primitive := gap6

end
end ProofGap.Exercise2122
