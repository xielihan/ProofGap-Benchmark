import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1944

noncomputable section

def polynomialRhs (a b c d e f g h l m lam x : ℝ) :=
  (9 * a * x ^ 8 + 8 * b * x ^ 7 + 7 * c * x ^ 6 +
    6 * d * x ^ 5 + 5 * e * x ^ 4 + 4 * f * x ^ 3 +
    3 * g * x ^ 2 + 2 * h * x + l) * (1 + x ^ 2) +
  x * (a * x ^ 9 + b * x ^ 8 + c * x ^ 7 + d * x ^ 6 +
    e * x ^ 5 + f * x ^ 4 + g * x ^ 3 + h * x ^ 2 + l * x + m) + lam
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def integrand (x : ℝ) := x ^ 10 / Real.sqrt (1 + x ^ 2)
def primitive (x : ℝ) :=
  (63 / 256 * x - 21 / 128 * x ^ 3 + 21 / 160 * x ^ 5 -
    9 / 80 * x ^ 7 + 1 / 10 * x ^ 9) * Real.sqrt (1 + x ^ 2) -
  63 / 256 * Real.log (x + Real.sqrt (1 + x ^ 2))

private theorem polynomialCoefficients
    (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    a = 1 / 10 ∧ b = 0 ∧ c = -9 / 80 ∧ d = 0 ∧ e = 21 / 160 ∧
      f = 0 ∧ g = -21 / 128 ∧ h = 0 ∧ l = 63 / 256 ∧ m = 0 ∧
      lam = -63 / 256 := by
  have hn5 := hpoly (-5)
  have hn4 := hpoly (-4)
  have hn3 := hpoly (-3)
  have hn2 := hpoly (-2)
  have hn1 := hpoly (-1)
  have h0 := hpoly 0
  have h1 := hpoly 1
  have h2 := hpoly 2
  have h3 := hpoly 3
  have h4 := hpoly 4
  have h5 := hpoly 5
  norm_num [polynomialRhs] at hn5 hn4 hn3 hn2 hn1 h0 h1 h2 h3 h4 h5
  refine ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

private def primitivePoly (x : ℝ) :=
  63 / 256 * x - 21 / 128 * x ^ 3 + 21 / 160 * x ^ 5 -
    9 / 80 * x ^ 7 + 1 / 10 * x ^ 9

private def primitivePolyDeriv (x : ℝ) :=
  63 / 256 - 63 / 128 * x ^ 2 + 21 / 32 * x ^ 4 -
    63 / 80 * x ^ 6 + 9 / 10 * x ^ 8

private theorem primitiveHasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hqpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hqpos
  have hsne : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt hspos
  have hs_sq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hqpos)
  have hsumpos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    nlinarith
  have hsumne : x + Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt hsumpos
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa only [id] using (hasDerivAt_id x)
  have h1 : HasDerivAt (fun y : ℝ => 63 / 256 * y) (63 / 256) x := by
    convert hid.const_mul (63 / 256) using 1 <;> ring
  have h3 : HasDerivAt (fun y : ℝ => 21 / 128 * y ^ 3)
      (63 / 128 * x ^ 2) x := by
    convert (hid.pow 3).const_mul (21 / 128) using 1 <;> ring
  have h5 : HasDerivAt (fun y : ℝ => 21 / 160 * y ^ 5)
      (21 / 32 * x ^ 4) x := by
    convert (hid.pow 5).const_mul (21 / 160) using 1 <;> ring
  have h7 : HasDerivAt (fun y : ℝ => 9 / 80 * y ^ 7)
      (63 / 80 * x ^ 6) x := by
    convert (hid.pow 7).const_mul (9 / 80) using 1 <;> ring
  have h9 : HasDerivAt (fun y : ℝ => 1 / 10 * y ^ 9)
      (9 / 10 * x ^ 8) x := by
    convert (hid.pow 9).const_mul (1 / 10) using 1 <;> ring
  have hp : HasDerivAt primitivePoly (primitivePolyDeriv x) x := by
    unfold primitivePoly primitivePolyDeriv
    convert ((((h1.sub h3).add h5).sub h7).add h9) using 1 <;> ring
  have hq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hid.pow 2) using 1 <;> ring
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hqpos)).comp x hq using 1 <;>
      field_simp [hsne] <;> ring
  have hu : HasDerivAt
      (fun y : ℝ => y + Real.sqrt (1 + y ^ 2))
      (1 + x / Real.sqrt (1 + x ^ 2)) x := by
    convert hid.add hs using 1 <;> ring
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (y + Real.sqrt (1 + y ^ 2)))
      ((1 + x / Real.sqrt (1 + x ^ 2)) /
        (x + Real.sqrt (1 + x ^ 2))) x := by
    convert (Real.hasDerivAt_log hsumne).comp x hu using 1 <;>
      field_simp [hsne, hsumne] <;> ring
  have hlogder :
      (1 + x / Real.sqrt (1 + x ^ 2)) /
          (x + Real.sqrt (1 + x ^ 2)) =
        1 / Real.sqrt (1 + x ^ 2) := by
    field_simp [hsne, hsumne]
    ring
  have hderiv :
      primitivePolyDeriv x * Real.sqrt (1 + x ^ 2) +
          primitivePoly x * (x / Real.sqrt (1 + x ^ 2)) -
          63 / 256 *
            ((1 + x / Real.sqrt (1 + x ^ 2)) /
              (x + Real.sqrt (1 + x ^ 2))) =
        integrand x := by
    rw [hlogder]
    unfold integrand
    calc
      primitivePolyDeriv x * Real.sqrt (1 + x ^ 2) +
            primitivePoly x * (x / Real.sqrt (1 + x ^ 2)) -
            63 / 256 * (1 / Real.sqrt (1 + x ^ 2)) =
          (primitivePolyDeriv x * Real.sqrt (1 + x ^ 2) ^ 2 +
            primitivePoly x * x - 63 / 256) /
            Real.sqrt (1 + x ^ 2) := by
              field_simp [hsne]
              <;> ring
      _ = (primitivePolyDeriv x * (1 + x ^ 2) +
            primitivePoly x * x - 63 / 256) /
            Real.sqrt (1 + x ^ 2) := by rw [hs_sq]
      _ = x ^ 10 / Real.sqrt (1 + x ^ 2) := by
        unfold primitivePoly primitivePolyDeriv
        ring
  have hraw : HasDerivAt primitive
      (primitivePolyDeriv x * Real.sqrt (1 + x ^ 2) +
        primitivePoly x * (x / Real.sqrt (1 + x ^ 2)) -
        63 / 256 *
          ((1 + x / Real.sqrt (1 + x ^ 2)) /
            (x + Real.sqrt (1 + x ^ 2)))) x := by
    simpa only [primitive, primitivePoly] using
      (hp.mul hs).sub (hlog.const_mul (63 / 256))
  rw [← hderiv]
  exact hraw

theorem gap1 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x := by
  exact hpoly
theorem gap2 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    a = 1 / 10 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact ha
theorem gap3 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    b = 0 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hb
theorem gap4 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    c = -9 / 80 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hc
theorem gap5 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    d = 0 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hd
theorem gap6 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    e = 21 / 160 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact he
theorem gap7 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    f = 0 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hf
theorem gap8 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    g = -21 / 128 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hg
theorem gap9 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    h = 0 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hh
theorem gap10 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    l = 63 / 256 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hl
theorem gap11 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    m = 0 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hm
theorem gap12 (a b c d e f g h l m lam : ℝ)
    (hpoly : ∀ x, x ^ 10 = polynomialRhs a b c d e f g h l m lam x) :
    lam = -63 / 256 := by
  rcases polynomialCoefficients a b c d e f g h l m lam hpoly with
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hl, hm, hlam⟩
  exact hlam
theorem gap13 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    change ∃ C : ℝ, ∀ x, F x = primitive x + C
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      convert (hF x).sub (primitiveHasDerivAt x) using 1 <;> ring
    have hmono : Monotone (fun y => F y - primitive y) :=
      monotone_of_deriv_nonneg
        (fun x => (hzero x).differentiableAt)
        (fun x => by rw [(hzero x).deriv])
    have hanti : Antitone (fun y => F y - primitive y) :=
      antitone_of_deriv_nonpos
        (fun x => (hzero x).differentiableAt)
        (fun x => by rw [(hzero x).deriv])
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx : F x - primitive x = F 0 - primitive 0 := by
      rcases le_total x 0 with hx0 | h0x
      · exact le_antisymm (hmono hx0) (hanti hx0)
      · exact le_antisymm (hanti h0x) (hmono h0x)
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x, F x = primitive x + C at hF
    change ∀ x, HasDerivAt F (integrand x) x
    rcases hF with ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := funext hC
    rw [hfun]
    intro x
    exact (primitiveHasDerivAt x).add_const C

end
end ProofGap.Exercise1944
