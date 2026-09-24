import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2138

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def r (x : ℝ) := Real.sqrt (x + x ^ 2)
def integrand (x : ℝ) := (1 + x) / (x + r x)
def rationalized (x : ℝ) :=
  (1 + x) * (x - r x) / ((x + r x) * (x - r x))
def expanded (x : ℝ) :=
  (x + x ^ 2 - r x - x * r x) / (-x)
def FirstReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn
      (fun x => Real.sqrt (1 + x) / Real.sqrt x),
    ∃ H ∈ AntiderivativesOn r,
    ∀ x ∈ branch, F x = -x - 1 / 2 * x ^ 2 + G x + H x}
def SecondReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt G
          (Real.sqrt (1 + (Real.sqrt x) ^ 2) * deriv Real.sqrt x) x) ∧
    ∃ H : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt H
          (Real.sqrt ((x + 1 / 2) ^ 2 - (1 / 2) ^ 2) *
            deriv (fun y : ℝ => y + 1 / 2) x) x) ∧
    ∀ x ∈ branch, F x = -x - 1 / 2 * x ^ 2 + 2 * G x + H x}
def primitiveLong (x : ℝ) :=
  -x - 1 / 2 * x ^ 2 +
    Real.sqrt x * Real.sqrt (1 + x) +
    Real.log (Real.sqrt x + Real.sqrt (1 + x)) +
    (2 * x + 1) / 4 * r x -
    1 / 8 * Real.log (x + 1 / 2 + r x)
def primitiveCombined (x : ℝ) :=
  -x - 1 / 2 * x ^ 2 +
    (5 + 2 * x) / 4 * r x +
    1 / 2 * Real.log (2 * x + 1 + 2 * r x) -
    1 / 8 * Real.log (x + 1 / 2 + r x)
def primitiveFinal (x : ℝ) :=
  -1 / 2 * (x + 1) ^ 2 +
    (5 + 2 * x) / 4 * r x +
    3 / 8 * Real.log (x + 1 / 2 + r x)

private def auxiliaryG (x : ℝ) :=
  Real.sqrt x * Real.sqrt (1 + x) +
    Real.log (Real.sqrt x + Real.sqrt (1 + x))

private def auxiliaryH (x : ℝ) :=
  (2 * x + 1) / 4 * r x -
    1 / 8 * Real.log (x + 1 / 2 + r x)

private theorem antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
    (f p : ℝ → ℝ) (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (f x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C
    let q : ℝ → ℝ := fun x => F x - p x
    have hq : ∀ x ∈ branch, HasDerivAt q 0 x := by
      intro x hx
      unfold q
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ q branch := by
      intro x hx
      exact (hq x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv q x = 0 := by
      intro x hx
      exact (hq x hx).deriv
    refine ⟨q 1, ?_⟩
    intro x hx
    have h1 : (1 : ℝ) ∈ branch := by norm_num [branch]
    have hc : q x = q 1 := by
      exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hzero hx h1
    unfold q at hc
    linarith
  · rintro ⟨C, hF⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact hF y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem auxiliaryG_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt auxiliaryG (Real.sqrt (1 + x) / Real.sqrt x) x := by
  have hx0 : 0 < x := hx
  have hx1 : 0 < 1 + x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs1 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 hx1
  have hsx2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
  have hs12 : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
    Real.sq_sqrt (le_of_lt hx1)
  have hdx := Real.hasDerivAt_sqrt (ne_of_gt hx0)
  have hd1 : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y))
      (1 / (2 * Real.sqrt (1 + x))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hx1)).comp x
      ((hasDerivAt_const x 1).add (hasDerivAt_id x)) using 1 <;> ring
  have hp := hdx.mul hd1
  have hs := hdx.add hd1
  have hlog := (Real.hasDerivAt_log (by positivity :
      Real.sqrt x + Real.sqrt (1 + x) ≠ 0)).comp x hs
  unfold auxiliaryG
  convert hp.add hlog using 1
  field_simp [ne_of_gt hsx, ne_of_gt hs1,
    ne_of_gt (show 0 < Real.sqrt x + Real.sqrt (1 + x) by linarith)]
  nlinarith

private theorem auxiliaryH_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt auxiliaryH (r x) x := by
  have hx0 : 0 < x := hx
  have hrad : 0 < x + x ^ 2 := by nlinarith [sq_nonneg x]
  have hr0 : 0 < r x := by simpa [r] using Real.sqrt_pos.2 hrad
  have hrsq : (r x) ^ 2 = x + x ^ 2 := by
    rw [r, Real.sq_sqrt (le_of_lt hrad)]
  have hin : HasDerivAt (fun y : ℝ => y + y ^ 2) (1 + 2 * x) x := by
    convert (hasDerivAt_id x).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hr : HasDerivAt r ((1 + 2 * x) / (2 * r x)) x := by
    unfold r
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hin using 1
    field_simp [ne_of_gt hr0]
    <;> ring
  have hc : HasDerivAt (fun y : ℝ => (2 * y + 1) / 4) (1 / 2) x := by
    convert (((hasDerivAt_id x).const_mul 2).add_const 1).const_mul (1 / 4) using 1 <;>
      simp [id_eq] <;> ring
  have hu0 : 0 < x + 1 / 2 + r x := by linarith
  have hu : HasDerivAt (fun y : ℝ => y + 1 / 2 + r y)
      (1 + (1 + 2 * x) / (2 * r x)) x := by
    convert ((hasDerivAt_id x).add_const (1 / 2)).add hr using 1 <;>
      simp [id_eq] <;> ring
  have hl := (Real.hasDerivAt_log (ne_of_gt hu0)).comp x hu
  unfold auxiliaryH
  convert (hc.mul hr).sub (hl.const_mul (1 / 8)) using 1
  field_simp [ne_of_gt hr0, ne_of_gt hu0]
  nlinarith

private theorem primitiveLong_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveLong (integrand x) x := by
  have hx0 : 0 < x := hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hx1 : 0 < 1 + x := by linarith
  have hs1 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 hx1
  have hsx2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
  have hs12 : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
    Real.sq_sqrt (le_of_lt hx1)
  have hrprod : r x = Real.sqrt x * Real.sqrt (1 + x) := by
    rw [r, show x + x ^ 2 = x * (1 + x) by ring,
      Real.sqrt_mul (le_of_lt hx0)]
  have hpoly : HasDerivAt (fun y : ℝ => -y - 1 / 2 * y ^ 2) (-1 - x) x := by
    convert (hasDerivAt_id x).neg.sub
      (((hasDerivAt_id x).pow 2).const_mul (1 / 2)) using 1 <;>
      simp [id_eq] <;> ring
  have hg := auxiliaryG_hasDerivAt x hx
  have hh := auxiliaryH_hasDerivAt x hx
  have hall := (hpoly.add hg).add hh
  have hfun : primitiveLong =
      (fun y : ℝ => -y - 1 / 2 * y ^ 2) + auxiliaryG + auxiliaryH := by
    funext y
    simp only [primitiveLong, auxiliaryG, auxiliaryH, Pi.add_apply]
    ring
  have hvalue :
      -1 - x + Real.sqrt (1 + x) / Real.sqrt x + r x = integrand x := by
    unfold integrand
    rw [hrprod]
    let a : ℝ := Real.sqrt x
    let b : ℝ := Real.sqrt (1 + x)
    have ha : 0 < a := by simpa [a] using hsx
    have hb : 0 < b := by simpa [b] using hs1
    have ha2 : a ^ 2 = x := by simpa [a] using hsx2
    have hb2 : b ^ 2 = 1 + x := by simpa [b] using hs12
    change -1 - x + b / a + a * b = (1 + x) / (x + a * b)
    have hminus : -1 - x = -(b ^ 2) := by nlinarith [hb2]
    have hden : x + a * b = a * (a + b) := by nlinarith [ha2]
    have hsum : 0 < a + b := by linarith
    have hdiff : (b - a) * (a + b) = 1 := by
      nlinarith [ha2, hb2]
    have hba : b - a = 1 / (a + b) := by
      apply (eq_div_iff (ne_of_gt hsum)).2
      exact hdiff
    rw [hminus, hden, ← hb2]
    calc
      -(b ^ 2) + b / a + a * b = b / a - b * (b - a) := by ring
      _ = b / a - b * (1 / (a + b)) := by rw [hba]
      _ = b ^ 2 / (a * (a + b)) := by
        field_simp [ne_of_gt ha, ne_of_gt hsum]
        <;> ring
  rw [hfun, ← hvalue]
  exact hall

private theorem secondG_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => (1 / 2 : ℝ) * auxiliaryG y)
      (Real.sqrt (1 + (Real.sqrt x) ^ 2) * deriv Real.sqrt x) x := by
  have hx0 : 0 < x := hx
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsx2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
  have hderiv : deriv Real.sqrt x = 1 / (2 * Real.sqrt x) :=
    (Real.hasDerivAt_sqrt (ne_of_gt hx0)).deriv
  convert (auxiliaryG_hasDerivAt x hx).const_mul (1 / 2) using 1
  rw [hderiv, hsx2]
  field_simp [ne_of_gt hsx0]
  <;> ring

private theorem secondH_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt auxiliaryH
      (Real.sqrt ((x + 1 / 2) ^ 2 - (1 / 2) ^ 2) *
        deriv (fun y : ℝ => y + 1 / 2) x) x := by
  have hshift : deriv (fun y : ℝ => y + 1 / 2) x = 1 :=
    ((hasDerivAt_id x).add_const (1 / 2)).deriv
  have heq : (x + 1 / 2) ^ 2 - (1 / 2) ^ 2 = x + x ^ 2 := by ring
  rw [hshift, mul_one, heq]
  simpa [r] using auxiliaryH_hasDerivAt x hx

private theorem primitiveCombined_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveCombined (integrand x) x := by
  have hx0 : 0 < x := hx
  have hrad : 0 < x + x ^ 2 := by nlinarith [sq_nonneg x]
  have hr0 : 0 < r x := by simpa [r] using Real.sqrt_pos.2 hrad
  have hrsq : (r x) ^ 2 = x + x ^ 2 := by
    rw [r, Real.sq_sqrt (le_of_lt hrad)]
  have hin : HasDerivAt (fun y : ℝ => y + y ^ 2) (1 + 2 * x) x := by
    convert (hasDerivAt_id x).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hr : HasDerivAt r ((1 + 2 * x) / (2 * r x)) x := by
    unfold r
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hin using 1
    field_simp [ne_of_gt hr0]
    <;> ring
  have hp : HasDerivAt (fun y : ℝ => -y - 1 / 2 * y ^ 2) (-1 - x) x := by
    convert (hasDerivAt_id x).neg.sub
      (((hasDerivAt_id x).pow 2).const_mul (1 / 2)) using 1 <;>
      simp [id_eq] <;> ring
  have hc : HasDerivAt (fun y : ℝ => (5 + 2 * y) / 4) (1 / 2) x := by
    convert (((hasDerivAt_id x).const_mul 2).const_add 5).const_mul (1 / 4) using 1 <;>
      simp [id_eq] <;> ring
  have hu0 : 0 < x + 1 / 2 + r x := by linarith
  have hu : HasDerivAt (fun y : ℝ => y + 1 / 2 + r y)
      (1 + (1 + 2 * x) / (2 * r x)) x := by
    convert ((hasDerivAt_id x).add_const (1 / 2)).add hr using 1 <;>
      simp [id_eq] <;> ring
  have hl := (Real.hasDerivAt_log (ne_of_gt hu0)).comp x hu
  have hbig : HasDerivAt (fun y : ℝ => 2 * y + 1 + 2 * r y)
      (2 + 2 * ((1 + 2 * x) / (2 * r x))) x := by
    convert (((hasDerivAt_id x).const_mul 2).add_const 1).add
      (hr.const_mul 2) using 1 <;> simp [id_eq] <;> ring
  have hbig0 : 0 < 2 * x + 1 + 2 * r x := by linarith
  have hlbig := (Real.hasDerivAt_log (ne_of_gt hbig0)).comp x hbig
  unfold primitiveCombined
  convert (((hp.add (hc.mul hr)).add (hlbig.const_mul (1 / 2))).sub
    (hl.const_mul (1 / 8))) using 1
  unfold integrand
  field_simp [ne_of_gt hr0, ne_of_gt hu0, ne_of_gt hbig0,
    ne_of_gt (show 0 < x + r x by linarith)]
  <;> nlinarith [hrsq]

private theorem primitiveFinal_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveFinal (integrand x) x := by
  have hx0 : 0 < x := hx
  have hrad : 0 < x + x ^ 2 := by nlinarith [sq_nonneg x]
  have hr0 : 0 < r x := by simpa [r] using Real.sqrt_pos.2 hrad
  have hrsq : (r x) ^ 2 = x + x ^ 2 := by
    rw [r, Real.sq_sqrt (le_of_lt hrad)]
  have hin : HasDerivAt (fun y : ℝ => y + y ^ 2) (1 + 2 * x) x := by
    convert (hasDerivAt_id x).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hr : HasDerivAt r ((1 + 2 * x) / (2 * r x)) x := by
    unfold r
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hin using 1
    field_simp [ne_of_gt hr0]
    <;> ring
  have hp : HasDerivAt (fun y : ℝ => -1 / 2 * (y + 1) ^ 2) (-x - 1) x := by
    convert (((hasDerivAt_id x).add_const 1).pow 2).const_mul (-1 / 2) using 1 <;>
      simp [id_eq] <;> ring
  have hc : HasDerivAt (fun y : ℝ => (5 + 2 * y) / 4) (1 / 2) x := by
    convert (((hasDerivAt_id x).const_mul 2).const_add 5).const_mul (1 / 4) using 1 <;>
      simp [id_eq] <;> ring
  have hu0 : 0 < x + 1 / 2 + r x := by linarith
  have hu : HasDerivAt (fun y : ℝ => y + 1 / 2 + r y)
      (1 + (1 + 2 * x) / (2 * r x)) x := by
    convert ((hasDerivAt_id x).add_const (1 / 2)).add hr using 1 <;>
      simp [id_eq] <;> ring
  have hl := (Real.hasDerivAt_log (ne_of_gt hu0)).comp x hu
  unfold primitiveFinal
  convert (hp.add (hc.mul hr)).add (hl.const_mul (3 / 8)) using 1
  unfold integrand
  field_simp [ne_of_gt hr0, ne_of_gt hu0,
    ne_of_gt (show 0 < x + r x by linarith)]
  <;> nlinarith [hrsq]

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn rationalized := by
  have hfun : ∀ x ∈ branch, integrand x = rationalized x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hr0 : 0 < r x := by
      rw [r]
      exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])
    have hrsq : (r x) ^ 2 = x + x ^ 2 := by
      rw [r, Real.sq_sqrt]
      nlinarith [sq_nonneg x]
    have hxm : x - r x ≠ 0 := by
      intro h
      have : r x = x := by linarith
      nlinarith
    have hxp : x + r x ≠ 0 := ne_of_gt (by linarith)
    unfold integrand rationalized
    field_simp [hxm, hxp]
    <;> ring
  apply Set.ext
  intro F
  constructor
  · intro h x hx
    simpa [hfun x hx] using h x hx
  · intro h x hx
    simpa [hfun x hx] using h x hx
theorem gap2 :
    AntiderivativesOn integrand = AntiderivativesOn expanded := by
  rw [gap1]
  apply Set.ext
  intro F
  have hfun : ∀ x ∈ branch, rationalized x = expanded x := by
    intro x hx
    have hrad : 0 ≤ x + x ^ 2 := by
      nlinarith [show 0 < x from hx, sq_nonneg x]
    have hrsq : (r x) ^ 2 = x + x ^ 2 := by
      rw [r, Real.sq_sqrt hrad]
    have hden : (x + r x) * (x - r x) = -x := by
      nlinarith
    unfold rationalized expanded
    rw [hden]
    ring
  constructor
  · intro h x hx
    simpa [hfun x hx] using h x hx
  · intro h x hx
    simpa [hfun x hx] using h x hx
theorem gap3 :
    AntiderivativesOn expanded = FirstReductionFamily := by
  have hmainInt : AntiderivativesOn integrand = PrimitiveFamily primitiveLong :=
    antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
      integrand primitiveLong primitiveLong_hasDerivAt
  have hmain : AntiderivativesOn expanded = PrimitiveFamily primitiveLong :=
    gap2.symm.trans hmainInt
  rw [hmain]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => auxiliaryG x + C, ?_, fun x => auxiliaryH x, ?_, ?_⟩
    · intro x hx
      exact (auxiliaryG_hasDerivAt x hx).add_const C
    · intro x hx
      exact auxiliaryH_hasDerivAt x hx
    · intro x hx
      specialize hF x hx
      simp only [primitiveLong, auxiliaryG, auxiliaryH] at hF ⊢
      linarith
  · rintro ⟨G, hG, H, hH, hF⟩
    have hGmem : G ∈ PrimitiveFamily auxiliaryG := by
      rw [← antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
        (fun x => Real.sqrt (1 + x) / Real.sqrt x) auxiliaryG auxiliaryG_hasDerivAt]
      exact hG
    have hHmem : H ∈ PrimitiveFamily auxiliaryH := by
      rw [← antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
        r auxiliaryH auxiliaryH_hasDerivAt]
      exact hH
    rcases hGmem with ⟨CG, hGeq⟩
    rcases hHmem with ⟨CH, hHeq⟩
    refine ⟨CG + CH, ?_⟩
    intro x hx
    specialize hF x hx
    specialize hGeq x hx
    specialize hHeq x hx
    simp only [primitiveLong, auxiliaryG, auxiliaryH] at hF hGeq hHeq ⊢
    linarith
theorem gap4 :
    AntiderivativesOn integrand = FirstReductionFamily := by
  exact gap2.trans gap3
theorem gap5 :
    AntiderivativesOn integrand = SecondReductionFamily := by
  have hmain : AntiderivativesOn integrand = PrimitiveFamily primitiveLong :=
    antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
      integrand primitiveLong primitiveLong_hasDerivAt
  rw [hmain]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => (1 / 2 : ℝ) * auxiliaryG x + C / 2, ?_,
      fun x => auxiliaryH x, ?_, ?_⟩
    · intro x hx
      exact (secondG_hasDerivAt x hx).add_const (C / 2)
    · intro x hx
      exact secondH_hasDerivAt x hx
    · intro x hx
      specialize hF x hx
      simp only [primitiveLong, auxiliaryG, auxiliaryH] at hF ⊢
      linarith
  · rintro ⟨G, hG, H, hH, hF⟩
    have hGmem : G ∈ PrimitiveFamily (fun x => (1 / 2 : ℝ) * auxiliaryG x) := by
      rw [← antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
        (fun x => Real.sqrt (1 + (Real.sqrt x) ^ 2) * deriv Real.sqrt x)
        (fun x => (1 / 2 : ℝ) * auxiliaryG x) secondG_hasDerivAt]
      exact hG
    have hHmem : H ∈ PrimitiveFamily auxiliaryH := by
      rw [← antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
        (fun x => Real.sqrt ((x + 1 / 2) ^ 2 - (1 / 2) ^ 2) *
          deriv (fun y : ℝ => y + 1 / 2) x)
        auxiliaryH secondH_hasDerivAt]
      exact hH
    rcases hGmem with ⟨CG, hGeq⟩
    rcases hHmem with ⟨CH, hHeq⟩
    refine ⟨2 * CG + CH, ?_⟩
    intro x hx
    specialize hF x hx
    specialize hGeq x hx
    specialize hHeq x hx
    simp only [primitiveLong, auxiliaryG, auxiliaryH] at hF hGeq hHeq ⊢
    linarith
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveLong := by
  exact antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
    integrand primitiveLong primitiveLong_hasDerivAt
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveCombined := by
  exact antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
    integrand primitiveCombined primitiveCombined_hasDerivAt
theorem gap8 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveFinal := by
  exact antiderivativesOn_eq_primitiveFamily_of_hasDerivAt
    integrand primitiveFinal primitiveFinal_hasDerivAt

end
end ProofGap.Exercise2138
