import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1943

noncomputable section

def q (x : ℝ) := 1 + 2 * x - x ^ 2
def branch : Set ℝ := {x | 0 < q x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def polynomialRhs (a b c lam x : ℝ) :=
  (2 * a * x + b) * q x + (a * x ^ 2 + b * x + c) * (1 - x) + lam
def integrand (x : ℝ) := x ^ 3 / Real.sqrt (q x)
def auxiliaryIntegrand (x : ℝ) := 1 / Real.sqrt (q x)
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn branch auxiliaryIntegrand,
    ∀ x ∈ branch,
      F x = -(19 + 5 * x + 2 * x ^ 2) / 6 * Real.sqrt (q x) + 4 * G x}
def primitive (x : ℝ) :=
  -(19 + 5 * x + 2 * x ^ 2) / 6 * Real.sqrt (q x) +
    4 * Real.arcsin ((x - 1) / Real.sqrt 2)

private theorem branch_isOpen : IsOpen branch := by
  have hqcont : Continuous q := by
    unfold q
    exact (continuous_const.add (continuous_const.mul continuous_id)).sub
      (continuous_id.pow 2)
  change IsOpen (q ⁻¹' Set.Ioi 0)
  exact isOpen_Ioi.preimage hqcont

private theorem branch_eq_interval :
    branch = Set.Ioo (1 - Real.sqrt 2) (1 + Real.sqrt 2) := by
  ext x
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [branch, Set.mem_setOf_eq, Set.mem_Ioo]
  unfold q
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    nlinarith

private theorem reductionTerm_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt
      (fun y => -(19 + 5 * y + 2 * y ^ 2) / 6 * Real.sqrt (q y))
      (integrand x - 4 * auxiliaryIntegrand x) x := by
  have hq : 0 < q x := hx
  have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hq' : HasDerivAt q (2 - 2 * x) x := by
    unfold q
    convert (((hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x))).sub
        ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((1 - x) / Real.sqrt (q x)) x := by
    have hd := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hq'
    convert hd using 1 <;> field_simp [hs]
  have hp : HasDerivAt (fun y : ℝ => 19 + 5 * y + 2 * y ^ 2)
      (5 + 4 * x) x := by
    convert (((hasDerivAt_const x (19 : ℝ)).add
      ((hasDerivAt_const x (5 : ℝ)).mul (hasDerivAt_id x))).add
        ((hasDerivAt_const x (2 : ℝ)).mul ((hasDerivAt_id x).pow 2))) using 1 <;>
      simp only [id_eq] <;> ring
  have ha : HasDerivAt (fun y : ℝ => -(19 + 5 * y + 2 * y ^ 2) / 6)
      (-(5 + 4 * x) / 6) x := by
    convert hp.neg.div_const 6 using 1 <;> ring
  have hb : HasDerivAt
      (fun y => -(19 + 5 * y + 2 * y ^ 2) / 6 * Real.sqrt (q y))
      ((-(5 + 4 * x) / 6) * Real.sqrt (q x) +
        (-(19 + 5 * x + 2 * x ^ 2) / 6) *
          ((1 - x) / Real.sqrt (q x))) x :=
    ha.mul hsqrt
  have hsq : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt hq)
  have hcoef :
      ((-(5 + 4 * x) / 6) * Real.sqrt (q x) +
        (-(19 + 5 * x + 2 * x ^ 2) / 6) *
          ((1 - x) / Real.sqrt (q x))) =
        integrand x - 4 * auxiliaryIntegrand x := by
    unfold integrand auxiliaryIntegrand
    field_simp [hs]
    rw [hsq]
    unfold q
    ring
  rw [hcoef] at hb
  exact hb

private theorem arcsinTerm_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.arcsin ((y - 1) / Real.sqrt 2))
      (auxiliaryIntegrand x) x := by
  have hq : 0 < q x := hx
  have hs2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2ne : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt hs2
  have hs2sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  let u : ℝ := (x - 1) / Real.sqrt 2
  have hxsq : (x - 1) ^ 2 < 2 := by
    unfold q at hq
    nlinarith
  have hu : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    dsimp [u]
    constructor
    · rw [lt_div_iff₀ hs2]
      nlinarith
    · rw [div_lt_iff₀ hs2]
      nlinarith
  have hu' : HasDerivAt (fun y : ℝ => (y - 1) / Real.sqrt 2)
      (1 / Real.sqrt 2) x := by
    convert ((hasDerivAt_id x).sub (hasDerivAt_const x (1 : ℝ))).div_const
      (Real.sqrt 2) using 1 <;> ring
  have hinside : 0 < 1 - u ^ 2 := by
    rcases hu with ⟨hlo, hhi⟩
    nlinarith
  have hrel : q x = 2 * (1 - u ^ 2) := by
    dsimp [u]
    unfold q
    field_simp [hs2ne]
    nlinarith [hs2sq]
  have hsqrtq : Real.sqrt (q x) =
      Real.sqrt 2 * Real.sqrt (1 - u ^ 2) := by
    rw [hrel, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hcoef :
      (1 / Real.sqrt (1 - u ^ 2)) * (1 / Real.sqrt 2) =
        auxiliaryIntegrand x := by
    unfold auxiliaryIntegrand
    rw [hsqrtq]
    field_simp [hs2ne, ne_of_gt (Real.sqrt_pos.2 hinside)]
  have hd := (Real.hasDerivAt_arcsin (ne_of_gt hu.1) (ne_of_lt hu.2)).comp x hu'
  rw [hcoef] at hd
  simpa [u] using hd

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  unfold primitive
  convert (reductionTerm_hasDerivAt x hx).add
    ((arcsinTerm_hasDerivAt x hx).const_mul 4) using 1 <;> ring

theorem gap1 (a b c lam x : ℝ) (hx : x ∈ branch)
    (hpoly : ∀ y, y ^ 3 = polynomialRhs a b c lam y) :
    x ^ 3 / Real.sqrt (q x) =
      (2 * a * x + b) * Real.sqrt (q x) +
      (a * x ^ 2 + b * x + c) * (1 - x) / Real.sqrt (q x) +
      lam / Real.sqrt (q x) := by
  have hq : 0 < q x := hx
  have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hsq : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt hq)
  field_simp [hs]
  rw [hsq]
  rw [hpoly x]
  unfold polynomialRhs
  ring
theorem gap2 (a b c lam : ℝ)
    (hred : ∀ x ∈ branch, x ^ 3 / Real.sqrt (q x) =
      (2 * a * x + b) * Real.sqrt (q x) +
      (a * x ^ 2 + b * x + c) * (1 - x) / Real.sqrt (q x) +
      lam / Real.sqrt (q x)) :
    ∀ x, x ^ 3 = polynomialRhs a b c lam x := by
  have hlocal : ∀ x ∈ branch, x ^ 3 = polynomialRhs a b c lam x := by
    intro x hx
    have hq : 0 < q x := hx
    have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
    have hsq : (Real.sqrt (q x)) ^ 2 = q x :=
      Real.sq_sqrt (le_of_lt hq)
    have hm := (div_eq_iff hs).1 (hred x hx)
    calc
      x ^ 3 = ((2 * a * x + b) * Real.sqrt (q x) +
          (a * x ^ 2 + b * x + c) * (1 - x) / Real.sqrt (q x) +
          lam / Real.sqrt (q x)) * Real.sqrt (q x) := hm
      _ = polynomialRhs a b c lam x := by
        unfold polynomialRhs
        field_simp [hs]
        rw [hsq]
  have h0 := hlocal 0 (by norm_num [branch, q])
  have h1 := hlocal 1 (by norm_num [branch, q])
  have h2 := hlocal 2 (by norm_num [branch, q])
  have hh := hlocal (1 / 2) (by norm_num [branch, q])
  norm_num [polynomialRhs, q] at h0 h1 h2 hh
  have ha : a = -1 / 3 := by linarith [h0, h1, h2, hh]
  have hb : b = -5 / 6 := by linarith [h0, h1, h2, hh]
  have hc : c = -19 / 6 := by linarith [h0, h1, h2, hh]
  have hlam : lam = 4 := by linarith [h0, h1, h2, hh]
  intro x
  rw [ha, hb, hc, hlam]
  unfold polynomialRhs q
  ring
theorem gap3 (a b c lam : ℝ)
    (hpoly : ∀ x, x ^ 3 = polynomialRhs a b c lam x) :
    -3 * a = 1 := by
  have h0 := hpoly 0
  have h1 := hpoly 1
  have h2 := hpoly 2
  have h3 := hpoly 3
  norm_num [polynomialRhs, q] at h0 h1 h2 h3
  linarith
theorem gap4 (a b c lam : ℝ)
    (hpoly : ∀ x, x ^ 3 = polynomialRhs a b c lam x) :
    5 * a - 2 * b = 0 := by
  have h0 := hpoly 0
  have h1 := hpoly 1
  have h2 := hpoly 2
  have h3 := hpoly 3
  norm_num [polynomialRhs, q] at h0 h1 h2 h3
  linarith
theorem gap5 (a b c lam : ℝ)
    (hpoly : ∀ x, x ^ 3 = polynomialRhs a b c lam x) :
    2 * a + 3 * b - c = 0 := by
  have h0 := hpoly 0
  have h1 := hpoly 1
  have h2 := hpoly 2
  have h3 := hpoly 3
  norm_num [polynomialRhs, q] at h0 h1 h2 h3
  linarith
theorem gap6 (a b c lam : ℝ)
    (hpoly : ∀ x, x ^ 3 = polynomialRhs a b c lam x) :
    b + c + lam = 0 := by
  have h0 := hpoly 0
  norm_num [polynomialRhs, q] at h0
  linarith
theorem gap7 (a : ℝ) (h : -3 * a = 1) :
    a = -1 / 3 := by
  linarith
theorem gap8 (a b : ℝ) (ha : a = -1 / 3) (h : 5 * a - 2 * b = 0) :
    b = -5 / 6 := by
  rw [ha] at h
  norm_num at h ⊢
  linarith
theorem gap9 (a b c : ℝ) (ha : a = -1 / 3) (hb : b = -5 / 6)
    (h : 2 * a + 3 * b - c = 0) :
    c = -19 / 6 := by
  rw [ha, hb] at h
  norm_num at h ⊢
  linarith
theorem gap10 (b c lam : ℝ) (hb : b = -5 / 6) (hc : c = -19 / 6)
    (h : b + c + lam = 0) :
    lam = 4 := by
  rw [hb, hc] at h
  norm_num at h ⊢
  linarith
theorem gap11 :
    AntiderivativesOn branch integrand = ReductionFamily := by
  ext F
  simp only [AntiderivativesOn, ReductionFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y =>
      (F y - (-(19 + 5 * y + 2 * y ^ 2) / 6 * Real.sqrt (q y))) / 4,
      ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).sub (reductionTerm_hasDerivAt x hx)
      convert hd.div_const 4 using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hcalc : HasDerivAt
        (fun y =>
          -(19 + 5 * y + 2 * y ^ 2) / 6 * Real.sqrt (q y) + 4 * G y)
        (integrand x) x := by
      convert (reductionTerm_hasDerivAt x hx).add
        ((hG x hx).const_mul 4) using 1 <;> ring
    have hev : F =ᶠ[nhds x] (fun y =>
        -(19 + 5 * y + 2 * y ^ 2) / 6 * Real.sqrt (q y) + 4 * G y) := by
      filter_upwards [branch_isOpen.mem_nhds hx] with y hy
      exact hFG y hy
    exact hcalc.congr_of_eventuallyEq hev
theorem gap12 :
    AntiderivativesOn branch integrand =
      PrimitiveFamilyOn branch primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (primitive_hasDerivAt x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y)
        (Set.Ioo (1 - Real.sqrt 2) (1 + Real.sqrt 2)) := by
      intro x hx
      have hxb : x ∈ branch := by
        rw [branch_eq_interval]
        exact hx
      exact (hzero x hxb).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ Set.Ioo (1 - Real.sqrt 2) (1 + Real.sqrt 2),
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hxb : x ∈ branch := by
        rw [branch_eq_interval]
        exact hx
      exact (hzero x hxb).deriv
    have hconst :
        ∀ x ∈ Set.Ioo (1 - Real.sqrt 2) (1 + Real.sqrt 2),
          ∀ y ∈ Set.Ioo (1 - Real.sqrt 2) (1 + Real.sqrt 2),
            F x - primitive x = F y - primitive y := by
      intro x hx y hy
      exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hderiv hx hy
    have h1I : (1 : ℝ) ∈ Set.Ioo
        (1 - Real.sqrt 2) (1 + Real.sqrt 2) := by
      have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
      constructor <;> linarith
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hxI : x ∈ Set.Ioo
        (1 - Real.sqrt 2) (1 + Real.sqrt 2) := by
      rw [← branch_eq_interval]
      exact hx
    have heq := hconst x hxI 1 h1I
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hcalc : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (primitive_hasDerivAt x hx).add_const C
    have hev : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [branch_isOpen.mem_nhds hx] with y hy
      exact hFC y hy
    exact hcalc.congr_of_eventuallyEq hev

end
end ProofGap.Exercise1943
