import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1976

noncomputable section

def sec (t : ℝ) := 1 / Real.cos t
def angleBranch : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def u (x : ℝ) := x * Real.sqrt 2 / (1 + x ^ 2)
def originalIntegrand (x : ℝ) :=
  (x ^ 2 - 1) / ((x ^ 2 + 1) * Real.sqrt (x ^ 4 + 1))
def normalizedIntegrand (x : ℝ) :=
  ((x ^ 2 - 1) / (x ^ 2 + 1) ^ 2) /
    Real.sqrt ((x ^ 4 + 1) / (x ^ 2 + 1) ^ 2)
def arcsineFormIntegrand (x : ℝ) :=
  ((x ^ 2 - 1) / (x ^ 2 + 1) ^ 2) /
    Real.sqrt (1 - u x ^ 2)
def tangentFormIntegrand (t : ℝ) :=
  (Real.tan t ^ 2 - 1) / sec t ^ 4 * sec t ^ 2
def doubleAngleIntegrand (t : ℝ) :=
  Real.sin t ^ 2 - Real.cos t ^ 2
def cosineIntegrand (t : ℝ) := Real.cos (2 * t)
def tPrimitive (t : ℝ) := -1 / 2 * Real.sin (2 * t)
def tangentPrimitive (t : ℝ) :=
  -Real.tan t / (1 + Real.tan t ^ 2)
def uArcsineIntegrand (x : ℝ) :=
  deriv u x / Real.sqrt (1 - u x ^ 2)
def xPrimitive (x : ℝ) :=
  -1 / Real.sqrt 2 * Real.arcsin (u x)
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def NegatedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn angleBranch cosineIntegrand,
    ∀ t ∈ angleBranch, F t = -G t}
def ScaledUFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn Set.univ uArcsineIntegrand,
    ∀ x, F x = -1 / Real.sqrt 2 * G x}

private theorem antiderivatives_eq_primitive_of_open_convex
    {s : Set ℝ} {f p : ℝ → ℝ}
    (hsopen : IsOpen s) (hsconvex : Convex ℝ s)
    (x₀ : ℝ) (hx₀ : x₀ ∈ s)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    refine ⟨F x₀ - p x₀, ?_⟩
    intro x hx
    have heq : F x - p x = F x₀ - p x₀ :=
      hsopen.is_const_of_deriv_eq_zero
        hsconvex.isPreconnected hdiff hderiv hx hx₀
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hmem : ∀ᶠ y in nhds x, y ∈ s := hsopen.mem_nhds hx
    have heq : F =ᶠ[nhds x] fun y => p y + C :=
      hmem.mono (fun y hy => hC y hy)
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem hasDerivAt_u (x : ℝ) :
    HasDerivAt u
      (Real.sqrt 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) x := by
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  have hnum :
      HasDerivAt (fun y : ℝ => y * Real.sqrt 2) (Real.sqrt 2) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.sqrt 2)
  have hden' : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2) using 1
      <;> simp [id_eq]
      <;> ring
  have hquot := hnum.div hden' hden
  change HasDerivAt (fun y : ℝ => y * Real.sqrt 2 / (1 + y ^ 2))
    (Real.sqrt 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) x
  convert hquot using 1 <;> field_simp [hden] <;> ring

theorem gap1 :
    AntiderivativesOn Set.univ originalIntegrand =
      AntiderivativesOn Set.univ normalizedIntegrand := by
  have heq : ∀ x : ℝ, originalIntegrand x = normalizedIntegrand x := by
    intro x
    have hA : 0 < x ^ 2 + 1 := by positivity
    have hB : 0 < x ^ 4 + 1 := by positivity
    have hsqrt :
        Real.sqrt ((x ^ 4 + 1) / (x ^ 2 + 1) ^ 2) =
          Real.sqrt (x ^ 4 + 1) / (x ^ 2 + 1) := by
      rw [Real.sqrt_div (le_of_lt hB), Real.sqrt_sq_eq_abs, abs_of_pos hA]
    unfold originalIntegrand normalizedIntegrand
    rw [hsqrt]
    field_simp [ne_of_gt hA, ne_of_gt (Real.sqrt_pos.2 hB)]
    <;> ring
  ext F
  constructor
  · intro h x hx
    simpa only [heq x] using h x hx
  · intro h x hx
    simpa only [heq x] using h x hx
theorem gap2 :
    AntiderivativesOn Set.univ normalizedIntegrand =
      AntiderivativesOn Set.univ arcsineFormIntegrand := by
  have heq : ∀ x : ℝ, normalizedIntegrand x = arcsineFormIntegrand x := by
    intro x
    have hA : 1 + x ^ 2 ≠ 0 := by positivity
    have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hrad :
        (x ^ 4 + 1) / (x ^ 2 + 1) ^ 2 = 1 - u x ^ 2 := by
      rw [show x ^ 2 + 1 = 1 + x ^ 2 by ring]
      unfold u
      field_simp [hA]
      rw [hsqrt2]
      ring
    unfold normalizedIntegrand arcsineFormIntegrand
    rw [hrad]
  ext F
  constructor
  · intro h x hx
    simpa only [heq x] using h x hx
  · intro h x hx
    simpa only [heq x] using h x hx
theorem gap3 :
    AntiderivativesOn Set.univ originalIntegrand =
      AntiderivativesOn Set.univ arcsineFormIntegrand := by
  calc
    AntiderivativesOn Set.univ originalIntegrand =
        AntiderivativesOn Set.univ normalizedIntegrand := gap1
    _ = AntiderivativesOn Set.univ arcsineFormIntegrand := gap2
theorem gap4 (t : ℝ) (ht : t ∈ angleBranch) :
    -Real.pi / 2 < t := by
  exact ht.1
theorem gap5 (t : ℝ) (ht : t ∈ angleBranch) :
    t < Real.pi / 2 := by
  exact ht.2
theorem gap6 :
    -Real.pi / 2 < Real.pi / 2 := by
  nlinarith [Real.pi_pos]
theorem gap7 (t : ℝ) (ht : t ∈ angleBranch) :
    HasDerivAt Real.tan (sec t ^ 2) t := by
  have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    exact ⟨by simpa only [neg_div] using gap4 t ht, gap5 t ht⟩
  have hcos : Real.cos t ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ht')
  simpa [sec, div_pow] using Real.hasDerivAt_tan hcos
theorem gap8 :
    AntiderivativesOn angleBranch
        (fun t => (Real.tan t ^ 2 - 1) / (Real.tan t ^ 2 + 1) ^ 2 *
          deriv Real.tan t) =
      AntiderivativesOn angleBranch tangentFormIntegrand := by
  have hpoint : ∀ t ∈ angleBranch,
      (Real.tan t ^ 2 - 1) / (Real.tan t ^ 2 + 1) ^ 2 *
          deriv Real.tan t = tangentFormIntegrand t := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      exact ⟨by simpa only [neg_div] using gap4 t ht, gap5 t ht⟩
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ht')
    have hderiv : deriv Real.tan t = sec t ^ 2 := (gap7 t ht).deriv
    have hs : Real.tan t ^ 2 + 1 = sec t ^ 2 := by
      unfold sec
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hcos]
      nlinarith [Real.sin_sq_add_cos_sq t]
    unfold tangentFormIntegrand
    rw [hderiv, hs]
    ring
  ext F
  constructor
  · intro h t ht
    simpa only [hpoint t ht] using h t ht
  · intro h t ht
    simpa only [hpoint t ht] using h t ht
theorem gap9 :
    AntiderivativesOn angleBranch tangentFormIntegrand =
      AntiderivativesOn angleBranch doubleAngleIntegrand := by
  have hpoint : ∀ t ∈ angleBranch,
      tangentFormIntegrand t = doubleAngleIntegrand t := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      exact ⟨by simpa only [neg_div] using gap4 t ht, gap5 t ht⟩
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ht')
    unfold tangentFormIntegrand doubleAngleIntegrand sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    <;> ring
  ext F
  constructor
  · intro h t ht
    simpa only [hpoint t ht] using h t ht
  · intro h t ht
    simpa only [hpoint t ht] using h t ht
theorem gap10 :
    AntiderivativesOn angleBranch doubleAngleIntegrand =
      NegatedFamily := by
  have htrig : ∀ t : ℝ,
      -doubleAngleIntegrand t = cosineIntegrand t := by
    intro t
    unfold doubleAngleIntegrand cosineIntegrand
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
  ext F
  constructor
  · intro hF
    refine ⟨fun t => -F t, ?_, ?_⟩
    · intro t ht
      simpa only [htrig t] using (hF t ht).neg
    · intro t ht
      simp
  · rintro ⟨G, hG, hFG⟩
    intro t ht
    have hmem : ∀ᶠ y in nhds t, y ∈ angleBranch :=
      isOpen_Ioo.mem_nhds ht
    have heq : F =ᶠ[nhds t] fun y => -G y :=
      hmem.mono (fun y hy => hFG y hy)
    have hneg : HasDerivAt (fun y => -G y) (doubleAngleIntegrand t) t := by
      simpa only [← htrig t, neg_neg] using (hG t ht).neg
    exact hneg.congr_of_eventuallyEq heq
theorem gap11 :
    NegatedFamily =
      PrimitiveFamilyOn angleBranch tPrimitive := by
  rw [← gap10]
  apply antiderivatives_eq_primitive_of_open_convex
      (s := angleBranch) (f := doubleAngleIntegrand) (p := tPrimitive)
      (x₀ := 0)
  · simpa [angleBranch, neg_div] using
      (isOpen_Ioo : IsOpen (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
  · simpa [angleBranch, neg_div] using
      (convex_Ioo (-(Real.pi / 2)) (Real.pi / 2) :
        Convex ℝ (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
  · exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  · intro t ht
    have hsin :
        HasDerivAt (fun y : ℝ => Real.sin (2 * y))
          (2 * Real.cos (2 * t)) t := by
      convert (Real.hasDerivAt_sin (2 * t)).comp t
        ((hasDerivAt_id t).const_mul 2) using 1 <;> ring
    have hprim : HasDerivAt tPrimitive (-Real.cos (2 * t)) t := by
      change HasDerivAt (fun y : ℝ => -1 / 2 * Real.sin (2 * y))
        (-Real.cos (2 * t)) t
      convert hsin.const_mul (-1 / 2) using 1 <;> ring
    convert hprim using 1
    unfold doubleAngleIntegrand
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
theorem gap12 :
    PrimitiveFamilyOn angleBranch tPrimitive =
      PrimitiveFamilyOn angleBranch tangentPrimitive := by
  have hpoint : ∀ t ∈ angleBranch, tPrimitive t = tangentPrimitive t := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      exact ⟨by simpa only [neg_div] using gap4 t ht, gap5 t ht⟩
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ht')
    have htrig : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    unfold tPrimitive tangentPrimitive
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp [hcos]
    rw [htrig]
    ring
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hC t ht, hpoint t ht]
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hC t ht, hpoint t ht]
theorem gap13 :
    AntiderivativesOn angleBranch
        (fun t => (Real.tan t ^ 2 - 1) / (Real.tan t ^ 2 + 1) ^ 2 *
          deriv Real.tan t) =
      PrimitiveFamilyOn angleBranch tangentPrimitive := by
  calc
    AntiderivativesOn angleBranch
        (fun t => (Real.tan t ^ 2 - 1) / (Real.tan t ^ 2 + 1) ^ 2 *
          deriv Real.tan t) =
      AntiderivativesOn angleBranch tangentFormIntegrand := gap8
    _ = AntiderivativesOn angleBranch doubleAngleIntegrand := gap9
    _ = NegatedFamily := gap10
    _ = PrimitiveFamilyOn angleBranch tPrimitive := gap11
    _ = PrimitiveFamilyOn angleBranch tangentPrimitive := gap12
theorem gap14 (x : ℝ) :
    (x ^ 2 - 1) / (x ^ 2 + 1) ^ 2 =
      -1 / Real.sqrt 2 * deriv u x := by
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [(hasDerivAt_u x).deriv]
  field_simp [hden, hsqrt]
  ring
theorem gap15 :
    AntiderivativesOn Set.univ originalIntegrand =
      ScaledUFamily := by
  rw [gap3]
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hscale : ∀ x : ℝ,
      arcsineFormIntegrand x =
        -1 / Real.sqrt 2 * uArcsineIntegrand x := by
    intro x
    unfold arcsineFormIntegrand uArcsineIntegrand
    rw [gap14 x]
    ring
  ext F
  constructor
  · intro hF
    refine ⟨fun x => -Real.sqrt 2 * F x, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul (-Real.sqrt 2)
      have hcoef :
          -Real.sqrt 2 * arcsineFormIntegrand x =
            uArcsineIntegrand x := by
        rw [hscale x]
        field_simp [hsqrt]
      simpa only [hcoef] using hd
    · intro x
      field_simp [hsqrt]
  · rintro ⟨G, hG, hFG⟩
    have hfun : F = fun x => -1 / Real.sqrt 2 * G x := funext hFG
    rw [hfun]
    intro x hx
    have hd := (hG x hx).const_mul (-1 / Real.sqrt 2)
    simpa only [← hscale x] using hd
theorem gap16 :
    ScaledUFamily =
      PrimitiveFamilyOn Set.univ xPrimitive := by
  let q : ℝ → ℝ := fun x => Real.arcsin (u x)
  have hp : ∀ x ∈ Set.univ, HasDerivAt q (uArcsineIntegrand x) x := by
    intro x hx
    have hden : 1 + x ^ 2 ≠ 0 := by positivity
    have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hrad :
        1 - u x ^ 2 = (x ^ 4 + 1) / (x ^ 2 + 1) ^ 2 := by
      rw [show x ^ 2 + 1 = 1 + x ^ 2 by ring]
      unfold u
      field_simp [hden]
      rw [hsqrt2]
      ring
    have hradpos : 0 < 1 - u x ^ 2 := by
      rw [hrad]
      positivity
    have hu_lt : u x ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor <;>
        nlinarith [sq_nonneg (u x - 1), sq_nonneg (u x + 1)]
    have hc := (Real.hasDerivAt_arcsin
      (ne_of_gt hu_lt.1) (ne_of_lt hu_lt.2)).comp x (hasDerivAt_u x)
    change HasDerivAt (fun y => Real.arcsin (u y))
      (deriv u x / Real.sqrt (1 - u x ^ 2)) x
    rw [(hasDerivAt_u x).deriv]
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using hc
  have hchar :
      AntiderivativesOn Set.univ uArcsineIntegrand =
        PrimitiveFamilyOn Set.univ q :=
    antiderivatives_eq_primitive_of_open_convex
      (s := Set.univ) (f := uArcsineIntegrand) (p := q)
      isOpen_univ convex_univ 0 (Set.mem_univ 0) hp
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hGp : G ∈ PrimitiveFamilyOn Set.univ q := by
      rw [← hchar]
      exact hG
    rcases hGp with ⟨C, hC⟩
    refine ⟨-1 / Real.sqrt 2 * C, ?_⟩
    intro x hx
    rw [hFG x, hC x hx]
    simp only [xPrimitive, q]
    ring
  · rintro ⟨C, hF⟩
    let G : ℝ → ℝ := fun x => q x - Real.sqrt 2 * C
    refine ⟨G, ?_, ?_⟩
    · rw [hchar]
      refine ⟨-Real.sqrt 2 * C, ?_⟩
      intro x hx
      simp [G, sub_eq_add_neg]
    · intro x
      rw [hF x (Set.mem_univ x)]
      simp only [G, q, xPrimitive]
      field_simp [hsqrt]
      ring
theorem gap17 :
    AntiderivativesOn Set.univ originalIntegrand =
      PrimitiveFamilyOn Set.univ xPrimitive := by
  calc
    AntiderivativesOn Set.univ originalIntegrand = ScaledUFamily := gap15
    _ = PrimitiveFamilyOn Set.univ xPrimitive := gap16

end
end ProofGap.Exercise1976
