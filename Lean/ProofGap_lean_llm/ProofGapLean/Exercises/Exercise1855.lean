import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Set Real

namespace ProofGap.Exercise1855

noncomputable section

def radius : ℝ := Real.sqrt ((1 + Real.sqrt 5) / 2)

def domain : Set ℝ := Set.Ioo (-radius) radius

def integrand (x : ℝ) : ℝ :=
  (x + x ^ 3) / Real.sqrt (1 + x ^ 2 - x ^ 4)

def splitIntegrand (x : ℝ) : ℝ :=
  -x * (1 - 2 * x ^ 2) / (2 * Real.sqrt (1 + x ^ 2 - x ^ 4)) +
    (3 / 2 : ℝ) * x / Real.sqrt (1 + x ^ 2 - x ^ 4)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.sqrt (1 + x ^ 2 - x ^ 4) +
    (3 / 4 : ℝ) * Real.arcsin ((2 * x ^ 2 - 1) / Real.sqrt 5)

private lemma radicand_pos {x : ℝ} (hx : x ∈ domain) :
    0 < 1 + x ^ 2 - x ^ 4 := by
  have hs5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hphi : 0 < (1 + Real.sqrt 5) / 2 := by positivity
  have hphi_gt_one : 1 < (1 + Real.sqrt 5) / 2 := by
    nlinarith [hs5]
  have hphi_sq : ((1 + Real.sqrt 5) / 2) ^ 2 =
      (1 + Real.sqrt 5) / 2 + 1 := by
    nlinarith [hs5]
  have hradius : 0 < radius := by
    unfold radius
    exact Real.sqrt_pos.2 hphi
  have hradius_sq : radius ^ 2 = (1 + Real.sqrt 5) / 2 := by
    unfold radius
    exact Real.sq_sqrt (le_of_lt hphi)
  have hleft : 0 < radius + x := by
    dsimp [domain] at hx
    linarith [hx.1]
  have hprod : 0 < (radius - x) * (radius + x) := by
    apply mul_pos
    · dsimp [domain] at hx
      linarith [hx.2]
    · exact hleft
  have hxsq : x ^ 2 < (1 + Real.sqrt 5) / 2 := by
    nlinarith [hradius_sq, hprod]
  have hsecond : 0 < x ^ 2 + (1 + Real.sqrt 5) / 2 - 1 := by
    nlinarith [sq_nonneg x, hphi_gt_one]
  have hfactor :
      0 < ((1 + Real.sqrt 5) / 2 - x ^ 2) *
        (x ^ 2 + (1 + Real.sqrt 5) / 2 - 1) :=
    mul_pos (sub_pos.2 hxsq) hsecond
  calc
    0 < ((1 + Real.sqrt 5) / 2 - x ^ 2) *
        (x ^ 2 + (1 + Real.sqrt 5) / 2 - 1) := hfactor
    _ = 1 + x ^ 2 - x ^ 4 := by
      nlinarith [hphi_sq]

private lemma integrand_eq_split {x : ℝ} (hx : x ∈ domain) :
    integrand x = splitIntegrand x := by
  have hroot : 0 < Real.sqrt (1 + x ^ 2 - x ^ 4) :=
    Real.sqrt_pos.2 (radicand_pos hx)
  have hne : Real.sqrt (1 + x ^ 2 - x ^ 4) ≠ 0 := ne_of_gt hroot
  unfold integrand splitIntegrand
  field_simp [hne]
  ring

private lemma primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (splitIntegrand x) x := by
  let q : ℝ := 1 + x ^ 2 - x ^ 4
  have hqpos : 0 < q := by
    simpa [q] using radicand_pos hx
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hsqrtqne : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hqpos)
  have hqderiv :
      HasDerivAt (fun y : ℝ => 1 + y ^ 2 - y ^ 4) (2 * x - 4 * x ^ 3) x := by
    convert (((hasDerivAt_const (x := x) (c := (1 : ℝ))).add
      ((hasDerivAt_id x).pow 2)).sub ((hasDerivAt_id x).pow 4)) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrtq := (Real.hasDerivAt_sqrt hqne).comp x hqderiv
  have hfirst :
      HasDerivAt
        (fun y : ℝ => -(1 / 2 : ℝ) * Real.sqrt (1 + y ^ 2 - y ^ 4))
        (-x * (1 - 2 * x ^ 2) / (2 * Real.sqrt q)) x := by
    convert hsqrtq.const_mul (-(1 / 2 : ℝ)) using 1
    field_simp [hsqrtqne, q]
    ring
  have hs5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs5ne : Real.sqrt 5 ≠ 0 := ne_of_gt hs5pos
  let a : ℝ := 2 * x ^ 2 - 1
  have ha_identity : 5 - a ^ 2 = 4 * q := by
    dsimp [a, q]
    ring
  have ha_sq : a ^ 2 < (Real.sqrt 5) ^ 2 := by
    rw [hs5]
    nlinarith [ha_identity, hqpos]
  have ha_lower : -Real.sqrt 5 < a := by
    nlinarith [ha_sq, hs5pos]
  have ha_upper : a < Real.sqrt 5 := by
    nlinarith [ha_sq, hs5pos]
  have harange : a / Real.sqrt 5 ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ hs5pos).2 (by nlinarith [ha_lower])
    · exact (div_lt_iff₀ hs5pos).2
        (by simpa only [one_mul] using ha_upper)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 - 1) (4 * x) x := by
    convert (((hasDerivAt_const (x := x) (c := (2 : ℝ))).mul
      ((hasDerivAt_id x).pow 2)).sub
        (hasDerivAt_const (x := x) (c := (1 : ℝ)))) using 1 <;>
      simp only [id_eq] <;> ring
  have hu :
      HasDerivAt (fun y : ℝ => (2 * y ^ 2 - 1) / Real.sqrt 5)
        (4 * x / Real.sqrt 5) x := by
    simpa using hnum.div_const (Real.sqrt 5)
  have hinside_eq : 1 - (a / Real.sqrt 5) ^ 2 = 4 * q / 5 := by
    calc
      1 - (a / Real.sqrt 5) ^ 2 =
          ((Real.sqrt 5) ^ 2 - a ^ 2) / (Real.sqrt 5) ^ 2 := by
            field_simp [hs5ne]
      _ = (5 - a ^ 2) / 5 := by rw [hs5]
      _ = 4 * q / 5 := by rw [ha_identity]
  have hinside_pos : 0 < 1 - (a / Real.sqrt 5) ^ 2 := by
    rw [hinside_eq]
    positivity
  have hsqrtq_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (le_of_lt hqpos)
  have hrhs_sq : (2 * Real.sqrt q / Real.sqrt 5) ^ 2 = 4 * q / 5 := by
    calc
      (2 * Real.sqrt q / Real.sqrt 5) ^ 2 =
          4 * (Real.sqrt q) ^ 2 / (Real.sqrt 5) ^ 2 := by ring
      _ = 4 * q / 5 := by rw [hsqrtq_sq, hs5]
  have hroot_identity :
      Real.sqrt (1 - (a / Real.sqrt 5) ^ 2) =
        2 * Real.sqrt q / Real.sqrt 5 := by
    have hleft_sq := Real.sq_sqrt (le_of_lt hinside_pos)
    have hleft_nonneg := Real.sqrt_nonneg (1 - (a / Real.sqrt 5) ^ 2)
    have hright_nonneg : 0 ≤ 2 * Real.sqrt q / Real.sqrt 5 := by positivity
    nlinarith [hleft_sq, hinside_eq, hrhs_sq]
  have harcsin :=
    (Real.hasDerivAt_arcsin (ne_of_gt harange.1) (ne_of_lt harange.2)).comp x hu
  have hsecond :
      HasDerivAt
        (fun y : ℝ => (3 / 4 : ℝ) *
          Real.arcsin ((2 * y ^ 2 - 1) / Real.sqrt 5))
        ((3 / 2 : ℝ) * x / Real.sqrt q) x := by
    convert harcsin.const_mul (3 / 4 : ℝ) using 1
    rw [hroot_identity]
    field_simp [hs5ne, hsqrtqne]
  have hsum := hfirst.add hsecond
  have hfun :
      (fun y : ℝ => -(1 / 2 : ℝ) * Real.sqrt (1 + y ^ 2 - y ^ 4)) +
        (fun y : ℝ => (3 / 4 : ℝ) *
          Real.arcsin ((2 * y ^ 2 - 1) / Real.sqrt 5)) = primitive := by
    funext y
    rfl
  rw [hfun] at hsum
  simpa only [splitIntegrand, q] using hsum

theorem gap1 : antiderivatives integrand = antiderivatives splitIntegrand := by
  ext F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    rw [hderiv x hx, integrand_eq_split hx]
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    rw [hderiv x hx, ← integrand_eq_split hx]

theorem gap2 :
    antiderivatives splitIntegrand = primitiveFamily primitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  have hopen : IsOpen domain := by
    change IsOpen (Set.Ioo (-radius) radius)
    exact isOpen_Ioo
  constructor
  · rintro ⟨hF, hderiv⟩
    have hprim : DifferentiableOn ℝ primitive domain :=
      fun x hx => (primitive_hasDerivAt hx).differentiableAt.differentiableWithinAt
    have hdiff : DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hF.sub hprim
    have hzero :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (hopen.mem_nhds hx)
      have hd := hFa.hasDerivAt.sub (primitive_hasDerivAt hx)
      simpa [hderiv x hx] using hd.deriv
    have hradius : 0 < radius := by
      unfold radius
      apply Real.sqrt_pos.2
      positivity
    have h0 : (0 : ℝ) ∈ domain := by
      simp [domain, hradius]
    refine ⟨F 0 - primitive 0, fun x hx => ?_⟩
    have heq : F x - primitive x = F 0 - primitive 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hx h0
    linarith
  · rintro ⟨C, hC⟩
    have hFx : ∀ x ∈ domain, HasDerivAt F (splitIntegrand x) x := by
      intro x hx
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) :=
        Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => hC y hy)
      exact ((primitive_hasDerivAt hx).add_const C).congr_of_eventuallyEq hevent
    refine ⟨fun x hx => (hFx x hx).differentiableAt.differentiableWithinAt, ?_⟩
    intro x hx
    exact (hFx x hx).deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  rw [gap1, gap2]

end

end ProofGap.Exercise1855
