import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1858

noncomputable section

def domain : Set ℝ := Set.Ioi (-1)

def integrand (x : ℝ) : ℝ :=
  1 / ((x + 1) * Real.sqrt (x ^ 2 + 1))

def shiftedIntegrand (x : ℝ) : ℝ :=
  1 / ((x + 1) * Real.sqrt ((x + 1) ^ 2 - 2 * (x + 1) + 2))

def reciprocalRewrite (x : ℝ) : ℝ :=
  1 / ((x + 1) * Real.sqrt (2 / (x + 1) ^ 2 - 2 / (x + 1) + 1) *
    (x + 1))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def substitutionPrimitive (x : ℝ) : ℝ :=
  -(1 / Real.sqrt 2) *
    Real.log |1 / (x + 1) - 1 / 2 +
      Real.sqrt ((x + 1) ^ 2 - 2 * (x + 1) + 2) /
        ((x + 1) * Real.sqrt 2)|

def primitive (x : ℝ) : ℝ :=
  -(1 / Real.sqrt 2) *
    Real.log |(1 - x + Real.sqrt (2 * (x ^ 2 + 1))) / (x + 1)|

private theorem integrand_eq_shifted (x : ℝ) :
    integrand x = shiftedIntegrand x := by
  unfold integrand shiftedIntegrand
  rw [show (x + 1) ^ 2 - 2 * (x + 1) + 2 = x ^ 2 + 1 by ring]

private theorem shifted_eq_reciprocal {x : ℝ} (hx : x ∈ domain) :
    shiftedIntegrand x = reciprocalRewrite x := by
  have hxm : -1 < x := by
    simpa only [domain, Set.mem_Ioi] using hx
  have ht : 0 < x + 1 := by linarith
  have ht0 : x + 1 ≠ 0 := ht.ne'
  let A : ℝ := 2 / (x + 1) ^ 2 - 2 / (x + 1) + 1
  let B : ℝ := (x + 1) ^ 2 - 2 * (x + 1) + 2
  have hB : 0 < B := by
    dsimp [B]
    nlinarith [sq_nonneg x]
  have hAeq : A = B / (x + 1) ^ 2 := by
    dsimp [A, B]
    field_simp [ht0]
    <;> ring
  have hA : 0 ≤ A := by
    rw [hAeq]
    positivity
  have hscale : A * (x + 1) ^ 2 = B := by
    rw [hAeq]
    field_simp [ht0]
  have hsquare : (Real.sqrt A * (x + 1)) ^ 2 = B := by
    rw [mul_pow, Real.sq_sqrt hA, hscale]
  have hroot : Real.sqrt A * (x + 1) = Real.sqrt B := by
    have hleft : 0 ≤ Real.sqrt A * (x + 1) :=
      mul_nonneg (Real.sqrt_nonneg A) ht.le
    have hright : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    have hright_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.le
    nlinarith
  unfold shiftedIntegrand reciprocalRewrite
  change 1 / ((x + 1) * Real.sqrt B) =
    1 / ((x + 1) * Real.sqrt A * (x + 1))
  rw [mul_assoc, hroot]

private theorem substitution_eq_primitive_add (x : ℝ) (hx : x ∈ domain) :
    substitutionPrimitive x =
      primitive x + (1 / Real.sqrt 2) * Real.log 2 := by
  have hxm : -1 < x := by
    simpa only [domain, Set.mem_Ioi] using hx
  have ht : 0 < x + 1 := by linarith
  have ht0 : x + 1 ≠ 0 := ht.ne'
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : 0 < x ^ 2 + 1 := by positivity
  have hr : 0 < 2 * (x ^ 2 + 1) := by positivity
  have hrsq : (Real.sqrt (2 * (x ^ 2 + 1))) ^ 2 = 2 * (x ^ 2 + 1) :=
    Real.sq_sqrt hr.le
  have hnum : 0 < 1 - x + Real.sqrt (2 * (x ^ 2 + 1)) := by
    have htt : 0 < (x + 1) ^ 2 := by positivity
    have hsnon : 0 ≤ Real.sqrt (2 * (x ^ 2 + 1)) := Real.sqrt_nonneg _
    by_contra hn
    have hle : Real.sqrt (2 * (x ^ 2 + 1)) ≤ x - 1 := by linarith
    have hx1 : 0 ≤ x - 1 := le_trans hsnon hle
    nlinarith
  have hp : 0 < (1 - x + Real.sqrt (2 * (x ^ 2 + 1))) / (x + 1) :=
    div_pos hnum ht
  have hrootmul :
      Real.sqrt (2 * (x ^ 2 + 1)) = Real.sqrt 2 * Real.sqrt (x ^ 2 + 1) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have harg :
      1 / (x + 1) - 1 / 2 +
          Real.sqrt ((x + 1) ^ 2 - 2 * (x + 1) + 2) /
            ((x + 1) * Real.sqrt 2) =
        ((1 - x + Real.sqrt (2 * (x ^ 2 + 1))) / (x + 1)) / 2 := by
    rw [show (x + 1) ^ 2 - 2 * (x + 1) + 2 = x ^ 2 + 1 by ring,
      hrootmul]
    field_simp [ht0, hs2.ne']
    nlinarith
  have hs : 0 <
      1 / (x + 1) - 1 / 2 +
        Real.sqrt ((x + 1) ^ 2 - 2 * (x + 1) + 2) /
          ((x + 1) * Real.sqrt 2) := by
    rw [harg]
    positivity
  unfold substitutionPrimitive primitive
  rw [abs_of_pos hs, abs_of_pos hp, harg, Real.log_div hp.ne' (by norm_num)]
  ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hxm : -1 < x := by
    simpa only [domain, Set.mem_Ioi] using hx
  have ht : 0 < x + 1 := by linarith
  have hq : 0 < x ^ 2 + 1 := by positivity
  have hr : 0 < 2 * (x ^ 2 + 1) := by positivity
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsr : 0 < Real.sqrt (2 * (x ^ 2 + 1)) := Real.sqrt_pos.2 hr
  have hsq : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 hq
  have hrootmul :
      Real.sqrt (2 * (x ^ 2 + 1)) = Real.sqrt 2 * Real.sqrt (x ^ 2 + 1) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrsq : (Real.sqrt (2 * (x ^ 2 + 1))) ^ 2 = 2 * (x ^ 2 + 1) :=
    Real.sq_sqrt hr.le
  have hnum : 0 < 1 - x + Real.sqrt (2 * (x ^ 2 + 1)) := by
    have htt : 0 < (x + 1) ^ 2 := by positivity
    have hsnon : 0 ≤ Real.sqrt (2 * (x ^ 2 + 1)) := Real.sqrt_nonneg _
    by_contra hn
    have hle : Real.sqrt (2 * (x ^ 2 + 1)) ≤ x - 1 := by linarith
    have hx1 : 0 ≤ x - 1 := le_trans hsnon hle
    nlinarith
  have hp : 0 < (1 - x + Real.sqrt (2 * (x ^ 2 + 1))) / (x + 1) :=
    div_pos hnum ht
  have hR : HasDerivAt (fun y : ℝ => 2 * (y ^ 2 + 1)) (4 * x) x := by
    convert (((hasDerivAt_id x).pow 2).add_const 1).const_mul 2 using 1
    <;> simp [id]
    <;> ring
  have hSraw : HasDerivAt (fun y : ℝ => Real.sqrt (2 * (y ^ 2 + 1)))
      ((1 / (2 * Real.sqrt (2 * (x ^ 2 + 1)))) * (4 * x)) x :=
    (Real.hasDerivAt_sqrt hr.ne').comp x hR
  have hS : HasDerivAt (fun y : ℝ => Real.sqrt (2 * (y ^ 2 + 1)))
      (2 * x / Real.sqrt (2 * (x ^ 2 + 1))) x := by
    convert hSraw using 1
    field_simp [hsr.ne'] <;> ring
  have hN : HasDerivAt
      (fun y : ℝ => 1 - y + Real.sqrt (2 * (y ^ 2 + 1)))
      (-1 + 2 * x / Real.sqrt (2 * (x ^ 2 + 1))) x := by
    convert ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add hS using 1
    <;> simp [id]
  have hT : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa [id] using (hasDerivAt_id x).add_const 1
  have hkey :
      (-1 + 2 * x / Real.sqrt (2 * (x ^ 2 + 1))) * (x + 1) -
          (1 - x + Real.sqrt (2 * (x ^ 2 + 1))) =
        -2 * (1 - x + Real.sqrt (2 * (x ^ 2 + 1))) /
          Real.sqrt (2 * (x ^ 2 + 1)) := by
    field_simp [hsr.ne']
    nlinarith [hrsq]
  have hP : HasDerivAt
      (fun y : ℝ => (1 - y + Real.sqrt (2 * (y ^ 2 + 1))) / (y + 1))
      ((-2 * (1 - x + Real.sqrt (2 * (x ^ 2 + 1))) /
          Real.sqrt (2 * (x ^ 2 + 1))) / (x + 1) ^ 2) x := by
    convert hN.div hT ht.ne' using 1
    rw [mul_one, hkey]
  have hlogcoef :
      ((-2 * (1 - x + Real.sqrt (2 * (x ^ 2 + 1))) /
            Real.sqrt (2 * (x ^ 2 + 1))) / (x + 1) ^ 2) /
          ((1 - x + Real.sqrt (2 * (x ^ 2 + 1))) / (x + 1)) =
        -2 / (Real.sqrt (2 * (x ^ 2 + 1)) * (x + 1)) := by
    field_simp [hnum.ne', ht.ne', hsr.ne'] <;> ring
  have hLog := hP.log hp.ne'
  rw [hlogcoef] at hLog
  have hfinalcoef :
      -(1 / Real.sqrt 2) *
          (-2 / (Real.sqrt (2 * (x ^ 2 + 1)) * (x + 1))) =
        1 / ((x + 1) * Real.sqrt (x ^ 2 + 1)) := by
    rw [hrootmul]
    field_simp [ht.ne', hs2.ne', hsq.ne']
    nlinarith [hs2sq]
  have hFinalRaw := hLog.const_mul (-(1 / Real.sqrt 2))
  rw [hfinalcoef] at hFinalRaw
  have hFinal : HasDerivAt
      (fun y : ℝ => -(1 / Real.sqrt 2) *
        Real.log ((1 - y + Real.sqrt (2 * (y ^ 2 + 1))) / (y + 1)))
      (integrand x) x := by
    simpa only [integrand] using hFinalRaw
  have hpos : ∀ᶠ y in nhds x,
      0 < (1 - y + Real.sqrt (2 * (y ^ 2 + 1))) / (y + 1) :=
    hP.continuousAt.eventually (Ioi_mem_nhds hp)
  have hev : primitive =ᶠ[nhds x]
      (fun y => -(1 / Real.sqrt 2) *
        Real.log ((1 - y + Real.sqrt (2 * (y ^ 2 + 1))) / (y + 1))) := by
    filter_upwards [hpos] with y hy
    unfold primitive
    rw [abs_of_pos hy]
  exact hFinal.congr_of_eventuallyEq hev

private theorem substitution_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt substitutionPrimitive (reciprocalRewrite x) x := by
  have hev : substitutionPrimitive =ᶠ[nhds x]
      (fun y => primitive y + (1 / Real.sqrt 2) * Real.log 2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact substitution_eq_primitive_add y hy
  have hbase : HasDerivAt
      (fun y => primitive y + (1 / Real.sqrt 2) * Real.log 2)
      (integrand x) x :=
    (primitive_hasDerivAt x hx).add_const ((1 / Real.sqrt 2) * Real.log 2)
  have hrec : integrand x = reciprocalRewrite x :=
    (integrand_eq_shifted x).trans (shifted_eq_reciprocal hx)
  rw [← hrec]
  exact hbase.congr_of_eventuallyEq hev

theorem gap1 : antiderivatives integrand = antiderivatives shiftedIntegrand := by
  ext F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hderiv x hx).trans (integrand_eq_shifted x)
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hderiv x hx).trans (integrand_eq_shifted x).symm

theorem gap2 :
    antiderivatives shiftedIntegrand = antiderivatives reciprocalRewrite := by
  ext F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [← shifted_eq_reciprocal hx]
    exact hderiv x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [shifted_eq_reciprocal hx]
    exact hderiv x hx

theorem gap3 :
    antiderivatives integrand = antiderivatives reciprocalRewrite := by
  exact gap1.trans gap2

theorem gap4 :
    antiderivatives reciprocalRewrite = primitiveFamily substitutionPrimitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    let H : ℝ → ℝ := fun x => F x - substitutionPrimitive x
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      have hFx : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      exact hFx.sub (substitution_hasDerivAt x hx).differentiableAt |>.differentiableWithinAt
    have hHzero : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      have hFx : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      have hd := hFx.hasDerivAt.sub (substitution_hasDerivAt x hx)
      simpa [H, hderiv x hx] using hd.deriv
    have hopen : IsOpen domain := by
      simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ)))
    have hpre : IsPreconnected domain := by
      simpa [domain] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (-1 : ℝ)))
    have hzero : (0 : ℝ) ∈ domain := by
      norm_num [domain]
    refine ⟨F 0 - substitutionPrimitive 0, ?_⟩
    intro x hx
    have hc : H x = H 0 :=
      hopen.is_const_of_deriv_eq_zero hpre hHdiff hHzero hx hzero
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hC⟩
    have hhas : ∀ x ∈ domain, HasDerivAt F (reciprocalRewrite x) x := by
      intro x hx
      have hev : F =ᶠ[nhds x] (fun y => substitutionPrimitive y + C) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact hC y hy
      exact ((substitution_hasDerivAt x hx).add_const C).congr_of_eventuallyEq hev
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv

theorem gap5 :
    primitiveFamily substitutionPrimitive = primitiveFamily primitive := by
  ext F
  simp only [primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + (1 / Real.sqrt 2) * Real.log 2, ?_⟩
    intro x hx
    rw [hC x hx, substitution_eq_primitive_add x hx]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - (1 / Real.sqrt 2) * Real.log 2, ?_⟩
    intro x hx
    rw [hC x hx, substitution_eq_primitive_add x hx]
    ring

theorem gap6 : antiderivatives integrand = primitiveFamily primitive := by
  exact gap3.trans (gap4.trans gap5)

end

end ProofGap.Exercise1858
