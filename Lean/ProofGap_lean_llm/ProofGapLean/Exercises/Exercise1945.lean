import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1945

noncomputable section

def branch (a : ℝ) : Set ℝ := {x | |x| < |a|}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, ∀ x ∈ s, F x = p x + K}
def integrand (a x : ℝ) := x ^ 4 * Real.sqrt (a ^ 2 - x ^ 2)
def rationalizedIntegrand (a x : ℝ) :=
  x ^ 4 * (a ^ 2 - x ^ 2) / Real.sqrt (a ^ 2 - x ^ 2)
def polynomialRhs (a A B C D E F lam x : ℝ) :=
  (5 * A * x ^ 4 + 4 * B * x ^ 3 + 3 * C * x ^ 2 +
    2 * D * x + E) * (a ^ 2 - x ^ 2) -
  x * (A * x ^ 5 + B * x ^ 4 + C * x ^ 3 + D * x ^ 2 + E * x + F) + lam
def CoeffIdentity (a A B C D E F lam : ℝ) : Prop :=
  ∀ x, x ^ 4 * (a ^ 2 - x ^ 2) = polynomialRhs a A B C D E F lam x
def primitive (a x : ℝ) :=
  (1 / 6 * x ^ 5 - a ^ 2 / 24 * x ^ 3 - a ^ 4 / 16 * x) *
      Real.sqrt (a ^ 2 - x ^ 2) +
    a ^ 6 / 16 * Real.arcsin (x / |a|)

private theorem coefficientEquations (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    6 * A - 1 = 0 ∧
    5 * B = 0 ∧
    (a ^ 2 - 5 * A * a ^ 2 + 4 * C = 0) ∧
    (3 * D - 4 * B * a ^ 2 = 0) ∧
    (2 * E - 3 * C * a ^ 2 = 0) ∧
    (F - 2 * D * a ^ 2 = 0) ∧
    (-E * a ^ 2 - lam = 0) := by
  have h0 := hpoly 0
  have h1 := hpoly 1
  have hm1 := hpoly (-1)
  have h2 := hpoly 2
  have hm2 := hpoly (-2)
  have h3 := hpoly 3
  have hm3 := hpoly (-3)
  norm_num [polynomialRhs] at h0 h1 hm1 h2 hm2 h3 hm3
  constructor
  · linarith [h0, h1, hm1, h2, hm2, h3, hm3]
  constructor
  · linarith [h0, h1, hm1, h2, hm2, h3, hm3]
  constructor
  · linarith [h0, h1, hm1, h2, hm2, h3, hm3]
  constructor
  · linarith [h0, h1, hm1, h2, hm2, h3, hm3]
  constructor
  · linarith [h0, h1, hm1, h2, hm2, h3, hm3]
  constructor
  · linarith [h0, h1, hm1, h2, hm2, h3, hm3]
  · linarith [h0, h1, hm1, h2, hm2, h3, hm3]

private theorem primitive_hasDerivAt (a x : ℝ) (hx : x ∈ branch a) :
    HasDerivAt (primitive a) (integrand a x) x := by
  have habs : |x| < |a| := hx
  have haabs : 0 < |a| := lt_of_le_of_lt (abs_nonneg x) habs
  have hbounds : -|a| < x ∧ x < |a| := (abs_lt.mp habs)
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    nlinarith [sq_lt_sq.mpr habs]
  have hsqrt_ne : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hsqrt_sq :
      Real.sqrt (a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 :=
    Real.sq_sqrt hrad.le
  have h2 := (hasDerivAt_id x).pow 2
  have h3 := (hasDerivAt_id x).pow 3
  have h5 := (hasDerivAt_id x).pow 5
  have hradfun :
      HasDerivAt (fun y : ℝ => a ^ 2 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (a ^ 2)).sub h2 using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt :=
    hradfun.sqrt (ne_of_gt hrad)
  have hpoly :=
    ((h5.const_mul (1 / 6 : ℝ)).sub
      (h3.const_mul (a ^ 2 / 24))).sub
      ((hasDerivAt_id x).const_mul (a ^ 4 / 16))
  have harg :
      HasDerivAt (fun y : ℝ => y / |a|) (1 / |a|) x := by
    convert (hasDerivAt_id x).div_const |a| using 1 <;> ring
  have hneg : x / |a| ≠ -1 := by
    intro h
    have : x = -|a| := by
      field_simp [ne_of_gt haabs] at h
      linarith
    linarith
  have hpos : x / |a| ≠ 1 := by
    intro h
    have : x = |a| := by
      field_simp [ne_of_gt haabs] at h
      linarith
    linarith
  have harcsin :=
    (Real.hasDerivAt_arcsin hneg hpos).comp x harg
  have hunit :
      1 - (x / |a|) ^ 2 = (a ^ 2 - x ^ 2) / a ^ 2 := by
    have ha : a ≠ 0 := abs_ne_zero.mp (ne_of_gt haabs)
    rw [div_pow, sq_abs]
    field_simp [ha]
  have harcsin' :
      HasDerivAt (fun y : ℝ => Real.arcsin (y / |a|))
        (1 / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    convert harcsin using 1
    rw [hunit, Real.sqrt_div hrad.le, Real.sqrt_sq_eq_abs]
    field_simp [ne_of_gt haabs, hsqrt_ne]
  have hraw :=
    (hpoly.mul hsqrt).add
      (harcsin'.const_mul (a ^ 6 / 16))
  unfold primitive integrand
  convert hraw using 1
  simp only [id_eq, Pi.pow_apply, Pi.sub_apply]
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]
  ring

theorem gap1 (a : ℝ) :
    AntiderivativesOn (branch a) (integrand a) =
      AntiderivativesOn (branch a) (rationalizedIntegrand a) := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    intro x hx
    have hrad : 0 < a ^ 2 - x ^ 2 := by
      have habs : |x| < |a| := hx
      nlinarith [sq_lt_sq.mpr habs]
    have hsqrt : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hrad)
    have hsq : Real.sqrt (a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 :=
      Real.sq_sqrt (le_of_lt hrad)
    have heq : rationalizedIntegrand a x = integrand a x := by
      unfold rationalizedIntegrand integrand
      apply (div_eq_iff hsqrt).2
      calc
        x ^ 4 * (a ^ 2 - x ^ 2) =
            x ^ 4 * Real.sqrt (a ^ 2 - x ^ 2) ^ 2 :=
          congrArg (fun t : ℝ => x ^ 4 * t) hsq.symm
        _ = x ^ 4 * Real.sqrt (a ^ 2 - x ^ 2) *
              Real.sqrt (a ^ 2 - x ^ 2) := by ring
    simpa [heq] using hF x hx
  · intro hF
    intro x hx
    have hrad : 0 < a ^ 2 - x ^ 2 := by
      have habs : |x| < |a| := hx
      nlinarith [sq_lt_sq.mpr habs]
    have hsqrt : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hrad)
    have hsq : Real.sqrt (a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 :=
      Real.sq_sqrt (le_of_lt hrad)
    have heq : rationalizedIntegrand a x = integrand a x := by
      unfold rationalizedIntegrand integrand
      apply (div_eq_iff hsqrt).2
      calc
        x ^ 4 * (a ^ 2 - x ^ 2) =
            x ^ 4 * Real.sqrt (a ^ 2 - x ^ 2) ^ 2 :=
          congrArg (fun t : ℝ => x ^ 4 * t) hsq.symm
        _ = x ^ 4 * Real.sqrt (a ^ 2 - x ^ 2) *
              Real.sqrt (a ^ 2 - x ^ 2) := by ring
    simpa [heq] using hF x hx
theorem gap2 (a : ℝ) :
    ∃ A B C D E F lam : ℝ, CoeffIdentity a A B C D E F lam := by
  refine ⟨1 / 6, 0, -a ^ 2 / 24, 0, -a ^ 4 / 16, 0, a ^ 6 / 16, ?_⟩
  intro x
  unfold polynomialRhs
  ring
theorem gap3 (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    A = 1 / 6 := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hlam⟩ :=
    coefficientEquations a A B C D E F lam hpoly
  linarith
theorem gap4 (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    B = 0 := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hlam⟩ :=
    coefficientEquations a A B C D E F lam hpoly
  linarith
theorem gap5 (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    C = -a ^ 2 / 24 := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hlam⟩ :=
    coefficientEquations a A B C D E F lam hpoly
  rw [show A = 1 / 6 by linarith] at hC
  nlinarith
theorem gap6 (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    D = 0 := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hlam⟩ :=
    coefficientEquations a A B C D E F lam hpoly
  rw [show B = 0 by linarith] at hD
  linarith
theorem gap7 (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    E = -a ^ 4 / 16 := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hlam⟩ :=
    coefficientEquations a A B C D E F lam hpoly
  rw [show A = 1 / 6 by linarith] at hC
  have hC' : C = -a ^ 2 / 24 := by
    nlinarith
  rw [hC'] at hE
  ring_nf at hE ⊢
  nlinarith
theorem gap8 (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    F = 0 := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hlam⟩ :=
    coefficientEquations a A B C D E F lam hpoly
  rw [show B = 0 by linarith] at hD
  have hD' : D = 0 := by
    linarith
  rw [hD'] at hF
  linarith
theorem gap9 (a A B C D E F lam : ℝ)
    (hpoly : CoeffIdentity a A B C D E F lam) :
    lam = a ^ 6 / 16 := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hlam⟩ :=
    coefficientEquations a A B C D E F lam hpoly
  rw [show A = 1 / 6 by linarith] at hC
  have hC' : C = -a ^ 2 / 24 := by
    nlinarith
  rw [hC'] at hE
  have hE' : E = -a ^ 4 / 16 := by
    ring_nf at hE ⊢
    nlinarith
  rw [hE'] at hlam
  ring_nf at hlam ⊢
  nlinarith
theorem gap10 (a : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn (branch a) (integrand a) =
      PrimitiveFamilyOn (branch a) (primitive a) := by
  have hopen : IsOpen (branch a) := by
    rw [show branch a = Set.Ioo (-|a|) |a| by
      ext x
      simp [branch, abs_lt]]
    exact isOpen_Ioo
  have hpre : IsPreconnected (branch a) := by
    rw [show branch a = Set.Ioo (-|a|) |a| by
      ext x
      simp [branch, abs_lt]]
    exact (convex_Ioo (-|a|) |a|).isPreconnected
  have hprimitive :
      ∀ x ∈ branch a, HasDerivAt (primitive a) (integrand a x) x := by
    intro x hx
    exact primitive_hasDerivAt a x hx
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch a, HasDerivAt F (integrand a x) x at hF
    change ∃ K : ℝ, ∀ x ∈ branch a, F x = primitive a x + K
    have hzero : ∀ x ∈ branch a,
        HasDerivAt (fun y => F y - primitive a y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprimitive x hx)
    have hdiff :
        DifferentiableOn ℝ (fun y => F y - primitive a y) (branch a) := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch a,
        deriv (fun y => F y - primitive a y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hzero_mem : (0 : ℝ) ∈ branch a := by
      change |(0 : ℝ)| < |a|
      simpa using abs_pos.mpr ha
    refine ⟨F 0 - primitive a 0, ?_⟩
    intro x hx
    have heq :
        F x - primitive a x = F 0 - primitive a 0 :=
      hopen.is_const_of_deriv_eq_zero hpre hdiff hderiv hx hzero_mem
    linarith
  · rintro ⟨K, hK⟩
    change ∀ x ∈ branch a, HasDerivAt F (integrand a x) x
    intro x hx
    apply ((hprimitive x hx).add_const K).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hK y hy

end
end ProofGap.Exercise1945
