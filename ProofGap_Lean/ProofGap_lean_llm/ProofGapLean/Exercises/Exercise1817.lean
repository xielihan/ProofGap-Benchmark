import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1817

noncomputable section

def branch (a : ℝ) : Set ℝ := if a = 0 then Set.Ioi 0 else Set.univ
def integrand (a x : ℝ) := 1 / (a ^ 2 + x ^ 2) ^ 2
def zeroIntegrand (x : ℝ) := 1 / x ^ 4
def firstIntegrand (a x : ℝ) := 1 / (x ^ 2 + a ^ 2)
def residual (a x : ℝ) :=
  (x ^ 2 + a ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2) ^ 2
def zeroPrimitive (x : ℝ) := -1 / (3 * x ^ 3)
def firstPrimitive (a x : ℝ) := (1 / a) * Real.arctan (x / a)
def boundary (a x : ℝ) := x / (x ^ 2 + a ^ 2)
def primitive (a x : ℝ) :=
  1 / (2 * a ^ 2) *
    (boundary a x + (1 / a) * Real.arctan (x / a))
def AntiderivativesOn (a : ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch a, HasDerivAt F (f x) x}
def PrimitiveFamily (a : ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch a, F x = p x + C}
def ReductionFamily (a : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn a (residual a),
    ∀ x ∈ branch a, F x = boundary a x + 2 * G x}

private theorem branch_isOpen (a : ℝ) : IsOpen (branch a) := by
  unfold branch
  by_cases h : a = 0
  · rw [if_pos h]
    exact isOpen_Ioi
  · rw [if_neg h]
    exact isOpen_univ

private theorem denom_ne_zero (a x : ℝ) (ha : a ≠ 0) :
    x ^ 2 + a ^ 2 ≠ 0 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  nlinarith [sq_nonneg x]

private theorem hasDerivAt_of_eqOn_open
    {s : Set ℝ} (hs : IsOpen s) {F P : ℝ → ℝ} {x d : ℝ}
    (hx : x ∈ s) (hEq : ∀ y ∈ s, F y = P y)
    (hP : HasDerivAt P d x) : HasDerivAt F d x := by
  have hev : F =ᶠ[nhds x] P := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hEq y hy
  exact hP.congr_of_eventuallyEq hev

private theorem constantOn_branch_of_hasDerivAt_zero
    (a : ℝ) (q : ℝ → ℝ)
    (hq : ∀ x ∈ branch a, HasDerivAt q 0 x) :
    ∀ x ∈ branch a, ∀ y ∈ branch a, q x = q y := by
  by_cases ha : a = 0
  · let r : ℝ → ℝ := q ∘ Real.exp
    have hr : ∀ t : ℝ, HasDerivAt r 0 t := by
      intro t
      have ht : Real.exp t ∈ branch a := by
        simp [branch, ha, Real.exp_pos]
      simpa [r] using
        (hq (Real.exp t) ht).comp t (Real.hasDerivAt_exp t)
    have hc : ∀ u v : ℝ, r u = r v :=
      is_const_of_deriv_eq_zero
        (fun t => (hr t).differentiableAt)
        (fun t => (hr t).deriv)
    intro x hx y hy
    have hx' : 0 < x := by simpa [branch, ha] using hx
    have hy' : 0 < y := by simpa [branch, ha] using hy
    simpa [r, Real.exp_log hx', Real.exp_log hy'] using
      hc (Real.log x) (Real.log y)
  · have hr : ∀ x : ℝ, HasDerivAt q 0 x := by
      intro x
      exact hq x (by simp [branch, ha])
    have hc : ∀ u v : ℝ, q u = q v :=
      is_const_of_deriv_eq_zero
        (fun x => (hr x).differentiableAt)
        (fun x => (hr x).deriv)
    intro x hx y hy
    exact hc x y

private theorem antiderivatives_eq_primitive
    (a : ℝ) (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch a, HasDerivAt p (f x) x) :
    AntiderivativesOn a f = PrimitiveFamily a p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    let q : ℝ → ℝ := fun x => F x - p x
    have hq : ∀ x ∈ branch a, HasDerivAt q 0 x := by
      intro x hx
      simpa [q] using (hF x hx).sub (hp x hx)
    have hc := constantOn_branch_of_hasDerivAt_zero a q hq
    have h1 : (1 : ℝ) ∈ branch a := by
      simp [branch]
    refine ⟨q 1, ?_⟩
    intro x hx
    have hconst := hc x hx 1 h1
    dsimp [q] at hconst ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    exact hasDerivAt_of_eqOn_open (branch_isOpen a) hx hC
      ((hp x hx).add_const C)

private theorem hasDerivAt_zeroPrimitive (x : ℝ) (hx : 0 < x) :
    HasDerivAt zeroPrimitive (zeroIntegrand x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hd :=
    (hasDerivAt_const (x := x) (-1 : ℝ)).div
      ((hasDerivAt_const (x := x) (3 : ℝ)).mul
        ((hasDerivAt_id x).pow 3))
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hx0))
  convert hd using 1
  unfold zeroIntegrand
  field_simp [hx0] <;> simp <;> ring

private theorem hasDerivAt_firstPrimitive
    (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (firstPrimitive a) (firstIntegrand a x) x := by
  have hq : 1 + (x / a) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x / a)]
  have hd :=
    ((Real.hasDerivAt_arctan (x / a)).comp x
      ((hasDerivAt_id x).div_const a)).const_mul (1 / a)
  convert hd using 1
  unfold firstIntegrand
  field_simp [ha, hq] <;> ring

private theorem hasDerivAt_boundary
    (a x : ℝ) (hden : x ^ 2 + a ^ 2 ≠ 0) :
    HasDerivAt (boundary a)
      ((a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2) x := by
  have hd :=
    (hasDerivAt_id x).div
      (((hasDerivAt_id x).pow 2).add_const (a ^ 2)) hden
  convert hd using 1
  field_simp [hden] <;> simp <;> ring

private theorem hasDerivAt_primitive
    (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (primitive a) (integrand a x) x := by
  have hden : x ^ 2 + a ^ 2 ≠ 0 := denom_ne_zero a x ha
  have hd :=
    ((hasDerivAt_boundary a x hden).add
      (hasDerivAt_firstPrimitive a x ha)).const_mul (1 / (2 * a ^ 2))
  have hcoef :
      1 / (2 * a ^ 2) *
          ((a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2 +
            firstIntegrand a x) = integrand a x := by
    unfold firstIntegrand integrand
    have hden' : a ^ 2 + x ^ 2 ≠ 0 := by
      simpa [add_comm] using hden
    field_simp [ha, hden, hden']
    ring
  rw [hcoef] at hd
  convert hd using 1

theorem gap1 (a : ℝ) (ha : a = 0) :
    AntiderivativesOn a (integrand a) =
      AntiderivativesOn a zeroIntegrand := by
  subst a
  apply Set.ext
  intro F
  constructor
  · intro h x hx
    convert h x hx using 1
    unfold integrand zeroIntegrand
    ring
  · intro h x hx
    convert h x hx using 1
    unfold integrand zeroIntegrand
    ring
theorem gap2 (a : ℝ) (ha : a = 0) :
    AntiderivativesOn a zeroIntegrand =
      PrimitiveFamily a zeroPrimitive := by
  apply antiderivatives_eq_primitive
  intro x hx
  have hx' : 0 < x := by
    simpa [branch, ha] using hx
  exact hasDerivAt_zeroPrimitive x hx'
theorem gap3 (a : ℝ) (ha : a = 0) :
    AntiderivativesOn a (integrand a) =
      PrimitiveFamily a zeroPrimitive := by
  calc
    AntiderivativesOn a (integrand a) =
        AntiderivativesOn a zeroIntegrand := gap1 a ha
    _ = PrimitiveFamily a zeroPrimitive := gap2 a ha
theorem gap4 (a : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn a (firstIntegrand a) =
      PrimitiveFamily a (firstPrimitive a) := by
  apply antiderivatives_eq_primitive
  intro x hx
  exact hasDerivAt_firstPrimitive a x ha
theorem gap5 (a : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn a (firstIntegrand a) =
      ReductionFamily a := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨fun x => (F x - boundary a x) / 2, ?_, ?_⟩
    · intro x hx
      have hden : x ^ 2 + a ^ 2 ≠ 0 := denom_ne_zero a x ha
      have hd :=
        ((hF x hx).sub (hasDerivAt_boundary a x hden)).div_const 2
      have hcoef :
          (firstIntegrand a x -
              (a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2) / 2 =
            residual a x := by
        unfold firstIntegrand residual
        field_simp [hden]
        ring
      rw [hcoef] at hd
      exact hd
    · intro x hx
      ring
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have hden : x ^ 2 + a ^ 2 ≠ 0 := denom_ne_zero a x ha
    have hd :=
      (hasDerivAt_boundary a x hden).add ((hG x hx).const_mul 2)
    have hcoef :
        (a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2 +
            2 * residual a x = firstIntegrand a x := by
      unfold residual firstIntegrand
      field_simp [hden]
      ring
    rw [hcoef] at hd
    exact hasDerivAt_of_eqOn_open (branch_isOpen a) hx hEq hd
theorem gap6 (a : ℝ) (ha : a ≠ 0) :
    PrimitiveFamily a (firstPrimitive a) =
      ReductionFamily a := by
  exact (gap4 a ha).symm.trans (gap5 a ha)
theorem gap7 (a : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn a (integrand a) =
      PrimitiveFamily a (primitive a) := by
  apply antiderivatives_eq_primitive
  intro x hx
  exact hasDerivAt_primitive a x ha

end
end ProofGap.Exercise1817
