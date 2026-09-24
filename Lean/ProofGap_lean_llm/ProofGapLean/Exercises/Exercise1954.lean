import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1954

noncomputable section

def q (x : ℝ) := x ^ 2 + x + 1
def branch : Set ℝ := {x | x ≠ -1}
def parameterBranch : Set ℝ := {t | t ≠ 0}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def integrand (x : ℝ) := Real.sqrt (q x) / (x + 1) ^ 2
def rationalized (x : ℝ) := q x / (x + 1) ^ 2 / Real.sqrt (q x)
def i1 (x : ℝ) := 1 / Real.sqrt (q x)
def i2 (x : ℝ) := 1 / ((x + 1) * Real.sqrt (q x))
def i3 (x : ℝ) := 1 / ((x + 1) ^ 2 * Real.sqrt (q x))
def xOf (t : ℝ) := -1 + 1 / t
def I1 := AntiderivativesOn Set.univ i1
def I2 := AntiderivativesOn branch i2
def I3 := AntiderivativesOn branch i3
def PullbackI3Family : Set (ℝ → ℝ) :=
  {G | ∃ F ∈ I3, ∀ t ∈ parameterBranch, G t = F (xOf t)}
def ThreePartFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ I1, ∃ B ∈ I2, ∃ D ∈ I3,
    ∀ x ∈ branch, F x = A x - B x + D x}
def primitiveI1 (x : ℝ) :=
  Real.log (x + 1 / 2 + Real.sqrt (q x))
def primitiveI2 (x : ℝ) :=
  -Real.log |(1 - x + 2 * Real.sqrt (q x)) / (x + 1)|
def qT (t : ℝ) := t ^ 2 - t + 1
def NegativeI3Family : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn parameterBranch
      (fun t => |t| / Real.sqrt (qT t)),
    ∀ t ∈ parameterBranch, F t = -G t}
def SplitI3Family : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn parameterBranch
      (fun t => Real.sign t * (2 * t - 1) / Real.sqrt (qT t)),
    ∃ B ∈ AntiderivativesOn parameterBranch
      (fun t => Real.sign t / Real.sqrt (qT t)),
    ∀ t ∈ parameterBranch, F t = -1 / 2 * A t - 1 / 2 * B t}
def primitiveI3T (t : ℝ) :=
  -Real.sign t * (Real.sqrt (qT t) +
    1 / 2 * Real.log |t - 1 / 2 + Real.sqrt (qT t)|)
def primitiveI3X (x : ℝ) :=
  -Real.sqrt (q x) / (x + 1) -
    1 / 2 * Real.log |(1 - x + 2 * Real.sqrt (q x)) / (x + 1)|
def finalPrimitive (x : ℝ) :=
  Real.log (x + 1 / 2 + Real.sqrt (q x)) -
    Real.sqrt (q x) / (x + 1) +
    1 / 2 * Real.log |(1 - x + 2 * Real.sqrt (q x)) / (x + 1)|
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn branch
      (fun x => Real.sqrt (q x) * deriv (fun y => 1 / (y + 1)) x),
    ∀ x ∈ branch, F x = -G x}
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn branch
      (fun x => (x + 1 / 2) / ((x + 1) * Real.sqrt (q x))),
    ∀ x ∈ branch, F x = -Real.sqrt (q x) / (x + 1) + G x}

theorem gap1 :
    AntiderivativesOn branch integrand =
      AntiderivativesOn branch rationalized := by
  ext F
  constructor
  · intro h x hx
    have hx1 : x + 1 ≠ 0 := by
      intro hx1
      apply hx
      linarith
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    convert h x hx using 1
    unfold integrand rationalized
    field_simp [hx1, hs]
    nlinarith [Real.sq_sqrt hq.le]
  · intro h x hx
    have hx1 : x + 1 ≠ 0 := by
      intro hx1
      apply hx
      linarith
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    convert h x hx using 1
    unfold integrand rationalized
    field_simp [hx1, hs]
    nlinarith [Real.sq_sqrt hq.le]

private lemma early_primitiveI1_hasDerivAt (x : ℝ) :
    HasDerivAt primitiveI1 (i1 x) x := by
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hs0 : 0 ≤ Real.sqrt (q x) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q x)) ^ 2 = x ^ 2 + x + 1 := by
    calc
      (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
      _ = x ^ 2 + x + 1 := rfl
  have hq' : HasDerivAt q (2 * x + 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).add
      (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((x + 1 / 2) / Real.sqrt (q x)) x := by
    have hd := (Real.hasDerivAt_sqrt hq.ne').comp x hq'
    convert hd using 1 <;> field_simp [hs] <;> ring
  have hu0 : 0 < x + 1 / 2 + Real.sqrt (q x) := by
    by_contra h
    have hsum : x + 1 / 2 + Real.sqrt (q x) ≤ 0 := le_of_not_gt h
    have hleft : 0 ≤ -(x + 1 / 2 + Real.sqrt (q x)) := by linarith
    have hright : 0 ≤ -(x + 1 / 2) + Real.sqrt (q x) := by linarith
    have hprod := mul_nonneg hleft hright
    unfold q at hsq hprod
    nlinarith
  have hu : HasDerivAt
      (fun y => y + 1 / 2 + Real.sqrt (q y))
      ((x + 1 / 2 + Real.sqrt (q x)) / Real.sqrt (q x)) x := by
    convert ((hasDerivAt_id x).add_const (1 / 2)).add hsqrt using 1 <;>
      field_simp [hs] <;> ring
  unfold primitiveI1 i1
  have hd := (Real.hasDerivAt_log hu0.ne').comp x hu
  have hcoef :
      (x + 1 / 2 + Real.sqrt (q x))⁻¹ *
          ((x + 1 / 2 + Real.sqrt (q x)) / Real.sqrt (q x)) =
        1 / Real.sqrt (q x) := by
    have hu2 : x * 2 + 1 + 2 * Real.sqrt (q x) ≠ 0 := by
      nlinarith [hu0]
    field_simp [hs, hu0.ne', hu2]
  rw [hcoef] at hd
  simpa [Function.comp_def] using hd

private lemma early_i2Numerator_pos (x : ℝ) :
    0 < 1 - x + 2 * Real.sqrt (q x) := by
  by_cases hx : x = -1
  · subst x
    norm_num [q]
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs0 : 0 ≤ Real.sqrt (q x) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  by_contra h
  have hn : 1 - x + 2 * Real.sqrt (q x) ≤ 0 := le_of_not_gt h
  have hxge : 1 ≤ x := by nlinarith
  have hleft : 0 ≤ x - 1 - 2 * Real.sqrt (q x) := by linarith
  have hright : 0 ≤ x - 1 + 2 * Real.sqrt (q x) := by nlinarith
  have hprod := mul_nonneg hleft hright
  have hx1sq : 0 < (x + 1) ^ 2 := sq_pos_of_ne_zero hx1
  unfold q at hsq hprod
  nlinarith

private lemma early_primitiveI2_eq_on (x : ℝ) (hx : x ∈ branch) :
    primitiveI2 x =
      -Real.log (1 - x + 2 * Real.sqrt (q x)) +
        Real.log (x + 1) := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hn := early_i2Numerator_pos x
  unfold primitiveI2
  rw [Real.log_abs, Real.log_div hn.ne' hx1]
  ring

private lemma early_branch_isOpen : IsOpen branch := by
  rw [show branch = ({-1} : Set ℝ)ᶜ by
    ext x
    simp [branch]]
  exact isClosed_singleton.isOpen_compl

private lemma early_primitiveI2_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveI2 (i2 x) x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hsq : (Real.sqrt (q x)) ^ 2 = x ^ 2 + x + 1 := by
    calc
      (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
      _ = x ^ 2 + x + 1 := rfl
  have hq' : HasDerivAt q (2 * x + 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).add
      (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x + 1) / (2 * Real.sqrt (q x))) x := by
    have hd := (Real.hasDerivAt_sqrt hq.ne').comp x hq'
    convert hd using 1 <;> field_simp [hs] <;> ring
  have hn0 : 0 < 1 - x + 2 * Real.sqrt (q x) :=
    early_i2Numerator_pos x
  have hn : HasDerivAt
      (fun y => 1 - y + 2 * Real.sqrt (q y))
      (-1 + (2 * x + 1) / Real.sqrt (q x)) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).sub
      (hasDerivAt_id x)).add (hsqrt.const_mul 2) using 1 <;>
      field_simp [hs] <;> ring
  have hlogn := (Real.hasDerivAt_log hn0.ne').comp x hn
  have hden : HasDerivAt (fun y => Real.log (y + 1))
      (1 / (x + 1)) x := by
    have hd := (Real.hasDerivAt_log hx1).comp x
      ((hasDerivAt_id x).add_const 1)
    simpa [one_div] using hd
  have hd := hlogn.neg.add hden
  have hcoef :
      -((1 - x + 2 * Real.sqrt (q x))⁻¹ *
          (-1 + (2 * x + 1) / Real.sqrt (q x))) +
          1 / (x + 1) = i2 x := by
    unfold i2
    field_simp [hx1, hs, hn0.ne']
    nlinarith [hsq]
  rw [hcoef] at hd
  have heq : primitiveI2 =ᶠ[nhds x]
      fun y => -Real.log (1 - y + 2 * Real.sqrt (q y)) +
        Real.log (y + 1) := by
    filter_upwards [early_branch_isOpen.mem_nhds hx] with y hy
    exact early_primitiveI2_eq_on y hy
  exact hd.congr_of_eventuallyEq heq

private lemma integrand_eq_three_parts (x : ℝ) (hx : x ∈ branch) :
    integrand x = i1 x - i2 x + i3 x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hsq : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt hq.le
  unfold integrand i1 i2 i3
  field_simp [hx1, hs]
  rw [hsq]
  unfold q
  ring
theorem gap2 :
    AntiderivativesOn branch integrand = ThreePartFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨primitiveI1, ?_, primitiveI2, ?_,
      fun y => F y - primitiveI1 y + primitiveI2 y, ?_, ?_⟩
    · intro x _
      exact early_primitiveI1_hasDerivAt x
    · exact early_primitiveI2_hasDerivAt
    · intro x hx
      have hd := (hF x hx).sub (early_primitiveI1_hasDerivAt x) |>.add
        (early_primitiveI2_hasDerivAt x hx)
      convert hd using 1
      rw [integrand_eq_three_parts x hx]
      ring
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, D, hD, hF⟩ x hx
    have hd := (hA x (Set.mem_univ x)).sub (hB x hx) |>.add (hD x hx)
    rw [← integrand_eq_three_parts x hx] at hd
    have heq : F =ᶠ[nhds x] fun y => A y - B y + D y := by
      filter_upwards [early_branch_isOpen.mem_nhds hx] with y hy
      exact hF y hy
    exact hd.congr_of_eventuallyEq heq
theorem gap3 :
    ∃ A B D : Set (ℝ → ℝ),
      A = I1 ∧ B = I2 ∧ D = I3 ∧ ThreePartFamily = ThreePartFamily := by
  exact ⟨I1, I2, I3, rfl, rfl, rfl, rfl⟩
theorem gap4 :
    ∃ A B D : Set (ℝ → ℝ),
      A = I1 ∧ B = I2 ∧ D = I3 ∧
        AntiderivativesOn branch integrand = ThreePartFamily := by
  exact ⟨I1, I2, I3, rfl, rfl, rfl, gap2⟩
theorem gap5 :
    ∃ A : Set (ℝ → ℝ), A = I1 := by
  exact ⟨I1, rfl⟩

private lemma primitiveI1_hasDerivAt (x : ℝ) :
    HasDerivAt primitiveI1 (i1 x) x := by
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hs0 : 0 ≤ Real.sqrt (q x) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  have hsq' : (Real.sqrt (q x)) ^ 2 = x ^ 2 + x + 1 := by
    calc
      (Real.sqrt (q x)) ^ 2 = q x := hsq
      _ = x ^ 2 + x + 1 := rfl
  have hq' : HasDerivAt q (2 * x + 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((x + 1 / 2) / Real.sqrt (q x)) x := by
    have hd := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hq'
    convert hd using 1 <;> field_simp [hs] <;> ring
  have hu0 : 0 < x + 1 / 2 + Real.sqrt (q x) := by
    by_contra h
    have hsum : x + 1 / 2 + Real.sqrt (q x) ≤ 0 := le_of_not_gt h
    have hleft : 0 ≤ -(x + 1 / 2 + Real.sqrt (q x)) := by linarith
    have hright : 0 ≤ -(x + 1 / 2) + Real.sqrt (q x) := by linarith
    have hprod := mul_nonneg hleft hright
    unfold q at hsq hprod
    nlinarith
  have hu : HasDerivAt
      (fun y => y + 1 / 2 + Real.sqrt (q y))
      ((x + 1 / 2 + Real.sqrt (q x)) / Real.sqrt (q x)) x := by
    convert ((hasDerivAt_id x).add_const (1 / 2)).add hsqrt using 1 <;>
      field_simp [hs] <;> ring
  unfold primitiveI1 i1
  have hd := (Real.hasDerivAt_log hu0.ne').comp x hu
  have hcoef :
      (x + 1 / 2 + Real.sqrt (q x))⁻¹ *
          ((x + 1 / 2 + Real.sqrt (q x)) / Real.sqrt (q x)) =
        1 / Real.sqrt (q x) := by
    have hu2 : x * 2 + 1 + 2 * Real.sqrt (q x) ≠ 0 := by
      nlinarith [hu0]
    field_simp [hs, hu0.ne', hu2]
  rw [hcoef] at hd
  simpa [Function.comp_def] using hd
theorem gap6 :
    I1 = PrimitiveFamilyOn Set.univ primitiveI1 := by
  ext F
  constructor
  · intro hF
    have hzero : ∀ x : ℝ,
        HasDerivAt (fun y => F y - primitiveI1 y) 0 x := by
      intro x
      convert (hF x (Set.mem_univ x)).sub (primitiveI1_hasDerivAt x) using 1 <;>
        ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitiveI1 y) Set.univ :=
      fun x _ => (hzero x).differentiableAt.differentiableWithinAt
    have hderiv : Set.univ.EqOn
        (deriv (fun y => F y - primitiveI1 y)) 0 :=
      fun x _ => (hzero x).deriv
    obtain ⟨C, hC⟩ :=
      isOpen_univ.exists_is_const_of_deriv_eq_zero isPreconnected_univ hdiff hderiv
    exact ⟨C, fun x _ => by
      have hxC : F x - primitiveI1 x = C := hC x (Set.mem_univ x)
      linarith⟩
  · rintro ⟨C, hFC⟩ x hx
    have heq : F = fun y => primitiveI1 y + C := by
      funext y
      exact hFC y (Set.mem_univ y)
    rw [heq]
    exact (primitiveI1_hasDerivAt x).add_const C
theorem gap7 :
    ∃ A : Set (ℝ → ℝ), A = PrimitiveFamilyOn Set.univ primitiveI1 := by
  exact ⟨PrimitiveFamilyOn Set.univ primitiveI1, rfl⟩
theorem gap8 :
    ∃ B : Set (ℝ → ℝ), B = I2 := by
  exact ⟨I2, rfl⟩

private lemma i2Numerator_pos (x : ℝ) :
    0 < 1 - x + 2 * Real.sqrt (q x) := by
  by_cases hx : x = -1
  · subst x
    norm_num [q]
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs0 : 0 ≤ Real.sqrt (q x) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  by_contra h
  have hn : 1 - x + 2 * Real.sqrt (q x) ≤ 0 := le_of_not_gt h
  have hxge : 1 ≤ x := by nlinarith
  have hleft : 0 ≤ x - 1 - 2 * Real.sqrt (q x) := by linarith
  have hright : 0 ≤ x - 1 + 2 * Real.sqrt (q x) := by nlinarith
  have hprod := mul_nonneg hleft hright
  have hx1sq : 0 < (x + 1) ^ 2 := sq_pos_of_ne_zero hx1
  unfold q at hsq hprod
  nlinarith

private lemma primitiveI2_eq_on (x : ℝ) (hx : x ∈ branch) :
    primitiveI2 x =
      -Real.log (1 - x + 2 * Real.sqrt (q x)) + Real.log (x + 1) := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hn := i2Numerator_pos x
  unfold primitiveI2
  rw [Real.log_abs, Real.log_div hn.ne' hx1]
  ring

private lemma branch_isOpen_early : IsOpen branch := by
  rw [show branch = ({-1} : Set ℝ)ᶜ by
    ext x
    simp [branch]]
  exact isClosed_singleton.isOpen_compl

private lemma primitiveI2_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveI2 (i2 x) x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hs0 : 0 ≤ Real.sqrt (q x) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  have hsq' : (Real.sqrt (q x)) ^ 2 = x ^ 2 + x + 1 := by
    calc
      (Real.sqrt (q x)) ^ 2 = q x := hsq
      _ = x ^ 2 + x + 1 := rfl
  have hq' : HasDerivAt q (2 * x + 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x + 1) / (2 * Real.sqrt (q x))) x := by
    have hd := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hq'
    convert hd using 1 <;> field_simp [hs] <;> ring
  have hn0 : 0 < 1 - x + 2 * Real.sqrt (q x) := i2Numerator_pos x
  have hn : HasDerivAt
      (fun y => 1 - y + 2 * Real.sqrt (q y))
      (-1 + (2 * x + 1) / Real.sqrt (q x)) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      (hsqrt.const_mul 2) using 1 <;> field_simp [hs] <;> ring
  have hlogn := (Real.hasDerivAt_log hn0.ne').comp x hn
  have hden : HasDerivAt (fun y => Real.log (y + 1)) (1 / (x + 1)) x := by
    have hd := (Real.hasDerivAt_log hx1).comp x ((hasDerivAt_id x).add_const 1)
    simpa [one_div] using hd
  have hd := hlogn.neg.add hden
  have hcoef :
      -((1 - x + 2 * Real.sqrt (q x))⁻¹ *
          (-1 + (2 * x + 1) / Real.sqrt (q x))) +
          1 / (x + 1) =
        i2 x := by
    unfold i2
    field_simp [hx1, hs, hn0.ne']
    nlinarith [hsq']
  rw [hcoef] at hd
  have heq : primitiveI2 =ᶠ[nhds x]
      fun y => -Real.log (1 - y + 2 * Real.sqrt (q y)) + Real.log (y + 1) := by
    filter_upwards [branch_isOpen_early.mem_nhds hx] with y hy
    exact primitiveI2_eq_on y hy
  exact hd.congr_of_eventuallyEq heq
theorem gap9 :
    I2 = BranchwisePrimitiveFamilyOn branch primitiveI2 := by
  ext F
  constructor
  · intro hF u huopen huconn hus
    have hzero : ∀ x ∈ u,
        HasDerivAt (fun y => F y - primitiveI2 y) 0 x := by
      intro x hx
      convert (hF x (hus hx)).sub (primitiveI2_hasDerivAt x (hus hx)) using 1 <;>
        ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitiveI2 y) u :=
      fun x hx => (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : u.EqOn (deriv (fun y => F y - primitiveI2 y)) 0 :=
      fun x hx => (hzero x hx).deriv
    obtain ⟨C, hC⟩ :=
      huopen.exists_is_const_of_deriv_eq_zero huconn hdiff hderiv
    exact ⟨C, fun x hx => by
      have hxC : F x - primitiveI2 x = C := hC x hx
      linarith⟩
  · intro hF x hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · obtain ⟨C, hC⟩ := hF (Set.Iio (-1)) isOpen_Iio isPreconnected_Iio
        (by
          intro y hy
          exact ne_of_lt hy) 
      have heq : F =ᶠ[nhds x] fun y => primitiveI2 y + C := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        exact hC y hy
      exact (primitiveI2_hasDerivAt x hx).add_const C |>.congr_of_eventuallyEq heq
    · obtain ⟨C, hC⟩ := hF (Set.Ioi (-1)) isOpen_Ioi isPreconnected_Ioi
        (by
          intro y hy
          exact ne_of_gt hy)
      have heq : F =ᶠ[nhds x] fun y => primitiveI2 y + C := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        exact hC y hy
      exact (primitiveI2_hasDerivAt x hx).add_const C |>.congr_of_eventuallyEq heq
theorem gap10 :
    ∃ B : Set (ℝ → ℝ),
      B = BranchwisePrimitiveFamilyOn branch primitiveI2 := by
  exact ⟨BranchwisePrimitiveFamilyOn branch primitiveI2, rfl⟩
theorem gap11 :
    ∃ X : ℝ → ℝ, X = xOf ∧
      ∀ t ∈ parameterBranch, HasDerivAt X (-1 / t ^ 2) t := by
  refine ⟨xOf, rfl, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := ht
  unfold xOf
  convert (hasDerivAt_const t (-1 : ℝ)).add
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0) using 1 <;>
    simp [id] <;> field_simp [ht0] <;> ring
theorem gap12 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (q (xOf t)) = Real.sqrt (qT t) / |t| := by
  have ht0 : t ≠ 0 := ht
  have hrad : 0 < qT t := by
    unfold qT
    nlinarith [sq_nonneg (t - 1 / 2)]
  have hq : q (xOf t) = qT t / t ^ 2 := by
    unfold q qT xOf
    field_simp [ht0]
    ring
  rw [hq, Real.sqrt_div hrad.le, Real.sqrt_sq_eq_abs]

private lemma pullbackI3_coefficient (t : ℝ) (ht : t ∈ parameterBranch) :
    i3 (xOf t) * (-1 / t ^ 2) =
      -(|t| / Real.sqrt (qT t)) := by
  have ht0 : t ≠ 0 := ht
  have habs0 : |t| ≠ 0 := abs_ne_zero.mpr ht0
  have hqT : 0 < qT t := by
    unfold qT
    nlinarith [sq_nonneg (t - 1 / 2)]
  have hs : Real.sqrt (qT t) ≠ 0 := (Real.sqrt_pos.2 hqT).ne'
  unfold i3
  rw [gap12 t ht]
  unfold xOf
  field_simp [ht0, habs0, hs]
  nlinarith [sq_abs t]

private lemma parameterBranch_isOpen : IsOpen parameterBranch := by
  rw [show parameterBranch = ({0} : Set ℝ)ᶜ by
    ext t
    simp [parameterBranch]]
  exact isClosed_singleton.isOpen_compl
theorem gap13 :
    PullbackI3Family = NegativeI3Family := by
  ext P
  constructor
  · rintro ⟨F, hF, hPF⟩
    refine ⟨fun t => -P t, ?_, ?_⟩
    · intro t ht
      have ht0 : t ≠ 0 := ht
      have hxt : xOf t ∈ branch := by
        change xOf t ≠ -1
        unfold xOf
        intro h
        have hzero : 1 / t = 0 := by linarith
        exact (one_div_ne_zero ht0) hzero
      have hxd : HasDerivAt xOf (-1 / t ^ 2) t := by
        rcases gap11 with ⟨X, hX, hder⟩
        subst X
        exact hder t ht
      have hcomp := (hF (xOf t) hxt).comp t hxd
      rw [pullbackI3_coefficient t ht] at hcomp
      have heq : P =ᶠ[nhds t] fun y => F (xOf y) := by
        filter_upwards [parameterBranch_isOpen.mem_nhds ht] with y hy
        exact hPF y hy
      have hP : HasDerivAt P (-(|t| / Real.sqrt (qT t))) t :=
        hcomp.congr_of_eventuallyEq heq
      convert hP.neg using 1 <;> ring
    · intro t ht
      ring
  · rintro ⟨G, hG, hPG⟩
    let tOf : ℝ → ℝ := fun x => 1 / (x + 1)
    refine ⟨fun x => P (tOf x), ?_, ?_⟩
    · intro x hx
      have hx1 : x + 1 ≠ 0 := by
        intro h
        apply hx
        linarith
      have htmem : tOf x ∈ parameterBranch := by
        dsimp [tOf, parameterBranch]
        exact one_div_ne_zero hx1
      have htder : HasDerivAt tOf (-1 / (x + 1) ^ 2) x := by
        dsimp [tOf]
        convert (hasDerivAt_const x (1 : ℝ)).div
          ((hasDerivAt_id x).add_const 1) hx1 using 1 <;>
          simp [id] <;> field_simp [hx1] <;> ring
      have hP : HasDerivAt P
          (- (|tOf x| / Real.sqrt (qT (tOf x)))) (tOf x) := by
        have heq : P =ᶠ[nhds (tOf x)] fun y => -G y := by
          filter_upwards [parameterBranch_isOpen.mem_nhds htmem] with y hy
          exact hPG y hy
        exact (hG (tOf x) htmem).neg.congr_of_eventuallyEq heq
      have hcomp := hP.comp x htder
      have hxo : xOf (tOf x) = x := by
        dsimp [xOf, tOf]
        field_simp [hx1]
        ring
      have hsrel := gap12 (tOf x) htmem
      rw [hxo] at hsrel
      convert hcomp using 1
      unfold i3
      rw [hsrel]
      dsimp [tOf]
      have ht0 : 1 / (x + 1) ≠ 0 := one_div_ne_zero hx1
      have habs0 : |1 / (x + 1)| ≠ 0 := abs_ne_zero.mpr ht0
      have hqT : 0 < qT (1 / (x + 1)) := by
        unfold qT
        nlinarith [sq_nonneg (1 / (x + 1) - 1 / 2)]
      have hsT : Real.sqrt (qT (1 / (x + 1))) ≠ 0 :=
        (Real.sqrt_pos.2 hqT).ne'
      field_simp [hx1, ht0, habs0, hsT]
    · intro t ht
      have ht0 : t ≠ 0 := ht
      dsimp [tOf, xOf]
      apply congrArg P
      field_simp [ht0]
      ring

private def logCoreI3T (t : ℝ) :=
  Real.log |t - 1 / 2 + Real.sqrt (qT t)|

private def signedLogI3T (t : ℝ) :=
  Real.sign t * logCoreI3T t

private def signedSqrtI3T (t : ℝ) :=
  Real.sign t * Real.sqrt (qT t)

private lemma qT_pos (t : ℝ) : 0 < qT t := by
  unfold qT
  nlinarith [sq_nonneg (t - 1 / 2)]

private lemma sqrt_qT_hasDerivAt (t : ℝ) :
    HasDerivAt (fun y => Real.sqrt (qT y))
      ((2 * t - 1) / (2 * Real.sqrt (qT t))) t := by
  have hq : HasDerivAt qT (2 * t - 1) t := by
    unfold qT
    convert (((hasDerivAt_id t).pow 2).sub (hasDerivAt_id t)).add_const 1
      using 1 <;> simp [id] <;> ring
  have hs := (Real.hasDerivAt_sqrt (qT_pos t).ne').comp t hq
  convert hs using 1 <;> ring

private lemma logCore_arg_pos (t : ℝ) :
    0 < t - 1 / 2 + Real.sqrt (qT t) := by
  have hs0 : 0 ≤ Real.sqrt (qT t) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (qT t)) ^ 2 = qT t :=
    Real.sq_sqrt (qT_pos t).le
  by_contra h
  have hsum : t - 1 / 2 + Real.sqrt (qT t) ≤ 0 := le_of_not_gt h
  have hleft : 0 ≤ -(t - 1 / 2 + Real.sqrt (qT t)) := by linarith
  have hright : 0 ≤ -(t - 1 / 2) + Real.sqrt (qT t) := by linarith
  have hprod := mul_nonneg hleft hright
  unfold qT at hsq hprod
  nlinarith

private lemma logCoreI3T_hasDerivAt (t : ℝ) :
    HasDerivAt logCoreI3T (1 / Real.sqrt (qT t)) t := by
  have hs0 : Real.sqrt (qT t) ≠ 0 :=
    (Real.sqrt_pos.2 (qT_pos t)).ne'
  have ha0 : t - 1 / 2 + Real.sqrt (qT t) ≠ 0 :=
    (logCore_arg_pos t).ne'
  have ha : HasDerivAt
      (fun y => y - 1 / 2 + Real.sqrt (qT y))
      (1 + (2 * t - 1) / (2 * Real.sqrt (qT t))) t := by
    convert ((hasDerivAt_id t).sub_const (1 / 2)).add
      (sqrt_qT_hasDerivAt t) using 1 <;> ring
  have hd := (Real.hasDerivAt_log ha0).comp t ha
  have hcoef :
      (t - 1 / 2 + Real.sqrt (qT t))⁻¹ *
          (1 + (2 * t - 1) / (2 * Real.sqrt (qT t))) =
        1 / Real.sqrt (qT t) := by
    have hnum :
        1 + (2 * t - 1) / (2 * Real.sqrt (qT t)) =
          (t - 1 / 2 + Real.sqrt (qT t)) /
            Real.sqrt (qT t) := by
      field_simp [hs0]
      ring
    rw [hnum]
    have ha2 :
        t * 2 - 1 + 2 * Real.sqrt (qT t) ≠ 0 := by
      nlinarith [logCore_arg_pos t]
    field_simp [ha0, ha2]
  rw [hcoef] at hd
  have hfun :
      logCoreI3T =
        fun y => Real.log (y - 1 / 2 + Real.sqrt (qT y)) := by
    funext y
    unfold logCoreI3T
    rw [abs_of_pos (logCore_arg_pos y)]
  rw [hfun]
  simpa [Function.comp_def] using hd

private lemma signedLogI3T_hasDerivAt (t : ℝ)
    (ht : t ∈ parameterBranch) :
    HasDerivAt signedLogI3T
      (Real.sign t / Real.sqrt (qT t)) t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have heq : signedLogI3T =ᶠ[nhds t] fun y => -logCoreI3T y := by
      filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
      simp [signedLogI3T, Real.sign_of_neg hy]
    rw [Real.sign_of_neg hneg]
    convert (logCoreI3T_hasDerivAt t).neg.congr_of_eventuallyEq heq
      using 1 <;> simp [div_eq_mul_inv]
  · have heq : signedLogI3T =ᶠ[nhds t] logCoreI3T := by
      filter_upwards [isOpen_Ioi.mem_nhds hpos] with y hy
      simp [signedLogI3T, Real.sign_of_pos hy]
    rw [Real.sign_of_pos hpos]
    simpa using (logCoreI3T_hasDerivAt t).congr_of_eventuallyEq heq

private lemma signedSqrtI3T_hasDerivAt (t : ℝ)
    (ht : t ∈ parameterBranch) :
    HasDerivAt signedSqrtI3T
      (Real.sign t * (2 * t - 1) /
        (2 * Real.sqrt (qT t))) t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have heq : signedSqrtI3T =ᶠ[nhds t]
        fun y => -Real.sqrt (qT y) := by
      filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
      simp [signedSqrtI3T, Real.sign_of_neg hy]
    rw [Real.sign_of_neg hneg]
    convert (sqrt_qT_hasDerivAt t).neg.congr_of_eventuallyEq heq using 1 <;>
      ring
  · have heq : signedSqrtI3T =ᶠ[nhds t]
        fun y => Real.sqrt (qT y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hpos] with y hy
      simp [signedSqrtI3T, Real.sign_of_pos hy]
    rw [Real.sign_of_pos hpos]
    convert (sqrt_qT_hasDerivAt t).congr_of_eventuallyEq heq using 1 <;>
      ring

private lemma primitiveI3T_hasDerivAt (t : ℝ)
    (ht : t ∈ parameterBranch) :
    HasDerivAt primitiveI3T
      (- (|t| / Real.sqrt (qT t))) t := by
  have hfun :
      primitiveI3T =
        fun y => -signedSqrtI3T y - 1 / 2 * signedLogI3T y := by
    funext y
    unfold primitiveI3T signedSqrtI3T signedLogI3T logCoreI3T
    ring
  rw [hfun]
  have hd := (signedSqrtI3T_hasDerivAt t ht).neg.sub
    ((signedLogI3T_hasDerivAt t ht).const_mul (1 / 2))
  convert hd using 1
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
    ring
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
    ring
theorem gap14 :
    NegativeI3Family = SplitI3Family := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun t => 2 * G t - signedLogI3T t, ?_,
      signedLogI3T, ?_, ?_⟩
    · intro t ht
      have hd := (hG t ht).const_mul 2 |>.sub
        (signedLogI3T_hasDerivAt t ht)
      convert hd using 1
      change Real.sign t * (2 * t - 1) / Real.sqrt (qT t) =
        2 * (|t| / Real.sqrt (qT t)) -
          Real.sign t / Real.sqrt (qT t)
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
        ring
      · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
        ring
    · exact signedLogI3T_hasDerivAt
    · intro t ht
      rw [hFG t ht]
      ring
  · rintro ⟨A, hA, B, hB, hF⟩
    refine ⟨fun t => 1 / 2 * A t + 1 / 2 * B t, ?_, ?_⟩
    · intro t ht
      have hd := (hA t ht).const_mul (1 / 2) |>.add
        ((hB t ht).const_mul (1 / 2))
      convert hd using 1
      change |t| / Real.sqrt (qT t) =
        1 / 2 * (Real.sign t * (2 * t - 1) / Real.sqrt (qT t)) +
          1 / 2 * (Real.sign t / Real.sqrt (qT t))
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
        ring
      · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
        ring
    · intro t ht
      rw [hF t ht]
      ring
theorem gap15 :
    PullbackI3Family = SplitI3Family := by
  rw [gap13, gap14]
theorem gap16 :
    NegativeI3Family =
      BranchwisePrimitiveFamilyOn parameterBranch primitiveI3T := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩ u huopen huconn hus
    have hFderiv : ∀ t ∈ u,
        HasDerivAt F (- (|t| / Real.sqrt (qT t))) t := by
      intro t ht
      have heq : F =ᶠ[nhds t] fun y => -G y := by
        filter_upwards [parameterBranch_isOpen.mem_nhds (hus ht)] with y hy
        exact hFG y hy
      exact (hG t (hus ht)).neg.congr_of_eventuallyEq heq
    have hzero : ∀ t ∈ u,
        HasDerivAt (fun y => F y - primitiveI3T y) 0 t := by
      intro t ht
      convert (hFderiv t ht).sub
        (primitiveI3T_hasDerivAt t (hus ht)) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ
        (fun y => F y - primitiveI3T y) u :=
      fun t ht => (hzero t ht).differentiableAt.differentiableWithinAt
    have hderiv : u.EqOn
        (deriv (fun y => F y - primitiveI3T y)) 0 :=
      fun t ht => (hzero t ht).deriv
    obtain ⟨C, hC⟩ :=
      huopen.exists_is_const_of_deriv_eq_zero huconn hdiff hderiv
    exact ⟨C, fun t ht => by
      have htC : F t - primitiveI3T t = C := hC t ht
      linarith⟩
  · intro hF
    refine ⟨fun t => -F t, ?_, ?_⟩
    · intro t ht
      have hFt :
          HasDerivAt F (- (|t| / Real.sqrt (qT t))) t := by
        rcases lt_or_gt_of_ne ht with hneg | hpos
        · obtain ⟨C, hC⟩ := hF (Set.Iio 0) isOpen_Iio
            isPreconnected_Iio (by
              intro y hy
              exact ne_of_lt hy)
          have heq : F =ᶠ[nhds t] fun y => primitiveI3T y + C := by
            filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
            exact hC y hy
          exact (primitiveI3T_hasDerivAt t ht).add_const C
            |>.congr_of_eventuallyEq heq
        · obtain ⟨C, hC⟩ := hF (Set.Ioi 0) isOpen_Ioi
            isPreconnected_Ioi (by
              intro y hy
              exact ne_of_gt hy)
          have heq : F =ᶠ[nhds t] fun y => primitiveI3T y + C := by
            filter_upwards [isOpen_Ioi.mem_nhds hpos] with y hy
            exact hC y hy
          exact (primitiveI3T_hasDerivAt t ht).add_const C
            |>.congr_of_eventuallyEq heq
      convert hFt.neg using 1 <;> ring
    · intro t ht
      ring

private lemma sqrtQuotient_hasDerivAtForI3 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.sqrt (q y) / (y + 1))
      ((x - 1) / (2 * (x + 1) ^ 2 * Real.sqrt (q x))) x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hqsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  have hq' : HasDerivAt q (2 * x + 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x + 1) / (2 * Real.sqrt (q x))) x := by
    have hd := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hq'
    convert hd using 1 <;> field_simp [hs] <;> ring
  have hd := hsqrt.div ((hasDerivAt_id x).add_const 1) hx1
  convert hd using 1
  simp only [id_eq]
  field_simp [hx1, hs]
  rw [hqsq]
  unfold q
  ring

private lemma primitiveI3X_eq :
    primitiveI3X =
      fun x => -Real.sqrt (q x) / (x + 1) + 1 / 2 * primitiveI2 x := by
  funext x
  unfold primitiveI3X primitiveI2
  ring

private lemma primitiveI3X_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveI3X (i3 x) x := by
  rw [primitiveI3X_eq]
  have hd := (sqrtQuotient_hasDerivAtForI3 x hx).neg.add
    ((primitiveI2_hasDerivAt x hx).const_mul (1 / 2))
  have hcoef :
      -((x - 1) / (2 * (x + 1) ^ 2 * Real.sqrt (q x))) +
          (1 / 2) * i2 x = i3 x := by
    unfold i2 i3
    have hx1 : x + 1 ≠ 0 := by
      intro h
      apply hx
      linarith
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    field_simp [hx1, hs]
    ring
  rw [hcoef] at hd
  have heq :
      (fun y => -Real.sqrt (q y) / (y + 1) + 1 / 2 * primitiveI2 y)
        =ᶠ[nhds x]
      ((-fun y => Real.sqrt (q y) / (y + 1)) +
        fun y => 1 / 2 * primitiveI2 y) := by
    filter_upwards [] with y
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  exact hd.congr_of_eventuallyEq heq
theorem gap17 :
    I3 = BranchwisePrimitiveFamilyOn branch primitiveI3X := by
  ext F
  constructor
  · intro hF u huopen huconn hus
    have hzero : ∀ x ∈ u,
        HasDerivAt (fun y => F y - primitiveI3X y) 0 x := by
      intro x hx
      convert (hF x (hus hx)).sub (primitiveI3X_hasDerivAt x (hus hx)) using 1 <;>
        ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitiveI3X y) u :=
      fun x hx => (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : u.EqOn (deriv (fun y => F y - primitiveI3X y)) 0 :=
      fun x hx => (hzero x hx).deriv
    obtain ⟨C, hC⟩ :=
      huopen.exists_is_const_of_deriv_eq_zero huconn hdiff hderiv
    exact ⟨C, fun x hx => by
      have hxC : F x - primitiveI3X x = C := hC x hx
      linarith⟩
  · intro hF x hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · obtain ⟨C, hC⟩ := hF (Set.Iio (-1)) isOpen_Iio isPreconnected_Iio
        (by
          intro y hy
          exact ne_of_lt hy)
      have heq : F =ᶠ[nhds x] fun y => primitiveI3X y + C := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        exact hC y hy
      exact (primitiveI3X_hasDerivAt x hx).add_const C |>.congr_of_eventuallyEq heq
    · obtain ⟨C, hC⟩ := hF (Set.Ioi (-1)) isOpen_Ioi isPreconnected_Ioi
        (by
          intro y hy
          exact ne_of_gt hy)
      have heq : F =ᶠ[nhds x] fun y => primitiveI3X y + C := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        exact hC y hy
      exact (primitiveI3X_hasDerivAt x hx).add_const C |>.congr_of_eventuallyEq heq

private lemma sqrtQuotient_hasDerivAtForFinal (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.sqrt (q y) / (y + 1))
      ((x - 1) / (2 * (x + 1) ^ 2 * Real.sqrt (q x))) x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hqsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  have hq' : HasDerivAt q (2 * x + 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x + 1) / (2 * Real.sqrt (q x))) x := by
    have hd := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hq'
    convert hd using 1 <;> field_simp [hs] <;> ring
  have hd := hsqrt.div ((hasDerivAt_id x).add_const 1) hx1
  convert hd using 1
  simp only [id_eq]
  field_simp [hx1, hs]
  rw [hqsq]
  unfold q
  ring

private lemma finalPrimitive_eq :
    finalPrimitive =
      fun x => primitiveI1 x - Real.sqrt (q x) / (x + 1) -
        1 / 2 * primitiveI2 x := by
  funext x
  unfold finalPrimitive primitiveI1 primitiveI2
  ring

private lemma finalPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt finalPrimitive (integrand x) x := by
  rw [finalPrimitive_eq]
  have hd := (primitiveI1_hasDerivAt x).sub (sqrtQuotient_hasDerivAtForFinal x hx)
  have htotal := hd.sub ((primitiveI2_hasDerivAt x hx).const_mul (1 / 2))
  convert htotal using 1
  unfold i1 i2 integrand
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  field_simp [hx1, hs]
  rw [hsq]
  unfold q
  ring
theorem gap18 :
    AntiderivativesOn branch integrand =
      BranchwisePrimitiveFamilyOn branch finalPrimitive := by
  ext F
  constructor
  · intro hF u huopen huconn hus
    have hzero : ∀ x ∈ u,
        HasDerivAt (fun y => F y - finalPrimitive y) 0 x := by
      intro x hx
      convert (hF x (hus hx)).sub (finalPrimitive_hasDerivAt x (hus hx)) using 1 <;>
        ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - finalPrimitive y) u :=
      fun x hx => (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : u.EqOn (deriv (fun y => F y - finalPrimitive y)) 0 :=
      fun x hx => (hzero x hx).deriv
    obtain ⟨C, hC⟩ :=
      huopen.exists_is_const_of_deriv_eq_zero huconn hdiff hderiv
    exact ⟨C, fun x hx => by
      have hxC : F x - finalPrimitive x = C := hC x hx
      linarith⟩
  · intro hF x hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · obtain ⟨C, hC⟩ := hF (Set.Iio (-1)) isOpen_Iio isPreconnected_Iio
        (by
          intro y hy
          exact ne_of_lt hy)
      have heq : F =ᶠ[nhds x] fun y => finalPrimitive y + C := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        exact hC y hy
      exact (finalPrimitive_hasDerivAt x hx).add_const C |>.congr_of_eventuallyEq heq
    · obtain ⟨C, hC⟩ := hF (Set.Ioi (-1)) isOpen_Ioi isPreconnected_Ioi
        (by
          intro y hy
          exact ne_of_gt hy)
      have heq : F =ᶠ[nhds x] fun y => finalPrimitive y + C := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        exact hC y hy
      exact (finalPrimitive_hasDerivAt x hx).add_const C |>.congr_of_eventuallyEq heq

private lemma branch_isOpen : IsOpen branch := by
  rw [show branch = ({-1} : Set ℝ)ᶜ by
    ext x
    simp [branch]]
  exact isClosed_singleton.isOpen_compl
theorem gap19 :
    AntiderivativesOn branch integrand = ByPartsFamily := by
  have hcoef : ∀ x ∈ branch,
      Real.sqrt (q x) * deriv (fun y => 1 / (y + 1)) x = -integrand x := by
    intro x hx
    have hx1 : x + 1 ≠ 0 := by
      intro h
      apply hx
      linarith
    have hd :
        HasDerivAt (fun y : ℝ => 1 / (y + 1)) (-1 / (x + 1) ^ 2) x := by
      convert (hasDerivAt_const x (1 : ℝ)).div
        ((hasDerivAt_id x).add_const 1) hx1 using 1 <;>
        simp [id] <;> field_simp [hx1] <;> ring
    rw [hd.deriv]
    unfold integrand
    ring
  ext F
  constructor
  · intro hF
    refine ⟨fun y => -F y, ?_, ?_⟩
    · intro x hx
      change HasDerivAt (fun y => -F y)
        (Real.sqrt (q x) * deriv (fun y => 1 / (y + 1)) x) x
      rw [hcoef x hx]
      exact (hF x hx).neg
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩ x hx
    have heq : F =ᶠ[nhds x] fun y => -G y := by
      filter_upwards [branch_isOpen.mem_nhds hx] with y hy
      exact hFG y hy
    have hcalc : HasDerivAt (fun y => -G y) (integrand x) x := by
      have h := (hG x hx).neg
      change HasDerivAt (fun y => -G y)
        (-(Real.sqrt (q x) * deriv (fun y => 1 / (y + 1)) x)) x at h
      rw [hcoef x hx] at h
      simpa using h
    exact hcalc.congr_of_eventuallyEq heq

private lemma sqrtQuotient_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.sqrt (q y) / (y + 1))
      ((x - 1) / (2 * (x + 1) ^ 2 * Real.sqrt (q x))) x := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hqsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
  have hq' : HasDerivAt q (2 * x + 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt : HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x + 1) / (2 * Real.sqrt (q x))) x := by
    have hd := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hq'
    convert hd using 1 <;> field_simp [hs] <;> ring
  have hd := hsqrt.div ((hasDerivAt_id x).add_const 1) hx1
  convert hd using 1
  · simp only [id_eq]
    field_simp [hx1, hs]
    rw [hqsq]
    unfold q
    ring
theorem gap20 :
    AntiderivativesOn branch integrand = ReductionFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => F y + Real.sqrt (q y) / (y + 1), ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).add (sqrtQuotient_hasDerivAt x hx)
      convert hd using 1
      unfold integrand
      have hx1 : x + 1 ≠ 0 := by
        intro h
        apply hx
        linarith
      have hq : 0 < q x := by
        unfold q
        nlinarith [sq_nonneg (x + 1 / 2)]
      have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
      have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
      field_simp [hx1, hs]
      rw [hsq]
      unfold q
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩ x hx
    have hcalc : HasDerivAt
        (fun y => -(Real.sqrt (q y) / (y + 1)) + G y)
        (integrand x) x := by
      have hd := (sqrtQuotient_hasDerivAt x hx).neg.add (hG x hx)
      convert hd using 1
      unfold integrand
      have hx1 : x + 1 ≠ 0 := by
        intro h
        apply hx
        linarith
      have hq : 0 < q x := by
        unfold q
        nlinarith [sq_nonneg (x + 1 / 2)]
      have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
      have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt hq.le
      field_simp [hx1, hs]
      rw [hsq]
      unfold q
      ring
    have heq : F =ᶠ[nhds x]
        (fun y => -(Real.sqrt (q y) / (y + 1)) + G y) := by
      filter_upwards [branch_isOpen.mem_nhds hx] with y hy
      simpa only [neg_div] using hFG y hy
    exact hcalc.congr_of_eventuallyEq heq
theorem gap21 :
    AntiderivativesOn branch integrand =
      BranchwisePrimitiveFamilyOn branch finalPrimitive := by
  exact gap18

end
end ProofGap.Exercise1954
