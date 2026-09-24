import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1789

noncomputable section

def radicand (a b x : ℝ) : ℝ := (x + a) * (x + b)
def integrand (a b x : ℝ) : ℝ := 1 / Real.sqrt (radicand a b x)
def posDomain (a : ℝ) : Set ℝ := Set.Ioi (-a)
def negDomain (b : ℝ) : Set ℝ := Set.Iio (-b)
def tPos (a b x : ℝ) : ℝ :=
  Real.log ((Real.sqrt (x + a) + Real.sqrt (x + b)) / Real.sqrt (b - a))
def tNeg (a b x : ℝ) : ℝ :=
  Real.log ((Real.sqrt (-x - a) + Real.sqrt (-x - b)) / Real.sqrt (b - a))
def posPrimitive (a b x : ℝ) : ℝ :=
  2 * Real.log (Real.sqrt (x + a) + Real.sqrt (x + b))
def negPrimitive (a b x : ℝ) : ℝ :=
  -2 * Real.log (Real.sqrt (-x - a) + Real.sqrt (-x - b))
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem realSinhAddCoshAux (z : ℝ) :
    Real.sinh z + Real.cosh z = Real.exp z := by
  rw [Real.sinh_eq, Real.cosh_eq]
  ring

private theorem hyperbolicProductAux (u v d : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hd : 0 < d)
    (hrel : v ^ 2 - u ^ 2 = d ∨ u ^ 2 - v ^ 2 = d) :
    d * Real.sinh (Real.log ((u + v) / Real.sqrt d)) *
      Real.cosh (Real.log ((u + v) / Real.sqrt d)) = u * v := by
  have hr : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hs : 0 < u + v := add_pos hu hv
  have hq : 0 < (u + v) / Real.sqrt d := div_pos hs hr
  have hexp : Real.exp (Real.log ((u + v) / Real.sqrt d)) =
      (u + v) / Real.sqrt d := Real.exp_log hq
  have hsqd : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg, hexp]
  rcases hrel with hrel | hrel
  · have hinv : ((u + v) / Real.sqrt d)⁻¹ =
        (v - u) / Real.sqrt d := by
      field_simp [hs.ne', hr.ne']
      nlinarith [hsqd, hrel]
    rw [hinv]
    field_simp [hr.ne']
    rw [hsqd]
    ring
  · have hinv : ((u + v) / Real.sqrt d)⁻¹ =
        (u - v) / Real.sqrt d := by
      field_simp [hs.ne', hr.ne']
      nlinarith [hsqd, hrel]
    rw [hinv]
    field_simp [hr.ne']
    rw [hsqd]
    ring

private theorem hasDerivAtTPosAux (a b x : ℝ) (hab : a < b)
    (hx : x ∈ posDomain a) :
    HasDerivAt (tPos a b)
      (1 / (2 * Real.sqrt (radicand a b x))) x := by
  have hx' : -a < x := by simpa [posDomain] using hx
  have hxa : 0 < x + a := by linarith
  have hxb : 0 < x + b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hu : 0 < Real.sqrt (x + a) := Real.sqrt_pos.2 hxa
  have hv : 0 < Real.sqrt (x + b) := Real.sqrt_pos.2 hxb
  have hr : 0 < Real.sqrt (b - a) := Real.sqrt_pos.2 hd
  have hs : 0 < Real.sqrt (x + a) + Real.sqrt (x + b) := add_pos hu hv
  have hdu : HasDerivAt (fun y : ℝ => Real.sqrt (y + a))
      (1 / (2 * Real.sqrt (x + a))) x := by
    simpa [one_div] using
      (Real.hasDerivAt_sqrt hxa.ne').comp x ((hasDerivAt_id x).add_const a)
  have hdv : HasDerivAt (fun y : ℝ => Real.sqrt (y + b))
      (1 / (2 * Real.sqrt (x + b))) x := by
    simpa [one_div] using
      (Real.hasDerivAt_sqrt hxb.ne').comp x ((hasDerivAt_id x).add_const b)
  have hsum := hdu.add hdv
  have hquot := hsum.div_const (Real.sqrt (b - a))
  have hlog := (Real.hasDerivAt_log (div_ne_zero hs.ne' hr.ne')).comp x hquot
  have hsrad : Real.sqrt (radicand a b x) =
      Real.sqrt (x + a) * Real.sqrt (x + b) := by
    rw [radicand, Real.sqrt_mul hxa.le]
  have hcoef :
      (((Real.sqrt (x + a) + Real.sqrt (x + b)) / Real.sqrt (b - a))⁻¹ *
        ((1 / (2 * Real.sqrt (x + a)) + 1 / (2 * Real.sqrt (x + b))) /
          Real.sqrt (b - a))) =
        1 / (2 * Real.sqrt (radicand a b x)) := by
    rw [hsrad]
    field_simp [hu.ne', hv.ne', hr.ne', hs.ne']
    ring
  rw [← hcoef]
  simpa only [tPos, Function.comp_apply] using hlog

private theorem hasDerivAtPosPrimitiveAux (a b x : ℝ) (hab : a < b)
    (hx : x ∈ posDomain a) :
    HasDerivAt (posPrimitive a b) (integrand a b x) x := by
  have hx' : -a < x := by simpa [posDomain] using hx
  have hxa : 0 < x + a := by linarith
  have hxb : 0 < x + b := by linarith
  have hu : 0 < Real.sqrt (x + a) := Real.sqrt_pos.2 hxa
  have hv : 0 < Real.sqrt (x + b) := Real.sqrt_pos.2 hxb
  have hs : 0 < Real.sqrt (x + a) + Real.sqrt (x + b) := add_pos hu hv
  have hdu : HasDerivAt (fun y : ℝ => Real.sqrt (y + a))
      (1 / (2 * Real.sqrt (x + a))) x := by
    simpa [one_div] using
      (Real.hasDerivAt_sqrt hxa.ne').comp x ((hasDerivAt_id x).add_const a)
  have hdv : HasDerivAt (fun y : ℝ => Real.sqrt (y + b))
      (1 / (2 * Real.sqrt (x + b))) x := by
    simpa [one_div] using
      (Real.hasDerivAt_sqrt hxb.ne').comp x ((hasDerivAt_id x).add_const b)
  have hlog := (Real.hasDerivAt_log hs.ne').comp x (hdu.add hdv)
  have hsrad : Real.sqrt (radicand a b x) =
      Real.sqrt (x + a) * Real.sqrt (x + b) := by
    rw [radicand, Real.sqrt_mul hxa.le]
  have hcoef :
      2 * ((Real.sqrt (x + a) + Real.sqrt (x + b))⁻¹ *
        (1 / (2 * Real.sqrt (x + a)) + 1 / (2 * Real.sqrt (x + b)))) =
        1 / Real.sqrt (radicand a b x) := by
    rw [hsrad]
    field_simp [hu.ne', hv.ne', hs.ne']
    ring
  have hscaled := hlog.const_mul 2
  rw [hcoef] at hscaled
  simpa only [posPrimitive, integrand, Function.comp_apply] using hscaled

private theorem hasDerivAtTNegAux (a b x : ℝ) (hab : a < b)
    (hx : x ∈ negDomain b) :
    HasDerivAt (tNeg a b)
      (-(1 / (2 * Real.sqrt (radicand a b x)))) x := by
  have hxb : x < -b := by simpa [negDomain] using hx
  have hA : 0 < -x - a := by linarith
  have hB : 0 < -x - b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hu : 0 < Real.sqrt (-x - a) := Real.sqrt_pos.2 hA
  have hv : 0 < Real.sqrt (-x - b) := Real.sqrt_pos.2 hB
  have hr : 0 < Real.sqrt (b - a) := Real.sqrt_pos.2 hd
  have hs : 0 < Real.sqrt (-x - a) + Real.sqrt (-x - b) := add_pos hu hv
  have hdu : HasDerivAt (fun y : ℝ => Real.sqrt (-y - a))
      (-(1 / (2 * Real.sqrt (-x - a)))) x := by
    convert (Real.hasDerivAt_sqrt hA.ne').comp x
      ((hasDerivAt_id x).neg.sub_const a) using 1 <;>
      field_simp [hu.ne']
  have hdv : HasDerivAt (fun y : ℝ => Real.sqrt (-y - b))
      (-(1 / (2 * Real.sqrt (-x - b)))) x := by
    convert (Real.hasDerivAt_sqrt hB.ne').comp x
      ((hasDerivAt_id x).neg.sub_const b) using 1 <;>
      field_simp [hv.ne']
  have hsum := hdu.add hdv
  have hquot := hsum.div_const (Real.sqrt (b - a))
  have hlog := (Real.hasDerivAt_log (div_ne_zero hs.ne' hr.ne')).comp x hquot
  have hrad : radicand a b x = (-x - a) * (-x - b) := by
    unfold radicand
    ring
  have hsrad : Real.sqrt (radicand a b x) =
      Real.sqrt (-x - a) * Real.sqrt (-x - b) := by
    rw [hrad, Real.sqrt_mul hA.le]
  have hcoef :
      (((Real.sqrt (-x - a) + Real.sqrt (-x - b)) / Real.sqrt (b - a))⁻¹ *
        ((-(1 / (2 * Real.sqrt (-x - a))) -
            1 / (2 * Real.sqrt (-x - b))) / Real.sqrt (b - a))) =
        -(1 / (2 * Real.sqrt (radicand a b x))) := by
    rw [hsrad]
    field_simp [hu.ne', hv.ne', hr.ne', hs.ne']
    ring
  rw [← hcoef]
  simpa only [tNeg, Function.comp_apply, neg_add_rev] using hlog

private theorem hasDerivAtNegPrimitiveAux (a b x : ℝ) (hab : a < b)
    (hx : x ∈ negDomain b) :
    HasDerivAt (negPrimitive a b) (integrand a b x) x := by
  have hxb : x < -b := by simpa [negDomain] using hx
  have hA : 0 < -x - a := by linarith
  have hB : 0 < -x - b := by linarith
  have hu : 0 < Real.sqrt (-x - a) := Real.sqrt_pos.2 hA
  have hv : 0 < Real.sqrt (-x - b) := Real.sqrt_pos.2 hB
  have hs : 0 < Real.sqrt (-x - a) + Real.sqrt (-x - b) := add_pos hu hv
  have hdu : HasDerivAt (fun y : ℝ => Real.sqrt (-y - a))
      (-(1 / (2 * Real.sqrt (-x - a)))) x := by
    convert (Real.hasDerivAt_sqrt hA.ne').comp x
      ((hasDerivAt_id x).neg.sub_const a) using 1 <;>
      field_simp [hu.ne']
  have hdv : HasDerivAt (fun y : ℝ => Real.sqrt (-y - b))
      (-(1 / (2 * Real.sqrt (-x - b)))) x := by
    convert (Real.hasDerivAt_sqrt hB.ne').comp x
      ((hasDerivAt_id x).neg.sub_const b) using 1 <;>
      field_simp [hv.ne']
  have hlog := (Real.hasDerivAt_log hs.ne').comp x (hdu.add hdv)
  have hrad : radicand a b x = (-x - a) * (-x - b) := by
    unfold radicand
    ring
  have hsrad : Real.sqrt (radicand a b x) =
      Real.sqrt (-x - a) * Real.sqrt (-x - b) := by
    rw [hrad, Real.sqrt_mul hA.le]
  have hcoef :
      (-2) * ((Real.sqrt (-x - a) + Real.sqrt (-x - b))⁻¹ *
        (-(1 / (2 * Real.sqrt (-x - a))) +
          -(1 / (2 * Real.sqrt (-x - b))))) =
        1 / Real.sqrt (radicand a b x) := by
    rw [hsrad]
    field_simp [hu.ne', hv.ne', hs.ne']
    ring
  have hscaled := hlog.const_mul (-2)
  rw [hcoef] at hscaled
  simpa only [negPrimitive, integrand, Function.comp_apply] using hscaled

private theorem familyEqTranslatesOfConvex (f P : ℝ → ℝ) (s : Set ℝ)
    (hconv : Convex ℝ s) (hopen : IsOpen s) (hne : s.Nonempty)
    (hP : IsAntiderivativeOn P f s) :
    Family f s = Translates P s := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    rcases hne with ⟨x₀, hx₀⟩
    let G : ℝ → ℝ := fun x => F x - P x
    have hG : ∀ x ∈ s, HasDerivAt G 0 x := by
      intro x hx
      simpa [G] using (hF x hx).sub (hP x hx)
    have hdiff : DifferentiableOn ℝ G s := by
      intro x hx
      exact (hG x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ s, deriv G x = 0 := by
      intro x hx
      exact (hG x hx).deriv
    refine ⟨G x₀, ?_⟩
    intro x hx
    have heq : G x = G x₀ :=
      hopen.is_const_of_deriv_eq_zero hconv.isPreconnected hdiff hzero hx hx₀
    dsimp [G] at heq ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    refine ((hP x hx).add_const C).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hFC y hy

theorem gap1 (a b x : ℝ) (hab : a < b) (hrad : 0 < radicand a b x) :
    x ∈ posDomain a ∨ x ∈ negDomain b := by
  simp only [posDomain, negDomain, Set.mem_Ioi, Set.mem_Iio]
  by_cases h : -a < x
  · exact Or.inl h
  · right
    have hxa : x + a ≤ 0 := by linarith
    by_contra hxb
    have hxb' : 0 ≤ x + b := by linarith
    have hp : (x + a) * (x + b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hxa hxb'
    unfold radicand at hrad
    linarith

theorem gap2 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    Real.sqrt (radicand a b x) =
      (b - a) * Real.sinh (tPos a b x) * Real.cosh (tPos a b x) := by
  have hx' : -a < x := by simpa [posDomain] using hx
  have hxa : 0 < x + a := by linarith
  have hxb : 0 < x + b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hu : 0 < Real.sqrt (x + a) := Real.sqrt_pos.2 hxa
  have hv : 0 < Real.sqrt (x + b) := Real.sqrt_pos.2 hxb
  have hrel : Real.sqrt (x + b) ^ 2 - Real.sqrt (x + a) ^ 2 = b - a := by
    rw [Real.sq_sqrt hxb.le, Real.sq_sqrt hxa.le]
    ring
  have hp := hyperbolicProductAux (Real.sqrt (x + a))
    (Real.sqrt (x + b)) (b - a) hu hv hd (Or.inl hrel)
  rw [radicand, Real.sqrt_mul hxa.le]
  simpa [tPos] using hp.symm

theorem gap3 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    1 = 2 * (b - a) * Real.sinh (tPos a b x) *
      Real.cosh (tPos a b x) * deriv (tPos a b) x := by
  have hx' : -a < x := by simpa [posDomain] using hx
  have hxa : 0 < x + a := by linarith
  have hxb : 0 < x + b := by linarith
  have hrad : 0 < radicand a b x := by
    unfold radicand
    positivity
  have hr : 0 < Real.sqrt (radicand a b x) := Real.sqrt_pos.2 hrad
  rw [(hasDerivAtTPosAux a b x hab hx).deriv]
  field_simp [hr.ne']
  nlinarith [gap2 a b x hab hx]

theorem gap4 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    integrand a b x = 2 * deriv (tPos a b) x := by
  have hx' : -a < x := by simpa [posDomain] using hx
  have hxa : 0 < x + a := by linarith
  have hxb : 0 < x + b := by linarith
  have hrad : 0 < radicand a b x := by
    unfold radicand
    positivity
  have hr : 0 < Real.sqrt (radicand a b x) := Real.sqrt_pos.2 hrad
  rw [(hasDerivAtTPosAux a b x hab hx).deriv]
  unfold integrand
  field_simp [hr.ne']

theorem gap5 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    HasDerivAt (fun y => 2 * tPos a b y) (integrand a b x) x := by
  have ht := hasDerivAtTPosAux a b x hab hx
  simpa only [gap4 a b x hab hx, ht.deriv] using ht.const_mul 2

theorem gap6 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    HasDerivAt (fun y => 2 * tPos a b y) (2 * deriv (tPos a b) x) x := by
  have ht := hasDerivAtTPosAux a b x hab hx
  rw [ht.deriv]
  simpa using ht.const_mul 2

theorem gap7 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    Real.sqrt (x + a) + Real.sqrt (x + b) =
      Real.sqrt (b - a) *
        (Real.sinh (tPos a b x) + Real.cosh (tPos a b x)) := by
  have hx' : -a < x := by simpa [posDomain] using hx
  have hxa : 0 < x + a := by linarith
  have hxb : 0 < x + b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hr : 0 < Real.sqrt (b - a) := Real.sqrt_pos.2 hd
  have hq : 0 < (Real.sqrt (x + a) + Real.sqrt (x + b)) /
      Real.sqrt (b - a) := by positivity
  rw [realSinhAddCoshAux]
  unfold tPos
  rw [Real.exp_log hq]
  field_simp [hr.ne']

theorem gap8 (a b x : ℝ) :
    Real.sinh (tPos a b x) + Real.cosh (tPos a b x) =
      Real.exp (tPos a b x) := by
  exact realSinhAddCoshAux (tPos a b x)

theorem gap9 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    Real.sqrt (x + a) + Real.sqrt (x + b) =
      Real.sqrt (b - a) * Real.exp (tPos a b x) := by
  calc
    Real.sqrt (x + a) + Real.sqrt (x + b) =
        Real.sqrt (b - a) *
          (Real.sinh (tPos a b x) + Real.cosh (tPos a b x)) :=
      gap7 a b x hab hx
    _ = Real.sqrt (b - a) * Real.exp (tPos a b x) := by
      rw [gap8]

theorem gap10 (a b x : ℝ) :
    tPos a b x =
      Real.log ((Real.sqrt (x + a) + Real.sqrt (x + b)) /
        Real.sqrt (b - a)) := by
  rfl

theorem gap11 (a b : ℝ) (hab : a < b) :
    Family (integrand a b) (posDomain a) =
      Translates (posPrimitive a b) (posDomain a) := by
  refine familyEqTranslatesOfConvex
    (f := integrand a b) (P := posPrimitive a b) (s := posDomain a) ?_ ?_ ?_ ?_
  · simpa [posDomain] using
      (convex_Ioi (-a) : Convex ℝ (Set.Ioi (-a)))
  · simpa [posDomain] using (isOpen_Ioi : IsOpen (Set.Ioi (-a)))
  · exact ⟨-a + 1, by simp [posDomain]⟩
  · intro x hx
    exact hasDerivAtPosPrimitiveAux a b x hab hx

theorem gap12 (a b x : ℝ) (hab : a < b) (hx : x ∈ negDomain b) :
    Real.sqrt (radicand a b x) =
      (b - a) * Real.sinh (tNeg a b x) * Real.cosh (tNeg a b x) := by
  have hxb : x < -b := by simpa [negDomain] using hx
  have hA : 0 < -x - a := by linarith
  have hB : 0 < -x - b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hu : 0 < Real.sqrt (-x - a) := Real.sqrt_pos.2 hA
  have hv : 0 < Real.sqrt (-x - b) := Real.sqrt_pos.2 hB
  have hrel : Real.sqrt (-x - a) ^ 2 - Real.sqrt (-x - b) ^ 2 = b - a := by
    rw [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    ring
  have hp := hyperbolicProductAux (Real.sqrt (-x - a))
    (Real.sqrt (-x - b)) (b - a) hu hv hd (Or.inr hrel)
  have hr : radicand a b x = (-x - a) * (-x - b) := by
    unfold radicand
    ring
  rw [hr, Real.sqrt_mul hA.le]
  simpa [tNeg] using hp.symm

theorem gap13 (a b x : ℝ) (hab : a < b) (hx : x ∈ negDomain b) :
    1 = -2 * (b - a) * Real.sinh (tNeg a b x) *
      Real.cosh (tNeg a b x) * deriv (tNeg a b) x := by
  have hx' : x < -b := by simpa [negDomain] using hx
  have hA : 0 < -x - a := by linarith
  have hB : 0 < -x - b := by linarith
  have hrad : 0 < radicand a b x := by
    unfold radicand
    nlinarith [mul_pos hA hB]
  have hr : 0 < Real.sqrt (radicand a b x) := Real.sqrt_pos.2 hrad
  rw [(hasDerivAtTNegAux a b x hab hx).deriv]
  field_simp [hr.ne']
  nlinarith [gap12 a b x hab hx]

theorem gap14 (a b x : ℝ) (hab : a < b) (hx : x ∈ negDomain b) :
    integrand a b x = -2 * deriv (tNeg a b) x := by
  have hx' : x < -b := by simpa [negDomain] using hx
  have hA : 0 < -x - a := by linarith
  have hB : 0 < -x - b := by linarith
  have hrad : 0 < radicand a b x := by
    unfold radicand
    nlinarith [mul_pos hA hB]
  have hr : 0 < Real.sqrt (radicand a b x) := Real.sqrt_pos.2 hrad
  rw [(hasDerivAtTNegAux a b x hab hx).deriv]
  unfold integrand
  field_simp [hr.ne']

theorem gap15 (a b x : ℝ) (hab : a < b) (hx : x ∈ negDomain b) :
    HasDerivAt (fun y => -2 * tNeg a b y) (integrand a b x) x := by
  have ht := hasDerivAtTNegAux a b x hab hx
  simpa only [gap14 a b x hab hx, ht.deriv] using ht.const_mul (-2)

theorem gap16 (a b x : ℝ) :
    tNeg a b x =
      Real.log ((Real.sqrt (-x - a) + Real.sqrt (-x - b)) /
        Real.sqrt (b - a)) := by
  rfl

theorem gap17 (a b : ℝ) (hab : a < b) :
    Family (integrand a b) (negDomain b) =
      Translates (negPrimitive a b) (negDomain b) := by
  refine familyEqTranslatesOfConvex
    (f := integrand a b) (P := negPrimitive a b) (s := negDomain b) ?_ ?_ ?_ ?_
  · simpa [negDomain] using
      (convex_Iio (-b) : Convex ℝ (Set.Iio (-b)))
  · simpa [negDomain] using (isOpen_Iio : IsOpen (Set.Iio (-b)))
  · exact ⟨-b - 1, by simp [negDomain]⟩
  · intro x hx
    exact hasDerivAtNegPrimitiveAux a b x hab hx

theorem gap18 (a b : ℝ) (hab : a < b) :
    Family (integrand a b) (posDomain a) =
        Translates (posPrimitive a b) (posDomain a) ∧
      Family (integrand a b) (negDomain b) =
        Translates (negPrimitive a b) (negDomain b) := by
  exact ⟨gap11 a b hab, gap17 a b hab⟩

end

end ProofGap.Exercise1789
