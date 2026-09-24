import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1790

noncomputable section

def radicand (a b x : ℝ) : ℝ := (x + a) * (x + b)
def integrand (a b x : ℝ) : ℝ := Real.sqrt (radicand a b x)
def posDomain (a : ℝ) : Set ℝ := Set.Ioi (-a)
def negDomain (b : ℝ) : Set ℝ := Set.Iio (-b)
def tPos (a b x : ℝ) : ℝ :=
  Real.log ((Real.sqrt (x + a) + Real.sqrt (x + b)) / Real.sqrt (b - a))
def posPrimitive (a b x : ℝ) : ℝ :=
  (2 * x + a + b) / 4 * Real.sqrt (radicand a b x) -
    (b - a) ^ 2 / 4 *
      Real.log (Real.sqrt (x + a) + Real.sqrt (x + b))
def negPrimitive (a b x : ℝ) : ℝ :=
  (2 * x + a + b) / 4 * Real.sqrt (radicand a b x) +
    (b - a) ^ 2 / 4 *
      Real.log (Real.sqrt (-x - a) + Real.sqrt (-x - b))
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem positive_substitution_facts
    (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    HasDerivAt (tPos a b)
        (1 / (2 * (Real.sqrt (x + a) * Real.sqrt (x + b)))) x ∧
      Real.sinh (tPos a b x) =
        Real.sqrt (x + a) / Real.sqrt (b - a) ∧
      Real.cosh (tPos a b x) =
        Real.sqrt (x + b) / Real.sqrt (b - a) ∧
      integrand a b x = Real.sqrt (x + a) * Real.sqrt (x + b) ∧
      Real.sqrt (b - a) ^ 2 = b - a := by
  have hp : 0 < x + a := by
    change -a < x at hx
    linarith
  have hq : 0 < x + b := by linarith
  have hd : 0 < b - a := sub_pos.2 hab
  have hu : 0 < Real.sqrt (x + a) := Real.sqrt_pos.2 hp
  have hv : 0 < Real.sqrt (x + b) := Real.sqrt_pos.2 hq
  have hr : 0 < Real.sqrt (b - a) := Real.sqrt_pos.2 hd
  have hu2 : Real.sqrt (x + a) ^ 2 = x + a := Real.sq_sqrt hp.le
  have hv2 : Real.sqrt (x + b) ^ 2 = x + b := Real.sq_sqrt hq.le
  have hr2 : Real.sqrt (b - a) ^ 2 = b - a := Real.sq_sqrt hd.le
  have hdu : HasDerivAt (fun y : ℝ => Real.sqrt (y + a))
      (1 / (2 * Real.sqrt (x + a))) x := by
    convert (Real.hasDerivAt_sqrt hp.ne').comp x
      ((hasDerivAt_id x).add_const a) using 1 <;> ring
  have hdv : HasDerivAt (fun y : ℝ => Real.sqrt (y + b))
      (1 / (2 * Real.sqrt (x + b))) x := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp x
      ((hasDerivAt_id x).add_const b) using 1 <;> ring
  have hsum := hdu.add hdv
  have hquot := hsum.div_const (Real.sqrt (b - a))
  have hratio : 0 <
      (Real.sqrt (x + a) + Real.sqrt (x + b)) / Real.sqrt (b - a) :=
    div_pos (add_pos hu hv) hr
  have hlog := (Real.hasDerivAt_log hratio.ne').comp x hquot
  have htRaw : HasDerivAt (tPos a b)
      (((Real.sqrt (x + a) + Real.sqrt (x + b)) / Real.sqrt (b - a))⁻¹ *
        ((1 / (2 * Real.sqrt (x + a)) +
          1 / (2 * Real.sqrt (x + b))) / Real.sqrt (b - a))) x := by
    simpa [tPos] using hlog
  have ht : HasDerivAt (tPos a b)
      (1 / (2 * (Real.sqrt (x + a) * Real.sqrt (x + b)))) x := by
    convert htRaw using 1
    field_simp [hu.ne', hv.ne', hr.ne', (add_pos hu hv).ne']
    ring
  have he : Real.exp (tPos a b x) =
      (Real.sqrt (x + a) + Real.sqrt (x + b)) / Real.sqrt (b - a) := by
    rw [tPos, Real.exp_log hratio]
  have hs : Real.sinh (tPos a b x) =
      Real.sqrt (x + a) / Real.sqrt (b - a) := by
    rw [Real.sinh_eq, Real.exp_neg, he]
    field_simp [hu.ne', hv.ne', hr.ne', (add_pos hu hv).ne']
    nlinarith [hu2, hv2, hr2]
  have hc : Real.cosh (tPos a b x) =
      Real.sqrt (x + b) / Real.sqrt (b - a) := by
    rw [Real.cosh_eq, Real.exp_neg, he]
    field_simp [hu.ne', hv.ne', hr.ne', (add_pos hu hv).ne']
    nlinarith [hu2, hv2, hr2]
  have hroot : integrand a b x =
      Real.sqrt (x + a) * Real.sqrt (x + b) := by
    unfold integrand radicand
    rw [Real.sqrt_mul hp.le]
  exact ⟨ht, hs, hc, hroot, hr2⟩

private theorem sinh_four_quarter (z : ℝ) :
    (1 / 4 : ℝ) * Real.sinh (4 * z) =
      Real.sinh z * Real.cosh z * (1 + 2 * Real.sinh z ^ 2) := by
  have hc : Real.cosh z ^ 2 = 1 + Real.sinh z ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq z]
  rw [show 4 * z = 2 * (2 * z) by ring, Real.sinh_two_mul,
    Real.sinh_two_mul, Real.cosh_two_mul, hc]
  ring

private theorem pos_transformed_identity
    (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    (1 / 4 : ℝ) * (b - a) ^ 2 *
      (Real.sinh (tPos a b x) * Real.cosh (tPos a b x) *
        (1 + 2 * Real.sinh (tPos a b x) ^ 2) - tPos a b x) =
      posPrimitive a b x + (b - a) ^ 2 / 8 * Real.log (b - a) := by
  obtain ⟨_, hs, hc, hroot, hr2⟩ := positive_substitution_facts a b x hab hx
  have hp : 0 < x + a := by
    change -a < x at hx
    linarith
  have hq : 0 < x + b := by linarith
  have hd : 0 < b - a := sub_pos.2 hab
  have hu : 0 < Real.sqrt (x + a) := Real.sqrt_pos.2 hp
  have hv : 0 < Real.sqrt (x + b) := Real.sqrt_pos.2 hq
  have hr : 0 < Real.sqrt (b - a) := Real.sqrt_pos.2 hd
  have hu2 : Real.sqrt (x + a) ^ 2 = x + a := Real.sq_sqrt hp.le
  have hsum : 0 < Real.sqrt (x + a) + Real.sqrt (x + b) := add_pos hu hv
  have hmul := Real.log_mul hr.ne' hr.ne'
  have hrr : Real.sqrt (b - a) * Real.sqrt (b - a) = b - a := by
    nlinarith [hr2]
  rw [hrr] at hmul
  have hlogr : Real.log (Real.sqrt (b - a)) =
      (1 / 2 : ℝ) * Real.log (b - a) := by
    linarith
  have htlog : tPos a b x =
      Real.log (Real.sqrt (x + a) + Real.sqrt (x + b)) -
        (1 / 2 : ℝ) * Real.log (b - a) := by
    rw [tPos, Real.log_div hsum.ne' hr.ne', hlogr]
  have hr4 : Real.sqrt (b - a) ^ 4 = (b - a) ^ 2 := by
    calc
      Real.sqrt (b - a) ^ 4 = (Real.sqrt (b - a) ^ 2) ^ 2 := by ring
      _ = (b - a) ^ 2 := by rw [hr2]
  have hmain :
      (1 / 4 : ℝ) * (b - a) ^ 2 *
        (Real.sinh (tPos a b x) * Real.cosh (tPos a b x) *
          (1 + 2 * Real.sinh (tPos a b x) ^ 2)) =
      (2 * x + a + b) / 4 * Real.sqrt (radicand a b x) := by
    rw [hs, hc]
    have hsqrt : Real.sqrt (radicand a b x) =
        Real.sqrt (x + a) * Real.sqrt (x + b) := by
      simpa [integrand] using hroot
    rw [hsqrt]
    field_simp [hr.ne']
    rw [hr4, hr2, hu2] <;> ring
  rw [show (1 / 4 : ℝ) * (b - a) ^ 2 *
      (Real.sinh (tPos a b x) * Real.cosh (tPos a b x) *
        (1 + 2 * Real.sinh (tPos a b x) ^ 2) - tPos a b x) =
      ((1 / 4 : ℝ) * (b - a) ^ 2 *
        (Real.sinh (tPos a b x) * Real.cosh (tPos a b x) *
          (1 + 2 * Real.sinh (tPos a b x) ^ 2))) -
        (b - a) ^ 2 / 4 * tPos a b x by ring]
  rw [hmain, htlog]
  simp only [posPrimitive]
  ring

private theorem family_eq_translates_on_open_convex
    (f P : ℝ → ℝ) (s : Set ℝ) (hsOpen : IsOpen s) (hsConv : Convex ℝ s)
    (x₀ : ℝ) (hx₀ : x₀ ∈ s)
    (hP : ∀ x ∈ s, HasDerivAt P (f x) x) :
    Family f s = Translates P s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F f s at hF
    change ∃ C, ∀ x ∈ s, F x = P x + C
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
    have hEq : G x = G x₀ :=
      hsOpen.is_const_of_deriv_eq_zero hsConv.isPreconnected
        hdiff hzero hx hx₀
    dsimp [G] at hEq ⊢
    linarith
  · rintro ⟨C, hFC⟩
    change IsAntiderivativeOn F f s
    intro x hx
    have hsN : s ∈ nhds x := hsOpen.mem_nhds hx
    have heq : F =ᶠ[nhds x] fun y => P y + C := by
      filter_upwards [hsN] with y hy
      exact hFC y hy
    have hPC : HasDerivAt (fun y => P y + C) (f x) x :=
      (hP x hx).add_const C
    exact hPC.congr_of_eventuallyEq heq

theorem gap1 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    integrand a b x =
      2 * (b - a) ^ 2 * Real.sinh (tPos a b x) ^ 2 *
        Real.cosh (tPos a b x) ^ 2 * deriv (tPos a b) x := by
  obtain ⟨ht, hs, hc, hroot, hr2⟩ := positive_substitution_facts a b x hab hx
  have hu : 0 < Real.sqrt (x + a) := Real.sqrt_pos.2 (by
    change -a < x at hx
    linarith)
  have hv : 0 < Real.sqrt (x + b) := Real.sqrt_pos.2 (by
    change -a < x at hx
    linarith)
  have hr : 0 < Real.sqrt (b - a) := Real.sqrt_pos.2 (sub_pos.2 hab)
  have hr4 : Real.sqrt (b - a) ^ 4 = (b - a) ^ 2 := by
    calc
      Real.sqrt (b - a) ^ 4 = (Real.sqrt (b - a) ^ 2) ^ 2 := by ring
      _ = (b - a) ^ 2 := by rw [hr2]
  rw [ht.deriv, hs, hc, hroot]
  field_simp [hu.ne', hv.ne', hr.ne']
  rw [hr4] <;> ring

theorem gap2 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    2 * (b - a) ^ 2 * Real.sinh (tPos a b x) ^ 2 *
        Real.cosh (tPos a b x) ^ 2 =
      (1 / 2 : ℝ) * (b - a) ^ 2 * Real.sinh (2 * tPos a b x) ^ 2 := by
  rw [Real.sinh_two_mul]
  ring

theorem gap3 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    integrand a b x =
      (1 / 2 : ℝ) * (b - a) ^ 2 * Real.sinh (2 * tPos a b x) ^ 2 *
        deriv (tPos a b) x := by
  calc
    integrand a b x =
        (2 * (b - a) ^ 2 * Real.sinh (tPos a b x) ^ 2 *
          Real.cosh (tPos a b x) ^ 2) * deriv (tPos a b) x := by
            simpa [mul_assoc] using gap1 a b x hab hx
    _ = ((1 / 2 : ℝ) * (b - a) ^ 2 *
          Real.sinh (2 * tPos a b x) ^ 2) * deriv (tPos a b) x := by
            rw [gap2 a b x hab hx]

theorem gap4 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    integrand a b x =
      (1 / 4 : ℝ) * (b - a) ^ 2 *
        (Real.cosh (4 * tPos a b x) - 1) * deriv (tPos a b) x := by
  have hsq : Real.sinh (2 * tPos a b x) ^ 2 =
      (Real.cosh (4 * tPos a b x) - 1) / 2 := by
    have hc := Real.cosh_sq_sub_sinh_sq (2 * tPos a b x)
    rw [show 4 * tPos a b x = 2 * (2 * tPos a b x) by ring,
      Real.cosh_two_mul]
    nlinarith
  rw [gap3 a b x hab hx, hsq]
  ring

theorem gap5 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    HasDerivAt
      (fun y => (1 / 4 : ℝ) * (b - a) ^ 2 *
        ((1 / 4 : ℝ) * Real.sinh (4 * tPos a b y) - tPos a b y))
      (integrand a b x) x := by
  obtain ⟨ht, _, _, _, _⟩ := positive_substitution_facts a b x hab hx
  have hsinh : HasDerivAt
      (Real.sinh ∘ fun y => 4 * tPos a b y)
      (Real.cosh (4 * tPos a b x) *
        (4 * (1 / (2 * (Real.sqrt (x + a) * Real.sqrt (x + b)))))) x := by
    exact (Real.hasDerivAt_sinh (4 * tPos a b x)).comp x (ht.const_mul 4)
  have hinner := (hsinh.const_mul (1 / 4 : ℝ)).sub ht
  have hout := hinner.const_mul ((1 / 4 : ℝ) * (b - a) ^ 2)
  have hg := gap4 a b x hab hx
  rw [ht.deriv] at hg
  convert hout using 1
  rw [hg]
  ring

theorem gap6 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    HasDerivAt (posPrimitive a b) (integrand a b x) x := by
  let Q : ℝ → ℝ := fun y => (1 / 4 : ℝ) * (b - a) ^ 2 *
    ((1 / 4 : ℝ) * Real.sinh (4 * tPos a b y) - tPos a b y)
  let C : ℝ := (b - a) ^ 2 / 8 * Real.log (b - a)
  have hQ : HasDerivAt Q (integrand a b x) x := by
    simpa [Q] using gap5 a b x hab hx
  have heq : Q =ᶠ[nhds x] fun y => posPrimitive a b y + C := by
    have hs : posDomain a ∈ nhds x :=
      (isOpen_Ioi : IsOpen (posDomain a)).mem_nhds hx
    filter_upwards [hs] with y hy
    calc
      Q y = (1 / 4 : ℝ) * (b - a) ^ 2 *
          (Real.sinh (tPos a b y) * Real.cosh (tPos a b y) *
            (1 + 2 * Real.sinh (tPos a b y) ^ 2) - tPos a b y) := by
              dsimp [Q]
              rw [sinh_four_quarter]
      _ = posPrimitive a b y + C := by
              simpa [C] using pos_transformed_identity a b y hab hy
  have hPC : HasDerivAt (fun y => posPrimitive a b y + C)
      (integrand a b x) x :=
    hQ.congr_of_eventuallyEq heq.symm
  simpa using hPC.sub_const C

theorem gap7 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    (1 / 4 : ℝ) * (b - a) ^ 2 *
      (Real.sinh (tPos a b x) * Real.cosh (tPos a b x) *
        (1 + 2 * Real.sinh (tPos a b x) ^ 2) - tPos a b x) =
      posPrimitive a b x + (b - a) ^ 2 / 8 * Real.log (b - a) := by
  exact pos_transformed_identity a b x hab hx

theorem gap8 (a b x : ℝ) (hab : a < b) (hx : x ∈ posDomain a) :
    HasDerivAt (posPrimitive a b) (integrand a b x) x := by
  exact gap6 a b x hab hx

theorem gap9 (a b : ℝ) (hab : a < b) :
    Family (integrand a b) (posDomain a) =
      Translates (posPrimitive a b) (posDomain a) := by
  refine family_eq_translates_on_open_convex
    (integrand a b) (posPrimitive a b) (posDomain a)
    (isOpen_Ioi : IsOpen (posDomain a))
    (show Convex ℝ (posDomain a) from convex_Ioi (-a))
    (-a + 1) ?_ ?_
  · change -a < -a + 1
    linarith
  · intro x hx
    exact gap6 a b x hab hx

theorem gap10 (a b : ℝ) (hab : a < b) :
    Family (integrand a b) (negDomain b) =
      Translates (negPrimitive a b) (negDomain b) := by
  have hneg : ∀ x ∈ negDomain b,
      HasDerivAt (negPrimitive a b) (integrand a b x) x := by
    intro x hx
    have hba : -b < -a := by linarith
    have hbneg : b < -x := by
      change x < -b at hx
      linarith
    have hdom : -x ∈ posDomain (-b) := by
      simpa [posDomain] using hbneg
    have hp := gap6 (-b) (-a) (-x) hba hdom
    have hcomp := hp.comp x ((hasDerivAt_id x).neg)
    have hraw := hcomp.neg
    have hfun : (fun y => -posPrimitive (-b) (-a) (-y)) =
        negPrimitive a b := by
      funext y
      simp [posPrimitive, negPrimitive, radicand, mul_comm, add_comm,
        add_left_comm]
      ring
    have hint : integrand (-b) (-a) (-x) = integrand a b x := by
      unfold integrand radicand
      congr 1
      ring
    change HasDerivAt (fun y => -posPrimitive (-b) (-a) (-y))
      (-(integrand (-b) (-a) (-x) * -1)) x at hraw
    rw [hfun] at hraw
    simpa [hint] using hraw
  refine family_eq_translates_on_open_convex
    (integrand a b) (negPrimitive a b) (negDomain b)
    (isOpen_Iio : IsOpen (negDomain b))
    (show Convex ℝ (negDomain b) from convex_Iio (-b))
    (-b - 1) ?_ hneg
  change -b - 1 < -b
  linarith

theorem gap11 (a b : ℝ) (hab : a < b) :
    Family (integrand a b) (posDomain a) =
        Translates (posPrimitive a b) (posDomain a) ∧
      Family (integrand a b) (negDomain b) =
        Translates (negPrimitive a b) (negDomain b) := by
  exact ⟨gap9 a b hab, gap10 a b hab⟩

end

end ProofGap.Exercise1790
