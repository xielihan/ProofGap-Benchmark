import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace ProofGap.Exercise1953

noncomputable section

def q (x : ℝ) := x ^ 2 - x - 1
def branch : Set ℝ := {x | q x > 0 ∧ x ≠ -1}
def parameterBranch : Set ℝ := {t | t ≠ 0 ∧ t ^ 2 - 3 * t + 1 > 0}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def WeightedSumFamily (A B : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ A, ∃ H ∈ B, ∀ x ∈ branch, F x = 1 / 2 * G x + 1 / 2 * H x}
def integrand (x : ℝ) := x / ((x ^ 2 - 1) * Real.sqrt (q x))
def combinedIntegrand (x : ℝ) :=
  (1 / (x + 1) + 1 / (x - 1)) / Real.sqrt (q x)
def i1Integrand (x : ℝ) := 1 / ((x + 1) * Real.sqrt (q x))
def i2Integrand (x : ℝ) := 1 / ((x - 1) * Real.sqrt (q x))
def xOf (t : ℝ) := -1 + 1 / t
def I1 := AntiderivativesOn branch i1Integrand
def I2 := AntiderivativesOn branch i2Integrand
def PullbackI1Family : Set (ℝ → ℝ) :=
  {G | ∃ F ∈ I1, ∀ t ∈ parameterBranch, G t = F (xOf t)}
def HalfCombinedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn branch combinedIntegrand,
    ∀ x ∈ branch, F x = 1 / 2 * G x}
def transformedI1 (t : ℝ) :=
  Real.sign t / Real.sqrt (t ^ 2 - 3 * t + 1)
def NegativeI1Family : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn parameterBranch transformedI1,
    ∀ t ∈ parameterBranch, F t = -G t}
def i1ParamPrimitive (t : ℝ) :=
  -Real.sign t *
    Real.log |t - 3 / 2 + Real.sqrt (t ^ 2 - 3 * t + 1)|
def i1Primitive (x : ℝ) :=
  -Real.log |(3 * x + 1 - 2 * Real.sqrt (q x)) / (x + 1)|
def i2Primitive (x : ℝ) :=
  Real.arcsin ((x - 3) / (|x - 1| * Real.sqrt 5))
def finalPrimitive (x : ℝ) :=
  -1 / 2 * Real.log
      |(3 * x + 1 - 2 * Real.sqrt (q x)) / (x + 1)| +
    1 / 2 * Real.arcsin ((x - 3) / (|x - 1| * Real.sqrt 5))

private lemma branch_isOpen : IsOpen branch := by
  have hq : Continuous q := by
    unfold q
    fun_prop
  rw [show branch = {x | 0 < q x} ∩ ({-1} : Set ℝ)ᶜ by
    ext x
    simp [branch]]
  exact (isOpen_lt continuous_const hq).inter isClosed_singleton.isOpen_compl

private lemma parameterBranch_isOpen : IsOpen parameterBranch := by
  have hr : Continuous (fun t : ℝ => t ^ 2 - 3 * t + 1) := by
    fun_prop
  rw [show parameterBranch =
      ({0} : Set ℝ)ᶜ ∩ {t | 0 < t ^ 2 - 3 * t + 1} by
    ext t
    simp [parameterBranch, and_comm]]
  exact isClosed_singleton.isOpen_compl.inter
    (isOpen_lt continuous_const hr)

private lemma combined_eq_two_integrand (x : ℝ) (hx : x ∈ branch) :
    combinedIntegrand x = 2 * integrand x := by
  have hq : 0 < q x := hx.1
  have hxp1 : x + 1 ≠ 0 := by
    intro h
    apply hx.2
    linarith
  have hxm1 : x - 1 ≠ 0 := by
    intro h
    have : x = 1 := by linarith
    subst x
    norm_num [q] at hq
  have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hsq : x ^ 2 - 1 ≠ 0 := by
    rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring]
    exact mul_ne_zero hxp1 hxm1
  unfold combinedIntegrand integrand
  field_simp [hxp1, hxm1, hs, hsq]
  ring

private lemma two_integrand_sub_i1_eq_i2 (x : ℝ) (hx : x ∈ branch) :
    2 * integrand x - i1Integrand x = i2Integrand x := by
  have hq : 0 < q x := hx.1
  have hxp1 : x + 1 ≠ 0 := by
    intro h
    apply hx.2
    linarith
  have hxm1 : x - 1 ≠ 0 := by
    intro h
    have : x = 1 := by linarith
    subst x
    norm_num [q] at hq
  have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hsq : x ^ 2 - 1 ≠ 0 := by
    rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring]
    exact mul_ne_zero hxp1 hxm1
  unfold integrand i1Integrand i2Integrand
  field_simp [hxp1, hxm1, hs, hsq]
  ring

private lemma antiderivatives_eq_branchwise
    {s : Set ℝ} (hs : IsOpen s) {g p : ℝ → ℝ}
    (hp : ∀ x ∈ s, HasDerivAt p (g x) x) :
    AntiderivativesOn s g = BranchwisePrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF u hu huconn hus
    have hz : ∀ x ∈ u, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      convert (hF x (hus hx)).sub (hp x (hus hx)) using 1
      ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) u :=
      fun x hx => (hz x hx).differentiableAt.differentiableWithinAt
    have hderiv : u.EqOn (deriv (fun y => F y - p y)) 0 :=
      fun x hx => (hz x hx).deriv
    obtain ⟨C, hC⟩ :=
      hu.exists_is_const_of_deriv_eq_zero huconn hdiff hderiv
    exact ⟨C, fun x hx => by
      have := hC x hx
      linarith⟩
  · intro hF x hx
    rcases mem_nhds_iff_exists_Ioo_subset.1 (hs.mem_nhds hx) with
      ⟨a, b, hxab, hab⟩
    rcases hF (Set.Ioo a b) isOpen_Ioo isPreconnected_Ioo hab with
      ⟨C, hC⟩
    have hevent : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [Ioo_mem_nhds hxab.1 hxab.2] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq hevent

private lemma hasDerivAt_log_abs {u : ℝ → ℝ} {u' x : ℝ}
    (hu : HasDerivAt u u' x) (hne : u x ≠ 0) :
    HasDerivAt (fun y => Real.log |u y|) (u' / u x) x := by
  have h := (Real.hasDerivAt_log hne).comp x hu
  simpa [Real.log_abs, div_eq_mul_inv, mul_comm] using h

private lemma hasDerivAt_sqrt_q (x : ℝ) (hx : 0 < q x) :
    HasDerivAt (fun y => Real.sqrt (q y))
      ((2 * x - 1) / (2 * Real.sqrt (q x))) x := by
  have hq : HasDerivAt q (2 * x - 1) x := by
    unfold q
    convert (((hasDerivAt_id x).pow 2).sub (hasDerivAt_id x)).sub_const 1 using 1 <;>
      simp [id] <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hx)).comp x hq
  convert hs using 1 <;> simp [div_eq_mul_inv] <;> ring

private lemma hasDerivAt_i1Primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt i1Primitive (i1Integrand x) x := by
  have hqpos : 0 < q x := hx.1
  have hspos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 hqpos
  have hs0 : Real.sqrt (q x) ≠ 0 := ne_of_gt hspos
  have hxp1 : x + 1 ≠ 0 := by
    intro h
    apply hx.2
    linarith
  let A : ℝ → ℝ :=
    fun y => (3 * y + 1 - 2 * Real.sqrt (q y)) / (y + 1)
  have hs := hasDerivAt_sqrt_q x hqpos
  have hn :
      HasDerivAt (fun y => 3 * y + 1 - 2 * Real.sqrt (q y))
        (3 - 2 * ((2 * x - 1) / (2 * Real.sqrt (q x)))) x := by
    convert (((hasDerivAt_id x).const_mul 3).add_const 1).sub
      (hs.const_mul 2) using 1 <;> simp [id] <;> ring
  have hd : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const 1
  have hA := hn.div hd hxp1
  have hsquare : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt hqpos.le
  have hnum0 : 3 * x + 1 - 2 * Real.sqrt (q x) ≠ 0 := by
    intro hzero
    have hsrel : 2 * Real.sqrt (q x) = 3 * x + 1 := by linarith
    have hsqrel : (2 * Real.sqrt (q x)) ^ 2 = (3 * x + 1) ^ 2 :=
      congrArg (fun z : ℝ => z ^ 2) hsrel
    unfold q at hsquare hsqrel
    have hxeq : x = -1 := by
      nlinarith [hsqrel]
    exact hx.2 hxeq
  have hA0 : A x ≠ 0 := by
    dsimp [A]
    exact div_ne_zero hnum0 hxp1
  have hxp1' : 1 + x ≠ 0 := by
    intro h
    apply hxp1
    linarith
  have hnum0' : 1 + (x * 3 - Real.sqrt (q x) * 2) ≠ 0 := by
    intro h
    apply hnum0
    linarith
  have hinvnum :
      (1 + (x * 3 - Real.sqrt (q x) * 2))⁻¹ *
          (1 + (x * 3 - Real.sqrt (q x) * 2)) = 1 :=
    inv_mul_cancel₀ hnum0'
  have hlog := hasDerivAt_log_abs hA hA0
  unfold i1Primitive i1Integrand
  dsimp [A] at hlog
  convert hlog.neg using 1
  field_simp [hxp1, hxp1', hs0, hnum0, hnum0']
  ring_nf at hinvnum ⊢
  have hsquare' : (Real.sqrt (q x)) ^ 2 = x ^ 2 - x - 1 := by
    simpa [q] using hsquare
  linear_combination
    -hinvnum +
      2 * (1 + (x * 3 - Real.sqrt (q x) * 2))⁻¹ * hsquare'

private lemma hasDerivAt_i2Primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt i2Primitive (i2Integrand x) x := by
  have hqpos : 0 < q x := hx.1
  have hxm1 : x - 1 ≠ 0 := by
    intro h
    have : x = 1 := by linarith
    subst x
    norm_num [q] at hqpos
  have habspos : 0 < |x - 1| := abs_pos.2 hxm1
  have hs5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs5ne : Real.sqrt 5 ≠ 0 := ne_of_gt hs5pos
  have hdenpos : 0 < |x - 1| * Real.sqrt 5 :=
    mul_pos habspos hs5pos
  have hden0 : |x - 1| * Real.sqrt 5 ≠ 0 := ne_of_gt hdenpos
  have hs5sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have habssq : |x - 1| ^ 2 = (x - 1) ^ 2 := by
    rw [sq_abs]
  let u : ℝ → ℝ :=
    fun y => (y - 3) / (|y - 1| * Real.sqrt 5)
  have hone_eq :
      1 - (u x) ^ 2 =
        4 * q x / (|x - 1| * Real.sqrt 5) ^ 2 := by
    dsimp [u]
    field_simp [hden0]
    rw [habssq, hs5sq]
    unfold q
    ring
  have honepos : 0 < 1 - (u x) ^ 2 := by
    rw [hone_eq]
    positivity
  have hune : u x ≠ -1 ∧ u x ≠ 1 := by
    constructor <;> intro h <;> rw [h] at honepos <;> norm_num at honepos
  have hsquare : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt hqpos.le
  have hsqrt :
      Real.sqrt (1 - (u x) ^ 2) =
        2 * Real.sqrt (q x) / (|x - 1| * Real.sqrt 5) := by
    apply (Real.sqrt_eq_iff_eq_sq honepos.le (by positivity)).2
    rw [hone_eq]
    field_simp [hden0]
    nlinarith [hsquare]
  rcases lt_or_gt_of_ne hxm1 with hlt | hgt
  · have habsderiv :
        HasDerivAt (fun y : ℝ => |y - 1|) (-1) x := by
      convert (hasDerivAt_abs_neg hlt).comp x
        ((hasDerivAt_id x).sub_const 1) using 1 <;> simp
    have huderiv :
        HasDerivAt u
          ((1 * (|x - 1| * Real.sqrt 5) -
              (x - 3) * (-1 * Real.sqrt 5)) /
            (|x - 1| * Real.sqrt 5) ^ 2) x := by
      exact ((hasDerivAt_id x).sub_const 3).div
        (habsderiv.mul_const (Real.sqrt 5)) hden0
    have harc := (Real.hasDerivAt_arcsin hune.1 hune.2).comp x huderiv
    unfold i2Primitive i2Integrand
    dsimp [u] at harc
    convert harc using 1
    rw [hsqrt, abs_of_neg hlt]
    field_simp [hxm1, hs5ne, ne_of_gt (Real.sqrt_pos.2 hqpos)]
    ring
  · have habsderiv :
        HasDerivAt (fun y : ℝ => |y - 1|) 1 x := by
      convert (hasDerivAt_abs_pos hgt).comp x
        ((hasDerivAt_id x).sub_const 1) using 1 <;> simp
    have huderiv :
        HasDerivAt u
          ((1 * (|x - 1| * Real.sqrt 5) -
              (x - 3) * (1 * Real.sqrt 5)) /
            (|x - 1| * Real.sqrt 5) ^ 2) x := by
      exact ((hasDerivAt_id x).sub_const 3).div
        (habsderiv.mul_const (Real.sqrt 5)) hden0
    have harc := (Real.hasDerivAt_arcsin hune.1 hune.2).comp x huderiv
    unfold i2Primitive i2Integrand
    dsimp [u] at harc
    convert harc using 1
    rw [hsqrt, abs_of_pos hgt]
    field_simp [hxm1, hs5ne, ne_of_gt (Real.sqrt_pos.2 hqpos)]
    ring

private lemma hasDerivAt_finalPrimitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt finalPrimitive (integrand x) x := by
  have hd :=
    ((hasDerivAt_i1Primitive x hx).const_mul (1 / 2 : ℝ)).add
      ((hasDerivAt_i2Primitive x hx).const_mul (1 / 2 : ℝ))
  convert hd using 1
  · funext y
    unfold finalPrimitive i1Primitive i2Primitive
    simp only [Pi.add_apply]
    congr 1
    · ring
  · have hrel := two_integrand_sub_i1_eq_i2 x hx
    linarith

private lemma hasDerivAt_i1ParamPrimitive
    (t : ℝ) (ht : t ∈ parameterBranch) :
    HasDerivAt i1ParamPrimitive (-transformedI1 t) t := by
  have ht0 : t ≠ 0 := ht.1
  have hrpos : 0 < t ^ 2 - 3 * t + 1 := ht.2
  have hspos : 0 < Real.sqrt (t ^ 2 - 3 * t + 1) :=
    Real.sqrt_pos.2 hrpos
  have hs0 : Real.sqrt (t ^ 2 - 3 * t + 1) ≠ 0 := ne_of_gt hspos
  have hsquare :
      (Real.sqrt (t ^ 2 - 3 * t + 1)) ^ 2 =
        t ^ 2 - 3 * t + 1 :=
    Real.sq_sqrt hrpos.le
  let v : ℝ → ℝ :=
    fun y => y - 3 / 2 + Real.sqrt (y ^ 2 - 3 * y + 1)
  have hsqrt :
      HasDerivAt (fun y => Real.sqrt (y ^ 2 - 3 * y + 1))
        ((2 * t - 3) /
          (2 * Real.sqrt (t ^ 2 - 3 * t + 1))) t := by
    have hpoly :
        HasDerivAt (fun y : ℝ => y ^ 2 - 3 * y + 1) (2 * t - 3) t := by
      convert (((hasDerivAt_id t).pow 2).sub
        ((hasDerivAt_id t).const_mul 3)).add_const 1 using 1 <;>
        simp [id] <;> ring
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrpos)).comp t hpoly using 1 <;>
      field_simp [hs0] <;> ring
  have hv :
      HasDerivAt v
        (1 + (2 * t - 3) /
          (2 * Real.sqrt (t ^ 2 - 3 * t + 1))) t := by
    dsimp [v]
    convert ((hasDerivAt_id t).sub_const (3 / 2 : ℝ)).add hsqrt using 1 <;>
      ring
  have hv0 : v t ≠ 0 := by
    intro h
    have hrel :
        Real.sqrt (t ^ 2 - 3 * t + 1) = 3 / 2 - t := by
      dsimp [v] at h
      linarith
    have hsqrel :
        (Real.sqrt (t ^ 2 - 3 * t + 1)) ^ 2 =
          (3 / 2 - t) ^ 2 := by rw [hrel]
    nlinarith [hsquare, hsqrel]
  have hlog := hasDerivAt_log_abs hv hv0
  have hw0 :
      -3 + t * 2 + Real.sqrt (t ^ 2 - 3 * t + 1) * 2 ≠ 0 := by
    intro h
    apply hv0
    dsimp [v]
    linarith
  have hlog' :
      HasDerivAt (fun y => Real.log |v y|)
        (1 / Real.sqrt (t ^ 2 - 3 * t + 1)) t := by
    convert hlog using 1
    dsimp [v]
    ring_nf at hs0 hw0 ⊢
    field_simp [hs0, hw0]
    ring
  have hsign :
      (fun y : ℝ => Real.sign y) =ᶠ[nhds t]
        fun _ => Real.sign t := by
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · filter_upwards [Iio_mem_nhds hneg] with y hy
      rw [Real.sign_of_neg hy, Real.sign_of_neg hneg]
    · filter_upwards [Ioi_mem_nhds hpos] with y hy
      rw [Real.sign_of_pos hy, Real.sign_of_pos hpos]
  have hpconst :=
    hlog'.const_mul (-Real.sign t)
  have hevent :
      i1ParamPrimitive =ᶠ[nhds t]
        fun y => -Real.sign t * Real.log |v y| := by
    filter_upwards [hsign] with y hy
    simp [i1ParamPrimitive, v, hy]
  convert hpconst.congr_of_eventuallyEq hevent using 1
  unfold transformedI1
  ring

private lemma negativeI1Family_eq_antiderivatives :
    NegativeI1Family =
      AntiderivativesOn parameterBranch (fun t => -transformedI1 t) := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩ t ht
    have hd := (hG t ht).neg
    have hevent : F =ᶠ[nhds t] fun y => -G y := by
      filter_upwards [parameterBranch_isOpen.mem_nhds ht] with y hy
      exact hFG y hy
    exact hd.congr_of_eventuallyEq hevent
  · intro hF
    refine ⟨fun t => -F t, ?_, ?_⟩
    · intro t ht
      convert (hF t ht).neg using 1 <;> simp
    · intro t ht
      simp

theorem gap1 :
    AntiderivativesOn branch integrand = HalfCombinedFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul 2
      convert hd using 1
      rw [combined_eq_two_integrand x hx]
    · intro x hx
      ring
  · intro hF
    rcases hF with ⟨G, hG, hFG⟩
    intro x hx
    have hd := (hG x hx).const_mul (1 / 2 : ℝ)
    have hevent : F =ᶠ[nhds x] fun y => 1 / 2 * G y := by
      filter_upwards [branch_isOpen.mem_nhds hx] with y hy
      exact hFG y hy
    have hlocal := hd.congr_of_eventuallyEq hevent
    convert hlocal using 1
    rw [combined_eq_two_integrand x hx]
    ring
theorem gap2 :
    AntiderivativesOn branch integrand = WeightedSumFamily I1 I2 := by
  ext F
  constructor
  · intro hF
    refine ⟨i1Primitive, ?_, (fun x => 2 * F x - i1Primitive x), ?_, ?_⟩
    · intro x hx
      exact hasDerivAt_i1Primitive x hx
    · intro x hx
      convert ((hF x hx).const_mul 2).sub (hasDerivAt_i1Primitive x hx) using 1
      exact (two_integrand_sub_i1_eq_i2 x hx).symm
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, hF⟩ x hx
    have hd :=
      ((hG x hx).const_mul (1 / 2 : ℝ)).add
        ((hH x hx).const_mul (1 / 2 : ℝ))
    have hevent :
        F =ᶠ[nhds x] fun y => 1 / 2 * G y + 1 / 2 * H y := by
      filter_upwards [branch_isOpen.mem_nhds hx] with y hy
      exact hF y hy
    have hlocal := hd.congr_of_eventuallyEq hevent
    convert hlocal using 1
    have hrel := two_integrand_sub_i1_eq_i2 x hx
    linarith
theorem gap3 :
    ∃ A B : Set (ℝ → ℝ),
      A = I1 ∧ B = I2 ∧ WeightedSumFamily I1 I2 = WeightedSumFamily A B := by
  exact ⟨I1, I2, rfl, rfl, rfl⟩
theorem gap4 :
    ∃ A B : Set (ℝ → ℝ),
      A = I1 ∧ B = I2 ∧
        AntiderivativesOn branch integrand = WeightedSumFamily A B := by
  exact ⟨I1, I2, rfl, rfl, gap2⟩
theorem gap5 :
    ∃ X : ℝ → ℝ, X = xOf ∧
      ∀ t ∈ parameterBranch, HasDerivAt X (-1 / t ^ 2) t := by
  refine ⟨xOf, rfl, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := ht.1
  unfold xOf
  convert (hasDerivAt_const t (-1 : ℝ)).add
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0) using 1 <;>
    simp [id] <;> field_simp [ht0] <;> ring
theorem gap6 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (q (xOf t)) =
      Real.sqrt (t ^ 2 - 3 * t + 1) / |t| := by
  have ht0 : t ≠ 0 := ht.1
  have hrad : 0 < t ^ 2 - 3 * t + 1 := ht.2
  have hq : q (xOf t) = (t ^ 2 - 3 * t + 1) / t ^ 2 := by
    unfold q xOf
    field_simp [ht0]
    ring
  rw [hq, Real.sqrt_div hrad.le, Real.sqrt_sq_eq_abs]

private def parameterOf (x : ℝ) := 1 / (x + 1)

private lemma xOf_mem_branch (t : ℝ) (ht : t ∈ parameterBranch) :
    xOf t ∈ branch := by
  have ht0 : t ≠ 0 := ht.1
  have hq :
      q (xOf t) = (t ^ 2 - 3 * t + 1) / t ^ 2 := by
    unfold q xOf
    field_simp [ht0]
    ring
  constructor
  · rw [hq]
    exact div_pos ht.2 (sq_pos_of_ne_zero ht0)
  · intro h
    unfold xOf at h
    have hone : (1 : ℝ) / t = 0 := by linarith
    exact (div_ne_zero one_ne_zero ht0) hone

private lemma parameterOf_mem_parameterBranch
    (x : ℝ) (hx : x ∈ branch) :
    parameterOf x ∈ parameterBranch := by
  have hxp1 : x + 1 ≠ 0 := by
    intro h
    apply hx.2
    linarith
  constructor
  · exact div_ne_zero one_ne_zero hxp1
  · have heq :
        (parameterOf x) ^ 2 - 3 * parameterOf x + 1 =
          q x / (x + 1) ^ 2 := by
      unfold parameterOf q
      field_simp [hxp1]
      ring
    rw [heq]
    exact div_pos hx.1 (sq_pos_of_ne_zero hxp1)

private lemma xOf_parameterOf (x : ℝ) (hxp1 : x + 1 ≠ 0) :
    xOf (parameterOf x) = x := by
  unfold xOf parameterOf
  field_simp [hxp1]
  ring

private lemma hasDerivAt_xOf (t : ℝ) (ht0 : t ≠ 0) :
    HasDerivAt xOf (-1 / t ^ 2) t := by
  unfold xOf
  convert (hasDerivAt_const t (-1 : ℝ)).add
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0) using 1 <;>
    simp [id] <;> field_simp [ht0] <;> ring

private lemma hasDerivAt_parameterOf (x : ℝ) (hxp1 : x + 1 ≠ 0) :
    HasDerivAt parameterOf (-1 / (x + 1) ^ 2) x := by
  unfold parameterOf
  convert (hasDerivAt_const x (1 : ℝ)).div
    ((hasDerivAt_id x).add_const 1) hxp1 using 1 <;>
    simp [id] <;> field_simp [hxp1] <;> ring

private lemma pullback_deriv_identity
    (t : ℝ) (ht : t ∈ parameterBranch) :
    i1Integrand (xOf t) * (-1 / t ^ 2) = -transformedI1 t := by
  have ht0 : t ≠ 0 := ht.1
  have hs0 :
      Real.sqrt (t ^ 2 - 3 * t + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 ht.2)
  unfold i1Integrand
  rw [show Real.sqrt (q (xOf t)) =
      Real.sqrt (t ^ 2 - 3 * t + 1) / |t| from gap6 t ht]
  unfold transformedI1 xOf
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · rw [abs_of_neg hneg, Real.sign_of_neg hneg]
    field_simp [ht0, hs0]
    ring
  · rw [abs_of_pos hpos, Real.sign_of_pos hpos]
    field_simp [ht0, hs0]
    ring
theorem gap7 :
    PullbackI1Family = NegativeI1Family := by
  rw [negativeI1Family_eq_antiderivatives]
  ext G
  constructor
  · rintro ⟨F, hF, hGF⟩ t ht
    have hd :=
      (hF (xOf t) (xOf_mem_branch t ht)).comp t
        (hasDerivAt_xOf t ht.1)
    have hevent : G =ᶠ[nhds t] fun y => F (xOf y) := by
      filter_upwards [parameterBranch_isOpen.mem_nhds ht] with y hy
      exact hGF y hy
    have hlocal := hd.congr_of_eventuallyEq hevent
    convert hlocal using 1
    exact (pullback_deriv_identity t ht).symm
  · intro hG
    refine ⟨fun x => G (parameterOf x), ?_, ?_⟩
    · intro x hx
      have hxp1 : x + 1 ≠ 0 := by
        intro h
        apply hx.2
        linarith
      have ht := parameterOf_mem_parameterBranch x hx
      have hd :=
        (hG (parameterOf x) ht).comp x
          (hasDerivAt_parameterOf x hxp1)
      convert hd using 1
      have hforward := pullback_deriv_identity (parameterOf x) ht
      rw [xOf_parameterOf x hxp1] at hforward
      change i1Integrand x =
        -transformedI1 (parameterOf x) * (-1 / (x + 1) ^ 2)
      rw [← hforward]
      unfold parameterOf
      field_simp [hxp1]
    · intro t ht
      have ht0 : t ≠ 0 := ht.1
      unfold parameterOf xOf
      congr 1
      field_simp [ht0]
      ring
theorem gap8 :
    NegativeI1Family =
      BranchwisePrimitiveFamilyOn parameterBranch i1ParamPrimitive := by
  rw [negativeI1Family_eq_antiderivatives]
  exact antiderivatives_eq_branchwise parameterBranch_isOpen
    hasDerivAt_i1ParamPrimitive
theorem gap9 :
    PullbackI1Family =
      BranchwisePrimitiveFamilyOn parameterBranch i1ParamPrimitive := by
  rw [gap7, gap8]
theorem gap10 :
    I1 = BranchwisePrimitiveFamilyOn branch i1Primitive := by
  exact antiderivatives_eq_branchwise branch_isOpen hasDerivAt_i1Primitive
theorem gap11 :
    I2 = BranchwisePrimitiveFamilyOn branch i2Primitive := by
  exact antiderivatives_eq_branchwise branch_isOpen hasDerivAt_i2Primitive
theorem gap12 :
    AntiderivativesOn branch integrand =
      BranchwisePrimitiveFamilyOn branch finalPrimitive := by
  exact antiderivatives_eq_branchwise branch_isOpen hasDerivAt_finalPrimitive

end
end ProofGap.Exercise1953
