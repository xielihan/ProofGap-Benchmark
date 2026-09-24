import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1941

noncomputable section

def xOf (t : ℝ) := (1 - t) / t
def tOf (x : ℝ) := 1 / (1 + x)
def radicand (x : ℝ) := 1 - x - x ^ 2
def xBranch : Set ℝ := {x | radicand x > 0 ∧ x ≠ -1}
def rightBranch : Set ℝ := {x | radicand x > 0 ∧ x + 1 > 0}
def leftBranch : Set ℝ := {x | radicand x > 0 ∧ x + 1 < 0}
def parameterBranch : Set ℝ := {t | t ≠ 0 ∧ t ^ 2 + t - 1 > 0}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def integrand (x : ℝ) := x / ((1 + x) * Real.sqrt (radicand x))
def splitIntegrand (x : ℝ) :=
  1 / Real.sqrt (radicand x) -
    1 / ((1 + x) * Real.sqrt (radicand x))
def AuxiliaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn xBranch
      (fun x => 1 / Real.sqrt (radicand x)),
    ∃ B ∈ AntiderivativesOn parameterBranch
      (fun t => 1 / Real.sqrt (t ^ 2 + t - 1)),
    ∀ x ∈ xBranch, F x = A x + Real.sign (tOf x) * B (tOf x)}
def signedPrimitive (x : ℝ) :=
  Real.arcsin ((2 * x + 1) / Real.sqrt 5) +
    Real.sign (1 + x) *
      Real.log |(3 + x + 2 * Real.sign (x + 1) * Real.sqrt (radicand x)) /
        (2 * (1 + x))|
def rightPrimitive (x : ℝ) :=
  Real.arcsin ((2 * x + 1) / Real.sqrt 5) +
    Real.log |(3 + x + 2 * Real.sqrt (radicand x)) / (1 + x)|
def leftPrimitiveRaw (x : ℝ) :=
  Real.arcsin ((2 * x + 1) / Real.sqrt 5) -
    Real.log |(3 + x - 2 * Real.sqrt (radicand x)) / (2 * (1 + x))|
def unifiedPrimitive (x : ℝ) :=
  Real.arcsin ((2 * x + 1) / Real.sqrt 5) +
    Real.log |(3 + x + 2 * Real.sqrt (radicand x)) / (1 + x)|
def unifiedPrimitiveWithTwo (x : ℝ) :=
  Real.arcsin ((2 * x + 1) / Real.sqrt 5) +
    Real.log |(3 + x + 2 * Real.sqrt (radicand x)) / (2 * (1 + x))|

private theorem radicand_hasDerivAt (x : ℝ) :
    HasDerivAt radicand (-1 - 2 * x) x := by
  unfold radicand
  convert ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).sub
    ((hasDerivAt_id x).pow 2) using 1 <;>
    simp only [id_eq] <;> ring

private theorem xBranch_isOpen : IsOpen xBranch := by
  have hr : IsOpen {x : ℝ | 0 < radicand x} := by
    exact isOpen_Ioi.preimage
      (((continuous_const.sub continuous_id).sub (continuous_id.pow 2)))
  have hn : IsOpen {x : ℝ | x ≠ -1} := isOpen_ne
  exact hr.inter hn

private theorem rightBranch_isOpen : IsOpen rightBranch := by
  have hr : IsOpen {x : ℝ | 0 < radicand x} := by
    exact isOpen_Ioi.preimage
      (((continuous_const.sub continuous_id).sub (continuous_id.pow 2)))
  have hp : IsOpen {x : ℝ | 0 < x + 1} :=
    isOpen_Ioi.preimage (continuous_id.add continuous_const)
  exact hr.inter hp

private theorem leftBranch_isOpen : IsOpen leftBranch := by
  have hr : IsOpen {x : ℝ | 0 < radicand x} := by
    exact isOpen_Ioi.preimage
      (((continuous_const.sub continuous_id).sub (continuous_id.pow 2)))
  have hp : IsOpen {x : ℝ | x + 1 < 0} :=
    isOpen_Iio.preimage (continuous_id.add continuous_const)
  exact hr.inter hp

private theorem branchwise_antiderivatives
    {s : Set ℝ} (hopen : IsOpen s) (f p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = BranchwisePrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF u huOpen huConn hus
    by_cases hne : u.Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hz : ∀ x ∈ u, HasDerivAt (fun y => F y - p y) 0 x := by
        intro x hx
        simpa using (hF x (hus hx)).sub (hp x (hus hx))
      have hdiff : DifferentiableOn ℝ (fun y => F y - p y) u := by
        intro x hx
        exact (hz x hx).differentiableAt.differentiableWithinAt
      have hder : ∀ x ∈ u, deriv (fun y => F y - p y) x = 0 := by
        intro x hx
        exact (hz x hx).deriv
      refine ⟨F x0 - p x0, ?_⟩
      intro x hx
      have heq : F x - p x = F x0 - p x0 :=
        huOpen.is_const_of_deriv_eq_zero huConn hdiff hder hx hx0
      linarith
    · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩
  · intro hF x hx
    rcases Metric.isOpen_iff.mp hopen x hx with ⟨ε, hε, hball⟩
    have hconn : IsPreconnected (Metric.ball x ε) :=
      (convex_ball x ε).isPreconnected
    rcases hF (Metric.ball x ε) Metric.isOpen_ball hconn hball with ⟨C, hC⟩
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [Metric.ball_mem_nhds x hε] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem connected_antiderivatives
    {s : Set ℝ} (hopen : IsOpen s) (hconn : IsPreconnected s)
    (hne : s.Nonempty) (f p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF
    rcases hne with ⟨x0, hx0⟩
    have hz : ∀ x ∈ s, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) s := by
      intro x hx
      exact (hz x hx).differentiableAt.differentiableWithinAt
    have hder : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      exact (hz x hx).deriv
    refine ⟨F x0 - p x0, ?_⟩
    intro x hx
    have heq : F x - p x = F x0 - p x0 :=
      hopen.is_const_of_deriv_eq_zero hconn hdiff hder hx hx0
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem primitiveFamily_eq_add_const
    {s : Set ℝ} (p q : ℝ → ℝ) (C : ℝ)
    (h : ∀ x ∈ s, p x = q x + C) :
    PrimitiveFamilyOn s p = PrimitiveFamilyOn s q := by
  ext F
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨C + K, fun x hx => by rw [hK x hx, h x hx]; ring⟩
  · rintro ⟨K, hK⟩
    exact ⟨K - C, fun x hx => by rw [hK x hx, h x hx]; ring⟩

private theorem hasDerivAt_arcsin_part
    (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt
      (fun y => Real.arcsin ((2 * y + 1) / Real.sqrt 5))
      (1 / Real.sqrt (radicand x)) x := by
  have hr : 0 < radicand x := hx.1
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs50 : Real.sqrt 5 ≠ 0 := hs5.ne'
  have hs5sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  let u := (2 * x + 1) / Real.sqrt 5
  have hu : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    dsimp [u]
    have hsquare : (2 * x + 1) ^ 2 < 5 := by
      unfold radicand at hr
      nlinarith
    constructor
    · rw [lt_div_iff₀ hs5]
      nlinarith
    · rw [div_lt_iff₀ hs5]
      nlinarith
  have huder : HasDerivAt
      (fun y : ℝ => (2 * y + 1) / Real.sqrt 5)
      (2 / Real.sqrt 5) x := by
    have hnum : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
      convert ((hasDerivAt_id x).const_mul 2).const_add 1 using 1
      · funext y
        simp only [id_eq]
        ring
      · ring
    exact hnum.div_const _
  have hinside : 0 < 1 - u ^ 2 := by
    nlinarith [hu.1, hu.2]
  have hrel : 5 * (1 - u ^ 2) = 4 * radicand x := by
    dsimp [u]
    field_simp [hs50]
    rw [hs5sq]
    unfold radicand
    ring
  have hsqrt :
      Real.sqrt 5 * Real.sqrt (1 - u ^ 2) =
        2 * Real.sqrt (radicand x) := by
    have hleft :
        (Real.sqrt 5 * Real.sqrt (1 - u ^ 2)) ^ 2 =
          5 * (1 - u ^ 2) := by
      rw [mul_pow, hs5sq, Real.sq_sqrt hinside.le]
    have hright :
        (2 * Real.sqrt (radicand x)) ^ 2 = 4 * radicand x := by
      rw [mul_pow, Real.sq_sqrt hr.le]
      ring
    have hnonneg : 0 ≤ Real.sqrt 5 * Real.sqrt (1 - u ^ 2) := by positivity
    have hnonneg' : 0 ≤ 2 * Real.sqrt (radicand x) := by positivity
    nlinarith
  have h :=
    (Real.hasDerivAt_arcsin (ne_of_gt hu.1) (ne_of_lt hu.2)).comp x huder
  convert h using 1
  field_simp [hs50, (Real.sqrt_pos.2 hinside).ne',
    (Real.sqrt_pos.2 hr).ne']
  nlinarith

private theorem hasDerivAt_log_part
    (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt
      (fun y => Real.log
        |(3 + y + 2 * Real.sqrt (radicand y)) / (2 * (1 + y))|)
      (-1 / ((1 + x) * Real.sqrt (radicand x))) x := by
  have hr : 0 < radicand x := hx.1
  have hs : 0 < Real.sqrt (radicand x) := Real.sqrt_pos.2 hr
  have hs0 : Real.sqrt (radicand x) ≠ 0 := hs.ne'
  have hs2 : (Real.sqrt (radicand x)) ^ 2 = radicand x :=
    Real.sq_sqrt hr.le
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx.2
    linarith
  have hsder : HasDerivAt (fun y => Real.sqrt (radicand y))
      ((-1 - 2 * x) / (2 * Real.sqrt (radicand x))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp x
      (radicand_hasDerivAt x) using 1 <;> ring
  have hnum : HasDerivAt
      (fun y => 3 + y + 2 * Real.sqrt (radicand y))
      (1 + 2 * ((-1 - 2 * x) / (2 * Real.sqrt (radicand x)))) x := by
    convert ((hasDerivAt_const x 3).add (hasDerivAt_id x)).add
      (hsder.const_mul 2) using 1 <;> ring
  have hden : HasDerivAt (fun y : ℝ => 2 * (1 + y)) 2 x := by
    convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).const_mul 2 using 1 <;>
      ring
  have hnumpos : 0 < 3 + x + 2 * Real.sqrt (radicand x) := by
    unfold radicand at hr
    nlinarith
  have hden0 : 2 * (1 + x) ≠ 0 := mul_ne_zero (by norm_num) hx1
  have hquot := hnum.div hden hden0
  have hquot0 :
      (3 + x + 2 * Real.sqrt (radicand x)) / (2 * (1 + x)) ≠ 0 :=
    div_ne_zero hnumpos.ne' hden0
  have hlog := hquot.log hquot0
  change HasDerivAt
    (fun y => Real.log
      ((3 + y + 2 * Real.sqrt (radicand y)) / (2 * (1 + y))))
    _ x at hlog
  have hcoef :
      (((1 + 2 * ((-1 - 2 * x) / (2 * Real.sqrt (radicand x)))) *
          (2 * (1 + x)) -
          (3 + x + 2 * Real.sqrt (radicand x)) * 2) /
        (2 * (1 + x)) ^ 2) /
          ((3 + x + 2 * Real.sqrt (radicand x)) / (2 * (1 + x))) =
        -1 / ((1 + x) * Real.sqrt (radicand x)) := by
    field_simp [hs0, hx1, hnumpos.ne']
    unfold radicand at hs2 ⊢
    ring_nf at hs2 ⊢
    nlinarith
  have hlog' : HasDerivAt
      (fun y => Real.log
        ((3 + y + 2 * Real.sqrt (radicand y)) / (2 * (1 + y))))
      (-1 / ((1 + x) * Real.sqrt (radicand x))) x := by
    convert hlog using 1
    simpa only [Pi.div_apply] using hcoef.symm
  simpa only [Real.log_abs] using hlog'

private theorem hasDerivAt_unifiedWithTwo
    (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt unifiedPrimitiveWithTwo (integrand x) x := by
  unfold unifiedPrimitiveWithTwo integrand
  convert (hasDerivAt_arcsin_part x hx).add
    (hasDerivAt_log_part x hx) using 1
  have hs0 : Real.sqrt (radicand x) ≠ 0 :=
    (Real.sqrt_pos.2 hx.1).ne'
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx.2
    linarith
  field_simp [hs0, hx1]
  ring

private theorem rightBranch_eq_interval :
    rightBranch = Set.Ioo (-1) ((Real.sqrt 5 - 1) / 2) := by
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs5sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ext x
  simp only [rightBranch, Set.mem_setOf_eq, Set.mem_Ioo]
  unfold radicand
  constructor
  · rintro ⟨hr, hx⟩
    constructor
    · linarith
    · nlinarith
  · rintro ⟨hxlo, hxhi⟩
    constructor
    · have hroot : (-1 - Real.sqrt 5) / 2 < -1 := by
        nlinarith
      have hpos : 0 < x - ((-1 - Real.sqrt 5) / 2) := by
        linarith
      have hneg : x - ((Real.sqrt 5 - 1) / 2) < 0 := by
        linarith
      have hm := mul_neg_of_pos_of_neg hpos hneg
      nlinarith
    · linarith

private theorem leftBranch_eq_interval :
    leftBranch = Set.Ioo ((-1 - Real.sqrt 5) / 2) (-1) := by
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs5sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ext x
  simp only [leftBranch, Set.mem_setOf_eq, Set.mem_Ioo]
  unfold radicand
  constructor
  · rintro ⟨hr, hx⟩
    constructor
    · nlinarith
    · linarith
  · rintro ⟨hxlo, hxhi⟩
    constructor
    · have hroot : -1 < (Real.sqrt 5 - 1) / 2 := by
        nlinarith
      have hpos : 0 < x - ((-1 - Real.sqrt 5) / 2) := by
        linarith
      have hneg : x - ((Real.sqrt 5 - 1) / 2) < 0 := by
        linarith
      have hm := mul_neg_of_pos_of_neg hpos hneg
      nlinarith
    · linarith

private theorem right_eq_unifiedWithTwo
    (x : ℝ) (hx : x ∈ rightBranch) :
    rightPrimitive x =
      unifiedPrimitiveWithTwo x + Real.log 2 := by
  have hr : 0 < radicand x := hx.1
  have hx1 : 0 < 1 + x := by linarith [hx.2]
  have hnpos : 0 < 3 + x + 2 * Real.sqrt (radicand x) := by
    unfold radicand at hr
    nlinarith [Real.sqrt_nonneg (radicand x)]
  let Q :=
    (3 + x + 2 * Real.sqrt (radicand x)) / (2 * (1 + x))
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact div_ne_zero hnpos.ne' (mul_ne_zero (by norm_num) hx1.ne')
  have harg :
      (3 + x + 2 * Real.sqrt (radicand x)) / (1 + x) = 2 * Q := by
    dsimp [Q]
    field_simp [hx1.ne']
  unfold rightPrimitive unifiedPrimitiveWithTwo
  rw [harg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (abs_ne_zero.mpr hQ0)]
  ring

private theorem unified_eq_unifiedWithTwo
    (x : ℝ) (hx : x ∈ xBranch) :
    unifiedPrimitive x =
      unifiedPrimitiveWithTwo x + Real.log 2 := by
  have hr : 0 < radicand x := hx.1
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx.2
    linarith
  have hnpos : 0 < 3 + x + 2 * Real.sqrt (radicand x) := by
    unfold radicand at hr
    nlinarith [Real.sqrt_nonneg (radicand x)]
  let Q :=
    (3 + x + 2 * Real.sqrt (radicand x)) / (2 * (1 + x))
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact div_ne_zero hnpos.ne' (mul_ne_zero (by norm_num) hx1)
  have harg :
      (3 + x + 2 * Real.sqrt (radicand x)) / (1 + x) = 2 * Q := by
    dsimp [Q]
    field_simp [hx1]
  unfold unifiedPrimitive unifiedPrimitiveWithTwo
  rw [harg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (abs_ne_zero.mpr hQ0)]
  ring

private theorem leftRaw_eq_unifiedWithTwo
    (x : ℝ) (hx : x ∈ leftBranch) :
    leftPrimitiveRaw x =
      unifiedPrimitiveWithTwo x - Real.log (5 / 4 : ℝ) := by
  have hr : 0 < radicand x := hx.1
  have hs2 : (Real.sqrt (radicand x)) ^ 2 = radicand x :=
    Real.sq_sqrt hr.le
  have hx1 : 1 + x ≠ 0 := by linarith [hx.2]
  let P :=
    (3 + x - 2 * Real.sqrt (radicand x)) / (2 * (1 + x))
  let Q :=
    (3 + x + 2 * Real.sqrt (radicand x)) / (2 * (1 + x))
  have hprod : P * Q = 5 / 4 := by
    dsimp [P, Q]
    field_simp [hx1]
    unfold radicand at hs2 ⊢
    ring_nf at hs2 ⊢
    nlinarith
  have hP0 : P ≠ 0 := by
    intro h
    rw [h] at hprod
    norm_num at hprod
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h] at hprod
    norm_num at hprod
  have hlogs : Real.log |P| + Real.log |Q| = Real.log (5 / 4 : ℝ) := by
    rw [← Real.log_mul (abs_ne_zero.mpr hP0) (abs_ne_zero.mpr hQ0),
      ← abs_mul, hprod, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
  unfold leftPrimitiveRaw unifiedPrimitiveWithTwo
  change
    Real.arcsin ((2 * x + 1) / Real.sqrt 5) - Real.log |P| =
      Real.arcsin ((2 * x + 1) / Real.sqrt 5) + Real.log |Q| -
        Real.log (5 / 4 : ℝ)
  linarith

private theorem hasDerivAt_rightPrimitive
    (x : ℝ) (hx : x ∈ rightBranch) :
    HasDerivAt rightPrimitive (integrand x) x := by
  have hxX : x ∈ xBranch := ⟨hx.1, by linarith [hx.2]⟩
  have heq : rightPrimitive =ᶠ[nhds x]
      fun y => unifiedPrimitiveWithTwo y + Real.log 2 := by
    filter_upwards [rightBranch_isOpen.mem_nhds hx] with y hy
    exact right_eq_unifiedWithTwo y hy
  exact ((hasDerivAt_unifiedWithTwo x hxX).add_const _).congr_of_eventuallyEq heq

private theorem hasDerivAt_leftRaw
    (x : ℝ) (hx : x ∈ leftBranch) :
    HasDerivAt leftPrimitiveRaw (integrand x) x := by
  have hxX : x ∈ xBranch := ⟨hx.1, by linarith [hx.2]⟩
  have heq : leftPrimitiveRaw =ᶠ[nhds x]
      fun y => unifiedPrimitiveWithTwo y - Real.log (5 / 4 : ℝ) := by
    filter_upwards [leftBranch_isOpen.mem_nhds hx] with y hy
    exact leftRaw_eq_unifiedWithTwo y hy
  exact ((hasDerivAt_unifiedWithTwo x hxX).sub_const _).congr_of_eventuallyEq heq

private theorem hasDerivAt_unified
    (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt unifiedPrimitive (integrand x) x := by
  have heq : unifiedPrimitive =ᶠ[nhds x]
      fun y => unifiedPrimitiveWithTwo y + Real.log 2 := by
    filter_upwards [xBranch_isOpen.mem_nhds hx] with y hy
    exact unified_eq_unifiedWithTwo y hy
  exact ((hasDerivAt_unifiedWithTwo x hx).add_const _).congr_of_eventuallyEq heq

private theorem hasDerivAt_signed
    (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt signedPrimitive (integrand x) x := by
  have hxne : x + 1 ≠ 0 := by
    intro h
    apply hx.2
    linarith
  rcases lt_or_gt_of_ne hxne with hleft | hright
  · have hxL : x ∈ leftBranch := ⟨hx.1, hleft⟩
    have heq : signedPrimitive =ᶠ[nhds x] leftPrimitiveRaw := by
      filter_upwards [leftBranch_isOpen.mem_nhds hxL] with y hy
      have hy1 : y + 1 < 0 := hy.2
      have hy1' : 1 + y < 0 := by linarith
      have htneg : tOf y < 0 := by
        unfold tOf
        exact one_div_neg.mpr (by linarith)
      unfold signedPrimitive leftPrimitiveRaw
      rw [Real.sign_of_neg hy1', Real.sign_of_neg hy1]
      ring
    exact (hasDerivAt_leftRaw x hxL).congr_of_eventuallyEq heq
  · have hxR : x ∈ rightBranch := ⟨hx.1, hright⟩
    have heq : signedPrimitive =ᶠ[nhds x] unifiedPrimitiveWithTwo := by
      filter_upwards [rightBranch_isOpen.mem_nhds hxR] with y hy
      have hy1 : 0 < y + 1 := hy.2
      have hy1' : 0 < 1 + y := by linarith
      have htpos : 0 < tOf y := by
        unfold tOf
        exact one_div_pos.mpr (by linarith)
      unfold signedPrimitive unifiedPrimitiveWithTwo
      rw [Real.sign_of_pos hy1', Real.sign_of_pos hy1]
      ring
    exact (hasDerivAt_unifiedWithTwo x hx).congr_of_eventuallyEq heq

private def auxiliaryBPrimitive (t : ℝ) :=
  Real.log |(2 * t + 1 + 2 * Real.sqrt (t ^ 2 + t - 1)) / 2|

private theorem parameter_radicand_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u : ℝ => u ^ 2 + u - 1) (2 * t + 1) t := by
  convert (((hasDerivAt_id t).pow 2).add (hasDerivAt_id t)).sub_const 1 using 1 <;>
    simp only [id_eq] <;> ring

private theorem hasDerivAt_auxiliaryBPrimitive
    (t : ℝ) (ht : t ∈ parameterBranch) :
    HasDerivAt auxiliaryBPrimitive
      (1 / Real.sqrt (t ^ 2 + t - 1)) t := by
  let r := t ^ 2 + t - 1
  have hr : 0 < r := ht.2
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hs0 : Real.sqrt r ≠ 0 := hs.ne'
  have hs2 : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
  have hsder : HasDerivAt
      (fun u => Real.sqrt (u ^ 2 + u - 1))
      ((2 * t + 1) / (2 * Real.sqrt r)) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp t
      (parameter_radicand_hasDerivAt t) using 1 <;> ring
  have hnum : HasDerivAt
      (fun u => 2 * u + 1 + 2 * Real.sqrt (u ^ 2 + u - 1))
      ((2 * t + 1 + 2 * Real.sqrt r) / Real.sqrt r) t := by
    have hraw := (((hasDerivAt_id t).const_mul 2).const_add 1).add
      (hsder.const_mul 2)
    convert hraw using 1
    · funext u
      simp only [Pi.add_apply, id_eq]
      ring
    · field_simp [hs0]
      ring
  have hconj :
      (2 * t + 1 + 2 * Real.sqrt r) *
        (2 * t + 1 - 2 * Real.sqrt r) = 5 := by
    rw [show r = t ^ 2 + t - 1 by rfl] at hs2
    nlinarith
  have hnum0 : 2 * t + 1 + 2 * Real.sqrt r ≠ 0 := by
    intro h
    rw [h] at hconj
    norm_num at hconj
  have hnum0' : 1 + t * 2 + Real.sqrt r * 2 ≠ 0 := by
    intro hzero
    apply hnum0
    linarith
  have hhalf := hnum.div_const 2
  have harg0 : (2 * t + 1 + 2 * Real.sqrt r) / 2 ≠ 0 :=
    div_ne_zero hnum0 (by norm_num)
  have hlog := hhalf.log harg0
  change HasDerivAt
    (fun y => Real.log
      ((2 * y + 1 + 2 * Real.sqrt (y ^ 2 + y - 1)) / 2))
    ((((2 * t + 1 + 2 * Real.sqrt r) / Real.sqrt r) / 2) /
      ((2 * t + 1 + 2 * Real.sqrt r) / 2)) t at hlog
  have hcoef :
      (((2 * t + 1 + 2 * Real.sqrt r) / Real.sqrt r) / 2) /
          ((2 * t + 1 + 2 * Real.sqrt r) / 2) =
        1 / Real.sqrt r := by
    field_simp [hs0, hnum0]
  rw [hcoef] at hlog
  unfold auxiliaryBPrimitive
  simpa only [Real.log_abs] using hlog

private theorem tOf_hasDerivAt
    (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt tOf (-1 / (1 + x) ^ 2) x := by
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx.2
    linarith
  unfold tOf
  have h := (hasDerivAt_const x 1).div
    ((hasDerivAt_id x).const_add 1) hx1
  convert h using 1 <;> simp only [id_eq] <;> ring

private theorem tOf_mem_parameter
    (x : ℝ) (hx : x ∈ xBranch) :
    tOf x ∈ parameterBranch := by
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx.2
    linarith
  constructor
  · unfold tOf
    exact one_div_ne_zero hx1
  · have hrel :
        tOf x ^ 2 + tOf x - 1 =
          radicand x / (1 + x) ^ 2 := by
      unfold tOf radicand
      field_simp [hx1]
      ring
    rw [hrel]
    exact div_pos hx.1 (sq_pos_of_ne_zero hx1)

private theorem sqrt_parameter_tOf
    (x : ℝ) (hx : x ∈ xBranch) :
    Real.sqrt (tOf x ^ 2 + tOf x - 1) =
      Real.sqrt (radicand x) / |1 + x| := by
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx.2
    linarith
  have hrel :
      tOf x ^ 2 + tOf x - 1 =
        radicand x / (1 + x) ^ 2 := by
    unfold tOf radicand
    field_simp [hx1]
    ring
  rw [hrel, Real.sqrt_div hx.1.le, Real.sqrt_sq_eq_abs]

private theorem composed_parameter_hasDerivAt
    (B : ℝ → ℝ)
    (hB : ∀ t ∈ parameterBranch,
      HasDerivAt B (1 / Real.sqrt (t ^ 2 + t - 1)) t)
    (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt (fun y => Real.sign (tOf y) * B (tOf y))
      (-1 / ((1 + x) * Real.sqrt (radicand x))) x := by
  have htmem := tOf_mem_parameter x hx
  have htder := tOf_hasDerivAt x hx
  have hcomp := (hB (tOf x) htmem).comp x htder
  have hsqrt := sqrt_parameter_tOf x hx
  have hs0 : Real.sqrt (radicand x) ≠ 0 :=
    (Real.sqrt_pos.2 hx.1).ne'
  have hx1 : 1 + x ≠ 0 := by
    intro h
    apply hx.2
    linarith
  rcases lt_or_gt_of_ne hx1 with hneg | hpos
  · have htneg : tOf x < 0 := by
      unfold tOf
      exact one_div_neg.mpr hneg
    have heq :
        (fun y => Real.sign (tOf y) * B (tOf y)) =ᶠ[nhds x]
          fun y => -B (tOf y) := by
      have hopen : IsOpen {y : ℝ | y + 1 < 0} :=
        isOpen_Iio.preimage (continuous_id.add continuous_const)
      filter_upwards [hopen.mem_nhds (by linarith : x + 1 < 0)] with y hy
      have hty : tOf y < 0 := by
        unfold tOf
        exact one_div_neg.mpr (by linarith)
      rw [Real.sign_of_neg hty]
      ring
    have hraw := hcomp.neg
    convert hraw.congr_of_eventuallyEq heq using 1
    rw [hsqrt, abs_of_neg hneg]
    field_simp [hx1, hs0]
  · have htpos : 0 < tOf x := by
      unfold tOf
      exact one_div_pos.mpr hpos
    have heq :
        (fun y => Real.sign (tOf y) * B (tOf y)) =ᶠ[nhds x]
          fun y => B (tOf y) := by
      have hopen : IsOpen {y : ℝ | 0 < y + 1} :=
        isOpen_Ioi.preimage (continuous_id.add continuous_const)
      filter_upwards [hopen.mem_nhds (by linarith : 0 < x + 1)] with y hy
      have hty : 0 < tOf y := by
        unfold tOf
        exact one_div_pos.mpr (by linarith)
      rw [Real.sign_of_pos hty, one_mul]
    convert hcomp.congr_of_eventuallyEq heq using 1
    rw [hsqrt, abs_of_pos hpos]
    field_simp [hx1, hs0]

theorem gap1 (t : ℝ) (ht : t ≠ 0) :
    xOf t = (1 - t) / t := by
  rfl
theorem gap2 (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt xOf (-1 / t ^ 2) t := by
  unfold xOf
  have h := ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div
    (hasDerivAt_id t) ht
  convert h using 1
  simp only [Pi.sub_apply, id_eq]
  field_simp [ht]
  ring
theorem gap3 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (radicand (xOf t)) =
      Real.sqrt (t ^ 2 + t - 1) / |t| := by
  have ht0 : t ≠ 0 := ht.1
  have hp : 0 < t ^ 2 + t - 1 := ht.2
  have habs : 0 < |t| := abs_pos.mpr ht0
  have hrad :
      radicand (xOf t) = (t ^ 2 + t - 1) / t ^ 2 := by
    unfold radicand xOf
    field_simp [ht0]
    ring
  rw [hrad, Real.sqrt_div (le_of_lt hp)]
  rw [Real.sqrt_sq_eq_abs]
theorem gap4 (t : ℝ) (ht : t ≠ 0) :
    Real.sqrt (t ^ 2 + t - 1) / |t| =
      Real.sign t * (Real.sqrt (t ^ 2 + t - 1) / t) := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
    field_simp [ht]
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
    ring
theorem gap5 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (radicand (xOf t)) =
      Real.sign t * (Real.sqrt (t ^ 2 + t - 1) / t) := by
  rw [gap3 t ht, gap4 t ht.1]
theorem gap6 :
    AntiderivativesOn xBranch integrand =
      AntiderivativesOn xBranch splitIntegrand := by
  ext F
  constructor <;> intro hF <;> intro x hx
  · rw [← show integrand x = splitIntegrand x by
      unfold integrand splitIntegrand
      have hs0 : Real.sqrt (radicand x) ≠ 0 :=
        (Real.sqrt_pos.2 hx.1).ne'
      have hx1 : 1 + x ≠ 0 := by
        intro h
        apply hx.2
        linarith
      field_simp [hs0, hx1]
      ring]
    exact hF x hx
  · rw [show integrand x = splitIntegrand x by
      unfold integrand splitIntegrand
      have hs0 : Real.sqrt (radicand x) ≠ 0 :=
        (Real.sqrt_pos.2 hx.1).ne'
      have hx1 : 1 + x ≠ 0 := by
        intro h
        apply hx.2
        linarith
      field_simp [hs0, hx1]
      ring]
    exact hF x hx
theorem gap7 :
    AntiderivativesOn xBranch integrand = AuxiliaryFamily := by
  ext F
  constructor
  · intro hF
    let B := auxiliaryBPrimitive
    let C : ℝ → ℝ := fun x => Real.sign (tOf x) * B (tOf x)
    let A : ℝ → ℝ := fun x => F x - C x
    refine ⟨A, ?_, B, ?_, ?_⟩
    · intro x hx
      have hC : HasDerivAt C
          (-1 / ((1 + x) * Real.sqrt (radicand x))) x := by
        exact composed_parameter_hasDerivAt B
          (fun t ht => hasDerivAt_auxiliaryBPrimitive t ht) x hx
      have h := (hF x hx).sub hC
      unfold A
      convert h using 1
      unfold integrand
      have hs0 : Real.sqrt (radicand x) ≠ 0 :=
        (Real.sqrt_pos.2 hx.1).ne'
      have hx1 : 1 + x ≠ 0 := by
        intro hzero
        apply hx.2
        linarith
      field_simp [hs0, hx1]
      ring
    · intro t ht
      exact hasDerivAt_auxiliaryBPrimitive t ht
    · intro x hx
      dsimp [A, C, B]
      ring
  · rintro ⟨A, hA, B, hB, hEq⟩
    intro x hx
    have hC := composed_parameter_hasDerivAt B hB x hx
    have hsum := (hA x hx).add hC
    have heq : F =ᶠ[nhds x]
        fun y => A y + Real.sign (tOf y) * B (tOf y) := by
      filter_upwards [xBranch_isOpen.mem_nhds hx] with y hy
      exact hEq y hy
    convert hsum.congr_of_eventuallyEq heq using 1
    unfold integrand
    have hs0 : Real.sqrt (radicand x) ≠ 0 :=
      (Real.sqrt_pos.2 hx.1).ne'
    have hx1 : 1 + x ≠ 0 := by
      intro hzero
      apply hx.2
      linarith
    field_simp [hs0, hx1]
    ring
theorem gap8 :
    AntiderivativesOn xBranch integrand =
      BranchwisePrimitiveFamilyOn xBranch signedPrimitive := by
  exact branchwise_antiderivatives xBranch_isOpen integrand signedPrimitive
    hasDerivAt_signed
theorem gap9 :
    AntiderivativesOn rightBranch integrand =
      PrimitiveFamilyOn rightBranch rightPrimitive := by
  apply connected_antiderivatives rightBranch_isOpen
  · rw [rightBranch_eq_interval]
    exact (convex_Ioo _ _).isPreconnected
  · exact ⟨0, by norm_num [rightBranch, radicand]⟩
  · exact hasDerivAt_rightPrimitive
theorem gap10 :
    AntiderivativesOn leftBranch integrand =
      PrimitiveFamilyOn leftBranch leftPrimitiveRaw := by
  apply connected_antiderivatives leftBranch_isOpen
  · rw [leftBranch_eq_interval]
    exact (convex_Ioo _ _).isPreconnected
  · exact ⟨-(3 / 2 : ℝ), by norm_num [leftBranch, radicand]⟩
  · exact hasDerivAt_leftRaw
theorem gap11 :
    AntiderivativesOn leftBranch integrand =
      PrimitiveFamilyOn leftBranch unifiedPrimitive := by
  apply connected_antiderivatives leftBranch_isOpen
  · rw [leftBranch_eq_interval]
    exact (convex_Ioo _ _).isPreconnected
  · exact ⟨-(3 / 2 : ℝ), by norm_num [leftBranch, radicand]⟩
  · intro x hx
    exact hasDerivAt_unified x ⟨hx.1, by linarith [hx.2]⟩
theorem gap12 :
    AntiderivativesOn xBranch integrand =
      BranchwisePrimitiveFamilyOn xBranch unifiedPrimitiveWithTwo := by
  exact branchwise_antiderivatives xBranch_isOpen integrand
    unifiedPrimitiveWithTwo hasDerivAt_unifiedWithTwo

end
end ProofGap.Exercise1941
