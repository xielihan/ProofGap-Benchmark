import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1961

noncomputable section

def sec (t : ℝ) := 1 / Real.cos t
def a : ℝ := Real.sqrt 5 / 2
def positiveXBranch : Set ℝ := {x | a < x + 1 / 2}
def negativeXBranch : Set ℝ := {x | x + 1 / 2 < -a}
def outerBranch : Set ℝ := {x | a < |x + 1 / 2|}
def positiveTBranch : Set ℝ := Set.Ioo 0 (Real.pi / 2)
def negativeTBranch : Set ℝ := Set.Ioo Real.pi ((3 / 2 : ℝ) * Real.pi)
def positiveSubstitution (x t : ℝ) : Prop :=
  x ∈ positiveXBranch ∧ t ∈ positiveTBranch ∧ x + 1 / 2 = a * sec t
def negativeSubstitution (x t : ℝ) : Prop :=
  x ∈ negativeXBranch ∧ t ∈ negativeTBranch ∧ x + 1 / 2 = a * sec t
def substitutionMap (t : ℝ) := a * sec t - 1 / 2
def originalIntegrand (x : ℝ) :=
  1 / ((x ^ 2 + x + 1) * Real.sqrt (x ^ 2 + x - 1))
def completedSquareIntegrand (x : ℝ) :=
  1 /
    (((x + 1 / 2) ^ 2 + 3 / 4) *
      Real.sqrt ((x + 1 / 2) ^ 2 - 5 / 4))
def secIntegrand (t : ℝ) := sec t / (5 * sec t ^ 2 + 3)
def cosIntegrand (t : ℝ) := Real.cos t / (5 + 3 * Real.cos t ^ 2)
def u (t : ℝ) := Real.sqrt 3 * Real.sin t
def uIntegrand (t : ℝ) :=
  deriv u t / (Real.sqrt 8 ^ 2 - u t ^ 2)
def primitiveT (t : ℝ) :=
  1 / Real.sqrt 6 *
    Real.log
      |(Real.sqrt 8 + Real.sqrt 3 * Real.sin t) /
        (Real.sqrt 8 - Real.sqrt 3 * Real.sin t)|
def primitiveX (x : ℝ) :=
  1 / Real.sqrt 6 *
    Real.log
      |((2 * x + 1) * Real.sqrt 2 +
          Real.sqrt (3 * (x ^ 2 + x - 1))) /
        ((2 * x + 1) * Real.sqrt 2 -
          Real.sqrt (3 * (x ^ 2 + x - 1)))|
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def ScaledFamily (s : Set ℝ) (f : ℝ → ℝ) (c : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn s f, ∀ x ∈ s, F x = c * G x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def PullbackFamily (map : ℝ → ℝ) (s : Set ℝ)
    (T : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ T, ∀ t ∈ s, F (map t) = G t}
def BranchwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ Cneg Cpos : ℝ,
    (∀ x ∈ negativeXBranch, F x = primitiveX x + Cneg) ∧
    (∀ x ∈ positiveXBranch, F x = primitiveX x + Cpos)}

private theorem antiderivatives_eq_primitive_on
    (s : Set ℝ) (hsopen : IsOpen s) (hsconn : IsPreconnected s)
    (hsne : s.Nonempty) (p f : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · intro hF
    rcases hsne with ⟨x₀, hx₀⟩
    refine ⟨F x₀ - p x₀, ?_⟩
    intro x hx
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => F y - p y) s := by
      intro y hy
      exact ((hF y hy).sub (hp y hy)).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ s, deriv (fun z : ℝ => F z - p z) y = 0 := by
      intro y hy
      have hd : HasDerivAt (fun z : ℝ => F z - p z) 0 y := by
        convert (hF y hy).sub (hp y hy) using 1 <;> ring
      exact hd.deriv
    have heq :=
      hsopen.is_const_of_deriv_eq_zero hsconn hdiff hzero hx₀ hx
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hd : HasDerivAt (fun y : ℝ => p y + C) (f x) x := by
      convert HasDerivAt.add (hp x hx) (hasDerivAt_const x C) using 1 <;> ring
    apply hd.congr_of_eventuallyEq
    filter_upwards [hsopen.mem_nhds hx] with y hy
    exact hC y hy

private theorem scaledFamily_eq_antiderivatives
    (s : Set ℝ) (hsopen : IsOpen s) (f : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) :
    ScaledFamily s f c = AntiderivativesOn s (fun x => c * f x) := by
  apply Set.ext
  intro F
  simp only [ScaledFamily, AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩ x hx
    have hd := (hG x hx).const_mul c
    apply hd.congr_of_eventuallyEq
    filter_upwards [hsopen.mem_nhds hx] with y hy
    exact hFG y hy
  · intro hF
    refine ⟨(fun y => F y / c), ?_, ?_⟩
    · intro x hx
      convert (hF x hx).div_const c using 1 <;> field_simp [hc]
    · intro x hx
      field_simp [hc]

private theorem hasDerivAt_primitiveT (t : ℝ) (ht : t ∈ positiveTBranch) :
    HasDerivAt primitiveT (4 * cosIntegrand t) t := by
  have hs8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hs8sq : (Real.sqrt 8) ^ 2 = 8 := by norm_num
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs6sq : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  have hs83 : Real.sqrt 8 * Real.sqrt 3 = 2 * Real.sqrt 6 := by
    have hp : (Real.sqrt 8 * Real.sqrt 3) ^ 2 = 24 := by
      rw [mul_pow, hs8sq, hs3sq]
      norm_num
    have hq : (2 * Real.sqrt 6) ^ 2 = 24 := by
      rw [mul_pow, hs6sq]
      norm_num
    nlinarith [mul_pos hs8 hs3]
  have hs8gt3 : Real.sqrt 3 < Real.sqrt 8 := by nlinarith
  have hsinle : Real.sin t ≤ 1 := Real.sin_le_one t
  have hsinge : -1 ≤ Real.sin t := Real.neg_one_le_sin t
  have hplus0 : Real.sqrt 8 + Real.sqrt 3 * Real.sin t ≠ 0 := by
    exact ne_of_gt (by nlinarith)
  have hminus0 : Real.sqrt 8 - Real.sqrt 3 * Real.sin t ≠ 0 := by
    exact ne_of_gt (by nlinarith)
  have hplus : HasDerivAt
      (fun y : ℝ => Real.sqrt 8 + Real.sqrt 3 * Real.sin y)
      (Real.sqrt 3 * Real.cos t) t := by
    convert HasDerivAt.add (hasDerivAt_const t (Real.sqrt 8))
      ((Real.hasDerivAt_sin t).const_mul (Real.sqrt 3)) using 1 <;> ring
  have hminus : HasDerivAt
      (fun y : ℝ => Real.sqrt 8 - Real.sqrt 3 * Real.sin y)
      (-(Real.sqrt 3 * Real.cos t)) t := by
    convert HasDerivAt.sub (hasDerivAt_const t (Real.sqrt 8))
      ((Real.hasDerivAt_sin t).const_mul (Real.sqrt 3)) using 1 <;> ring
  have hratio := hplus.div hminus hminus0
  have hlog : HasDerivAt
      (fun y : ℝ =>
        Real.log |(Real.sqrt 8 + Real.sqrt 3 * Real.sin y) /
          (Real.sqrt 8 - Real.sqrt 3 * Real.sin y)|)
      (((Real.sqrt 3 * Real.cos t) *
            (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) -
          (Real.sqrt 8 + Real.sqrt 3 * Real.sin t) *
            (-(Real.sqrt 3 * Real.cos t))) /
        (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) ^ 2 /
        ((Real.sqrt 8 + Real.sqrt 3 * Real.sin t) /
          (Real.sqrt 8 - Real.sqrt 3 * Real.sin t))) t := by
    simpa only [Real.log_abs, Function.comp_apply] using
      hratio.log (div_ne_zero hplus0 hminus0)
  have hscaled := hlog.const_mul (1 / Real.sqrt 6)
  have hden : 8 - 3 * Real.sin t ^ 2 ≠ 0 := by
    nlinarith [Real.sin_sq_le_one t]
  have hdenprod :
      (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) *
          (Real.sqrt 8 + Real.sqrt 3 * Real.sin t) =
        8 - 3 * Real.sin t ^ 2 := by
    calc
      _ = (Real.sqrt 8) ^ 2 -
          (Real.sqrt 3) ^ 2 * Real.sin t ^ 2 := by ring
      _ = 8 - 3 * Real.sin t ^ 2 := by rw [hs8sq, hs3sq]
  have hraw :
      (((Real.sqrt 3 * Real.cos t) *
            (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) -
          (Real.sqrt 8 + Real.sqrt 3 * Real.sin t) *
            (-(Real.sqrt 3 * Real.cos t))) /
        (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) ^ 2 /
        ((Real.sqrt 8 + Real.sqrt 3 * Real.sin t) /
          (Real.sqrt 8 - Real.sqrt 3 * Real.sin t))) =
      2 * Real.sqrt 8 * Real.sqrt 3 * Real.cos t /
        ((Real.sqrt 8 - Real.sqrt 3 * Real.sin t) *
          (Real.sqrt 8 + Real.sqrt 3 * Real.sin t)) := by
    field_simp [hplus0, hminus0]
    ring
  have hcoef :
      1 / Real.sqrt 6 *
          (((Real.sqrt 3 * Real.cos t) *
                (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) -
              (Real.sqrt 8 + Real.sqrt 3 * Real.sin t) *
                (-(Real.sqrt 3 * Real.cos t))) /
            (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) ^ 2 /
            ((Real.sqrt 8 + Real.sqrt 3 * Real.sin t) /
              (Real.sqrt 8 - Real.sqrt 3 * Real.sin t))) =
        4 * cosIntegrand t := by
    rw [hraw, hdenprod]
    rw [show 2 * Real.sqrt 8 * Real.sqrt 3 =
      4 * Real.sqrt 6 by
        calc
          2 * Real.sqrt 8 * Real.sqrt 3 =
              2 * (Real.sqrt 8 * Real.sqrt 3) := by ring
          _ = 2 * (2 * Real.sqrt 6) := by rw [hs83]
          _ = 4 * Real.sqrt 6 := by ring]
    unfold cosIntegrand
    rw [show 8 - 3 * Real.sin t ^ 2 =
      5 + 3 * Real.cos t ^ 2 by
        nlinarith [Real.sin_sq_add_cos_sq t]]
    field_simp [ne_of_gt hs6]
  convert hscaled.congr_deriv hcoef using 1

private theorem scaledCos_eq_primitiveT :
    ScaledFamily positiveTBranch cosIntegrand 4 =
      PrimitiveFamilyOn positiveTBranch primitiveT := by
  rw [scaledFamily_eq_antiderivatives positiveTBranch
    (by simpa [positiveTBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2))))
    cosIntegrand 4 (by norm_num)]
  apply antiderivatives_eq_primitive_on
  · simpa [positiveTBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)))
  · simpa [positiveTBranch] using
      (isPreconnected_Ioo : IsPreconnected (Set.Ioo (0 : ℝ) (Real.pi / 2)))
  · refine ⟨Real.pi / 4, ?_⟩
    change 0 < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2
    constructor <;> nlinarith [Real.pi_pos]
  · exact hasDerivAt_primitiveT

private theorem scaledSec_eq_primitiveT :
    ScaledFamily positiveTBranch secIntegrand 4 =
      PrimitiveFamilyOn positiveTBranch primitiveT := by
  have hfun : secIntegrand = cosIntegrand := by
    funext t
    unfold secIntegrand cosIntegrand sec
    by_cases hcos : Real.cos t = 0
    · simp [hcos]
    · field_simp [hcos]
  rw [hfun]
  exact scaledCos_eq_primitiveT

private theorem scaledU_eq_primitiveT :
    ScaledFamily positiveTBranch uIntegrand (4 / Real.sqrt 3) =
      PrimitiveFamilyOn positiveTBranch primitiveT := by
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs8sq : (Real.sqrt 8) ^ 2 = 8 := by norm_num
  have hfun :
      (fun t => (4 / Real.sqrt 3) * uIntegrand t) =
        (fun t => 4 * cosIntegrand t) := by
    funext t
    have hu : HasDerivAt u (Real.sqrt 3 * Real.cos t) t := by
      unfold u
      convert (Real.hasDerivAt_sin t).const_mul (Real.sqrt 3) using 1 <;> ring
    have huderiv := hu.deriv
    unfold uIntegrand cosIntegrand
    rw [huderiv, hs8sq]
    unfold u
    rw [show 8 - (Real.sqrt 3 * Real.sin t) ^ 2 =
      5 + 3 * Real.cos t ^ 2 by
        rw [mul_pow, hs3sq]
        nlinarith [Real.sin_sq_add_cos_sq t]]
    field_simp [ne_of_gt hs3]
  rw [scaledFamily_eq_antiderivatives positiveTBranch
    (by simpa [positiveTBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2))))
    uIntegrand (4 / Real.sqrt 3) (div_ne_zero (by norm_num) (ne_of_gt hs3))]
  rw [hfun]
  apply antiderivatives_eq_primitive_on
  · simpa [positiveTBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)))
  · simpa [positiveTBranch] using
      (isPreconnected_Ioo : IsPreconnected (Set.Ioo (0 : ℝ) (Real.pi / 2)))
  · refine ⟨Real.pi / 4, ?_⟩
    change 0 < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2
    constructor <;> nlinarith [Real.pi_pos]
  · exact hasDerivAt_primitiveT

private theorem hasDerivAt_primitiveX (x : ℝ) (hx : x ∈ outerBranch) :
    HasDerivAt primitiveX (originalIntegrand x) x := by
  have ha : 0 < a := by
    unfold a
    positivity
  have ha2 : a ^ 2 = 5 / 4 := by
    unfold a
    rw [div_pow]
    norm_num
  have hy2 : a ^ 2 < (x + 1 / 2) ^ 2 := by
    change a < |x + 1 / 2| at hx
    have habs2 : a ^ 2 < |x + 1 / 2| ^ 2 :=
      (sq_lt_sq₀ ha.le (abs_nonneg _)).2 hx
    simpa only [sq_abs] using habs2
  have hq : 0 < x ^ 2 + x - 1 := by
    nlinarith
  let qx := x ^ 2 + x - 1
  let sx := Real.sqrt (3 * qx)
  have hs : 0 < sx := by
    unfold sx qx
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) hq)
  have hs0 : sx ≠ 0 := ne_of_gt hs
  have hs2 : sx ^ 2 = 3 * qx := by
    unfold sx
    exact Real.sq_sqrt (mul_nonneg (by norm_num) hq.le)
  have hqroot : 0 < Real.sqrt qx := Real.sqrt_pos.2 hq
  have hqroot0 : Real.sqrt qx ≠ 0 := ne_of_gt hqroot
  have hqroot2 : (Real.sqrt qx) ^ 2 = qx := Real.sq_sqrt hq.le
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs2root : sx = Real.sqrt 3 * Real.sqrt qx := by
    have hp : (Real.sqrt 3 * Real.sqrt qx) ^ 2 = 3 * qx := by
      rw [mul_pow, hs3sq, hqroot2]
    nlinarith [mul_pos hs3 hqroot]
  have hr2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hr6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hr6sq : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  have hr6rel : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    have hp : (Real.sqrt 3 * Real.sqrt 2) ^ 2 = 6 := by
      rw [mul_pow, hs3sq, hr2sq]
      norm_num
    nlinarith [mul_pos hs3 hr2]
  have hinner : HasDerivAt (fun y : ℝ => 3 * (y ^ 2 + y - 1))
      (3 * (2 * x + 1)) x := by
    have hpoly : HasDerivAt (fun y : ℝ => y ^ 2 + y - 1)
        (2 * x + 1) x := by
      convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).sub_const 1
        using 1 <;> simp only [id_eq] <;> ring
    convert hpoly.const_mul 3 using 1 <;> ring
  have hsder : HasDerivAt (fun y : ℝ =>
      Real.sqrt (3 * (y ^ 2 + y - 1)))
      (3 * (2 * x + 1) / (2 * sx)) x := by
    convert (Real.hasDerivAt_sqrt
      (mul_ne_zero (by norm_num) (ne_of_gt hq))).comp x hinner using 1 <;>
      unfold sx qx <;> field_simp [hs0] <;> ring
  have hlinder : HasDerivAt (fun y : ℝ => (2 * y + 1) * Real.sqrt 2)
      (2 * Real.sqrt 2) x := by
    have hlin : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
      have hmul : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
      convert HasDerivAt.add hmul (hasDerivAt_const x 1) using 1 <;> ring
    convert hlin.mul_const (Real.sqrt 2) using 1 <;> ring
  have hplus0 : (2 * x + 1) * Real.sqrt 2 + sx ≠ 0 := by
    intro hz
    have hz2 := congrArg (fun z : ℝ => z ^ 2) hz
    unfold qx at hs2
    nlinarith [hs2, hr2sq, sq_nonneg (2 * x + 1)]
  have hminus0 : (2 * x + 1) * Real.sqrt 2 - sx ≠ 0 := by
    intro hz
    have hz2 := congrArg (fun z : ℝ => z ^ 2) hz
    unfold qx at hs2
    nlinarith [hs2, hr2sq, sq_nonneg (2 * x + 1)]
  have hplus := hlinder.add hsder
  have hminus := hlinder.sub hsder
  have hratio := hplus.div hminus hminus0
  have hlog : HasDerivAt
      (fun y : ℝ =>
        Real.log |((2 * y + 1) * Real.sqrt 2 +
            Real.sqrt (3 * (y ^ 2 + y - 1))) /
          ((2 * y + 1) * Real.sqrt 2 -
            Real.sqrt (3 * (y ^ 2 + y - 1)))|)
      (((2 * Real.sqrt 2 + 3 * (2 * x + 1) / (2 * sx)) *
            ((2 * x + 1) * Real.sqrt 2 - sx) -
          ((2 * x + 1) * Real.sqrt 2 + sx) *
            (2 * Real.sqrt 2 - 3 * (2 * x + 1) / (2 * sx))) /
        ((2 * x + 1) * Real.sqrt 2 - sx) ^ 2 /
        (((2 * x + 1) * Real.sqrt 2 + sx) /
          ((2 * x + 1) * Real.sqrt 2 - sx))) x := by
    simpa only [Real.log_abs, Function.comp_apply, qx, sx] using
      hratio.log (div_ne_zero hplus0 hminus0)
  have hscaled := hlog.const_mul (1 / Real.sqrt 6)
  have hden : x ^ 2 + x + 1 ≠ 0 := by
    nlinarith
  have hprod :
      ((2 * x + 1) * Real.sqrt 2 - sx) *
          ((2 * x + 1) * Real.sqrt 2 + sx) =
        5 * (x ^ 2 + x + 1) := by
    calc
      _ = ((2 * x + 1) * Real.sqrt 2) ^ 2 - sx ^ 2 := by ring
      _ = 5 * (x ^ 2 + x + 1) := by
        rw [mul_pow, hr2sq, hs2]
        unfold qx
        ring
  have hprod' :
      (Real.sqrt 2 * (2 * x + 1) - sx) *
          (Real.sqrt 2 * (2 * x + 1) + sx) =
        5 * (x * (x + 1) + 1) := by
    calc
      _ = ((2 * x + 1) * Real.sqrt 2 - sx) *
          ((2 * x + 1) * Real.sqrt 2 + sx) := by ring
      _ = 5 * (x ^ 2 + x + 1) := hprod
      _ = 5 * (x * (x + 1) + 1) := by ring
  have hden' : x * (x + 1) + 1 ≠ 0 := by
    intro hz
    apply hden
    nlinarith
  have hnum :
      (2 * Real.sqrt 2 + 3 * (2 * x + 1) / (2 * sx)) *
            ((2 * x + 1) * Real.sqrt 2 - sx) -
          ((2 * x + 1) * Real.sqrt 2 + sx) *
            (2 * Real.sqrt 2 - 3 * (2 * x + 1) / (2 * sx)) =
        15 * Real.sqrt 2 / sx := by
    field_simp [hs0]
    ring_nf
    rw [hs2]
    unfold qx
    ring
  have hraw :
      (((2 * Real.sqrt 2 + 3 * (2 * x + 1) / (2 * sx)) *
            ((2 * x + 1) * Real.sqrt 2 - sx) -
          ((2 * x + 1) * Real.sqrt 2 + sx) *
            (2 * Real.sqrt 2 - 3 * (2 * x + 1) / (2 * sx))) /
        ((2 * x + 1) * Real.sqrt 2 - sx) ^ 2 /
        (((2 * x + 1) * Real.sqrt 2 + sx) /
          ((2 * x + 1) * Real.sqrt 2 - sx))) =
      3 * Real.sqrt 2 / (sx * (x ^ 2 + x + 1)) := by
    rw [hnum]
    field_simp [hs0, hplus0, hminus0, hden]
    rw [hprod']
    field_simp [hden']
    norm_num
  have hcoef :
      1 / Real.sqrt 6 *
          (((2 * Real.sqrt 2 + 3 * (2 * x + 1) / (2 * sx)) *
                ((2 * x + 1) * Real.sqrt 2 - sx) -
              ((2 * x + 1) * Real.sqrt 2 + sx) *
                (2 * Real.sqrt 2 - 3 * (2 * x + 1) / (2 * sx))) /
            ((2 * x + 1) * Real.sqrt 2 - sx) ^ 2 /
            (((2 * x + 1) * Real.sqrt 2 + sx) /
              ((2 * x + 1) * Real.sqrt 2 - sx))) =
        originalIntegrand x := by
    rw [hraw, hs2root, hr6rel]
    unfold originalIntegrand qx
    field_simp [ne_of_gt hr2, ne_of_gt hs3, hqroot0, hden]
    rw [hs3sq]
  have hfinal := hscaled.congr_deriv hcoef
  apply hfinal.congr_of_eventuallyEq
  filter_upwards [] with y
  rfl

theorem gap1 :
    AntiderivativesOn outerBranch originalIntegrand =
      AntiderivativesOn outerBranch completedSquareIntegrand := by
  apply congrArg (AntiderivativesOn outerBranch)
  funext x
  unfold originalIntegrand completedSquareIntegrand
  congr 2 <;> ring
theorem gap2 (x t : ℝ) (h : positiveSubstitution x t) :
    0 < t := by
  exact h.2.1.1
theorem gap3 (x t : ℝ) (h : positiveSubstitution x t) :
    t < Real.pi / 2 := by
  exact h.2.1.2
theorem gap4 (x t : ℝ) (h : positiveSubstitution x t) :
    0 < Real.pi / 2 := by
  positivity
theorem gap5 (x t : ℝ) (h : positiveSubstitution x t) :
    HasDerivAt substitutionMap (a * sec t * Real.tan t) t := by
  have ht0 := gap2 x t h
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], gap3 x t h⟩
  have hcos0 : Real.cos t ≠ 0 := ne_of_gt hcos
  have hsec : HasDerivAt sec (sec t * Real.tan t) t := by
    unfold sec
    convert (hasDerivAt_const t (1 : ℝ)).div
      (Real.hasDerivAt_cos t) hcos0 using 1 <;>
      rw [Real.tan_eq_sin_div_cos] <;> field_simp [hcos0] <;> ring
  unfold substitutionMap
  convert (hsec.const_mul a).sub_const (1 / 2) using 1 <;> ring
theorem gap6 (x t : ℝ) (h : positiveSubstitution x t) :
    Real.sqrt (x ^ 2 + x - 1) = a * Real.tan t := by
  have ht0 := gap2 x t h
  have ht1 := gap3 x t h
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by nlinarith [Real.pi_pos])
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have ha : 0 < a := by
    unfold a
    positivity
  have ha2 : a ^ 2 = 5 / 4 := by
    unfold a
    rw [div_pow]
    norm_num
  have hrad : x ^ 2 + x - 1 = (a * Real.tan t) ^ 2 := by
    have hxt := h.2.2
    have htrig := Real.sin_sq_add_cos_sq t
    unfold sec at hxt
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos] at hxt ⊢
    nlinarith
  rw [hrad, Real.sqrt_sq (le_of_lt (mul_pos ha htan))]
theorem gap7 (x t : ℝ) (h : positiveSubstitution x t) :
    x ^ 2 + x + 1 = 1 / 4 * (5 * sec t ^ 2 + 3) := by
  have hxt := h.2.2
  have ha2 : a ^ 2 = 5 / 4 := by
    unfold a
    rw [div_pow]
    norm_num
  nlinarith [sq_nonneg (x + 1 / 2 - a * sec t)]

private theorem antiderivatives_positiveX_eq_primitiveX :
    AntiderivativesOn positiveXBranch originalIntegrand =
      PrimitiveFamilyOn positiveXBranch primitiveX := by
  have hs : positiveXBranch = Set.Ioi (a - 1 / 2) := by
    ext x
    simp only [positiveXBranch, Set.mem_setOf_eq, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  apply antiderivatives_eq_primitive_on
  · rw [hs]
    exact isOpen_Ioi
  · rw [hs]
    exact isPreconnected_Ioi
  · refine ⟨a + 1, ?_⟩
    change a < a + 1 + 1 / 2
    linarith
  · intro x hx
    apply hasDerivAt_primitiveX x
    have ha : 0 < a := by
      unfold a
      positivity
    change a < x + 1 / 2 at hx
    change a < |x + 1 / 2|
    rw [abs_of_pos (by linarith)]
    exact hx

private theorem antiderivatives_negativeX_eq_primitiveX :
    AntiderivativesOn negativeXBranch originalIntegrand =
      PrimitiveFamilyOn negativeXBranch primitiveX := by
  have hs : negativeXBranch = Set.Iio (-a - 1 / 2) := by
    ext x
    simp only [negativeXBranch, Set.mem_setOf_eq, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  apply antiderivatives_eq_primitive_on
  · rw [hs]
    exact isOpen_Iio
  · rw [hs]
    exact isPreconnected_Iio
  · refine ⟨-a - 1, ?_⟩
    change -a - 1 + 1 / 2 < -a
    linarith
  · intro x hx
    apply hasDerivAt_primitiveX x
    have ha : 0 < a := by
      unfold a
      positivity
    change x + 1 / 2 < -a at hx
    change a < |x + 1 / 2|
    rw [abs_of_neg (by linarith)]
    linarith

private theorem substitutionMap_mem_positive (t : ℝ)
    (ht : t ∈ positiveTBranch) :
    substitutionMap t ∈ positiveXBranch := by
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, ht.1], ht.2⟩
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by
      nlinarith [Real.pi_pos, ht.2])
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hsec : 0 < sec t := by
    unfold sec
    positivity
  have hsq : sec t ^ 2 - 1 = Real.tan t ^ 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hsec1 : 1 < sec t := by
    nlinarith [sq_pos_of_pos htan]
  have ha : 0 < a := by
    unfold a
    positivity
  change a < substitutionMap t + 1 / 2
  unfold substitutionMap
  nlinarith

private theorem primitiveT_eq_primitiveX_substitutionMap
    (t : ℝ) (ht : t ∈ positiveTBranch) :
    primitiveT t = primitiveX (substitutionMap t) := by
  have hsub : positiveSubstitution (substitutionMap t) t := by
    refine ⟨substitutionMap_mem_positive t ht, ht, ?_⟩
    unfold substitutionMap
    ring
  have hroot := gap6 (substitutionMap t) t hsub
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, ht.1], ht.2⟩
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by
      nlinarith [Real.pi_pos, ht.2])
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have ha : 0 < a := by
    unfold a
    positivity
  have hqroot : 0 < Real.sqrt
      (substitutionMap t ^ 2 + substitutionMap t - 1) := by
    rw [hroot]
    exact mul_pos ha htan
  have hq : 0 < substitutionMap t ^ 2 + substitutionMap t - 1 :=
    Real.sqrt_pos.mp hqroot
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hroot3 :
      Real.sqrt (3 * (substitutionMap t ^ 2 + substitutionMap t - 1)) =
        Real.sqrt 3 * (a * Real.tan t) := by
    have hsquare :
        (Real.sqrt (3 *
          (substitutionMap t ^ 2 + substitutionMap t - 1))) ^ 2 =
          3 * (substitutionMap t ^ 2 + substitutionMap t - 1) :=
      Real.sq_sqrt (mul_nonneg (by norm_num) hq.le)
    have hp :
        (Real.sqrt 3 * (a * Real.tan t)) ^ 2 =
          3 * (substitutionMap t ^ 2 + substitutionMap t - 1) := by
      rw [mul_pow, hs3sq, ← hroot]
      rw [Real.sq_sqrt hq.le]
    nlinarith [Real.sqrt_nonneg
      (3 * (substitutionMap t ^ 2 + substitutionMap t - 1)),
      mul_pos hs3 (mul_pos ha htan)]
  have hs8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs8sq : (Real.sqrt 8) ^ 2 = 8 := by norm_num
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hs8rel : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    have hp : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, hs2sq]
      norm_num
    nlinarith
  have hcore : Real.sqrt 3 < 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (2 * Real.sqrt 2 - Real.sqrt 3)]
  have hcorePlus :
      0 < 2 * Real.sqrt 2 + Real.sqrt 3 * Real.sin t := by
    nlinarith [Real.neg_one_le_sin t]
  have hcoreMinus :
      0 < 2 * Real.sqrt 2 - Real.sqrt 3 * Real.sin t := by
    nlinarith [Real.sin_le_one t]
  have hnumEq :
      (2 * substitutionMap t + 1) * Real.sqrt 2 +
          Real.sqrt (3 * (substitutionMap t ^ 2 + substitutionMap t - 1)) =
        (a / Real.cos t) *
          (2 * Real.sqrt 2 + Real.sqrt 3 * Real.sin t) := by
    rw [hroot3]
    unfold substitutionMap sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    ring
  have hdenEq :
      (2 * substitutionMap t + 1) * Real.sqrt 2 -
          Real.sqrt (3 * (substitutionMap t ^ 2 + substitutionMap t - 1)) =
        (a / Real.cos t) *
          (2 * Real.sqrt 2 - Real.sqrt 3 * Real.sin t) := by
    rw [hroot3]
    unfold substitutionMap sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    ring
  have hratio :
      (((2 * substitutionMap t + 1) * Real.sqrt 2 +
          Real.sqrt (3 * (substitutionMap t ^ 2 + substitutionMap t - 1))) /
        ((2 * substitutionMap t + 1) * Real.sqrt 2 -
          Real.sqrt (3 * (substitutionMap t ^ 2 + substitutionMap t - 1)))) =
      (Real.sqrt 8 + Real.sqrt 3 * Real.sin t) /
        (Real.sqrt 8 - Real.sqrt 3 * Real.sin t) := by
    rw [hnumEq, hdenEq, hs8rel]
    field_simp [ne_of_gt hcos, ne_of_gt ha,
      ne_of_gt hcorePlus, ne_of_gt hcoreMinus]
  unfold primitiveT primitiveX
  rw [hratio]

private theorem pullback_primitiveT_eq_primitiveX :
    PullbackFamily substitutionMap positiveTBranch
        (PrimitiveFamilyOn positiveTBranch primitiveT) =
      PrimitiveFamilyOn positiveXBranch primitiveX := by
  apply Set.ext
  intro F
  simp only [PullbackFamily, PrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, ⟨C, hGC⟩, hFG⟩
    refine ⟨C, ?_⟩
    intro x hx
    have ha : 0 < a := by
      unfold a
      positivity
    change a < x + 1 / 2 at hx
    have hy : 0 < x + 1 / 2 := by linarith
    have hzpos : 0 < a / (x + 1 / 2) := div_pos ha hy
    have hzlt : a / (x + 1 / 2) < 1 := by
      rw [div_lt_one hy]
      exact hx
    have hzlow : -1 ≤ a / (x + 1 / 2) := by linarith
    have hzup : a / (x + 1 / 2) ≤ 1 := le_of_lt hzlt
    let t := Real.arccos (a / (x + 1 / 2))
    have ht : t ∈ positiveTBranch :=
      ⟨Real.arccos_pos.mpr hzlt,
        Real.arccos_lt_pi_div_two.mpr hzpos⟩
    have hcos : Real.cos t = a / (x + 1 / 2) :=
      Real.cos_arccos hzlow hzup
    have hmap : substitutionMap t = x := by
      unfold substitutionMap sec
      rw [hcos]
      field_simp [ne_of_gt ha, ne_of_gt hy]
      ring
    calc
      F x = F (substitutionMap t) := by rw [hmap]
      _ = G t := hFG t ht
      _ = primitiveT t + C := hGC t ht
      _ = primitiveX (substitutionMap t) + C := by
        rw [primitiveT_eq_primitiveX_substitutionMap t ht]
      _ = primitiveX x + C := by rw [hmap]
  · rintro ⟨C, hFC⟩
    refine ⟨(fun t => primitiveT t + C), ⟨C, fun _ _ => rfl⟩, ?_⟩
    intro t ht
    have hmap := substitutionMap_mem_positive t ht
    calc
      F (substitutionMap t) =
          primitiveX (substitutionMap t) + C := hFC _ hmap
      _ = primitiveT t + C := by
        rw [primitiveT_eq_primitiveX_substitutionMap t ht]
theorem gap8 :
    AntiderivativesOn positiveXBranch originalIntegrand =
      PullbackFamily substitutionMap positiveTBranch
        (ScaledFamily positiveTBranch secIntegrand 4) := by
  rw [antiderivatives_positiveX_eq_primitiveX,
    scaledSec_eq_primitiveT, pullback_primitiveT_eq_primitiveX]
theorem gap9 :
    PullbackFamily substitutionMap positiveTBranch
        (ScaledFamily positiveTBranch secIntegrand 4) =
      PullbackFamily substitutionMap positiveTBranch
        (ScaledFamily positiveTBranch cosIntegrand 4) := by
  have hfun : secIntegrand = cosIntegrand := by
    funext t
    unfold secIntegrand cosIntegrand sec
    by_cases hcos : Real.cos t = 0
    · simp [hcos]
    · field_simp [hcos]
  rw [hfun]
theorem gap10 :
    AntiderivativesOn positiveXBranch originalIntegrand =
      PullbackFamily substitutionMap positiveTBranch
        (ScaledFamily positiveTBranch cosIntegrand 4) := by
  rw [gap8, gap9]
theorem gap11 :
    AntiderivativesOn positiveXBranch originalIntegrand =
      PullbackFamily substitutionMap positiveTBranch
        (ScaledFamily positiveTBranch uIntegrand (4 / Real.sqrt 3)) := by
  rw [gap10, scaledCos_eq_primitiveT, scaledU_eq_primitiveT]
theorem gap12 :
    AntiderivativesOn positiveXBranch originalIntegrand =
      PullbackFamily substitutionMap positiveTBranch
        (PrimitiveFamilyOn positiveTBranch primitiveT) := by
  rw [gap11, scaledU_eq_primitiveT]
theorem gap13 :
    AntiderivativesOn positiveXBranch originalIntegrand =
      PrimitiveFamilyOn positiveXBranch primitiveX := by
  exact antiderivatives_positiveX_eq_primitiveX
theorem gap14 (x t : ℝ) (h : negativeSubstitution x t) :
    Real.pi < t := by
  exact h.2.1.1
theorem gap15 (x t : ℝ) (h : negativeSubstitution x t) :
    t < (3 / 2 : ℝ) * Real.pi := by
  exact h.2.1.2
theorem gap16 (x t : ℝ) (h : negativeSubstitution x t) :
    Real.pi < (3 / 2 : ℝ) * Real.pi := by
  nlinarith [Real.pi_pos]
theorem gap17 :
    AntiderivativesOn negativeXBranch originalIntegrand =
      PrimitiveFamilyOn negativeXBranch primitiveX := by
  exact antiderivatives_negativeX_eq_primitiveX
theorem gap18 :
    AntiderivativesOn outerBranch originalIntegrand =
      BranchwisePrimitiveFamily := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, BranchwisePrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hneg : F ∈ AntiderivativesOn negativeXBranch originalIntegrand := by
      intro x hx
      apply hF x
      have ha : 0 < a := by
        unfold a
        positivity
      change x + 1 / 2 < -a at hx
      change a < |x + 1 / 2|
      rw [abs_of_neg (by linarith)]
      linarith
    have hpos : F ∈ AntiderivativesOn positiveXBranch originalIntegrand := by
      intro x hx
      apply hF x
      have ha : 0 < a := by
        unfold a
        positivity
      change a < x + 1 / 2 at hx
      change a < |x + 1 / 2|
      rw [abs_of_pos (by linarith)]
      exact hx
    rw [gap17] at hneg
    rw [gap13] at hpos
    rcases hneg with ⟨Cneg, hCneg⟩
    rcases hpos with ⟨Cpos, hCpos⟩
    exact ⟨Cneg, Cpos, hCneg, hCpos⟩
  · rintro ⟨Cneg, Cpos, hCneg, hCpos⟩ x hx
    have ha : 0 < a := by
      unfold a
      positivity
    change a < |x + 1 / 2| at hx
    by_cases hy : 0 ≤ x + 1 / 2
    · have hxpos : x ∈ positiveXBranch := by
        change a < x + 1 / 2
        rw [abs_of_nonneg hy] at hx
        exact hx
      have hmem : F ∈ PrimitiveFamilyOn positiveXBranch primitiveX :=
        ⟨Cpos, hCpos⟩
      rw [← gap13] at hmem
      exact hmem x hxpos
    · have hxneg : x ∈ negativeXBranch := by
        change x + 1 / 2 < -a
        rw [abs_of_neg (lt_of_not_ge hy)] at hx
        linarith
      have hmem : F ∈ PrimitiveFamilyOn negativeXBranch primitiveX :=
        ⟨Cneg, hCneg⟩
      rw [← gap17] at hmem
      exact hmem x hxneg

end
end ProofGap.Exercise1961
