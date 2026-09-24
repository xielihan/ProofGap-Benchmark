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

namespace ProofGap.Exercise1958

noncomputable section

def sec (t : ℝ) := 1 / Real.cos t
def positiveXBranch : Set ℝ := {x | 1 < x}
def negativeXBranch : Set ℝ := {x | x < -1}
def outerBranch : Set ℝ := {x | 1 < |x|}
def positiveTBranch : Set ℝ := Set.Ioo 0 (Real.pi / 2)
def negativeTBranch : Set ℝ := Set.Ioo Real.pi ((3 / 2 : ℝ) * Real.pi)
def positiveSubstitution (x t : ℝ) : Prop :=
  x ∈ positiveXBranch ∧ t ∈ positiveTBranch ∧ x = sec t
def negativeSubstitution (x t : ℝ) : Prop :=
  x ∈ negativeXBranch ∧ t ∈ negativeTBranch ∧ x = sec t
def xIntegrand (x : ℝ) :=
  1 / ((x ^ 2 + 1) * Real.sqrt (x ^ 2 - 1))
def secIntegrand (t : ℝ) := sec t / (1 + sec t ^ 2)
def cosIntegrand (t : ℝ) := Real.cos t / (Real.cos t ^ 2 + 1)
def sinIntegrand (t : ℝ) := deriv Real.sin t / (2 - Real.sin t ^ 2)
def primitiveT (t : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log |(Real.sqrt 2 + Real.sin t) / (Real.sqrt 2 - Real.sin t)|
def primitiveX (x : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log
      |(Real.sqrt 2 * x + Real.sqrt (x ^ 2 - 1)) /
        (Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1))|
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
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

private theorem hasDerivAt_primitiveT (t : ℝ) (ht : t ∈ positiveTBranch) :
    HasDerivAt primitiveT (sinIntegrand t) t := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt0 : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrt_cube : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt_sq]
  have hsqrt_gt_one : 1 < Real.sqrt 2 := by
    nlinarith [hsqrt_sq]
  have hsin_le : Real.sin t ≤ 1 := Real.sin_le_one t
  have hsin_ge : -1 ≤ Real.sin t := Real.neg_one_le_sin t
  have hplus0 : Real.sqrt 2 + Real.sin t ≠ 0 := by
    exact ne_of_gt (by nlinarith)
  have hminus0 : Real.sqrt 2 - Real.sin t ≠ 0 := by
    exact ne_of_gt (by nlinarith)
  have hden2 : 2 - Real.sin t ^ 2 ≠ 0 := by
    nlinarith [Real.sin_sq_le_one t]
  have hplus : HasDerivAt
      (fun y : ℝ => Real.sqrt 2 + Real.sin y) (Real.cos t) t := by
    convert HasDerivAt.add (hasDerivAt_const t (Real.sqrt 2))
      (Real.hasDerivAt_sin t) using 1 <;> ring
  have hminus : HasDerivAt
      (fun y : ℝ => Real.sqrt 2 - Real.sin y) (-Real.cos t) t := by
    convert HasDerivAt.sub (hasDerivAt_const t (Real.sqrt 2))
      (Real.hasDerivAt_sin t) using 1 <;> ring
  have hratio := hplus.div hminus hminus0
  have hlog : HasDerivAt
      (fun y : ℝ =>
        Real.log |(Real.sqrt 2 + Real.sin y) /
          (Real.sqrt 2 - Real.sin y)|)
      (((Real.cos t) * (Real.sqrt 2 - Real.sin t) -
          (Real.sqrt 2 + Real.sin t) * (-Real.cos t)) /
        (Real.sqrt 2 - Real.sin t) ^ 2 /
        ((Real.sqrt 2 + Real.sin t) /
          (Real.sqrt 2 - Real.sin t))) t := by
    simpa only [Real.log_abs, Function.comp_apply] using
      hratio.log (div_ne_zero hplus0 hminus0)
  have hscaled := hlog.const_mul (1 / (2 * Real.sqrt 2))
  have hcoef :
      1 / (2 * Real.sqrt 2) *
          ((((Real.cos t) * (Real.sqrt 2 - Real.sin t) -
              (Real.sqrt 2 + Real.sin t) * (-Real.cos t)) /
            (Real.sqrt 2 - Real.sin t) ^ 2) /
            ((Real.sqrt 2 + Real.sin t) /
              (Real.sqrt 2 - Real.sin t))) =
        sinIntegrand t := by
    unfold sinIntegrand
    rw [(Real.hasDerivAt_sin t).deriv]
    field_simp [hsqrt0, hplus0, hminus0, hden2]
    ring_nf
    rw [hsqrt_cube]
    ring
  convert hscaled.congr_deriv hcoef using 1

private theorem hasDerivAt_primitiveX (x : ℝ)
    (hx : x ∈ outerBranch) :
    HasDerivAt primitiveX (xIntegrand x) x := by
  have hxabs : 1 < |x| := hx
  have hxsq : 1 < x ^ 2 := by
    rw [← sq_abs x]
    nlinarith [sq_nonneg (|x| - 1)]
  have hrad : 0 < x ^ 2 - 1 := by linarith
  have hs : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hrad
  have hs0 : Real.sqrt (x ^ 2 - 1) ≠ 0 := ne_of_gt hs
  have hs_sq : (Real.sqrt (x ^ 2 - 1)) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt hrad.le
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr0 : Real.sqrt 2 ≠ 0 := ne_of_gt hr
  have hr_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hr_cube : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hr_sq]
  have hs_sq' : (Real.sqrt (-1 + x ^ 2)) ^ 2 = -1 + x ^ 2 := by
    simpa [sub_eq_add_neg, add_comm] using hs_sq
  have hroot : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
      (x / Real.sqrt (x ^ 2 - 1)) x := by
    have hinner : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;>
        simp only [id_eq] <;> ring
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner using 1 <;>
      field_simp [hs0] <;> ring
  have hlinear : HasDerivAt (fun y : ℝ => Real.sqrt 2 * y)
      (Real.sqrt 2) x := by
    convert (hasDerivAt_id x).const_mul (Real.sqrt 2) using 1 <;> ring
  have hplus : HasDerivAt
      (fun y : ℝ => Real.sqrt 2 * y + Real.sqrt (y ^ 2 - 1))
      (Real.sqrt 2 + x / Real.sqrt (x ^ 2 - 1)) x :=
    HasDerivAt.add hlinear hroot
  have hminus : HasDerivAt
      (fun y : ℝ => Real.sqrt 2 * y - Real.sqrt (y ^ 2 - 1))
      (Real.sqrt 2 - x / Real.sqrt (x ^ 2 - 1)) x :=
    HasDerivAt.sub hlinear hroot
  have hplus0 :
      Real.sqrt 2 * x + Real.sqrt (x ^ 2 - 1) ≠ 0 := by
    intro hzero
    have hsqzero := congrArg (fun z : ℝ => z ^ 2) hzero
    nlinarith [sq_nonneg x, hr_sq, hs_sq]
  have hminus0 :
      Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1) ≠ 0 := by
    intro hzero
    have hsqzero := congrArg (fun z : ℝ => z ^ 2) hzero
    nlinarith [sq_nonneg x, hr_sq, hs_sq]
  have hratio := hplus.div hminus hminus0
  have hlog : HasDerivAt
      (fun y : ℝ =>
        Real.log |(Real.sqrt 2 * y + Real.sqrt (y ^ 2 - 1)) /
          (Real.sqrt 2 * y - Real.sqrt (y ^ 2 - 1))|)
      (((Real.sqrt 2 + x / Real.sqrt (x ^ 2 - 1)) *
            (Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1)) -
          (Real.sqrt 2 * x + Real.sqrt (x ^ 2 - 1)) *
            (Real.sqrt 2 - x / Real.sqrt (x ^ 2 - 1))) /
        (Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1)) ^ 2 /
        ((Real.sqrt 2 * x + Real.sqrt (x ^ 2 - 1)) /
          (Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1)))) x := by
    simpa only [Real.log_abs, Function.comp_apply] using
      hratio.log (div_ne_zero hplus0 hminus0)
  have hscaled := hlog.const_mul (1 / (2 * Real.sqrt 2))
  have hcoef :
      1 / (2 * Real.sqrt 2) *
          (((Real.sqrt 2 + x / Real.sqrt (x ^ 2 - 1)) *
              (Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1)) -
            (Real.sqrt 2 * x + Real.sqrt (x ^ 2 - 1)) *
              (Real.sqrt 2 - x / Real.sqrt (x ^ 2 - 1))) /
            (Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1)) ^ 2 /
            ((Real.sqrt 2 * x + Real.sqrt (x ^ 2 - 1)) /
              (Real.sqrt 2 * x - Real.sqrt (x ^ 2 - 1)))) =
        xIntegrand x := by
    unfold xIntegrand
    field_simp [hr0, hs0, hplus0, hminus0]
    ring_nf
    rw [hs_sq', hr_cube]
    ring
  have hfinal := hscaled.congr_deriv hcoef
  apply hfinal.congr_of_eventuallyEq
  filter_upwards [] with y
  rfl

private theorem antiderivatives_sin_eq_primitiveT :
    AntiderivativesOn positiveTBranch sinIntegrand =
      PrimitiveFamilyOn positiveTBranch primitiveT := by
  apply antiderivatives_eq_primitive_on
  · simpa [positiveTBranch] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)))
  · simpa [positiveTBranch] using
      (isPreconnected_Ioo : IsPreconnected (Set.Ioo (0 : ℝ) (Real.pi / 2)))
  · refine ⟨Real.pi / 4, ?_⟩
    change 0 < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2
    constructor <;> nlinarith [Real.pi_pos]
  · exact hasDerivAt_primitiveT

theorem gap1 (x t : ℝ) (h : positiveSubstitution x t) :
    0 < t := by
  exact h.2.1.1
theorem gap2 (x t : ℝ) (h : positiveSubstitution x t) :
    t < Real.pi / 2 := by
  exact h.2.1.2
theorem gap3 (x t : ℝ) (h : positiveSubstitution x t) :
    0 < Real.pi / 2 := by positivity
theorem gap4 (x t : ℝ) (h : positiveSubstitution x t) :
    HasDerivAt sec (sec t * Real.tan t) t := by
  have ht0 := gap1 x t h
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], gap2 x t h⟩
  have hcos0 : Real.cos t ≠ 0 := ne_of_gt hcos
  unfold sec
  convert (hasDerivAt_const t (1 : ℝ)).div
    (Real.hasDerivAt_cos t) hcos0 using 1 <;>
    rw [Real.tan_eq_sin_div_cos] <;> field_simp [hcos0] <;> ring
theorem gap5 (x t : ℝ) (h : positiveSubstitution x t) :
    Real.sqrt (x ^ 2 - 1) = Real.tan t := by
  have ht0 := gap1 x t h
  have ht1 := gap2 x t h
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by nlinarith [Real.pi_pos])
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hrad : sec t ^ 2 - 1 = Real.tan t ^ 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [h.2.2, hrad, Real.sqrt_sq (le_of_lt htan)]

private theorem sec_mem_positiveXBranch (t : ℝ) (ht : t ∈ positiveTBranch) :
    sec t ∈ positiveXBranch := by
  have ht0 : 0 < t := ht.1
  have ht1 : t < Real.pi / 2 := ht.2
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ht1⟩
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by nlinarith [Real.pi_pos])
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
  change 1 < sec t
  nlinarith [sq_pos_of_pos htan]

private theorem primitiveT_eq_primitiveX_sec (t : ℝ)
    (ht : t ∈ positiveTBranch) :
    primitiveT t = primitiveX (sec t) := by
  have hsub : positiveSubstitution (sec t) t :=
    ⟨sec_mem_positiveXBranch t ht, ht, rfl⟩
  have hroot := gap5 (sec t) t hsub
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, ht.1], ht.2⟩
  have hratio :
      (Real.sqrt 2 * sec t + Real.tan t) /
          (Real.sqrt 2 * sec t - Real.tan t) =
        (Real.sqrt 2 + Real.sin t) /
          (Real.sqrt 2 - Real.sin t) := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
  unfold primitiveT primitiveX
  rw [hroot, hratio]

private theorem antiderivatives_positiveX_eq_primitiveX :
    AntiderivativesOn positiveXBranch xIntegrand =
      PrimitiveFamilyOn positiveXBranch primitiveX := by
  apply antiderivatives_eq_primitive_on
  · simpa [positiveXBranch] using (isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ)))
  · simpa [positiveXBranch] using (isPreconnected_Ioi : IsPreconnected (Set.Ioi (1 : ℝ)))
  · refine ⟨2, ?_⟩
    norm_num [positiveXBranch]
  · intro x hx
    apply hasDerivAt_primitiveX x
    change 1 < x at hx
    change 1 < |x|
    rw [abs_of_pos (by linarith)]
    exact hx

private theorem antiderivatives_sec_eq_primitiveT :
    AntiderivativesOn positiveTBranch secIntegrand =
      PrimitiveFamilyOn positiveTBranch primitiveT := by
  have hsec_cos : secIntegrand = cosIntegrand := by
    funext t
    unfold secIntegrand cosIntegrand sec
    by_cases hcos : Real.cos t = 0
    · simp [hcos]
    · field_simp [hcos]
  have hcos_sin : cosIntegrand = sinIntegrand := by
    funext t
    unfold cosIntegrand sinIntegrand
    rw [(Real.hasDerivAt_sin t).deriv]
    rw [show 2 - Real.sin t ^ 2 = Real.cos t ^ 2 + 1 by
      nlinarith [Real.sin_sq_add_cos_sq t]]
  rw [hsec_cos, hcos_sin]
  exact antiderivatives_sin_eq_primitiveT

private theorem pullback_primitiveT_eq_primitiveX :
    PullbackFamily sec positiveTBranch
        (PrimitiveFamilyOn positiveTBranch primitiveT) =
      PrimitiveFamilyOn positiveXBranch primitiveX := by
  apply Set.ext
  intro F
  simp only [PullbackFamily, PrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, ⟨C, hGC⟩, hFG⟩
    refine ⟨C, ?_⟩
    intro x hx
    change 1 < x at hx
    have hxpos : 0 < x := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hzpos : 0 < 1 / x := one_div_pos.mpr hxpos
    have hzlt : 1 / x < 1 := by
      rw [div_lt_iff₀ hxpos]
      simpa using hx
    have hzlow : -1 ≤ 1 / x := by linarith
    have hzup : 1 / x ≤ 1 := le_of_lt hzlt
    let t := Real.arccos (1 / x)
    have ht : t ∈ positiveTBranch := by
      constructor
      · exact Real.arccos_pos.mpr hzlt
      · exact Real.arccos_lt_pi_div_two.mpr hzpos
    have hcos : Real.cos t = 1 / x := by
      exact Real.cos_arccos hzlow hzup
    have hsec : sec t = x := by
      unfold sec
      rw [hcos]
      field_simp [hx0]
    calc
      F x = F (sec t) := by rw [hsec]
      _ = G t := hFG t ht
      _ = primitiveT t + C := hGC t ht
      _ = primitiveX (sec t) + C := by rw [primitiveT_eq_primitiveX_sec t ht]
      _ = primitiveX x + C := by rw [hsec]
  · rintro ⟨C, hFC⟩
    refine ⟨(fun t => primitiveT t + C), ?_, ?_⟩
    · exact ⟨C, fun _ _ => rfl⟩
    · intro t ht
      have hsec := sec_mem_positiveXBranch t ht
      calc
        F (sec t) = primitiveX (sec t) + C := hFC (sec t) hsec
        _ = primitiveT t + C := by rw [primitiveT_eq_primitiveX_sec t ht]
theorem gap6 :
    AntiderivativesOn positiveXBranch xIntegrand =
      PullbackFamily sec positiveTBranch
        (AntiderivativesOn positiveTBranch secIntegrand) := by
  rw [antiderivatives_positiveX_eq_primitiveX,
    antiderivatives_sec_eq_primitiveT, pullback_primitiveT_eq_primitiveX]
theorem gap7 :
    AntiderivativesOn positiveTBranch secIntegrand =
      AntiderivativesOn positiveTBranch cosIntegrand := by
  apply congrArg (AntiderivativesOn positiveTBranch)
  funext t
  unfold secIntegrand cosIntegrand sec
  by_cases hcos : Real.cos t = 0
  · simp [hcos]
  · field_simp [hcos]
theorem gap8 :
    AntiderivativesOn positiveTBranch cosIntegrand =
      AntiderivativesOn positiveTBranch sinIntegrand := by
  apply congrArg (AntiderivativesOn positiveTBranch)
  funext t
  unfold cosIntegrand sinIntegrand
  rw [(Real.hasDerivAt_sin t).deriv]
  rw [show 2 - Real.sin t ^ 2 = Real.cos t ^ 2 + 1 by
    nlinarith [Real.sin_sq_add_cos_sq t]]
theorem gap9 :
    AntiderivativesOn positiveXBranch xIntegrand =
      PullbackFamily sec positiveTBranch
        (AntiderivativesOn positiveTBranch sinIntegrand) := by
  rw [gap6, gap7, gap8]
theorem gap10 :
    AntiderivativesOn positiveXBranch xIntegrand =
      PullbackFamily sec positiveTBranch
        (PrimitiveFamilyOn positiveTBranch primitiveT) := by
  rw [antiderivatives_positiveX_eq_primitiveX,
    pullback_primitiveT_eq_primitiveX]
theorem gap11 :
    PullbackFamily sec positiveTBranch
        (PrimitiveFamilyOn positiveTBranch primitiveT) =
      PrimitiveFamilyOn positiveXBranch primitiveX := by
  exact pullback_primitiveT_eq_primitiveX
theorem gap12 :
    AntiderivativesOn positiveXBranch xIntegrand =
      PrimitiveFamilyOn positiveXBranch primitiveX := by
  apply antiderivatives_eq_primitive_on
  · simpa [positiveXBranch] using (isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ)))
  · simpa [positiveXBranch] using (isPreconnected_Ioi : IsPreconnected (Set.Ioi (1 : ℝ)))
  · refine ⟨2, ?_⟩
    norm_num [positiveXBranch]
  · intro x hx
    apply hasDerivAt_primitiveX x
    change 1 < x at hx
    change 1 < |x|
    rw [abs_of_pos (by
      linarith)]
    exact hx
theorem gap13 (x t : ℝ) (h : negativeSubstitution x t) :
    Real.pi < t := by
  exact h.2.1.1
theorem gap14 (x t : ℝ) (h : negativeSubstitution x t) :
    t < (3 / 2 : ℝ) * Real.pi := by
  exact h.2.1.2
theorem gap15 (x t : ℝ) (h : negativeSubstitution x t) :
    Real.pi < (3 / 2 : ℝ) * Real.pi := by
  nlinarith [Real.pi_pos]
theorem gap16 :
    AntiderivativesOn negativeXBranch xIntegrand =
      PrimitiveFamilyOn negativeXBranch primitiveX := by
  apply antiderivatives_eq_primitive_on
  · simpa [negativeXBranch] using (isOpen_Iio : IsOpen (Set.Iio (-1 : ℝ)))
  · simpa [negativeXBranch] using (isPreconnected_Iio : IsPreconnected (Set.Iio (-1 : ℝ)))
  · refine ⟨-2, ?_⟩
    norm_num [negativeXBranch]
  · intro x hx
    apply hasDerivAt_primitiveX x
    change x < -1 at hx
    change 1 < |x|
    rw [abs_of_neg (by
      linarith)]
    linarith
theorem gap17 :
    AntiderivativesOn outerBranch xIntegrand =
      BranchwisePrimitiveFamily := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, BranchwisePrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hneg : F ∈ AntiderivativesOn negativeXBranch xIntegrand := by
      intro x hx
      apply hF x
      change x < -1 at hx
      change 1 < |x|
      rw [abs_of_neg (by linarith)]
      linarith
    have hpos : F ∈ AntiderivativesOn positiveXBranch xIntegrand := by
      intro x hx
      apply hF x
      change 1 < x at hx
      change 1 < |x|
      rw [abs_of_pos (by linarith)]
      exact hx
    rw [gap16] at hneg
    rw [gap12] at hpos
    rcases hneg with ⟨Cneg, hCneg⟩
    rcases hpos with ⟨Cpos, hCpos⟩
    exact ⟨Cneg, Cpos, hCneg, hCpos⟩
  · rintro ⟨Cneg, Cpos, hCneg, hCpos⟩ x hx
    change 1 < |x| at hx
    by_cases hx0 : 0 ≤ x
    · have hxpos : x ∈ positiveXBranch := by
        change 1 < x
        simpa [abs_of_nonneg hx0] using hx
      have hmem : F ∈ PrimitiveFamilyOn positiveXBranch primitiveX :=
        ⟨Cpos, hCpos⟩
      rw [← gap12] at hmem
      exact hmem x hxpos
    · have hxneg : x ∈ negativeXBranch := by
        change x < -1
        rw [abs_of_neg (lt_of_not_ge hx0)] at hx
        linarith
      have hmem : F ∈ PrimitiveFamilyOn negativeXBranch primitiveX :=
        ⟨Cneg, hCneg⟩
      rw [← gap16] at hmem
      exact hmem x hxneg

end
end ProofGap.Exercise1958
