import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1974

noncomputable section

def q (x : ℝ) := x ^ 2 + x + 1
def root (x : ℝ) := Real.sqrt (q x)
def nonzeroBranch : Set ℝ := {x | x ≠ 0}
def positiveBranch : Set ℝ := Set.Ioi 0
def negativeBranch : Set ℝ := Set.Iio 0
def tBranch : Set ℝ := Set.Ioi 0
def reciprocal (t : ℝ) := 1 / t
def substitution (x t : ℝ) : Prop := t ≠ 0 ∧ x = reciprocal t
def originalIntegrand (x : ℝ) :=
  (x + root x) / (1 + x + root x)
def conjugateIntegrand (x : ℝ) :=
  (x + root x) * (1 + x - root x) / ((1 + x) ^ 2 - q x)
def simplifiedIntegrand (x : ℝ) := (root x - 1) / x
def auxiliaryIntegrand (x : ℝ) := root x / x
def tRawIntegrand (t : ℝ) := Real.sqrt (t ^ 2 + t + 1) / t ^ 2
def inverseWeightedIntegrand (t : ℝ) :=
  Real.sqrt (t ^ 2 + t + 1) * deriv reciprocal t
def byPartsResidual (t : ℝ) :=
  (2 * t + 1) / (t * Real.sqrt (1 + t + t ^ 2))
def firstResidual (t : ℝ) := 1 / Real.sqrt (1 + t + t ^ 2)
def secondResidual (t : ℝ) :=
  1 / (t * Real.sqrt (1 + t + t ^ 2))
def reciprocalResidual (t : ℝ) :=
  deriv reciprocal t /
    Real.sqrt (reciprocal t ^ 2 + reciprocal t + 1)
def auxiliaryPrimitive₁ (x : ℝ) :=
  root x -
    Real.log ((2 + x + 2 * root x) / (2 * x)) +
    1 / 2 * Real.log ((2 * x + 1 + 2 * root x) / 2)
def auxiliaryPrimitive₂ (x : ℝ) :=
  root x +
    1 / 2 *
      Real.log
        ((2 * x + 1 + 2 * root x) / (2 + x + 2 * root x) ^ 2) +
    Real.log x
def finalPrimitive (x : ℝ) :=
  root x +
    1 / 2 *
      Real.log
        ((2 * x + 1 + 2 * root x) / (2 + x + 2 * root x) ^ 2)
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def PullbackFamily (map : ℝ → ℝ) (s : Set ℝ)
    (T : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ T, ∀ t ∈ s, F (map t) = G t}
def SubtractLogFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn nonzeroBranch auxiliaryIntegrand,
    ∀ x ∈ nonzeroBranch, F x = G x - Real.log |x|}
def NegatedRawFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn tBranch tRawIntegrand,
    ∀ t ∈ tBranch, F t = -G t}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn tBranch byPartsResidual,
    ∀ t ∈ tBranch,
      F t = Real.sqrt (t ^ 2 + t + 1) / t - 1 / 2 * G t}
def SplitResidualFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn tBranch firstResidual,
    ∃ H ∈ AntiderivativesOn tBranch secondResidual,
      ∀ t ∈ tBranch,
        F t = Real.sqrt (t ^ 2 + t + 1) / t - G t - 1 / 2 * H t}
def LogReciprocalFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn tBranch reciprocalResidual,
    ∀ t ∈ tBranch,
      F t =
        Real.sqrt (t ^ 2 + t + 1) / t -
          Real.log (t + 1 / 2 + Real.sqrt (1 + t + t ^ 2)) +
          1 / 2 * G t}

theorem gap1 :
    AntiderivativesOn nonzeroBranch originalIntegrand =
      AntiderivativesOn nonzeroBranch conjugateIntegrand := by
  ext F
  constructor
  · intro hF x hx
    have hx0 : x ≠ 0 := hx
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hrsq : root x ^ 2 = q x := by
      unfold root
      exact Real.sq_sqrt hq.le
    unfold q at hrsq
    have hden : 1 + x + root x ≠ 0 := by
      intro hzero
      have hr : 0 ≤ root x := by unfold root; positivity
      apply hx
      nlinarith
    convert hF x hx using 1
    unfold originalIntegrand conjugateIntegrand q
    rw [show (1 + x) ^ 2 - (x ^ 2 + x + 1) = x by ring]
    field_simp [hx0, hden]
    linear_combination -(x + root x) * hrsq
  · intro hF x hx
    have hx0 : x ≠ 0 := hx
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hrsq : root x ^ 2 = q x := by
      unfold root
      exact Real.sq_sqrt hq.le
    unfold q at hrsq
    have hden : 1 + x + root x ≠ 0 := by
      intro hzero
      have hr : 0 ≤ root x := by unfold root; positivity
      apply hx
      nlinarith
    convert hF x hx using 1
    unfold originalIntegrand conjugateIntegrand q
    rw [show (1 + x) ^ 2 - (x ^ 2 + x + 1) = x by ring]
    field_simp [hx0, hden]
    linear_combination (x + root x) * hrsq
theorem gap2 :
    AntiderivativesOn nonzeroBranch originalIntegrand =
      AntiderivativesOn nonzeroBranch simplifiedIntegrand := by
  rw [gap1]
  ext F
  constructor
  · intro hF x hx
    have hx0 : x ≠ 0 := hx
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hrsq : root x ^ 2 = x ^ 2 + x + 1 := by
      unfold root q
      exact Real.sq_sqrt (by
        unfold q at hq
        exact hq.le)
    convert hF x hx using 1
    unfold conjugateIntegrand simplifiedIntegrand q
    rw [show (1 + x) ^ 2 - (x ^ 2 + x + 1) = x by ring]
    field_simp [hx0]
    nlinarith
  · intro hF x hx
    have hx0 : x ≠ 0 := hx
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hrsq : root x ^ 2 = x ^ 2 + x + 1 := by
      unfold root q
      exact Real.sq_sqrt (by
        unfold q at hq
        exact hq.le)
    convert hF x hx using 1
    unfold conjugateIntegrand simplifiedIntegrand q
    rw [show (1 + x) ^ 2 - (x ^ 2 + x + 1) = x by ring]
    field_simp [hx0]
    nlinarith
theorem gap3 :
    AntiderivativesOn nonzeroBranch simplifiedIntegrand =
      SubtractLogFamily := by
  have hlog : ∀ x, x ≠ 0 →
      HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    intro x hx
    have hfun : (fun y : ℝ => Real.log |y|) = Real.log := by
      funext y
      exact Real.log_abs y
    rw [hfun]
    simpa [one_div] using Real.hasDerivAt_log hx
  ext F
  constructor
  · intro hF
    refine ⟨fun x => F x + Real.log |x|, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).add (hlog x hx) using 1
      unfold simplifiedIntegrand auxiliaryIntegrand
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hF⟩ x hx
    have hopen : IsOpen nonzeroBranch := by
      rw [show nonzeroBranch = ({0} : Set ℝ)ᶜ by
        ext y
        simp [nonzeroBranch]]
      exact isClosed_singleton.isOpen_compl
    have heq : F =ᶠ[nhds x] (fun y => G y - Real.log |y|) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hF y hy
    convert ((hG x hx).sub (hlog x hx)).congr_of_eventuallyEq heq using 1
    unfold simplifiedIntegrand auxiliaryIntegrand
    ring
theorem gap4 :
    AntiderivativesOn nonzeroBranch originalIntegrand =
      SubtractLogFamily := by
  rw [gap2, gap3]
theorem gap5 (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt reciprocal (-1 / t ^ 2) t := by
  unfold reciprocal
  convert (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht using 1 <;>
    simp [id] <;> field_simp [ht] <;> ring
theorem gap6 (x t : ℝ) (h : substitution x t) :
    root x = Real.sqrt (t ^ 2 + t + 1) / |t| := by
  have ht : t ≠ 0 := h.1
  rw [h.2]
  have hrad : 0 < t ^ 2 + t + 1 := by
    nlinarith [sq_nonneg (t + 1 / 2)]
  have hq : q (reciprocal t) = (t ^ 2 + t + 1) / t ^ 2 := by
    unfold q reciprocal
    field_simp [ht]
    ring
  unfold root
  rw [hq, Real.sqrt_div hrad.le, Real.sqrt_sq_eq_abs]
theorem gap7 :
    AntiderivativesOn positiveBranch auxiliaryIntegrand =
      PullbackFamily reciprocal tBranch NegatedRawFamily := by
  ext F
  constructor
  · intro hF
    let G : ℝ → ℝ := fun t => F (reciprocal t)
    let H : ℝ → ℝ := fun t => -F (reciprocal t)
    have hH : H ∈ AntiderivativesOn tBranch tRawIntegrand := by
      intro t ht
      have htpos : 0 < t := ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      have hrt : 0 < reciprocal t := by
        unfold reciprocal
        exact one_div_pos.mpr htpos
      have hr := gap6 (reciprocal t) t ⟨ht0, rfl⟩
      rw [abs_of_pos ht] at hr
      have hd := ((hF (reciprocal t) hrt).comp t (gap5 t ht0)).neg
      dsimp [H]
      convert hd using 1
      unfold auxiliaryIntegrand tRawIntegrand
      rw [hr]
      unfold reciprocal
      field_simp [ht0]
    have hG : G ∈ NegatedRawFamily := by
      refine ⟨H, hH, ?_⟩
      intro t ht
      dsimp [G, H]
      ring
    exact ⟨G, hG, fun t ht => rfl⟩
  · rintro ⟨G, ⟨H, hH, hGH⟩, hFG⟩
    intro x hx
    have hxpos : 0 < x := hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have htx : 0 < reciprocal x := by
      unfold reciprocal
      exact one_div_pos.mpr hxpos
    have heq : F =ᶠ[nhds x] (fun y => -H (reciprocal y)) := by
      filter_upwards [(show IsOpen positiveBranch by
        unfold positiveBranch
        exact isOpen_Ioi).mem_nhds hx] with y hy
      have hypos : 0 < y := hy
      have hy0 : y ≠ 0 := ne_of_gt hy
      have hty : 0 < reciprocal y := by
        unfold reciprocal
        exact one_div_pos.mpr hypos
      calc
        F y = F (reciprocal (reciprocal y)) := by
          unfold reciprocal
          field_simp [hy0]
        _ = G (reciprocal y) := hFG (reciprocal y) hty
        _ = -H (reciprocal y) := hGH (reciprocal y) hty
    have hr := gap6 x (reciprocal x) ⟨by
      unfold reciprocal
      exact one_div_ne_zero hx0, by
        unfold reciprocal
        field_simp [hx0]⟩
    rw [abs_of_pos htx] at hr
    have hd := ((hH (reciprocal x) htx).comp x (gap5 x hx0)).neg
    convert hd.congr_of_eventuallyEq heq using 1
    unfold reciprocal at hr
    unfold auxiliaryIntegrand tRawIntegrand reciprocal
    rw [hr]
    field_simp [hx0]
theorem gap8 :
    NegatedRawFamily =
      AntiderivativesOn tBranch inverseWeightedIntegrand := by
  have hcoef : ∀ t ∈ tBranch,
      inverseWeightedIntegrand t = -tRawIntegrand t := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have : 0 < t := ht
      positivity
    unfold inverseWeightedIntegrand tRawIntegrand
    rw [(gap5 t ht0).deriv]
    ring
  ext F
  constructor
  · rintro ⟨G, hG, hF⟩ t ht
    have heq : F =ᶠ[nhds t] (fun y => -G y) := by
      filter_upwards [(show IsOpen tBranch by
        unfold tBranch
        exact isOpen_Ioi).mem_nhds ht] with y hy
      exact hF y hy
    convert ((hG t ht).neg.congr_of_eventuallyEq heq) using 1
    rw [hcoef t ht]
  · intro hF
    refine ⟨fun t => -F t, ?_, ?_⟩
    · intro t ht
      convert (hF t ht).neg using 1
      rw [hcoef t ht]
      ring
    · intro t ht
      ring
theorem gap9 :
    AntiderivativesOn positiveBranch auxiliaryIntegrand =
      PullbackFamily reciprocal tBranch
        (AntiderivativesOn tBranch inverseWeightedIntegrand) := by
  rw [gap7, gap8]
private lemma hasDerivAt_sqrt_div (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + y + 1) / y)
      (1 / 2 * byPartsResidual t - tRawIntegrand t) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hrad : 0 < t ^ 2 + t + 1 := by
    nlinarith [sq_nonneg (t + 1 / 2)]
  have hinner :
      HasDerivAt (fun y : ℝ => y ^ 2 + y + 1) (2 * t + 1) t := by
    convert (((hasDerivAt_id t).pow 2).add (hasDerivAt_id t)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hsqrt :=
    (Real.hasDerivAt_sqrt hrad.ne').comp t hinner
  have hd := hsqrt.div (hasDerivAt_id t) ht0
  have hd' :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + y + 1) / y)
        (((1 / (2 * Real.sqrt (t ^ 2 + t + 1)) * (2 * t + 1)) * t -
          Real.sqrt (t ^ 2 + t + 1)) / t ^ 2) t := by
    simpa [Function.comp_def, id] using hd
  convert hd' using 1
  unfold byPartsResidual tRawIntegrand
  have hsqrt0 : Real.sqrt (t ^ 2 + t + 1) ≠ 0 := by positivity
  field_simp [ht0, hsqrt0]
  ring
theorem gap10 :
    AntiderivativesOn positiveBranch auxiliaryIntegrand =
      PullbackFamily reciprocal tBranch ByPartsFamily := by
  rw [gap7]
  suffices hfamilies : NegatedRawFamily = ByPartsFamily by rw [hfamilies]
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    let U : ℝ → ℝ := fun t => Real.sqrt (t ^ 2 + t + 1) / t
    let K : ℝ → ℝ := fun t => 2 * (U t - F t)
    have hK : K ∈ AntiderivativesOn tBranch byPartsResidual := by
      intro t ht
      have htpos : 0 < t := ht
      have heq : F =ᶠ[nhds t] (fun y => -G y) := by
        filter_upwards [(show IsOpen tBranch by
          unfold tBranch
          exact isOpen_Ioi).mem_nhds ht] with y hy
        exact hFG y hy
      have hFd : HasDerivAt F (-tRawIntegrand t) t :=
        (hG t ht).neg.congr_of_eventuallyEq heq
      have hUd : HasDerivAt U
          (1 / 2 * byPartsResidual t - tRawIntegrand t) t := by
        simpa [U] using hasDerivAt_sqrt_div t htpos
      dsimp [K]
      convert (hUd.sub hFd).const_mul 2 using 1 <;> ring
    refine ⟨K, hK, ?_⟩
    intro t ht
    dsimp [K, U]
    ring
  · rintro ⟨K, hK, hFK⟩
    let G : ℝ → ℝ := fun t => -F t
    have hG : G ∈ AntiderivativesOn tBranch tRawIntegrand := by
      intro t ht
      have htpos : 0 < t := ht
      have heq : F =ᶠ[nhds t]
          (fun y => Real.sqrt (y ^ 2 + y + 1) / y - 1 / 2 * K y) := by
        filter_upwards [(show IsOpen tBranch by
          unfold tBranch
          exact isOpen_Ioi).mem_nhds ht] with y hy
        exact hFK y hy
      have hUd := hasDerivAt_sqrt_div t htpos
      have hFd : HasDerivAt F (-tRawIntegrand t) t := by
        convert (hUd.sub ((hK t ht).const_mul (1 / 2))).congr_of_eventuallyEq heq using 1 <;>
          ring
      dsimp [G]
      convert hFd.neg using 1 <;> ring
    exact ⟨G, hG, fun t ht => by dsimp [G]; ring⟩
private lemma hasDerivAt_log_first (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun y : ℝ =>
        Real.log (y + 1 / 2 + Real.sqrt (1 + y + y ^ 2)))
      (firstResidual t) t := by
  have hrad : 0 < 1 + t + t ^ 2 := by
    nlinarith [sq_nonneg (t + 1 / 2)]
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + y + y ^ 2) (1 + 2 * t) t := by
    convert ((hasDerivAt_const t 1).add (hasDerivAt_id t)).add
      ((hasDerivAt_id t).pow 2) using 1 <;> simp [id] <;> ring
  have hsqrt :=
    (Real.hasDerivAt_sqrt hrad.ne').comp t hinner
  have harg : 0 < t + 1 / 2 + Real.sqrt (1 + t + t ^ 2) := by positivity
  have hargDeriv :
      HasDerivAt
        (fun y : ℝ => y + 1 / 2 + Real.sqrt (1 + y + y ^ 2))
        (1 + 1 / (2 * Real.sqrt (1 + t + t ^ 2)) * (1 + 2 * t)) t := by
    convert ((hasDerivAt_id t).add_const (1 / 2)).add hsqrt using 1 <;>
      simp [Function.comp_def, id] <;> ring
  have hd := (Real.hasDerivAt_log harg.ne').comp t hargDeriv
  convert hd using 1
  unfold firstResidual
  have hsqrt0 : Real.sqrt (1 + t + t ^ 2) ≠ 0 := by positivity
  field_simp [harg.ne', hsqrt0]
  ring
theorem gap11 :
    AntiderivativesOn positiveBranch auxiliaryIntegrand =
      PullbackFamily reciprocal tBranch SplitResidualFamily := by
  rw [gap10]
  suffices hfamilies : ByPartsFamily = SplitResidualFamily by rw [hfamilies]
  ext F
  constructor
  · rintro ⟨K, hK, hFK⟩
    let L : ℝ → ℝ := fun t =>
      Real.log (t + 1 / 2 + Real.sqrt (1 + t + t ^ 2))
    let H : ℝ → ℝ := fun t => K t - 2 * L t
    have hL : L ∈ AntiderivativesOn tBranch firstResidual := by
      intro t ht
      simpa [L] using hasDerivAt_log_first t (show 0 < t from ht)
    have hH : H ∈ AntiderivativesOn tBranch secondResidual := by
      intro t ht
      dsimp [H]
      convert (hK t ht).sub ((hL t ht).const_mul 2) using 1
      unfold byPartsResidual firstResidual secondResidual
      have ht0 : t ≠ 0 := ne_of_gt (show 0 < t from ht)
      have hr : Real.sqrt (1 + t + t ^ 2) ≠ 0 := by
        apply Real.sqrt_ne_zero'.mpr
        nlinarith [sq_nonneg (t + 1 / 2)]
      field_simp [ht0, hr]
      ring
    refine ⟨L, hL, H, hH, ?_⟩
    intro t ht
    rw [hFK t ht]
    dsimp [H]
    ring
  · rintro ⟨G, hG, H, hH, hF⟩
    let K : ℝ → ℝ := fun t => 2 * G t + H t
    have hK : K ∈ AntiderivativesOn tBranch byPartsResidual := by
      intro t ht
      dsimp [K]
      convert ((hG t ht).const_mul 2).add (hH t ht) using 1
      unfold byPartsResidual firstResidual secondResidual
      have ht0 : t ≠ 0 := ne_of_gt (show 0 < t from ht)
      have hr : Real.sqrt (1 + t + t ^ 2) ≠ 0 := by
        apply Real.sqrt_ne_zero'.mpr
        nlinarith [sq_nonneg (t + 1 / 2)]
      field_simp [ht0, hr]
    refine ⟨K, hK, ?_⟩
    intro t ht
    rw [hF t ht]
    dsimp [K]
    ring
private lemma reciprocalResidual_eq (t : ℝ) (ht : 0 < t) :
    reciprocalResidual t = -secondResidual t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hr := gap6 (reciprocal t) t ⟨ht0, rfl⟩
  rw [abs_of_pos ht] at hr
  unfold reciprocalResidual secondResidual
  change deriv reciprocal t / root (reciprocal t) =
    -(1 / (t * Real.sqrt (1 + t + t ^ 2)))
  rw [(gap5 t ht0).deriv, hr]
  field_simp [ht0]
  ring
theorem gap12 :
    AntiderivativesOn positiveBranch auxiliaryIntegrand =
      PullbackFamily reciprocal tBranch LogReciprocalFamily := by
  rw [gap11]
  suffices hfamilies : SplitResidualFamily = LogReciprocalFamily by rw [hfamilies]
  let L : ℝ → ℝ := fun t =>
    Real.log (t + 1 / 2 + Real.sqrt (1 + t + t ^ 2))
  have hL : L ∈ AntiderivativesOn tBranch firstResidual := by
    intro t ht
    simpa [L] using hasDerivAt_log_first t (show 0 < t from ht)
  ext F
  constructor
  · rintro ⟨G, hG, H, hH, hF⟩
    let R : ℝ → ℝ := fun t => -(H t + 2 * (G t - L t))
    have hR : R ∈ AntiderivativesOn tBranch reciprocalResidual := by
      intro t ht
      dsimp [R]
      have hd :=
        ((hH t ht).add (((hG t ht).sub (hL t ht)).const_mul 2)).neg
      convert hd using 1
      rw [reciprocalResidual_eq t (show 0 < t from ht)]
      ring
    refine ⟨R, hR, ?_⟩
    intro t ht
    rw [hF t ht]
    dsimp [R, L]
    ring
  · rintro ⟨R, hR, hF⟩
    let H : ℝ → ℝ := fun t => -R t
    have hH : H ∈ AntiderivativesOn tBranch secondResidual := by
      intro t ht
      dsimp [H]
      convert (hR t ht).neg using 1
      rw [reciprocalResidual_eq t (show 0 < t from ht)]
      ring
    refine ⟨L, hL, H, hH, ?_⟩
    intro t ht
    rw [hF t ht]
    dsimp [H, L]
    ring
private lemma root_sq (x : ℝ) : root x ^ 2 = x ^ 2 + x + 1 := by
  unfold root q
  exact Real.sq_sqrt (by nlinarith [sq_nonneg (x + 1 / 2)])

private lemma root_pos (x : ℝ) : 0 < root x := by
  unfold root q
  rw [Real.sqrt_pos]
  nlinarith [sq_nonneg (x + 1 / 2)]

private lemma hasDerivAt_root (x : ℝ) :
    HasDerivAt root ((2 * x + 1) / (2 * root x)) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => y ^ 2 + y + 1) (2 * x + 1) x := by
    convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  unfold root q
  convert (Real.hasDerivAt_sqrt (by
    nlinarith [sq_nonneg (x + 1 / 2)] :
      x ^ 2 + x + 1 ≠ 0)).comp x hinner using 1 <;>
    ring

private lemma first_log_arg_pos (x : ℝ) :
    0 < 2 * x + 1 + 2 * root x := by
  have hr := root_pos x
  have hrsq := root_sq x
  nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (root x + x + 1 / 2)]

private lemma second_log_arg_pos (x : ℝ) (hx : x ≠ 0) :
    0 < 2 + x + 2 * root x := by
  have hr := root_pos x
  have hrsq := root_sq x
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  nlinarith [sq_nonneg (x / 2 + 1), sq_nonneg (root x + x / 2 + 1)]

private lemma original_den_pos (x : ℝ) (hx : x ≠ 0) :
    0 < 1 + x + root x := by
  have hr := root_pos x
  have hrsq := root_sq x
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · nlinarith [sq_nonneg (x + 1), sq_nonneg (root x + x + 1)]
  · nlinarith

private lemma hasDerivAt_final (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt finalPrimitive (originalIntegrand x) x := by
  let A : ℝ → ℝ := fun y => 2 * y + 1 + 2 * root y
  let B : ℝ → ℝ := fun y => 2 + y + 2 * root y
  let d : ℝ := (2 * x + 1) / (2 * root x)
  have hroot : HasDerivAt root d x := by
    simpa [d] using hasDerivAt_root x
  have hA : HasDerivAt A (2 + 2 * d) x := by
    dsimp [A]
    convert (((hasDerivAt_id x).const_mul 2).add_const 1).add
      (hroot.const_mul 2) using 1 <;> ring
  have hB : HasDerivAt B (1 + 2 * d) x := by
    dsimp [B]
    convert ((hasDerivAt_const x 2).add (hasDerivAt_id x)).add
      (hroot.const_mul 2) using 1 <;> ring
  have hApos : 0 < A x := by simpa [A] using first_log_arg_pos x
  have hBpos : 0 < B x := by simpa [B] using second_log_arg_pos x hx
  have hlogA : HasDerivAt (fun y => Real.log (A y)) ((2 + 2 * d) / A x) x := by
    convert (Real.hasDerivAt_log hApos.ne').comp x hA using 1 <;> ring
  have hlogB : HasDerivAt (fun y => Real.log (B y)) ((1 + 2 * d) / B x) x := by
    convert (Real.hasDerivAt_log hBpos.ne').comp x hB using 1 <;> ring
  have hfun :
      finalPrimitive =
        fun y => root y + 1 / 2 * Real.log (A y) - Real.log (B y) := by
    funext y
    have hAy : A y ≠ 0 := by
      have := first_log_arg_pos y
      positivity
    have hBy : B y ≠ 0 := by
      by_cases hy : y = 0
      · subst y
        norm_num [B, root, q]
      · have := second_log_arg_pos y hy
        positivity
    unfold finalPrimitive
    rw [Real.log_div hAy (pow_ne_zero 2 hBy), Real.log_pow]
    dsimp [A, B]
    ring
  rw [hfun]
  have hd :=
    (hroot.add (hlogA.const_mul (1 / 2))).sub hlogB
  convert hd using 1
  unfold originalIntegrand
  dsimp [A, B, d]
  have hr0 : root x ≠ 0 := (root_pos x).ne'
  have hden0 : 1 + x + root x ≠ 0 := (original_den_pos x hx).ne'
  have hA0 : 2 * x + 1 + 2 * root x ≠ 0 := (first_log_arg_pos x).ne'
  have hB0 : 2 + x + 2 * root x ≠ 0 := (second_log_arg_pos x hx).ne'
  have hA0' : x * 2 + 1 + root x * 2 ≠ 0 := by
    nlinarith
  have hB0' : 2 + x + root x * 2 ≠ 0 := by
    nlinarith
  have hr3 : root x ^ 3 = root x * (x ^ 2 + x + 1) := by
    calc
      root x ^ 3 = root x * root x ^ 2 := by ring
      _ = root x * (x ^ 2 + x + 1) := by rw [root_sq x]
  have hr4 : root x ^ 4 = (x ^ 2 + x + 1) ^ 2 := by
    calc
      root x ^ 4 = (root x ^ 2) ^ 2 := by ring
      _ = (x ^ 2 + x + 1) ^ 2 := by rw [root_sq x]
  field_simp [hr0, hden0, hA0, hB0, hA0', hB0']
  ring_nf
  rw [hr3, hr4, root_sq x]
  ring

private lemma antiderivatives_eq_primitive
    (s : Set ℝ) (f p : ℝ → ℝ)
    (hopen : IsOpen s) (hpre : IsPreconnected s)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF
    have hz : ∀ x ∈ s, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) s :=
      fun x hx => (hz x hx).differentiableAt.differentiableWithinAt
    have hderiv : s.EqOn (deriv (fun y => F y - p y)) 0 :=
      fun x hx => (hz x hx).deriv
    obtain ⟨C, hC⟩ :=
      hopen.exists_is_const_of_deriv_eq_zero hpre hdiff hderiv
    exact ⟨C, fun x hx => by
      have hxC : F x - p x = C := hC x hx
      linarith⟩
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private lemma original_add_inv_eq_auxiliary (x : ℝ) (hx : x ≠ 0) :
    originalIntegrand x + 1 / x = auxiliaryIntegrand x := by
  have hden : 1 + x + root x ≠ 0 := (original_den_pos x hx).ne'
  unfold originalIntegrand auxiliaryIntegrand
  field_simp [hx, hden]
  nlinarith [root_sq x]

private lemma hasDerivAt_auxiliaryPrimitive₂ (x : ℝ) (hx : 0 < x) :
    HasDerivAt auxiliaryPrimitive₂ (auxiliaryIntegrand x) x := by
  have hfun :
      auxiliaryPrimitive₂ =
        fun y => finalPrimitive y + Real.log y := by
    funext y
    unfold auxiliaryPrimitive₂ finalPrimitive
    ring
  rw [hfun]
  convert (hasDerivAt_final x hx.ne').add (Real.hasDerivAt_log hx.ne') using 1
  simpa [one_div] using (original_add_inv_eq_auxiliary x hx.ne').symm

private lemma auxiliaryPrimitive₁_eq_auxiliaryPrimitive₂_add (x : ℝ)
    (hx : 0 < x) :
    auxiliaryPrimitive₁ x =
      auxiliaryPrimitive₂ x + 1 / 2 * Real.log 2 := by
  have hA : 2 * x + 1 + 2 * root x ≠ 0 :=
    (first_log_arg_pos x).ne'
  have hB : 2 + x + 2 * root x ≠ 0 :=
    (second_log_arg_pos x hx.ne').ne'
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  unfold auxiliaryPrimitive₁ auxiliaryPrimitive₂
  rw [Real.log_div hB (mul_ne_zero htwo hx.ne'),
    Real.log_mul htwo hx.ne', Real.log_div hA htwo,
    Real.log_div hA (pow_ne_zero 2 hB), Real.log_pow]
  ring

private lemma hasDerivAt_auxiliaryPrimitive₁ (x : ℝ) (hx : 0 < x) :
    HasDerivAt auxiliaryPrimitive₁ (auxiliaryIntegrand x) x := by
  have heq :
      auxiliaryPrimitive₁ =ᶠ[nhds x]
        fun y => auxiliaryPrimitive₂ y + 1 / 2 * Real.log 2 := by
    filter_upwards [(show IsOpen positiveBranch from by
      unfold positiveBranch
      exact isOpen_Ioi).mem_nhds hx] with y hy
    exact auxiliaryPrimitive₁_eq_auxiliaryPrimitive₂_add y hy
  exact ((hasDerivAt_auxiliaryPrimitive₂ x hx).add_const
    (1 / 2 * Real.log 2)).congr_of_eventuallyEq heq
theorem gap13 :
    AntiderivativesOn positiveBranch auxiliaryIntegrand =
      PrimitiveFamilyOn positiveBranch auxiliaryPrimitive₁ := by
  exact antiderivatives_eq_primitive positiveBranch auxiliaryIntegrand
    auxiliaryPrimitive₁ (by
      unfold positiveBranch
      exact isOpen_Ioi) (by
      unfold positiveBranch
      exact isPreconnected_Ioi) (fun x hx =>
        hasDerivAt_auxiliaryPrimitive₁ x hx)
theorem gap14 :
    AntiderivativesOn positiveBranch auxiliaryIntegrand =
      PrimitiveFamilyOn positiveBranch auxiliaryPrimitive₂ := by
  exact antiderivatives_eq_primitive positiveBranch auxiliaryIntegrand
    auxiliaryPrimitive₂ (by
      unfold positiveBranch
      exact isOpen_Ioi) (by
      unfold positiveBranch
      exact isPreconnected_Ioi) (fun x hx =>
        hasDerivAt_auxiliaryPrimitive₂ x hx)
theorem gap15 :
    AntiderivativesOn positiveBranch originalIntegrand =
      PrimitiveFamilyOn positiveBranch finalPrimitive := by
  have hpaux : ∀ x ∈ positiveBranch,
      HasDerivAt auxiliaryPrimitive₂ (auxiliaryIntegrand x) x := by
    have hmem : auxiliaryPrimitive₂ ∈
        PrimitiveFamilyOn positiveBranch auxiliaryPrimitive₂ :=
      ⟨0, fun x _ => by simp⟩
    rw [← gap14] at hmem
    exact hmem
  have hlog : ∀ x ∈ positiveBranch,
      HasDerivAt Real.log (1 / x) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have : 0 < x := hx
      positivity
    simpa [one_div] using Real.hasDerivAt_log hx0
  have hcoef : ∀ x ∈ positiveBranch,
      originalIntegrand x = auxiliaryIntegrand x - 1 / x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have : 0 < x := hx
      positivity
    have hq : 0 < q x := by
      unfold q
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hrsq : root x ^ 2 = x ^ 2 + x + 1 := by
      unfold root q
      exact Real.sq_sqrt (by
        unfold q at hq
        exact hq.le)
    have hden : 1 + x + root x ≠ 0 := by
      intro hzero
      have hr : 0 ≤ root x := by unfold root; positivity
      apply hx0
      nlinarith
    unfold originalIntegrand auxiliaryIntegrand
    field_simp [hx0, hden]
    nlinarith
  have hfun :
      finalPrimitive = fun x => auxiliaryPrimitive₂ x - Real.log x := by
    funext x
    unfold finalPrimitive auxiliaryPrimitive₂
    ring
  have hp : ∀ x ∈ positiveBranch,
      HasDerivAt finalPrimitive (originalIntegrand x) x := by
    intro x hx
    rw [hfun]
    convert (hpaux x hx).sub (hlog x hx) using 1
    exact hcoef x hx
  ext F
  constructor
  · intro hF
    have hz : ∀ x ∈ positiveBranch,
        HasDerivAt (fun y => F y - finalPrimitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ
        (fun y => F y - finalPrimitive y) positiveBranch :=
      fun x hx => (hz x hx).differentiableAt.differentiableWithinAt
    have hderiv : positiveBranch.EqOn
        (deriv (fun y => F y - finalPrimitive y)) 0 :=
      fun x hx => (hz x hx).deriv
    obtain ⟨C, hC⟩ :=
      (show IsOpen positiveBranch from by
        unfold positiveBranch
        exact isOpen_Ioi).exists_is_const_of_deriv_eq_zero
        (show IsPreconnected positiveBranch from by
          unfold positiveBranch
          exact isPreconnected_Ioi) hdiff hderiv
    exact ⟨C, fun x hx => by
      have hxC : F x - finalPrimitive x = C := hC x hx
      linarith⟩
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => finalPrimitive y + C) := by
      filter_upwards [(show IsOpen positiveBranch from by
        unfold positiveBranch
        exact isOpen_Ioi).mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq
theorem gap16 :
    AntiderivativesOn negativeBranch originalIntegrand =
      PrimitiveFamilyOn negativeBranch finalPrimitive := by
  exact antiderivatives_eq_primitive negativeBranch originalIntegrand
    finalPrimitive (by
      unfold negativeBranch
      exact isOpen_Iio) (by
      unfold negativeBranch
      exact isPreconnected_Iio) (fun x hx =>
        hasDerivAt_final x hx.ne)

end
end ProofGap.Exercise1974
