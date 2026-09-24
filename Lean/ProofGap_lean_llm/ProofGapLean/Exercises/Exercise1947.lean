import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1947

noncomputable section

def xOf (t : ℝ) := 1 / t
def parameterBranch : Set ℝ := {t | 0 < t}
def xBranch : Set ℝ := {x | x ≠ 0}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def sourceParamIntegrand (t : ℝ) :=
  1 / (xOf t ^ 3 * Real.sqrt (xOf t ^ 2 + 1)) * deriv xOf t
def transformed₁ (t : ℝ) := t ^ 2 / Real.sqrt (t ^ 2 + 1)
def transformed₂ (t : ℝ) := (t ^ 2 + 1 - 1) / Real.sqrt (t ^ 2 + 1)
def NegativeFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn parameterBranch p,
    ∀ t ∈ parameterBranch, F t = -G t}
def AuxiliaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn parameterBranch
      (fun t => Real.sqrt (t ^ 2 + 1)),
    ∃ B ∈ AntiderivativesOn parameterBranch
      (fun t => 1 / Real.sqrt (t ^ 2 + 1)),
    ∀ t ∈ parameterBranch, F t = -A t + B t}
def parameterPrimitive (t : ℝ) :=
  -t / 2 * Real.sqrt (t ^ 2 + 1) +
    1 / 2 * Real.log |t + Real.sqrt (t ^ 2 + 1)|
def sourceXIntegrand (x : ℝ) := 1 / (x ^ 3 * Real.sqrt (x ^ 2 + 1))
def xPrimitive (x : ℝ) :=
  -Real.sqrt (x ^ 2 + 1) / (2 * x ^ 2) +
    1 / 2 * Real.log ((1 + Real.sqrt (x ^ 2 + 1)) / |x|)

private theorem parameterBranch_open : IsOpen parameterBranch := by
  simpa [parameterBranch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem parameterBranch_preconnected : IsPreconnected parameterBranch := by
  simpa [parameterBranch] using
    (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))

private theorem hasDerivAt_congr_on_open
    {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ} {x d : ℝ}
    (hx : x ∈ s) (hfg : ∀ y ∈ s, f y = g y)
    (hg : HasDerivAt g d x) : HasDerivAt f d x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy
  exact hfg y hy

private theorem constant_on_of_hasDerivAt_zero
    {u : Set ℝ} (huopen : IsOpen u) (huconn : IsPreconnected u)
    {f : ℝ → ℝ} (hf : ∀ x ∈ u, HasDerivAt f 0 x) :
    ∀ x ∈ u, ∀ y ∈ u, f x = f y := by
  have hdiff : DifferentiableOn ℝ f u := by
    intro x hx
    exact (hf x hx).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv f) 0 u := by
    intro x hx
    exact (hf x hx).deriv
  intro x hx y hy
  exact huopen.is_const_of_deriv_eq_zero huconn hdiff hzero hx hy

private theorem hasDerivAt_xOf (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt xOf (-1 / t ^ 2) t := by
  have h := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht
  simpa [xOf] using h

private theorem sqrt_xOf_eq (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (xOf t ^ 2 + 1) = Real.sqrt (t ^ 2 + 1) / t := by
  have htpos : 0 < t := ht
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hin : 0 ≤ xOf t ^ 2 + 1 := by positivity
  have hout : 0 ≤ t ^ 2 + 1 := by positivity
  have hl := Real.sqrt_nonneg (xOf t ^ 2 + 1)
  have hr : 0 ≤ Real.sqrt (t ^ 2 + 1) / t :=
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt htpos)
  have hsq :
      Real.sqrt (xOf t ^ 2 + 1) ^ 2 =
        (Real.sqrt (t ^ 2 + 1) / t) ^ 2 := by
    rw [Real.sq_sqrt hin]
    rw [div_pow, Real.sq_sqrt hout]
    simp only [xOf]
    field_simp [ht0] <;> ring
  nlinarith

private theorem sourceParam_eq_neg_transformed₁ (t : ℝ)
    (ht : t ∈ parameterBranch) :
    sourceParamIntegrand t = -transformed₁ t := by
  have htpos : 0 < t := ht
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hspos : 0 < Real.sqrt (t ^ 2 + 1) :=
    Real.sqrt_pos.2 (by positivity)
  unfold sourceParamIntegrand
  rw [(hasDerivAt_xOf t ht0).deriv, sqrt_xOf_eq t ht]
  simp only [xOf, transformed₁]
  field_simp [ht0, ne_of_gt hspos] <;> ring

private def auxiliaryLog (t : ℝ) :=
  Real.log (t + Real.sqrt (t ^ 2 + 1))

private def auxiliaryA (t : ℝ) :=
  t / 2 * Real.sqrt (t ^ 2 + 1) + 1 / 2 * auxiliaryLog t

private def auxiliaryB (t : ℝ) := auxiliaryLog t

private theorem hasDerivAt_sqrt_sq_add_one (t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 1))
      (t / Real.sqrt (t ^ 2 + 1)) t := by
  have hp : 0 < t ^ 2 + 1 := by positivity
  have hspos : 0 < Real.sqrt (t ^ 2 + 1) := Real.sqrt_pos.2 hp
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).add_const 1 using 1 <;>
      simp only [id_eq] <;> ring
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp t hinner
  convert h using 1 <;>
    field_simp [ne_of_gt hspos] <;> ring

private theorem hasDerivAt_auxiliaryB (t : ℝ)
    (ht : t ∈ parameterBranch) :
    HasDerivAt auxiliaryB (1 / Real.sqrt (t ^ 2 + 1)) t := by
  have htpos : 0 < t := ht
  have hp : 0 < t ^ 2 + 1 := by positivity
  have hspos : 0 < Real.sqrt (t ^ 2 + 1) := Real.sqrt_pos.2 hp
  have hs := hasDerivAt_sqrt_sq_add_one t
  have hg : HasDerivAt
      (fun y : ℝ => y + Real.sqrt (y ^ 2 + 1))
      (1 + t / Real.sqrt (t ^ 2 + 1)) t :=
    (hasDerivAt_id t).add hs
  have hlog := (Real.hasDerivAt_log
    (ne_of_gt (add_pos htpos hspos))).comp t hg
  change HasDerivAt
    (fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 + 1)))
    (1 / Real.sqrt (t ^ 2 + 1)) t
  convert hlog using 1 <;>
    field_simp [ne_of_gt hspos, ne_of_gt (add_pos htpos hspos)] <;>
    ring

private theorem hasDerivAt_auxiliaryA (t : ℝ)
    (ht : t ∈ parameterBranch) :
    HasDerivAt auxiliaryA (Real.sqrt (t ^ 2 + 1)) t := by
  have hp : 0 < t ^ 2 + 1 := by positivity
  have hspos : 0 < Real.sqrt (t ^ 2 + 1) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt (le_of_lt hp)
  have hs := hasDerivAt_sqrt_sq_add_one t
  have hlinear : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) t := by
    simpa only [id_eq] using (hasDerivAt_id t).div_const 2
  have hprod := hlinear.mul hs
  have hlog := (hasDerivAt_auxiliaryB t ht).const_mul (1 / 2)
  unfold auxiliaryA
  have h := hprod.add hlog
  convert h using 1
  field_simp [ne_of_gt hspos] <;> nlinarith [hsq]

private theorem parameterPrimitive_eq_auxiliaries (t : ℝ)
    (ht : t ∈ parameterBranch) :
    parameterPrimitive t = -auxiliaryA t + auxiliaryB t := by
  have htpos : 0 < t := ht
  have hsnonneg : 0 ≤ Real.sqrt (t ^ 2 + 1) := Real.sqrt_nonneg _
  have hsum : 0 < t + Real.sqrt (t ^ 2 + 1) :=
    add_pos_of_pos_of_nonneg htpos hsnonneg
  simp only [parameterPrimitive, auxiliaryA, auxiliaryB, auxiliaryLog,
    abs_of_pos hsum]
  ring

private theorem hasDerivAt_parameterPrimitive (t : ℝ)
    (ht : t ∈ parameterBranch) :
    HasDerivAt parameterPrimitive (-transformed₁ t) t := by
  have hA := (hasDerivAt_auxiliaryA t ht).neg
  have hB := hasDerivAt_auxiliaryB t ht
  have h := hA.add hB
  apply hasDerivAt_congr_on_open parameterBranch_open ht
    (fun y hy => parameterPrimitive_eq_auxiliaries y hy)
  convert h using 1
  simp only [transformed₁]
  have hp : 0 < t ^ 2 + 1 := by positivity
  have hspos : 0 < Real.sqrt (t ^ 2 + 1) := Real.sqrt_pos.2 hp
  field_simp [ne_of_gt hspos] <;>
    nlinarith [Real.sq_sqrt (le_of_lt hp)]

private theorem antiderivatives_eq_primitive_positive
    {f p : ℝ → ℝ}
    (hp : ∀ t ∈ parameterBranch, HasDerivAt p (f t) t) :
    AntiderivativesOn parameterBranch f =
      PrimitiveFamilyOn parameterBranch p := by
  ext F
  constructor
  · intro hF
    change ∀ t ∈ parameterBranch, HasDerivAt F (f t) t at hF
    change ∃ C : ℝ, ∀ t ∈ parameterBranch, F t = p t + C
    refine ⟨F 1 - p 1, ?_⟩
    have hzero : ∀ y ∈ parameterBranch,
        HasDerivAt (fun z => F z - p z) 0 y := by
      intro y hy
      simpa using (hF y hy).sub (hp y hy)
    have hconst := constant_on_of_hasDerivAt_zero
      parameterBranch_open parameterBranch_preconnected hzero
    intro t ht
    have hone : (1 : ℝ) ∈ parameterBranch := by
      change 0 < (1 : ℝ)
      norm_num
    have heq := hconst t ht 1 hone
    linarith
  · rintro ⟨C, hFC⟩
    change ∀ t ∈ parameterBranch, HasDerivAt F (f t) t
    intro t ht
    apply hasDerivAt_congr_on_open parameterBranch_open ht hFC
    exact (hp t ht).add_const C

private theorem hasDerivAt_xPrimitive (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt xPrimitive (sourceXIntegrand x) x := by
  set_option maxHeartbeats 1000000 in
    have hx0 : x ≠ 0 := hx
    have hp : 0 < x ^ 2 + 1 := by positivity
    have hspos : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 hp
    have hs0 : Real.sqrt (x ^ 2 + 1) ≠ 0 := ne_of_gt hspos
    have hsq := Real.sq_sqrt (le_of_lt hp)
    have hs := hasDerivAt_sqrt_sq_add_one x
    have hden : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul 2 using 1 <;>
        simp only [id_eq] <;> ring
    have hden0 : 2 * x ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)
    have hfirst := (hs.div hden hden0).neg
    have hfirstCoeff :
        -((x / Real.sqrt (x ^ 2 + 1) * (2 * x ^ 2) -
            Real.sqrt (x ^ 2 + 1) * (4 * x)) / (2 * x ^ 2) ^ 2) =
          Real.sqrt (x ^ 2 + 1) / x ^ 3 -
            1 / (2 * x * Real.sqrt (x ^ 2 + 1)) := by
      field_simp [hx0, hs0] <;> ring
    have hfirst' : HasDerivAt
        (fun y : ℝ => -(Real.sqrt (y ^ 2 + 1) / (2 * y ^ 2)))
        (Real.sqrt (x ^ 2 + 1) / x ^ 3 -
          1 / (2 * x * Real.sqrt (x ^ 2 + 1))) x := by
      simpa only [hfirstCoeff] using hfirst
    have hnum : HasDerivAt
        (fun y : ℝ => 1 + Real.sqrt (y ^ 2 + 1))
        (x / Real.sqrt (x ^ 2 + 1)) x := by
      simpa only [id_eq, zero_add] using
        (hasDerivAt_const x (1 : ℝ)).add hs
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · have hminus : HasDerivAt (fun y : ℝ => -y) (-1) x :=
        (hasDerivAt_id x).neg
      have hquot := hnum.div hminus (neg_ne_zero.mpr hx0)
      have hqpos : 0 <
          (1 + Real.sqrt (x ^ 2 + 1)) / (-x) :=
        div_pos (add_pos zero_lt_one hspos) (neg_pos.mpr hxneg)
      have hq0 : (1 + Real.sqrt (x ^ 2 + 1)) / (-x) ≠ 0 :=
        ne_of_gt hqpos
      have hlogBase : HasDerivAt Real.log
          (((1 + Real.sqrt (x ^ 2 + 1)) / (-x))⁻¹)
          ((1 + Real.sqrt (x ^ 2 + 1)) / (-x)) :=
        Real.hasDerivAt_log hq0
      have hlog := hlogBase.comp x hquot
      have hlogCoeff :
          ((1 + Real.sqrt (x ^ 2 + 1)) / (-x))⁻¹ *
              ((x / Real.sqrt (x ^ 2 + 1) * (-x) -
                (1 + Real.sqrt (x ^ 2 + 1)) * (-1)) / (-x) ^ 2) =
            -1 / (x * Real.sqrt (x ^ 2 + 1)) := by
        field_simp [hx0, hs0,
          ne_of_gt (add_pos zero_lt_one hspos), hq0] <;>
          nlinarith [hsq]
      have hlog' : HasDerivAt
          (fun y : ℝ => Real.log
            ((1 + Real.sqrt (y ^ 2 + 1)) / (-y)))
          (-1 / (x * Real.sqrt (x ^ 2 + 1))) x := by
        simpa only [Function.comp_apply, hlogCoeff] using hlog
      have htotal := hfirst'.add (hlog'.const_mul (1 / 2))
      have hderiv :
          (Real.sqrt (x ^ 2 + 1) / x ^ 3 -
              1 / (2 * x * Real.sqrt (x ^ 2 + 1))) +
              1 / 2 * (-1 / (x * Real.sqrt (x ^ 2 + 1))) =
            sourceXIntegrand x := by
        unfold sourceXIntegrand
        field_simp [hx0, hs0] <;> nlinarith [hsq]
      rw [hderiv] at htotal
      have hcore : HasDerivAt
          (fun y : ℝ =>
            -Real.sqrt (y ^ 2 + 1) / (2 * y ^ 2) +
              1 / 2 * Real.log
                ((1 + Real.sqrt (y ^ 2 + 1)) / (-y)))
          (sourceXIntegrand x) x := by
        simpa only [Pi.add_apply, neg_div, Function.comp_apply] using htotal
      apply hasDerivAt_congr_on_open isOpen_Iio hxneg _ hcore
      intro y hy
      have hyneg : y < 0 := hy
      simp only [xPrimitive, abs_of_neg hyneg]
    · let q : ℝ → ℝ := fun y : ℝ =>
        (1 + Real.sqrt (y ^ 2 + 1)) / y
      have hquotRaw := hnum.div (hasDerivAt_id x) hx0
      have hquot : HasDerivAt q
          ((x / Real.sqrt (x ^ 2 + 1) * x -
            (1 + Real.sqrt (x ^ 2 + 1)) * 1) / x ^ 2) x := by
        simpa only [q, Pi.div_apply, id_eq] using hquotRaw
      have hqpos : 0 < q x := by
        dsimp only [q]
        exact div_pos (add_pos zero_lt_one hspos) hxpos
      have hq0 : q x ≠ 0 := ne_of_gt hqpos
      have hlogBase : HasDerivAt Real.log ((q x)⁻¹) (q x) :=
        Real.hasDerivAt_log hq0
      have hlog : HasDerivAt (Real.log ∘ q)
          ((q x)⁻¹ *
            ((x / Real.sqrt (x ^ 2 + 1) * x -
              (1 + Real.sqrt (x ^ 2 + 1)) * 1) / x ^ 2)) x :=
        hlogBase.comp x hquot
      have hlogCoeff :
          (q x)⁻¹ *
              ((x / Real.sqrt (x ^ 2 + 1) * x -
                (1 + Real.sqrt (x ^ 2 + 1)) * 1) / x ^ 2) =
            -1 / (x * Real.sqrt (x ^ 2 + 1)) := by
        dsimp only [q]
        field_simp [hx0, hs0,
          ne_of_gt (add_pos zero_lt_one hspos), hq0] <;>
          nlinarith [hsq]
      have hlog' : HasDerivAt
          (fun y : ℝ => Real.log
            ((1 + Real.sqrt (y ^ 2 + 1)) / y))
          (-1 / (x * Real.sqrt (x ^ 2 + 1))) x := by
        simpa only [Function.comp_apply, q, hlogCoeff] using hlog
      have htotal := hfirst'.add (hlog'.const_mul (1 / 2))
      have hderiv :
          (Real.sqrt (x ^ 2 + 1) / x ^ 3 -
              1 / (2 * x * Real.sqrt (x ^ 2 + 1))) +
              1 / 2 * (-1 / (x * Real.sqrt (x ^ 2 + 1))) =
            sourceXIntegrand x := by
        unfold sourceXIntegrand
        field_simp [hx0, hs0] <;> nlinarith [hsq]
      rw [hderiv] at htotal
      have hcore : HasDerivAt
          (fun y : ℝ =>
            -Real.sqrt (y ^ 2 + 1) / (2 * y ^ 2) +
              1 / 2 * Real.log
                ((1 + Real.sqrt (y ^ 2 + 1)) / y))
          (sourceXIntegrand x) x := by
        simpa only [Pi.add_apply, neg_div, Function.comp_apply] using htotal
      apply hasDerivAt_congr_on_open isOpen_Ioi hxpos _ hcore
      intro y hy
      have hypos : 0 < y := hy
      simp only [xPrimitive, abs_of_pos hypos]

theorem gap1 (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt xOf (-1 / t ^ 2) t := by
  exact hasDerivAt_xOf t ht
theorem gap2 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (xOf t ^ 2 + 1) = Real.sqrt (t ^ 2 + 1) / t := by
  exact sqrt_xOf_eq t ht
theorem gap3 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      NegativeFamily transformed₁ := by
  ext F
  constructor
  · intro hF
    change ∀ t ∈ parameterBranch, HasDerivAt F (sourceParamIntegrand t) t at hF
    change ∃ G ∈ AntiderivativesOn parameterBranch transformed₁,
      ∀ t ∈ parameterBranch, F t = -G t
    refine ⟨fun t => -F t, ?_, ?_⟩
    · intro t ht
      have hd := (hF t ht).neg
      rw [sourceParam_eq_neg_transformed₁ t ht] at hd
      simpa using hd
    · intro t ht
      simp
  · rintro ⟨G, hG, hFG⟩
    change ∀ t ∈ parameterBranch, HasDerivAt F (sourceParamIntegrand t) t
    intro t ht
    have hneg : HasDerivAt (fun y => -G y) (sourceParamIntegrand t) t := by
      have hd := (hG t ht).neg
      rw [sourceParam_eq_neg_transformed₁ t ht]
      simpa using hd
    apply hasDerivAt_congr_on_open parameterBranch_open ht hFG hneg
theorem gap4 :
    NegativeFamily transformed₁ = NegativeFamily transformed₂ := by
  have h : transformed₁ = transformed₂ := by
    funext t
    simp only [transformed₁, transformed₂]
    ring
  rw [h]
theorem gap5 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      NegativeFamily transformed₂ := by
  rw [gap3, gap4]
theorem gap6 :
    AntiderivativesOn parameterBranch sourceParamIntegrand = AuxiliaryFamily := by
  have hsource :
      AntiderivativesOn parameterBranch sourceParamIntegrand =
        PrimitiveFamilyOn parameterBranch parameterPrimitive := by
    apply antiderivatives_eq_primitive_positive
    intro t ht
    have hd := hasDerivAt_parameterPrimitive t ht
    rw [sourceParam_eq_neg_transformed₁ t ht]
    simpa using hd
  have hA :
      AntiderivativesOn parameterBranch
          (fun t => Real.sqrt (t ^ 2 + 1)) =
        PrimitiveFamilyOn parameterBranch auxiliaryA :=
    antiderivatives_eq_primitive_positive hasDerivAt_auxiliaryA
  have hB :
      AntiderivativesOn parameterBranch
          (fun t => 1 / Real.sqrt (t ^ 2 + 1)) =
        PrimitiveFamilyOn parameterBranch auxiliaryB :=
    antiderivatives_eq_primitive_positive hasDerivAt_auxiliaryB
  rw [hsource]
  ext F
  constructor
  · rintro ⟨C, hFC⟩
    change F ∈ AuxiliaryFamily
    refine ⟨auxiliaryA, ?_, (fun t => auxiliaryB t + C), ?_, ?_⟩
    · rw [hA]
      exact ⟨0, by intro t ht; ring⟩
    · intro t ht
      exact (hasDerivAt_auxiliaryB t ht).add_const C
    · intro t ht
      rw [hFC t ht, parameterPrimitive_eq_auxiliaries t ht]
      ring
  · rintro ⟨A, hAmem, B, hBmem, hF⟩
    have hAc : A ∈ PrimitiveFamilyOn parameterBranch auxiliaryA := by
      rw [← hA]
      exact hAmem
    have hBc : B ∈ PrimitiveFamilyOn parameterBranch auxiliaryB := by
      rw [← hB]
      exact hBmem
    rcases hAc with ⟨CA, hCA⟩
    rcases hBc with ⟨CB, hCB⟩
    refine ⟨-CA + CB, ?_⟩
    intro t ht
    rw [hF t ht, hCA t ht, hCB t ht,
      parameterPrimitive_eq_auxiliaries t ht]
    ring
theorem gap7 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      PrimitiveFamilyOn parameterBranch parameterPrimitive := by
  apply antiderivatives_eq_primitive_positive
  intro t ht
  have hd := hasDerivAt_parameterPrimitive t ht
  rw [sourceParam_eq_neg_transformed₁ t ht]
  simpa using hd
theorem gap8 :
    AntiderivativesOn xBranch sourceXIntegrand =
      BranchwisePrimitiveFamilyOn xBranch xPrimitive := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ xBranch, HasDerivAt F (sourceXIntegrand x) x at hF
    change ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ xBranch →
      ∃ C : ℝ, ∀ x ∈ u, F x = xPrimitive x + C
    intro u huopen huconn husub
    by_cases hnonempty : u.Nonempty
    · rcases hnonempty with ⟨a, ha⟩
      refine ⟨F a - xPrimitive a, ?_⟩
      have hzero : ∀ y ∈ u,
          HasDerivAt (fun z => F z - xPrimitive z) 0 y := by
        intro y hy
        have hybranch := husub hy
        simpa using (hF y hybranch).sub (hasDerivAt_xPrimitive y hybranch)
      have hconst :=
        constant_on_of_hasDerivAt_zero huopen huconn hzero
      intro x hx
      have heq := hconst x hx a ha
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hnonempty ⟨x, hx⟩).elim
  · intro hF
    change ∀ x ∈ xBranch, HasDerivAt F (sourceXIntegrand x) x
    intro x hx
    have hx0 : x ≠ 0 := hx
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · have hsubset : Set.Iio (0 : ℝ) ⊆ xBranch := by
        intro y hy
        exact ne_of_lt hy
      rcases hF (Set.Iio 0) isOpen_Iio isPreconnected_Iio hsubset with
        ⟨C, hC⟩
      apply hasDerivAt_congr_on_open isOpen_Iio hxneg hC
      exact (hasDerivAt_xPrimitive x hx).add_const C
    · have hsubset : Set.Ioi (0 : ℝ) ⊆ xBranch := by
        intro y hy
        exact ne_of_gt hy
      rcases hF (Set.Ioi 0) isOpen_Ioi isPreconnected_Ioi hsubset with
        ⟨C, hC⟩
      apply hasDerivAt_congr_on_open isOpen_Ioi hxpos hC
      exact (hasDerivAt_xPrimitive x hx).add_const C

end
end ProofGap.Exercise1947
