import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2144_1

noncomputable section

def branch : Set ℝ := Set.Ioi 1
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def t (x : ℝ) := Real.sqrt (x ^ 2 + 1)
def integrand (x : ℝ) :=
  x * Real.sqrt (x ^ 2 + 1) * Real.log (Real.sqrt (x ^ 2 - 1))
def InitialSubstitutionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x ∈ branch,
      HasDerivAt G
        (Real.log (Real.sqrt (x ^ 2 - 1)) *
          deriv (fun y : ℝ => t y ^ 3) x) x) ∧
    ∀ x ∈ branch, F x = 1 / 3 * G x}
def residualIntegrand (x : ℝ) :=
  t x ^ 3 * x / (x ^ 2 - 1)
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residualIntegrand,
    ∀ x ∈ branch,
      F x = 1 / 3 * t x ^ 3 * Real.log (Real.sqrt (x ^ 2 - 1)) -
        1 / 3 * G x}
def NegativeResidualFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residualIntegrand,
    ∀ x ∈ branch, F x = -1 / 3 * G x}
def parameterPullback (x : ℝ) :=
  t x ^ 4 / (t x ^ 2 - 2) * deriv t x
def ParameterFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn parameterPullback,
    ∀ x ∈ branch, F x = -1 / 3 * G x}
def expandedParameterPullback (x : ℝ) :=
  (t x ^ 2 + 2 + 4 / (t x ^ 2 - 2)) * deriv t x
def ExpandedParameterFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn expandedParameterPullback,
    ∀ x ∈ branch, F x = -1 / 3 * G x}
def residualPrimitiveT (x : ℝ) :=
  -1 / 9 * t x ^ 3 - 2 / 3 * t x -
    Real.sqrt 2 / 3 *
      Real.log |(t x - Real.sqrt 2) / (t x + Real.sqrt 2)|
def residualPrimitiveX (x : ℝ) :=
  -(x ^ 2 + 7) / 9 * Real.sqrt (1 + x ^ 2) -
    Real.sqrt 2 / 3 *
      Real.log
        ((Real.sqrt (1 + x ^ 2) - Real.sqrt 2) /
          (Real.sqrt (1 + x ^ 2) + Real.sqrt 2))
def primitive (x : ℝ) :=
  1 / 3 * t x ^ 3 * Real.log (Real.sqrt (x ^ 2 - 1)) +
    residualPrimitiveX x

private theorem hasDerivAt_t (x : ℝ) : HasDerivAt t (x / t x) x := by
  have hpos : 0 < x ^ 2 + 1 := by positivity
  have hi : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
    simpa [pow_two] using ((hasDerivAt_id x).pow 2).add_const 1
  have hs0 := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hi
  convert hs0 using 1
  have hn : Real.sqrt (x ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  unfold t
  field_simp [hn]

private theorem hasDerivAt_log_sqrt_sq_sub_one
    (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.log (Real.sqrt (y ^ 2 - 1)))
      (x / (x ^ 2 - 1)) x := by
  have hx' : 1 < x := by simpa [branch] using hx
  have hu : 0 < x ^ 2 - 1 := by nlinarith
  have hi : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    simpa [pow_two] using ((hasDerivAt_id x).pow 2).sub_const 1
  have hs0 := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hi
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
      (x / Real.sqrt (x ^ 2 - 1)) x := by
    convert hs0 using 1
    have hn : Real.sqrt (x ^ 2 - 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hu)
    field_simp [hn]
  have hl0 :=
    (Real.hasDerivAt_log (ne_of_gt (Real.sqrt_pos.2 hu))).comp x hs
  have hsquare : (Real.sqrt (x ^ 2 - 1)) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hu)
  have hn : Real.sqrt (x ^ 2 - 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu)
  have hcoef :
      (Real.sqrt (x ^ 2 - 1))⁻¹ *
          (x / Real.sqrt (x ^ 2 - 1)) = x / (x ^ 2 - 1) := by
    calc
      (Real.sqrt (x ^ 2 - 1))⁻¹ *
            (x / Real.sqrt (x ^ 2 - 1)) =
          x / (Real.sqrt (x ^ 2 - 1)) ^ 2 := by
        field_simp [hn]
      _ = x / (x ^ 2 - 1) := by rw [hsquare]
  simpa only [Function.comp_apply, hcoef] using hl0

private theorem hasDerivAt_parts_product
    (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt
      (fun y : ℝ =>
        1 / 3 * t y ^ 3 * Real.log (Real.sqrt (y ^ 2 - 1)))
      (integrand x + 1 / 3 * residualIntegrand x) x := by
  have hx' : 1 < x := by simpa [branch] using hx
  have hu : 0 < x ^ 2 - 1 := by nlinarith
  have ht := hasDerivAt_t x
  have hl := hasDerivAt_log_sqrt_sq_sub_one x hx
  have hP0 := ((ht.pow 3).const_mul (1 / 3)).mul hl
  simp only [Pi.pow_apply] at hP0
  convert hP0 using 1
  have ht0 : t x ≠ 0 := by
    unfold t
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  unfold integrand residualIntegrand t
  field_simp [ht0, ne_of_gt hu] <;> ring

private theorem antiderivativesOn_eq_primitive_of_deriv
    (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 2 - p 2, ?_⟩
    intro x hx
    have hd : DifferentiableOn ℝ (fun y => F y - p y) (Set.Ioi 1) := by
      intro y hy
      have hy' : y ∈ branch := by simpa [branch] using hy
      exact ((hF y hy').sub (hp y hy')).differentiableAt.differentiableWithinAt
    have hz : ∀ y ∈ Set.Ioi (1 : ℝ), deriv (fun z => F z - p z) y = 0 := by
      intro y hy
      have hy' : y ∈ branch := by simpa [branch] using hy
      simpa using ((hF y hy').sub (hp y hy')).deriv
    have hc : F x - p x = F 2 - p 2 := by
      exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hd hz
        (by simpa [branch] using hx) (by norm_num)
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    have hs := (hp x hx).add_const C
    have hnb : Set.Ioi (1 : ℝ) ∈ nhds x :=
      isOpen_Ioi.mem_nhds (by simpa [branch] using hx)
    have hev : (fun y => p y + C) =ᶠ[nhds x] F :=
      Filter.mem_of_superset hnb
        (fun y hy => (hF y (by simpa [branch] using hy)).symm)
    exact hs.congr_of_eventuallyEq hev.symm

theorem gap1 :
    AntiderivativesOn integrand = InitialSubstitutionFamily := by
  ext F
  simp only [AntiderivativesOn, InitialSubstitutionFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 3 * F y, ?_, ?_⟩
    · intro x hx
      have ht3 : HasDerivAt (fun y : ℝ => t y ^ 3)
          (3 * t x ^ 2 * (x / t x)) x := by
        simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub] using
          ((hasDerivAt_t x).pow 3)
      have hid :
          Real.log (Real.sqrt (x ^ 2 - 1)) *
              deriv (fun y : ℝ => t y ^ 3) x =
            3 * integrand x := by
        rw [ht3.deriv]
        have ht0 : t x ≠ 0 := by
          unfold t
          exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
        unfold integrand t
        field_simp [ht0] <;> ring
      have hs := (hF x hx).const_mul 3
      rw [← hid] at hs
      exact hs
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have ht3 : HasDerivAt (fun y : ℝ => t y ^ 3)
        (3 * t x ^ 2 * (x / t x)) x := by
      simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub] using
        ((hasDerivAt_t x).pow 3)
    have hid :
        Real.log (Real.sqrt (x ^ 2 - 1)) *
              deriv (fun y : ℝ => t y ^ 3) x =
          3 * integrand x := by
      rw [ht3.deriv]
      have ht0 : t x ≠ 0 := by
        unfold t
        exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
      unfold integrand t
      field_simp [ht0] <;> ring
    have hs := (hG x hx).const_mul (1 / 3)
    have hcoef :
        1 / 3 *
            (Real.log (Real.sqrt (x ^ 2 - 1)) *
              deriv (fun y : ℝ => t y ^ 3) x) = integrand x := by
      rw [hid]
      ring
    rw [hcoef] at hs
    have hnb : Set.Ioi (1 : ℝ) ∈ nhds x :=
      isOpen_Ioi.mem_nhds (by simpa [branch] using hx)
    have hev : (fun y => 1 / 3 * G y) =ᶠ[nhds x] F :=
      Filter.mem_of_superset hnb
        (fun y hy => (hFG y (by simpa [branch] using hy)).symm)
    exact hs.congr_of_eventuallyEq hev.symm
theorem gap2 :
    AntiderivativesOn integrand = ByPartsFamily := by
  ext F
  simp only [AntiderivativesOn, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 3 *
        (1 / 3 * t y ^ 3 * Real.log (Real.sqrt (y ^ 2 - 1)) - F y), ?_, ?_⟩
    · intro x hx
      have hP := hasDerivAt_parts_product x hx
      convert (hP.sub (hF x hx)).const_mul 3 using 1
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hP := hasDerivAt_parts_product x hx
    have hcandidate := hP.sub ((hG x hx).const_mul (1 / 3))
    have hcandidate' : HasDerivAt
        (fun y => 1 / 3 * t y ^ 3 * Real.log (Real.sqrt (y ^ 2 - 1)) -
          1 / 3 * G y) (integrand x) x := by
      convert hcandidate using 1
      ring
    have hnb : Set.Ioi (1 : ℝ) ∈ nhds x :=
      isOpen_Ioi.mem_nhds (by simpa [branch] using hx)
    have hev :
        (fun y => 1 / 3 * t y ^ 3 * Real.log (Real.sqrt (y ^ 2 - 1)) -
          1 / 3 * G y) =ᶠ[nhds x] F :=
      Filter.mem_of_superset hnb
        (fun y hy => (hFG y (by simpa [branch] using hy)).symm)
    exact hcandidate'.congr_of_eventuallyEq hev.symm
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    x ^ 2 + 1 = t x ^ 2 := by
  unfold t
  exact (Real.sq_sqrt (by positivity : 0 ≤ x ^ 2 + 1)).symm
theorem gap4 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt t (x / t x) x ∧ x = t x * deriv t x := by
  have ht := hasDerivAt_t x
  refine ⟨ht, ?_⟩
  rw [ht.deriv]
  have ht0 : t x ≠ 0 := by
    unfold t
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp [ht0]
theorem gap5 :
    NegativeResidualFamily = ParameterFamily := by
  ext F
  simp only [NegativeResidualFamily, ParameterFamily, Set.mem_setOf_eq]
  have heq : ∀ x ∈ branch, residualIntegrand x = parameterPullback x := by
    intro x hx
    have hd : x ^ 2 - 1 = t x ^ 2 - 2 := by
      nlinarith [gap3 x hx]
    have hxder : x = t x * deriv t x := (gap4 x hx).2
    have hnum : t x ^ 3 * x = t x ^ 4 * deriv t x := by
      calc
        t x ^ 3 * x = t x ^ 3 * (t x * deriv t x) :=
          congrArg (fun z : ℝ => t x ^ 3 * z) hxder
        _ = t x ^ 4 * deriv t x := by ring
    unfold residualIntegrand parameterPullback
    rw [hd]
    calc
      t x ^ 3 * x / (t x ^ 2 - 2) =
          (t x ^ 4 * deriv t x) / (t x ^ 2 - 2) :=
        congrArg (fun z : ℝ => z / (t x ^ 2 - 2)) hnum
      _ = t x ^ 4 / (t x ^ 2 - 2) * deriv t x := by ring
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    simpa only [heq x hx] using hG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    simpa only [← heq x hx] using hG x hx
theorem gap6 :
    ParameterFamily = ExpandedParameterFamily := by
  ext F
  simp only [ParameterFamily, ExpandedParameterFamily, Set.mem_setOf_eq]
  have heq : ∀ x ∈ branch,
      parameterPullback x = expandedParameterPullback x := by
    intro x hx
    have hx' : 1 < x := by simpa [branch] using hx
    have hd : t x ^ 2 - 2 ≠ 0 := by
      have hsq := gap3 x hx
      nlinarith
    unfold parameterPullback expandedParameterPullback
    field_simp [hd] <;> ring
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    simpa only [heq x hx] using hG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    simpa only [← heq x hx] using hG x hx
theorem gap7 :
    NegativeResidualFamily = ExpandedParameterFamily := by
  exact gap5.trans gap6
theorem gap8 :
    NegativeResidualFamily = PrimitiveFamily residualPrimitiveT := by
  let q : ℝ → ℝ := fun x => -1 / 3 * expandedParameterPullback x
  have hp : ∀ x ∈ branch, HasDerivAt residualPrimitiveT (q x) x := by
    intro x hx
    have hx' : 1 < x := by simpa [branch] using hx
    have ht := (gap4 x hx).1
    have htpos : 0 < t x := by
      unfold t
      exact Real.sqrt_pos.2 (by positivity)
    have ha0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have ha2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have htx2 := gap3 x hx
    have hlt : Real.sqrt 2 < t x := by
      nlinarith
    have hplus : t x + Real.sqrt 2 ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg htpos ha0)
    have hminus : t x - Real.sqrt 2 ≠ 0 :=
      ne_of_gt (sub_pos.mpr hlt)
    have hratio : 0 < (t x - Real.sqrt 2) / (t x + Real.sqrt 2) :=
      div_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg htpos ha0)
    have hratio0 : (t x - Real.sqrt 2) / (t x + Real.sqrt 2) ≠ 0 :=
      ne_of_gt hratio
    have hden : t x ^ 2 - 2 ≠ 0 := by nlinarith
    have hr := (ht.sub_const (Real.sqrt 2)).div
      (ht.add_const (Real.sqrt 2)) hplus
    have habs := (hasDerivAt_abs hratio0).comp x hr
    have hlog :=
      (Real.hasDerivAt_log (abs_ne_zero.mpr hratio0)).comp x habs
    simp [hratio] at hlog
    have habsx :
        |(t x - Real.sqrt 2) / (t x + Real.sqrt 2)| =
          (t x - Real.sqrt 2) / (t x + Real.sqrt 2) :=
      abs_of_pos hratio
    have hlog' : HasDerivAt
        (fun y : ℝ => Real.log
          |(t y - Real.sqrt 2) / (t y + Real.sqrt 2)|)
        (((t x - Real.sqrt 2) / (t x + Real.sqrt 2))⁻¹ *
          ((x / t x * (t x + Real.sqrt 2) -
              (t x - Real.sqrt 2) * (x / t x)) /
            (t x + Real.sqrt 2) ^ 2)) x := by
      simpa only [Function.comp_apply, Pi.div_apply, habsx] using hlog
    have hcalc := (((ht.pow 3).const_mul (-1 / 9)).sub
      (ht.const_mul (2 / 3))).sub
      (hlog'.const_mul (Real.sqrt 2 / 3))
    have hcalc' : HasDerivAt residualPrimitiveT
        (-1 / 9 * (3 * t x ^ 2 * (x / t x)) -
          2 / 3 * (x / t x) -
          Real.sqrt 2 / 3 *
            (((t x - Real.sqrt 2) / (t x + Real.sqrt 2))⁻¹ *
              ((x / t x * (t x + Real.sqrt 2) -
                  (t x - Real.sqrt 2) * (x / t x)) /
                (t x + Real.sqrt 2) ^ 2))) x := by
      simpa only [residualPrimitiveT, Pi.pow_apply, Pi.sub_apply,
        Nat.cast_ofNat, Nat.reduceSub] using hcalc
    have hcoef :
        -1 / 9 * (3 * t x ^ 2 * (x / t x)) -
            2 / 3 * (x / t x) -
            Real.sqrt 2 / 3 *
              (((t x - Real.sqrt 2) / (t x + Real.sqrt 2))⁻¹ *
                ((x / t x * (t x + Real.sqrt 2) -
                    (t x - Real.sqrt 2) * (x / t x)) /
                  (t x + Real.sqrt 2) ^ 2)) = q x := by
      dsimp [q]
      unfold expandedParameterPullback
      rw [ht.deriv]
      field_simp [htpos.ne', hplus, hminus, hden, hratio0]
      ring_nf
      norm_num [ha2]
      ring
    rw [hcoef] at hcalc'
    exact hcalc'
  have hscale : ExpandedParameterFamily = AntiderivativesOn q := by
    ext F
    simp only [ExpandedParameterFamily, AntiderivativesOn, Set.mem_setOf_eq]
    constructor
    · rintro ⟨G, hG, hFG⟩
      intro x hx
      have hs : HasDerivAt (fun y => -1 / 3 * G y) (q x) x := by
        simpa [q] using (hG x hx).const_mul (-1 / 3)
      have hnb : Set.Ioi (1 : ℝ) ∈ nhds x :=
        isOpen_Ioi.mem_nhds (by simpa [branch] using hx)
      have hev : (fun y => -1 / 3 * G y) =ᶠ[nhds x] F :=
        Filter.mem_of_superset hnb
          (fun y hy => (hFG y (by simpa [branch] using hy)).symm)
      exact hs.congr_of_eventuallyEq hev.symm
    · intro hF
      refine ⟨fun y => -3 * F y, ?_, ?_⟩
      · intro x hx
        convert (hF x hx).const_mul (-3) using 1
        dsimp [q]
        ring
      · intro x hx
        ring
  calc
    NegativeResidualFamily = ExpandedParameterFamily := gap7
    _ = AntiderivativesOn q := hscale
    _ = PrimitiveFamily residualPrimitiveT :=
      antiderivativesOn_eq_primitive_of_deriv q residualPrimitiveT hp
theorem gap9 :
    PrimitiveFamily residualPrimitiveT =
      PrimitiveFamily residualPrimitiveX := by
  have hpoint : ∀ x ∈ branch, residualPrimitiveT x = residualPrimitiveX x := by
    intro x hx
    have hx' : 1 < x := by simpa [branch] using hx
    have hnon : 0 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have ht : t x = Real.sqrt (1 + x ^ 2) := by
      unfold t
      congr 1
      ring
    have hs : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt hnon
    have htpos : 0 < t x := by
      unfold t
      exact Real.sqrt_pos.2 (by positivity)
    have ha0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hlt : Real.sqrt 2 < t x := by
      have hsq := gap3 x hx
      have ha2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have ht0 : 0 ≤ t x := le_of_lt htpos
      nlinarith
    have hdenpos : 0 < t x + Real.sqrt 2 :=
      add_pos_of_pos_of_nonneg htpos ha0
    have hratio : 0 < (t x - Real.sqrt 2) / (t x + Real.sqrt 2) :=
      div_pos (sub_pos.mpr hlt) hdenpos
    have hpoly :
        -1 / 9 * t x ^ 3 - 2 / 3 * t x =
          -(x ^ 2 + 7) / 9 * Real.sqrt (1 + x ^ 2) := by
      rw [ht]
      calc
        -1 / 9 * Real.sqrt (1 + x ^ 2) ^ 3 -
              2 / 3 * Real.sqrt (1 + x ^ 2) =
            -((Real.sqrt (1 + x ^ 2)) ^ 2 + 6) / 9 *
              Real.sqrt (1 + x ^ 2) := by ring
        _ = -(x ^ 2 + 7) / 9 * Real.sqrt (1 + x ^ 2) := by
          rw [hs]
          ring
    unfold residualPrimitiveT residualPrimitiveX
    rw [hpoly, abs_of_pos hratio, ht]
  ext F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, hpoint x hx]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, hpoint x hx]
theorem gap10 :
    NegativeResidualFamily = PrimitiveFamily residualPrimitiveX := by
  exact gap8.trans gap9
theorem gap11 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap2]
  ext F
  simp only [ByPartsFamily, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hneg : (fun y => -1 / 3 * G y) ∈ NegativeResidualFamily :=
      ⟨G, hG, fun x hx => rfl⟩
    have hprim : (fun y => -1 / 3 * G y) ∈
        PrimitiveFamily residualPrimitiveX := by
      rw [← gap10]
      exact hneg
    rcases hprim with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hc : -1 / 3 * G x = residualPrimitiveX x + C := by
      simpa using hC x hx
    rw [hFG x hx]
    unfold primitive
    calc
      1 / 3 * t x ^ 3 * Real.log (Real.sqrt (x ^ 2 - 1)) -
            1 / 3 * G x =
          1 / 3 * t x ^ 3 * Real.log (Real.sqrt (x ^ 2 - 1)) +
            (-1 / 3 * G x) := by ring
      _ = 1 / 3 * t x ^ 3 * Real.log (Real.sqrt (x ^ 2 - 1)) +
            (residualPrimitiveX x + C) := by rw [hc]
      _ = 1 / 3 * t x ^ 3 * Real.log (Real.sqrt (x ^ 2 - 1)) +
            residualPrimitiveX x + C := by ring
  · rintro ⟨C, hF⟩
    have hprim : (fun y => residualPrimitiveX y + C) ∈
        PrimitiveFamily residualPrimitiveX := ⟨C, fun x hx => rfl⟩
    have hneg : (fun y => residualPrimitiveX y + C) ∈
        NegativeResidualFamily := by
      rw [gap10]
      exact hprim
    rcases hneg with ⟨G, hG, hGform⟩
    refine ⟨G, hG, ?_⟩
    intro x hx
    rw [hF x hx]
    have heq := hGform x hx
    unfold primitive
    linarith

end
end ProofGap.Exercise2144_1
