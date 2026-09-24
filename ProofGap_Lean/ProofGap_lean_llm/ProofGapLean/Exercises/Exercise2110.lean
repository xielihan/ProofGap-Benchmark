import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2110
noncomputable section

def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Ioo 0 1 ∨ U = Set.Ioi 1
def phase (x : ℝ) :=
  Real.arcsin (2 * Real.sqrt x / (1 + x))
def integrand (x : ℝ) := phase x
def reciprocalSqrt (x : ℝ) := 1 / Real.sqrt x
def primitive (x : ℝ) :=
  (x + 1) * phase x - 2 * Real.sqrt x * SignType.sign (1 - x)
def rawDerivative (x : ℝ) :=
  ((1 / (1 + x) ^ 2) * ((1 + x) / Real.sqrt x - 2 * Real.sqrt x)) /
    Real.sqrt (1 - 4 * x / (1 + x) ^ 2)
def middleDerivative (x : ℝ) :=
  1 / (1 + x) * ((1 - x) / (Real.sqrt ((1 - x) ^ 2) * Real.sqrt x))
def simplifiedDerivative (x : ℝ) :=
  1 / (1 + x) * SignType.sign (1 - x) * (1 / Real.sqrt x)

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def ShiftDifferentialFamily (U : Set ℝ) :=
  Family U (fun x => phase x * deriv (fun y : ℝ => y + 1) x)
def ByPartsFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U reciprocalSqrt, ∀ x ∈ U,
    F x = (x + 1) * phase x - SignType.sign (1 - x) * A x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem branch_point_data {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : 0 < x ∧ x ≠ 1 := by
  rcases hU with rfl | rfl
  · exact ⟨hx.1, ne_of_lt hx.2⟩
  · exact ⟨lt_trans zero_lt_one hx, ne_of_gt hx⟩

private theorem coe_sign_of_pos {x : ℝ} (hx : 0 < x) :
    (SignType.sign x : ℝ) = 1 := by
  simp [SignType.sign, hx]

private theorem coe_sign_of_neg {x : ℝ} (hx : x < 0) :
    (SignType.sign x : ℝ) = -1 := by
  have hnx : ¬ 0 < x := not_lt_of_ge (le_of_lt hx)
  simp [SignType.sign, hnx, hx]

private theorem phase_argument_mem {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    2 * Real.sqrt x / (1 + x) ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hs1 : Real.sqrt x ≠ 1 := by
    intro h
    apply hx1
    nlinarith
  have hd : 0 < 1 + x := by linarith
  have hsq : 0 < (Real.sqrt x - 1) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hs1)
  constructor
  · have hq : 0 < 2 * Real.sqrt x / (1 + x) :=
      div_pos (mul_pos (by norm_num) hs) hd
    linarith
  · rw [div_lt_iff₀ hd]
    nlinarith

private theorem phase_hasDeriv_raw {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt phase (rawDerivative x) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hd : 0 < 1 + x := by linarith
  have hdx : x + 1 ≠ 0 := by linarith
  have hq0 :=
    ((Real.hasDerivAt_sqrt (ne_of_gt hx)).const_mul 2).div
      ((hasDerivAt_id x).add_const 1) hdx
  have hq0' : HasDerivAt (fun y : ℝ => 2 * Real.sqrt y / (y + 1))
      ((2 * (1 / (2 * Real.sqrt x)) * (x + 1) - 2 * Real.sqrt x) /
        (x + 1) ^ 2) x := by
    simpa only [id_eq, mul_one] using hq0
  have hderiv :
      (2 * (1 / (2 * Real.sqrt x)) * (x + 1) - 2 * Real.sqrt x) /
          (x + 1) ^ 2 =
        (1 / (1 + x) ^ 2) *
          ((1 + x) / Real.sqrt x - 2 * Real.sqrt x) := by
    field_simp [ne_of_gt hs, hdx, ne_of_gt hd]
    ring
  rw [hderiv] at hq0'
  have hq : HasDerivAt (fun y : ℝ => 2 * Real.sqrt y / (1 + y))
      ((1 / (1 + x) ^ 2) * ((1 + x) / Real.sqrt x - 2 * Real.sqrt x)) x := by
    simpa [add_comm] using hq0'
  have hm := phase_argument_mem hx hx1
  have hqm1 : 2 * Real.sqrt x / (1 + x) ≠ -1 := ne_of_gt hm.1
  have hq1 : 2 * Real.sqrt x / (1 + x) ≠ 1 := ne_of_lt hm.2
  have ha := Real.hasDerivAt_arcsin hqm1 hq1
  have hc := ha.comp x hq
  have hrad :
      1 - (2 * Real.sqrt x / (1 + x)) ^ 2 =
        1 - 4 * x / (1 + x) ^ 2 := by
    field_simp [ne_of_gt hd]
    nlinarith
  have hcoef :
      (1 / Real.sqrt (1 - (2 * Real.sqrt x / (1 + x)) ^ 2)) *
          ((1 / (1 + x) ^ 2) *
            ((1 + x) / Real.sqrt x - 2 * Real.sqrt x)) =
        rawDerivative x := by
    rw [hrad]
    unfold rawDerivative
    ring
  rw [hcoef] at hc
  simpa [phase, Function.comp_def] using hc

private theorem raw_eq_middle {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    rawDerivative x = middleDerivative x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hd : 0 < 1 + x := by linarith
  have ha : |1 - x| ≠ 0 := by
    rw [abs_ne_zero]
    exact sub_ne_zero.mpr hx1.symm
  have hrad :
      1 - 4 * x / (1 + x) ^ 2 = ((1 - x) / (1 + x)) ^ 2 := by
    field_simp [ne_of_gt hd]
    ring
  have hsrad :
      Real.sqrt (1 - 4 * x / (1 + x) ^ 2) = |1 - x| / (1 + x) := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hd]
  have hsquare : Real.sqrt ((1 - x) ^ 2) = |1 - x| :=
    Real.sqrt_sq_eq_abs (1 - x)
  unfold rawDerivative middleDerivative
  rw [hsrad, hsquare]
  field_simp [ne_of_gt hs, ne_of_gt hd, ha]
  nlinarith [hs2]

private theorem middle_eq_simplified_of_lt {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    middleDerivative x = simplifiedDerivative x := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hne : 1 - x ≠ 0 := ne_of_gt hpos
  unfold middleDerivative simplifiedDerivative
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hpos, coe_sign_of_pos hpos]
  field_simp [hs, hne] <;> ring

private theorem middle_eq_simplified_of_gt {x : ℝ} (hx : 1 < x) :
    middleDerivative x = simplifiedDerivative x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx0)
  have hneg : 1 - x < 0 := sub_neg.mpr hx
  have hne : 1 - x ≠ 0 := ne_of_lt hneg
  unfold middleDerivative simplifiedDerivative
  rw [Real.sqrt_sq_eq_abs, abs_of_neg hneg, coe_sign_of_neg hneg]
  field_simp [hs, hne] <;> ring

private theorem phase_hasDeriv_simplified {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : HasDerivAt phase (simplifiedDerivative x) x := by
  obtain ⟨hx0, hx1⟩ := branch_point_data hU hx
  have hraw := phase_hasDeriv_raw hx0 hx1
  rw [raw_eq_middle hx0 hx1] at hraw
  rcases hU with rfl | rfl
  · rw [middle_eq_simplified_of_lt hx.1 hx.2] at hraw
    exact hraw
  · rw [middle_eq_simplified_of_gt hx] at hraw
    exact hraw

private theorem hasDerivAt_of_eqOn_open {U : Set ℝ} (hU : IsOpen U)
    {F G : ℝ → ℝ} {x d : ℝ} (hx : x ∈ U)
    (hFG : ∀ y ∈ U, F y = G y) (hG : HasDerivAt G d x) :
    HasDerivAt F d x := by
  have heq : F =ᶠ[nhds x] G := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hFG y hy
  exact hG.congr_of_eventuallyEq heq

private theorem primitive_hasDeriv {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : HasDerivAt primitive (integrand x) x := by
  have hsqrt : HasDerivAt (fun y : ℝ => 2 * Real.sqrt y)
      (1 / Real.sqrt x) x := by
    have hx0 := (branch_point_data hU hx).1
    convert (Real.hasDerivAt_sqrt (ne_of_gt hx0)).const_mul 2 using 1 <;>
      field_simp [ne_of_gt (Real.sqrt_pos.2 hx0)] <;> ring
  have hphase := phase_hasDeriv_simplified hU hx
  rcases hU with rfl | rfl
  · have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hd : 1 + x ≠ 0 := by linarith
    have hcalc : HasDerivAt
        (fun y : ℝ => (y + 1) * phase y - 2 * Real.sqrt y) (phase x) x := by
      convert (((hasDerivAt_id x).add_const 1).mul hphase).sub hsqrt using 1 <;>
        simp [simplifiedDerivative, coe_sign_of_pos (sub_pos.mpr hx1)] <;>
        field_simp [hd, ne_of_gt (Real.sqrt_pos.2 hx0)] <;> ring
    apply hasDerivAt_of_eqOn_open isOpen_Ioo hx _ hcalc
    intro y hy
    unfold primitive
    rw [coe_sign_of_pos (sub_pos.mpr hy.2)]
    ring
  · have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hd : 1 + x ≠ 0 := by linarith
    have hcalc : HasDerivAt
        (fun y : ℝ => (y + 1) * phase y + 2 * Real.sqrt y) (phase x) x := by
      convert (((hasDerivAt_id x).add_const 1).mul hphase).add hsqrt using 1 <;>
        simp [simplifiedDerivative, coe_sign_of_neg (sub_neg.mpr hx)] <;>
        field_simp [hd, ne_of_gt (Real.sqrt_pos.2 hx0)] <;> ring
    apply hasDerivAt_of_eqOn_open isOpen_Ioi hx _ hcalc
    intro y hy
    unfold primitive
    rw [coe_sign_of_neg (sub_neg.mpr hy)]
    ring

private theorem family_eq_translates_on_open {U : Set ℝ} (hopen : IsOpen U)
    (hconn : IsPreconnected U) (b : ℝ) (hb : b ∈ U)
    {f p : ℝ → ℝ} (hp : ∀ x ∈ U, HasDerivAt p (f x) x) :
    Family U f = Translates U p := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hz : ∀ x ∈ U, HasDerivAt (fun y : ℝ => F y - p y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => F y - p y) U := by
      intro x hx
      exact (hz x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ U, deriv (fun y : ℝ => F y - p y) x = 0 := by
      intro x hx
      exact (hz x hx).deriv
    refine ⟨F b - p b, ?_⟩
    intro x hx
    have hc := hopen.is_const_of_deriv_eq_zero hconn hdiff hderiv hx hb
    linarith
  · rintro ⟨C, hC⟩ x hx
    apply hasDerivAt_of_eqOn_open hopen hx hC
    exact (hp x hx).add_const C

private theorem family_eq_translates_of_admissible {U : Set ℝ}
    (hU : AdmissibleBranch U) {f p : ℝ → ℝ}
    (hp : ∀ x ∈ U, HasDerivAt p (f x) x) :
    Family U f = Translates U p := by
  rcases hU with rfl | rfl
  · apply family_eq_translates_on_open isOpen_Ioo isPreconnected_Ioo (1 / 2 : ℝ)
      (by norm_num) hp
  · apply family_eq_translates_on_open isOpen_Ioi isPreconnected_Ioi 2
      (by norm_num) hp

private theorem family_phase_eq_translates (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  apply family_eq_translates_of_admissible hU
  intro x hx
  exact primitive_hasDeriv hU hx

private theorem sqrt_primitive_hasDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => 2 * Real.sqrt y) (reciprocalSqrt x) x := by
  unfold reciprocalSqrt
  convert (Real.hasDerivAt_sqrt (ne_of_gt hx)).const_mul 2 using 1 <;>
    field_simp [ne_of_gt (Real.sqrt_pos.2 hx)] <;> ring

private theorem family_reciprocal_eq_translates (U : Set ℝ)
    (hU : AdmissibleBranch U) :
    Family U reciprocalSqrt = Translates U (fun x : ℝ => 2 * Real.sqrt x) := by
  apply family_eq_translates_of_admissible hU
  intro x hx
  exact sqrt_primitive_hasDeriv (branch_point_data hU hx).1

private theorem byparts_eq_translates (U : Set ℝ) (hU : AdmissibleBranch U) :
    ByPartsFamily U = Translates U primitive := by
  rcases hU with rfl | rfl
  · apply Set.ext
    intro F
    simp only [ByPartsFamily, Translates, Set.mem_setOf_eq]
    constructor
    · rintro ⟨A, hA, hFA⟩
      rw [family_reciprocal_eq_translates (Set.Ioo 0 1) (Or.inl rfl)] at hA
      rcases hA with ⟨C, hC⟩
      refine ⟨-C, ?_⟩
      intro x hx
      rw [hFA x hx, hC x hx]
      unfold primitive
      rw [coe_sign_of_pos (sub_pos.mpr hx.2)]
      ring
    · rintro ⟨C, hF⟩
      refine ⟨fun x : ℝ => 2 * Real.sqrt x - C, ?_, ?_⟩
      · intro x hx
        exact (sqrt_primitive_hasDeriv hx.1).sub_const C
      · intro x hx
        rw [hF x hx]
        unfold primitive
        rw [coe_sign_of_pos (sub_pos.mpr hx.2)]
        ring
  · apply Set.ext
    intro F
    simp only [ByPartsFamily, Translates, Set.mem_setOf_eq]
    constructor
    · rintro ⟨A, hA, hFA⟩
      rw [family_reciprocal_eq_translates (Set.Ioi 1) (Or.inr rfl)] at hA
      rcases hA with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro x hx
      rw [hFA x hx, hC x hx]
      unfold primitive
      rw [coe_sign_of_neg (sub_neg.mpr hx)]
      ring
    · rintro ⟨C, hF⟩
      refine ⟨fun x : ℝ => 2 * Real.sqrt x + C, ?_, ?_⟩
      · intro x hx
        exact (sqrt_primitive_hasDeriv (lt_trans zero_lt_one hx)).add_const C
      · intro x hx
        rw [hF x hx]
        unfold primitive
        rw [coe_sign_of_neg (sub_neg.mpr hx)]
        ring

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = ShiftDifferentialFamily U := by
  apply Set.ext
  intro F
  simp only [Family, ShiftDifferentialFamily, integrand, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    have hd : deriv (fun y : ℝ => y + 1) x = 1 :=
      ((hasDerivAt_id x).add_const 1).deriv
    simpa [hd] using h x hx
  · intro h x hx
    have hd : deriv (fun y : ℝ => y + 1) x = 1 :=
      ((hasDerivAt_id x).add_const 1).deriv
    simpa [hd] using h x hx
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) :
    ShiftDifferentialFamily U = ByPartsFamily U := by
  calc
    ShiftDifferentialFamily U = Family U integrand := (gap1 U hU).symm
    _ = Translates U primitive := family_phase_eq_translates U hU
    _ = ByPartsFamily U := (byparts_eq_translates U hU).symm
theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = ByPartsFamily U := by
  exact (gap1 U hU).trans (gap2 U hU)
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  exact family_phase_eq_translates U hU
theorem gap5 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    HasDerivAt phase (rawDerivative x) x := by
  obtain ⟨hx0, hx1⟩ := branch_point_data hU hx
  exact phase_hasDeriv_raw hx0 hx1
theorem gap6 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    rawDerivative x = middleDerivative x := by
  obtain ⟨hx0, hx1⟩ := branch_point_data hU hx
  exact raw_eq_middle hx0 hx1
theorem gap7 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    middleDerivative x = simplifiedDerivative x := by
  rcases hU with rfl | rfl
  · exact middle_eq_simplified_of_lt hx.1 hx.2
  · exact middle_eq_simplified_of_gt hx
theorem gap8 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    HasDerivAt phase (simplifiedDerivative x) x := by
  exact phase_hasDeriv_simplified hU hx

end
end ProofGap.Exercise2110
