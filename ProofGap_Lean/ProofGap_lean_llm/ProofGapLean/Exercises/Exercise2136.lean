import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2136
noncomputable section

def threshold : ℝ := Real.sqrt (1 + Real.sqrt 2)
def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Iio (-threshold) ∨ U = Set.Ioi threshold
def integrand (x : ℝ) := 1 / (x * Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1))
def normalized (x : ℝ) :=
  1 / (x ^ 3 * Real.sqrt (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4))
def u (x : ℝ) := x⁻¹ ^ 2 + 1
def uDifferential (x : ℝ) := deriv u x / Real.sqrt (2 - u x ^ 2)
def primitiveAsin (x : ℝ) :=
  -(1 / 2 : ℝ) * Real.arcsin (u x / Real.sqrt 2)
def primitiveArccos (x : ℝ) :=
  (1 / 2 : ℝ) * Real.arccos ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 2))

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def MinusHalfFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U uDifferential,
    ∀ x ∈ U, F x = -(1 / 2 : ℝ) * A x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem admissible_isOpen {U : Set ℝ} (hU : AdmissibleBranch U) : IsOpen U := by
  rcases hU with rfl | rfl
  · exact isOpen_Iio
  · exact isOpen_Ioi

private theorem admissible_nonempty {U : Set ℝ} (hU : AdmissibleBranch U) : U.Nonempty := by
  rcases hU with rfl | rfl
  · exact ⟨-threshold - 1, by simp⟩
  · exact ⟨threshold + 1, by simp⟩

private theorem admissible_sq_gt {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : 1 + Real.sqrt 2 < x ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have ht0 : 0 ≤ threshold := by
    unfold threshold
    exact Real.sqrt_nonneg _
  have ht2 : threshold ^ 2 = 1 + Real.sqrt 2 := by
    unfold threshold
    rw [Real.sq_sqrt]
    positivity
  rcases hU with rfl | rfl
  · change x < -threshold at hx
    have h₁ : 0 < -x - threshold := by linarith
    have h₂ : 0 < -x + threshold := by linarith
    have hp := mul_pos h₁ h₂
    nlinarith
  · change threshold < x at hx
    have h₁ : 0 < x - threshold := by linarith
    have h₂ : 0 < x + threshold := by linarith
    have hp := mul_pos h₁ h₂
    nlinarith

private theorem admissible_ne_zero {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : x ≠ 0 := by
  have h := admissible_sq_gt hU hx
  intro hzero
  subst x
  norm_num at h
  nlinarith [Real.sqrt_nonneg 2]

private theorem admissible_radicand_pos {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : 0 < x ^ 4 - 2 * x ^ 2 - 1 := by
  have hsq := admissible_sq_gt hU hx
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h₁ : 0 < x ^ 2 - (1 + Real.sqrt 2) := by linarith
  have h₂ : 0 < x ^ 2 + (Real.sqrt 2 - 1) := by nlinarith
  have hp := mul_pos h₁ h₂
  nlinarith

private theorem admissible_normalized_radicand_pos {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    0 < 1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4 := by
  have hx0 := admissible_ne_zero hU hx
  have hr := admissible_radicand_pos hU hx
  have hx4 : 0 < x ^ 4 := by positivity
  have heq :
      1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4 =
        (x ^ 4 - 2 * x ^ 2 - 1) / x ^ 4 := by
    field_simp [hx0] <;> ring
  rw [heq]
  exact div_pos hr hx4

private theorem integrand_eq_normalized {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    integrand x = normalized x := by
  have hx0 := admissible_ne_zero hU hx
  have hr := admissible_radicand_pos hU hx
  have hn := admissible_normalized_radicand_pos hU hx
  have heq :
      x ^ 4 * (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4) =
        x ^ 4 - 2 * x ^ 2 - 1 := by
    field_simp [hx0] <;> ring
  have hsq₁ := Real.sq_sqrt hr.le
  have hsq₂ := Real.sq_sqrt hn.le
  have hscaled :
      (x ^ 2 * Real.sqrt (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4)) ^ 2 =
        x ^ 4 - 2 * x ^ 2 - 1 := by
    calc
      (x ^ 2 * Real.sqrt (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4)) ^ 2 =
          x ^ 4 * (Real.sqrt (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4)) ^ 2 := by ring
      _ = x ^ 4 * (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4) := by rw [hsq₂]
      _ = x ^ 4 - 2 * x ^ 2 - 1 := heq
  have hsqrt :
      Real.sqrt (x ^ 4 - 2 * x ^ 2 - 1) =
        x ^ 2 * Real.sqrt (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4) := by
    have hleft := Real.sqrt_nonneg (x ^ 4 - 2 * x ^ 2 - 1)
    have hright :
        0 ≤ x ^ 2 * Real.sqrt (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4) :=
      mul_nonneg (sq_nonneg x) (Real.sqrt_nonneg _)
    nlinarith
  unfold integrand normalized
  rw [hsqrt]
  congr 1 <;> ring

private theorem hasDerivAt_u {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : HasDerivAt u (-2 / x ^ 3) x := by
  have hx0 := admissible_ne_zero hU hx
  unfold u
  convert ((((hasDerivAt_id x).inv hx0).pow 2).add_const 1) using 1 <;>
    simp [hx0] <;> field_simp [hx0] <;> ring

private theorem normalized_eq_half_uDifferential {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    normalized x = -(1 / 2 : ℝ) * uDifferential x := by
  have hx0 := admissible_ne_zero hU hx
  have hn := admissible_normalized_radicand_pos hU hx
  have hs0 : Real.sqrt (1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hn)
  have hu' := (hasDerivAt_u hU hx).deriv
  have hrad : 2 - u x ^ 2 = 1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4 := by
    unfold u
    ring
  unfold normalized uDifferential
  rw [hu', hrad]
  field_simp [hx0, hs0] <;> ring

private theorem hasDerivAt_congr_on_open {U : Set ℝ} (hopen : IsOpen U)
    {F G : ℝ → ℝ} {d x : ℝ} (hx : x ∈ U)
    (hFG : ∀ y ∈ U, F y = G y) (hG : HasDerivAt G d x) :
    HasDerivAt F d x := by
  have heq : F =ᶠ[nhds x] G :=
    Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => hFG y hy)
  exact hG.congr_of_eventuallyEq heq

private theorem primitiveAsin_hasDerivAt {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt primitiveAsin (normalized x) x := by
  let s : ℝ := Real.sqrt 2
  have hx0 := admissible_ne_zero hU hx
  have hn := admissible_normalized_radicand_pos hU hx
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by norm_num)
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs2 : s ^ 2 = 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hrad : 2 - u x ^ 2 = 1 - 2 * x⁻¹ ^ 2 - x⁻¹ ^ 4 := by
    unfold u
    ring
  have hrb : 0 < 2 - u x ^ 2 := by simpa only [hrad] using hn
  have hu0 : 0 < u x := by
    unfold u
    positivity
  have hus : u x < s := by
    by_contra hnot
    have hsu : s ≤ u x := le_of_not_gt hnot
    have hmul : 0 ≤ (u x - s) * (u x + s) :=
      mul_nonneg (sub_nonneg.mpr hsu) (add_nonneg hu0.le hs.le)
    nlinarith
  have harg : u x / s ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · have hpos : 0 < u x / s := div_pos hu0 hs
      linarith
    · exact (div_lt_one hs).2 hus
  have hra : 0 < 1 - (u x / s) ^ 2 := by
    have hpos : 0 < u x / s := div_pos hu0 hs
    have hplus : 0 < 1 + u x / s := by linarith
    have hprod : 0 < (1 - u x / s) * (1 + u x / s) :=
      mul_pos (sub_pos.mpr harg.2) hplus
    nlinarith
  have hcalc : s ^ 2 * (1 - (u x / s) ^ 2) = 2 - u x ^ 2 := by
    field_simp [hs0] <;> nlinarith [hs2]
  have hscaled_sq :
      (s * Real.sqrt (1 - (u x / s) ^ 2)) ^ 2 = 2 - u x ^ 2 := by
    calc
      (s * Real.sqrt (1 - (u x / s) ^ 2)) ^ 2 =
          s ^ 2 * (Real.sqrt (1 - (u x / s) ^ 2)) ^ 2 := by ring
      _ = s ^ 2 * (1 - (u x / s) ^ 2) := by rw [Real.sq_sqrt hra.le]
      _ = 2 - u x ^ 2 := hcalc
  have hsqrt_scaled :
      s * Real.sqrt (1 - (u x / s) ^ 2) = Real.sqrt (2 - u x ^ 2) := by
    have h₁ : 0 ≤ s * Real.sqrt (1 - (u x / s) ^ 2) :=
      mul_nonneg hs.le (Real.sqrt_nonneg _)
    have h₂ := Real.sqrt_nonneg (2 - u x ^ 2)
    have h₂sq := Real.sq_sqrt hrb.le
    nlinarith
  have h := ((Real.hasDerivAt_arcsin
    (ne_of_gt harg.1) (ne_of_lt harg.2)).comp x
      ((hasDerivAt_u hU hx).div_const s)).const_mul (-(1 / 2 : ℝ))
  have hra0 : Real.sqrt (1 - (u x / s) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hra)
  have hcoef :
      normalized x =
        -(1 / 2 : ℝ) *
          (1 / Real.sqrt (1 - (u x / s) ^ 2) * (-2 / x ^ 3 / s)) := by
    unfold normalized
    rw [← hrad, ← hsqrt_scaled]
    field_simp [hx0, hs0, hra0] <;> ring
  rw [hcoef]
  simpa only [primitiveAsin, Function.comp_apply] using h

private theorem eq_on_admissible_of_hasDerivAt_zero {U : Set ℝ}
    (hU : AdmissibleBranch U) {f : ℝ → ℝ}
    (hf : ∀ z ∈ U, HasDerivAt f 0 z) {x y : ℝ}
    (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  have hdiff : DifferentiableOn ℝ f U := fun z hz =>
    (hf z hz).differentiableAt.differentiableWithinAt
  have hzero : ∀ z ∈ U, deriv f z = 0 := fun z hz => (hf z hz).deriv
  rcases hU with rfl | rfl
  · exact isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio hdiff hzero hx hy
  · exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hx hy

private theorem asin_argument_eq {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) :
    u x / Real.sqrt 2 = (x ^ 2 + 1) / (x ^ 2 * Real.sqrt 2) := by
  have hx0 := admissible_ne_zero hU hx
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold u
  field_simp [hx0, hs0] <;> ring

private theorem translates_congr_on {U : Set ℝ} {p q : ℝ → ℝ}
    (h : ∀ x ∈ U, p x = q x) : Translates U p = Translates U q := by
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    exact ⟨C, fun x hx => by rw [← h x hx]; exact hF x hx⟩
  · rintro ⟨C, hF⟩
    exact ⟨C, fun x hx => by rw [h x hx]; exact hF x hx⟩

private theorem translates_eq_of_add_const {U : Set ℝ} {p q : ℝ → ℝ}
    {K : ℝ} (h : ∀ x ∈ U, q x = p x + K) :
    Translates U p = Translates U q := by
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C - K, ?_⟩
    intro x hx
    rw [h x hx, hF x hx]
    ring
  · rintro ⟨C, hF⟩
    refine ⟨C + K, ?_⟩
    intro x hx
    rw [hF x hx, h x hx]
    ring

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Family U normalized := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa only [integrand_eq_normalized hU hx] using hF x hx
  · intro hF x hx
    simpa only [integrand_eq_normalized hU hx] using hF x hx
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U normalized = MinusHalfFamily U := by
  ext F
  simp only [Family, MinusHalfFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => -2 * F y, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).const_mul (-2)
      convert h using 1
      nlinarith [normalized_eq_half_uDifferential hU hx]
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have hscaled := (hA x hx).const_mul (-(1 / 2 : ℝ))
    have hscaled' :
        HasDerivAt (fun y => -(1 / 2 : ℝ) * A y) (normalized x) x := by
      simpa only [normalized_eq_half_uDifferential hU hx] using hscaled
    exact hasDerivAt_congr_on_open (admissible_isOpen hU) hx hFA hscaled'
theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) :
    MinusHalfFamily U = Translates U primitiveAsin := by
  ext F
  simp only [MinusHalfFamily, Family, Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hFA⟩
    obtain ⟨x₀, hx₀⟩ := admissible_nonempty hU
    refine ⟨F x₀ - primitiveAsin x₀, ?_⟩
    intro x hx
    have hFx : HasDerivAt F (normalized x) x := by
      have hscaled := (hA x hx).const_mul (-(1 / 2 : ℝ))
      have hscaled' :
          HasDerivAt (fun y => -(1 / 2 : ℝ) * A y) (normalized x) x := by
        simpa only [normalized_eq_half_uDifferential hU hx] using hscaled
      exact hasDerivAt_congr_on_open (admissible_isOpen hU) hx hFA hscaled'
    have hzero :
        HasDerivAt (fun y => F y - primitiveAsin y) 0 x := by
      convert hFx.sub (primitiveAsin_hasDerivAt hU hx) using 1 <;> ring
    have hconst := eq_on_admissible_of_hasDerivAt_zero hU
      (fun y hy => by
        have hFy : HasDerivAt F (normalized y) y := by
          have hscaled := (hA y hy).const_mul (-(1 / 2 : ℝ))
          have hscaled' :
              HasDerivAt (fun z => -(1 / 2 : ℝ) * A z) (normalized y) y := by
            simpa only [normalized_eq_half_uDifferential hU hy] using hscaled
          exact hasDerivAt_congr_on_open (admissible_isOpen hU) hy hFA hscaled'
        convert hFy.sub (primitiveAsin_hasDerivAt hU hy) using 1 <;> ring)
      hx hx₀
    dsimp at hconst
    linarith
  · rintro ⟨C, hFC⟩
    refine ⟨fun y => -2 * F y, ?_, ?_⟩
    · intro x hx
      have hbase := (primitiveAsin_hasDerivAt hU hx).add_const C
      have hF : HasDerivAt F (normalized x) x :=
        hasDerivAt_congr_on_open (admissible_isOpen hU) hx hFC hbase
      have hscaled := hF.const_mul (-2)
      convert hscaled using 1
      nlinarith [normalized_eq_half_uDifferential hU hx]
    · intro x hx
      ring
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitiveAsin := by
  calc
    Family U integrand = Family U normalized := gap1 U hU
    _ = MinusHalfFamily U := gap2 U hU
    _ = Translates U primitiveAsin := gap3 U hU
theorem gap5 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand =
      Translates U (fun x =>
        -(1 / 2 : ℝ) *
          Real.arcsin ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 2))) := by
  calc
    Family U integrand = Translates U primitiveAsin := gap4 U hU
    _ = Translates U (fun x =>
        -(1 / 2 : ℝ) *
          Real.arcsin ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 2))) := by
      apply translates_congr_on
      intro x hx
      unfold primitiveAsin
      congr 2
      exact asin_argument_eq hU hx
theorem gap6 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Translates U (fun x =>
      -(1 / 2 : ℝ) * Real.arcsin ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 2))) =
        Translates U primitiveArccos := by
  apply translates_eq_of_add_const (K := Real.pi / 4)
  intro x hx
  unfold primitiveArccos
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  ring
theorem gap7 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitiveArccos := by
  calc
    Family U integrand =
        Translates U (fun x =>
          -(1 / 2 : ℝ) *
            Real.arcsin ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 2))) := gap5 U hU
    _ = Translates U primitiveArccos := gap6 U hU

end
end ProofGap.Exercise2136
