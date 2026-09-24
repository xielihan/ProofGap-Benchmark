import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3989

noncomputable section

open MeasureTheory
open scoped Interval

def region (a : ℝ) : Set (ℝ × ℝ) :=
  {p |
    (p.1 ^ 2 + p.2 ^ 2) ^ 2 ≤
      a * (p.1 ^ 3 - 3 * p.1 * p.2 ^ 2)}

def regionArea (a : ℝ) : ℝ :=
  ∫ _p in region a, (1 : ℝ)

def radial (a θ : ℝ) : ℝ :=
  a * Real.cos (3 * θ)

theorem gap1 (a θ : ℝ) :
    radial a θ =
      a * Real.cos θ * (4 * Real.cos θ ^ 2 - 3) := by
  unfold radial
  rw [Real.cos_three_mul]
  ring

theorem gap2 (θ : ℝ)
    (hθ :
      (0 ≤ θ ∧ θ ≤ Real.pi / 6) ∨
        (Real.pi / 2 ≤ θ ∧ θ ≤ 5 * Real.pi / 6)) :
    0 ≤ Real.cos θ * (4 * Real.cos θ ^ 2 - 3) := by
  have hid :
      Real.cos θ * (4 * Real.cos θ ^ 2 - 3) =
        Real.cos (3 * θ) := by
    rw [Real.cos_three_mul]
    ring
  rw [hid]
  rcases hθ with hθ | hθ
  · exact
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos], by linarith⟩
  · rw [← Real.cos_sub_two_pi (3 * θ)]
    exact
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos], by linarith⟩

theorem gap3 (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    0 ≤ Real.cos θ * (4 * Real.cos θ ^ 2 - 3) ↔
      (0 ≤ θ ∧ θ ≤ Real.pi / 6) ∨
        (Real.pi / 2 ≤ θ ∧ θ ≤ 5 * Real.pi / 6) := by
  constructor
  · intro hcos
    have hid :
        Real.cos θ * (4 * Real.cos θ ^ 2 - 3) =
          Real.cos (3 * θ) := by
      rw [Real.cos_three_mul]
      ring
    rw [hid] at hcos
    by_contra hnot
    push_neg at hnot
    rcases hθ with ⟨hθ0, hθpi⟩
    have hfirst : Real.pi / 6 < θ := hnot.1 hθ0
    by_cases hmiddle : θ < Real.pi / 2
    · have hneg :=
        Real.cos_neg_of_pi_div_two_lt_of_lt
          (x := 3 * θ) (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])
      linarith
    · have hlast : 5 * Real.pi / 6 < θ :=
        hnot.2 (le_of_not_gt hmiddle)
      have hneg :
          Real.cos (3 * θ - 2 * Real.pi) < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt
          (x := 3 * θ - 2 * Real.pi)
          (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])
      rw [Real.cos_sub_two_pi] at hneg
      linarith
  · exact gap2 θ

private def polarDomain (a : ℝ) : Set (ℝ × ℝ) :=
  {q |
    0 < q.1 ∧ -Real.pi < q.2 ∧ q.2 < Real.pi ∧
      q.1 ≤ radial a q.2}

private noncomputable def polarDensity
    (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  (polarDomain a).indicator (fun p => p.1) q

private lemma region_measurable (a : ℝ) :
    MeasurableSet (region a) := by
  unfold region
  exact measurableSet_le (by fun_prop) (by fun_prop)

private lemma polar_mem_region_iff
    (a : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ polarCoord.target) :
    polarCoord.symm q ∈ region a ↔
      q.1 ≤ radial a q.2 := by
  rcases hq with ⟨hr, hθ⟩
  have hr0 : 0 < q.1 := hr
  have htrig :
      Real.cos q.2 ^ 3 -
          3 * Real.cos q.2 * Real.sin q.2 ^ 2 =
        Real.cos (3 * q.2) := by
    rw [Real.cos_three_mul]
    have hsincos :
        Real.sin q.2 ^ 2 = 1 - Real.cos q.2 ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq q.2]
    rw [hsincos]
    ring
  simp only [polarCoord_symm_apply]
  change
    ((q.1 * Real.cos q.2) ^ 2 +
        (q.1 * Real.sin q.2) ^ 2) ^ 2 ≤
        a * ((q.1 * Real.cos q.2) ^ 3 -
          3 * (q.1 * Real.cos q.2) *
            (q.1 * Real.sin q.2) ^ 2) ↔
      q.1 ≤ a * Real.cos (3 * q.2)
  rw [show
      (q.1 * Real.cos q.2) ^ 2 +
          (q.1 * Real.sin q.2) ^ 2 = q.1 ^ 2 by
        nlinarith [Real.sin_sq_add_cos_sq q.2],
    show
      (q.1 * Real.cos q.2) ^ 3 -
          3 * (q.1 * Real.cos q.2) *
            (q.1 * Real.sin q.2) ^ 2 =
        q.1 ^ 3 * Real.cos (3 * q.2) by
      rw [← htrig]
      ring]
  constructor <;> intro h
  · nlinarith [pow_pos hr0 3]
  · nlinarith [pow_pos hr0 3]

private lemma region_integral_eq_polarDensity
    (a : ℝ) :
    (∫ _p in region a, (1 : ℝ)) =
      ∫ q, polarDensity a q := by
  classical
  have hpolar :=
    integral_comp_polarCoord_symm
      ((region a).indicator
        (fun _ : ℝ × ℝ => (1 : ℝ)))
  rw [← MeasureTheory.integral_indicator
    (region_measurable a)]
  rw [← hpolar]
  have hrestrict :
      (∫ q, polarDensity a q) =
        ∫ q in polarCoord.target, polarDensity a q := by
    rw [← MeasureTheory.integral_indicator
      polarCoord.open_target.measurableSet]
    apply integral_congr_ae
    filter_upwards with q
    by_cases hD : q ∈ polarDomain a
    · have ht : q ∈ polarCoord.target := by
        rcases hD with ⟨hr, hθl, hθu, _⟩
        exact ⟨hr, hθl, hθu⟩
      exact
        (Set.indicator_of_mem ht
          (polarDensity a)).symm
    · rw [polarDensity, Set.indicator_of_notMem hD]
      by_cases ht : q ∈ polarCoord.target
      · rw [Set.indicator_of_mem ht]
        unfold polarDensity
        rw [Set.indicator_of_notMem hD]
      · rw [Set.indicator_of_notMem ht]
  rw [hrestrict]
  apply setIntegral_congr_fun
    polarCoord.open_target.measurableSet
  intro q hq
  have hq' :
      q ∈ polarDomain a ↔
        polarCoord.symm q ∈ region a := by
    simp only [polarDomain, Set.mem_setOf_eq]
    rcases hq with ⟨hr, hθ⟩
    constructor
    · intro h
      exact
        (polar_mem_region_iff a q ⟨hr, hθ⟩).2
          h.2.2.2
    · intro h
      exact
        ⟨hr, hθ.1, hθ.2,
          (polar_mem_region_iff a q ⟨hr, hθ⟩).1 h⟩
  unfold polarDensity
  by_cases hD : q ∈ polarDomain a
  · have hR : polarCoord.symm q ∈ region a :=
      hq'.1 hD
    change
      q.1 •
          (region a).indicator
            (fun _ : ℝ × ℝ => (1 : ℝ))
            (polarCoord.symm q) =
        (polarDomain a).indicator
          (fun p => p.1) q
    rw [Set.indicator_of_mem hD,
      Set.indicator_of_mem hR]
    simp [smul_eq_mul]
  · have hR : polarCoord.symm q ∉ region a := by
      intro h
      exact hD (hq'.2 h)
    change
      q.1 •
          (region a).indicator
            (fun _ : ℝ × ℝ => (1 : ℝ))
            (polarCoord.symm q) =
        (polarDomain a).indicator
          (fun p => p.1) q
    rw [Set.indicator_of_notMem hD,
      Set.indicator_of_notMem hR]
    simp

private lemma polarDomain_measurable (a : ℝ) :
    MeasurableSet (polarDomain a) := by
  unfold polarDomain
  exact
    (measurableSet_lt measurable_const measurable_fst).inter <|
      (measurableSet_lt measurable_const measurable_snd).inter <|
        (measurableSet_lt measurable_snd measurable_const).inter <|
          measurableSet_le measurable_fst (by
            unfold radial
            fun_prop)

private lemma polarDensity_integrable
    (a : ℝ) (ha : 0 < a) :
    Integrable (polarDensity a) := by
  have hsubset :
      polarDomain a ⊆
        Set.Icc (0 : ℝ) a ×ˢ
          Set.Icc (-Real.pi) Real.pi := by
    intro q hq
    rcases hq with ⟨hr, hθl, hθu, hrad⟩
    constructor
    · constructor
      · exact hr.le
      · have hcos : Real.cos (3 * q.2) ≤ 1 :=
          Real.cos_le_one _
        unfold radial at hrad
        nlinarith
    · exact ⟨hθl.le, hθu.le⟩
  have hcompact :
      IsCompact
        (Set.Icc (0 : ℝ) a ×ˢ
          Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hrect :
      IntegrableOn (fun q : ℝ × ℝ => q.1)
        (Set.Icc (0 : ℝ) a ×ˢ
          Set.Icc (-Real.pi) Real.pi) :=
    continuous_fst.continuousOn.integrableOn_compact
      hcompact
  unfold polarDensity
  rw [integrable_indicator_iff
    (polarDomain_measurable a)]
  exact hrect.mono_set hsubset

private lemma polarDensity_fubini
    (a : ℝ) (ha : 0 < a) :
    (∫ q, polarDensity a q) =
      ∫ θ : ℝ, ∫ r : ℝ, polarDensity a (r, θ) := by
  simpa only [Measure.volume_eq_prod] using
    (MeasureTheory.integral_prod_symm
      (polarDensity a) (polarDensity_integrable a ha))

private noncomputable def angularDensity
    (a θ : ℝ) : ℝ :=
  if -Real.pi < θ ∧ θ < Real.pi ∧
      0 ≤ radial a θ then
    radial a θ ^ 2 / 2
  else
    0

private lemma polarDensity_inner_integral (a θ : ℝ) :
    (∫ r : ℝ, polarDensity a (r, θ)) =
      angularDensity a θ := by
  by_cases h :
      -Real.pi < θ ∧ θ < Real.pi ∧
        0 ≤ radial a θ
  · rw [angularDensity, if_pos h]
    have hfun :
        (fun r : ℝ => polarDensity a (r, θ)) =
          (Set.Ioc (0 : ℝ) (radial a θ)).indicator
            (fun r => r) := by
      funext r
      simp only [polarDensity, polarDomain]
      by_cases hr : 0 < r ∧ r ≤ radial a θ
      · have hD :
            (r, θ) ∈
              {q |
                0 < q.1 ∧ -Real.pi < q.2 ∧
                  q.2 < Real.pi ∧
                  q.1 ≤ radial a q.2} :=
          ⟨hr.1, h.1, h.2.1, hr.2⟩
        have hI :
            r ∈ Set.Ioc (0 : ℝ) (radial a θ) := hr
        rw [Set.indicator_of_mem hD,
          Set.indicator_of_mem hI]
      · have hD :
            (r, θ) ∉
              {q |
                0 < q.1 ∧ -Real.pi < q.2 ∧
                  q.2 < Real.pi ∧
                  q.1 ≤ radial a q.2} := by
          intro hD
          exact hr ⟨hD.1, hD.2.2.2⟩
        have hI :
            r ∉ Set.Ioc (0 : ℝ) (radial a θ) := hr
        rw [Set.indicator_of_notMem hD,
          Set.indicator_of_notMem hI]
    rw [hfun,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le h.2.2,
      integral_id]
    ring
  · rw [angularDensity, if_neg h]
    have hzero :
        (fun r : ℝ => polarDensity a (r, θ)) =
          fun _ => (0 : ℝ) := by
      funext r
      unfold polarDensity
      rw [Set.indicator_of_notMem]
      intro hD
      apply h
      exact
        ⟨hD.2.1, hD.2.2.1,
          le_trans hD.1.le hD.2.2.2⟩
    rw [hzero, integral_zero]

private def positiveAngles : Set ℝ :=
  Set.Icc (-5 * Real.pi / 6) (-Real.pi / 2) ∪
    Set.Icc (-Real.pi / 6) (Real.pi / 6) ∪
      Set.Icc (Real.pi / 2) (5 * Real.pi / 6)

private lemma angular_condition_iff_positiveAngles
    (a θ : ℝ) (ha : 0 < a) :
    (-Real.pi < θ ∧ θ < Real.pi ∧
        0 ≤ radial a θ) ↔
      θ ∈ positiveAngles := by
  constructor
  · rintro ⟨hθl, hθu, hrad⟩
    have hproduct :
        0 ≤
          Real.cos θ *
            (4 * Real.cos θ ^ 2 - 3) := by
      rw [gap1] at hrad
      nlinarith
    by_cases hθ0 : 0 ≤ θ
    · have hsign :=
        (gap3 θ ⟨hθ0, hθu.le⟩).1 hproduct
      unfold positiveAngles
      rcases hsign with hsign | hsign
      · exact
          Or.inl
            (Or.inr ⟨by linarith, hsign.2⟩)
      · exact Or.inr hsign
    · have hθ0' : 0 ≤ -θ := by linarith
      have hθpi' : -θ ≤ Real.pi := by linarith
      have hproduct' :
          0 ≤
            Real.cos (-θ) *
              (4 * Real.cos (-θ) ^ 2 - 3) := by
        simpa only [Real.cos_neg] using hproduct
      have hsign :=
        (gap3 (-θ) ⟨hθ0', hθpi'⟩).1 hproduct'
      unfold positiveAngles
      rcases hsign with hsign | hsign
      · exact
          Or.inl
            (Or.inr ⟨by linarith, by linarith⟩)
      · exact
          Or.inl
            (Or.inl ⟨by linarith, by linarith⟩)
  · intro hS
    have hθbounds :
        -Real.pi < θ ∧ θ < Real.pi := by
      unfold positiveAngles at hS
      simp only [Set.mem_union, Set.mem_Icc] at hS
      rcases hS with hS | hS
      · rcases hS with hS | hS <;>
          constructor <;> linarith [Real.pi_pos]
      · constructor <;> linarith [Real.pi_pos]
    refine ⟨hθbounds.1, hθbounds.2, ?_⟩
    have hproduct :
        0 ≤
          Real.cos θ *
            (4 * Real.cos θ ^ 2 - 3) := by
      by_cases hθ0 : 0 ≤ θ
      · have hsign :
            (0 ≤ θ ∧ θ ≤ Real.pi / 6) ∨
              (Real.pi / 2 ≤ θ ∧
                θ ≤ 5 * Real.pi / 6) := by
          unfold positiveAngles at hS
          simp only [Set.mem_union, Set.mem_Icc] at hS
          rcases hS with hS | hS
          · rcases hS with hS | hS
            · exfalso
              linarith [Real.pi_pos]
            · exact Or.inl ⟨hθ0, hS.2⟩
          · exact Or.inr hS
        exact
          (gap3 θ ⟨hθ0, hθbounds.2.le⟩).2
            hsign
      · have hθ0' : 0 ≤ -θ := by linarith
        have hsign :
            (0 ≤ -θ ∧ -θ ≤ Real.pi / 6) ∨
              (Real.pi / 2 ≤ -θ ∧
                -θ ≤ 5 * Real.pi / 6) := by
          unfold positiveAngles at hS
          simp only [Set.mem_union, Set.mem_Icc] at hS
          rcases hS with hS | hS
          · rcases hS with hS | hS
            · exact
                Or.inr ⟨by linarith, by linarith⟩
            · exact Or.inl ⟨hθ0', by linarith⟩
          · exfalso
            linarith [Real.pi_pos]
        have hproduct' :=
          (gap3 (-θ)
            ⟨hθ0', by linarith [hθbounds.1]⟩).2
              hsign
        simpa only [Real.cos_neg] using hproduct'
    rw [gap1]
    rw [show
      a * Real.cos θ *
          (4 * Real.cos θ ^ 2 - 3) =
        a *
          (Real.cos θ *
            (4 * Real.cos θ ^ 2 - 3)) by ring]
    exact mul_nonneg ha.le hproduct

private lemma angularDensity_eq_indicator
    (a : ℝ) (ha : 0 < a) :
    angularDensity a =
      positiveAngles.indicator
        (fun θ => radial a θ ^ 2 / 2) := by
  funext θ
  by_cases hS : θ ∈ positiveAngles
  · have hcond :=
      (angular_condition_iff_positiveAngles
        a θ ha).2 hS
    rw [angularDensity, if_pos hcond,
      Set.indicator_of_mem hS]
  · have hcond :
        ¬(-Real.pi < θ ∧ θ < Real.pi ∧
          0 ≤ radial a θ) := by
      intro h
      exact hS
        ((angular_condition_iff_positiveAngles
          a θ ha).1 h)
    rw [angularDensity, if_neg hcond,
      Set.indicator_of_notMem hS]

private lemma angularDensity_integral
    (a : ℝ) (ha : 0 < a) :
    (∫ θ : ℝ, angularDensity a θ) =
      2 *
          (1 / 2 *
            ∫ θ in (0 : ℝ)..Real.pi / 6,
              radial a θ ^ 2) +
        2 *
          (1 / 2 *
            ∫ θ in Real.pi / 2..5 * Real.pi / 6,
              radial a θ ^ 2) := by
  let f : ℝ → ℝ := fun θ => radial a θ ^ 2 / 2
  let A : Set ℝ :=
    Set.Icc (-5 * Real.pi / 6) (-Real.pi / 2)
  let B : Set ℝ :=
    Set.Icc (-Real.pi / 6) (Real.pi / 6)
  let C : Set ℝ :=
    Set.Icc (Real.pi / 2) (5 * Real.pi / 6)
  have hfcont : Continuous f := by
    dsimp [f]
    unfold radial
    fun_prop
  have hA : IntegrableOn f A := by
    dsimp [A]
    exact hfcont.continuousOn.integrableOn_Icc
  have hB : IntegrableOn f B := by
    dsimp [B]
    exact hfcont.continuousOn.integrableOn_Icc
  have hC : IntegrableOn f C := by
    dsimp [C]
    exact hfcont.continuousOn.integrableOn_Icc
  have hdAB : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    intro θ hθA hθB
    dsimp [A] at hθA
    dsimp [B] at hθB
    simp only [Set.mem_Icc] at hθA hθB
    linarith [Real.pi_pos]
  have hdABC : Disjoint (A ∪ B) C := by
    refine Set.disjoint_left.2 ?_
    intro θ hθAB hθC
    dsimp [C] at hθC
    simp only [Set.mem_Icc] at hθC
    rcases hθAB with hθA | hθB
    · dsimp [A] at hθA
      simp only [Set.mem_Icc] at hθA
      linarith [Real.pi_pos]
    · dsimp [B] at hθB
      simp only [Set.mem_Icc] at hθB
      linarith [Real.pi_pos]
  have hAle :
      -5 * Real.pi / 6 ≤ -Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hBle :
      -Real.pi / 6 ≤ Real.pi / 6 := by
    linarith [Real.pi_pos]
  have hCle :
      Real.pi / 2 ≤ 5 * Real.pi / 6 := by
    linarith [Real.pi_pos]
  have hsetA :
      (∫ θ in A, f θ) =
        ∫ θ in -5 * Real.pi / 6..-Real.pi / 2,
          f θ := by
    dsimp [A]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hAle]
  have hsetB :
      (∫ θ in B, f θ) =
        ∫ θ in -Real.pi / 6..Real.pi / 6,
          f θ := by
    dsimp [B]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hBle]
  have hsetC :
      (∫ θ in C, f θ) =
        ∫ θ in Real.pi / 2..5 * Real.pi / 6,
          f θ := by
    dsimp [C]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hCle]
  have heven (θ : ℝ) : f (-θ) = f θ := by
    dsimp [f]
    unfold radial
    rw [show 3 * -θ = -(3 * θ) by ring,
      Real.cos_neg]
  have hAeqC :
      (∫ θ in -5 * Real.pi / 6..-Real.pi / 2,
          f θ) =
        ∫ θ in Real.pi / 2..5 * Real.pi / 6,
          f θ := by
    symm
    calc
      (∫ θ in Real.pi / 2..5 * Real.pi / 6,
          f θ) =
          ∫ θ in Real.pi / 2..5 * Real.pi / 6,
            f (-θ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            exact (heven θ).symm
      _ =
          ∫ θ in -(5 * Real.pi / 6)..-(Real.pi / 2),
            f θ := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := Real.pi / 2)
            (b := 5 * Real.pi / 6))
      _ =
          ∫ θ in -5 * Real.pi / 6..-Real.pi / 2,
            f θ := by
        ring_nf
  have hnegMiddle :
      (∫ θ in -Real.pi / 6..(0 : ℝ), f θ) =
        ∫ θ in (0 : ℝ)..Real.pi / 6, f θ := by
    symm
    calc
      (∫ θ in (0 : ℝ)..Real.pi / 6, f θ) =
          ∫ θ in (0 : ℝ)..Real.pi / 6,
            f (-θ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            exact (heven θ).symm
      _ =
          ∫ θ in -(Real.pi / 6)..-(0 : ℝ),
            f θ := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ))
            (b := Real.pi / 6))
      _ =
          ∫ θ in -Real.pi / 6..(0 : ℝ),
            f θ := by
        ring_nf
  have hmiddle :
      (∫ θ in -Real.pi / 6..Real.pi / 6,
          f θ) =
        2 * ∫ θ in (0 : ℝ)..Real.pi / 6,
          f θ := by
    have hleft :
        IntervalIntegrable f volume
          (-Real.pi / 6) 0 :=
      hfcont.intervalIntegrable _ _
    have hright :
        IntervalIntegrable f volume
          0 (Real.pi / 6) :=
      hfcont.intervalIntegrable _ _
    rw [←
      intervalIntegral.integral_add_adjacent_intervals
        hleft hright,
      hnegMiddle]
    ring
  rw [angularDensity_eq_indicator a ha,
    MeasureTheory.integral_indicator]
  · change (∫ θ in (A ∪ B) ∪ C, f θ) = _
    rw [MeasureTheory.setIntegral_union hdABC
      measurableSet_Icc (hA.union hB) hC,
      MeasureTheory.setIntegral_union hdAB
        measurableSet_Icc hA hB,
      hsetA, hsetB, hsetC, hAeqC, hmiddle]
    dsimp [f]
    simp only [intervalIntegral.integral_div]
    ring
  · exact
      ((measurableSet_Icc.union
          measurableSet_Icc).union
        measurableSet_Icc)

theorem gap4 (a : ℝ) (ha : 0 < a) :
    regionArea a =
      2 *
        (1 / 2 *
          ∫ θ in (0 : ℝ)..Real.pi / 6,
            radial a θ ^ 2) +
          2 *
        (1 / 2 *
          ∫ θ in Real.pi / 2..5 * Real.pi / 6,
            radial a θ ^ 2) := by
  rw [regionArea, region_integral_eq_polarDensity a,
    polarDensity_fubini a ha]
  simp_rw [polarDensity_inner_integral]
  exact angularDensity_integral a ha

theorem gap5 (a : ℝ) :
    (∫ θ in Real.pi / 2..5 * Real.pi / 6,
        a ^ 2 * Real.cos θ ^ 2 *
          (4 * Real.cos θ ^ 2 - 3) ^ 2) =
      ∫ θ in Real.pi / 6..Real.pi / 2,
        a ^ 2 * Real.cos θ ^ 2 *
          (4 * Real.cos θ ^ 2 - 3) ^ 2 := by
  let g : ℝ → ℝ := fun θ =>
    a ^ 2 * Real.cos θ ^ 2 *
      (4 * Real.cos θ ^ 2 - 3) ^ 2
  have hsub :=
    intervalIntegral.integral_comp_sub_left
      (f := g) (a := Real.pi / 6)
      (b := Real.pi / 2) Real.pi
  have heven (θ : ℝ) :
      g (Real.pi - θ) = g θ := by
    dsimp [g]
    rw [Real.cos_pi_sub]
    ring
  calc
    (∫ θ in Real.pi / 2..5 * Real.pi / 6,
        a ^ 2 * Real.cos θ ^ 2 *
          (4 * Real.cos θ ^ 2 - 3) ^ 2) =
        ∫ θ in Real.pi / 6..Real.pi / 2,
          g (Real.pi - θ) := by
      convert hsub.symm using 1 <;>
        dsimp [g] <;> ring
    _ = ∫ θ in Real.pi / 6..Real.pi / 2,
        g θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact heven θ
    _ = ∫ θ in Real.pi / 6..Real.pi / 2,
        a ^ 2 * Real.cos θ ^ 2 *
          (4 * Real.cos θ ^ 2 - 3) ^ 2 := rfl

theorem gap6 (a : ℝ) (ha : 0 < a) :
    regionArea a =
      ∫ θ in (0 : ℝ)..Real.pi / 2,
        a ^ 2 * Real.cos θ ^ 2 *
          (4 * Real.cos θ ^ 2 - 3) ^ 2 := by
  let g : ℝ → ℝ := fun θ =>
    a ^ 2 * Real.cos θ ^ 2 *
      (4 * Real.cos θ ^ 2 - 3) ^ 2
  have hirad (c d : ℝ) :
      (∫ θ in c..d, radial a θ ^ 2) =
        ∫ θ in c..d, g θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    change radial a θ ^ 2 = g θ
    rw [gap1 a θ]
    dsimp [g]
    ring
  calc
    regionArea a =
        (∫ θ in (0 : ℝ)..Real.pi / 6, g θ) +
          ∫ θ in Real.pi / 2..5 * Real.pi / 6,
            g θ := by
      rw [gap4 a ha, hirad, hirad]
      ring
    _ =
        (∫ θ in (0 : ℝ)..Real.pi / 6, g θ) +
          ∫ θ in Real.pi / 6..Real.pi / 2,
            g θ := by
      rw [show
        (∫ θ in Real.pi / 2..5 * Real.pi / 6,
            g θ) =
          ∫ θ in Real.pi / 6..Real.pi / 2,
            g θ by
        exact gap5 a]
    _ = ∫ θ in (0 : ℝ)..Real.pi / 2,
        g θ := by
      exact
        intervalIntegral.integral_add_adjacent_intervals
          ((by
            dsimp [g]
            fun_prop :
              Continuous g).intervalIntegrable _ _)
          ((by
            dsimp [g]
            fun_prop :
              Continuous g).intervalIntegrable _ _)
    _ = ∫ θ in (0 : ℝ)..Real.pi / 2,
        a ^ 2 * Real.cos θ ^ 2 *
          (4 * Real.cos θ ^ 2 - 3) ^ 2 := rfl

theorem gap7 (a : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        a ^ 2 * Real.cos θ ^ 2 *
          (4 * Real.cos θ ^ 2 - 3) ^ 2) =
      a ^ 2 *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          16 * Real.cos θ ^ 6 -
            24 * Real.cos θ ^ 4 +
              9 * Real.cos θ ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  ring

theorem gap8 (a : ℝ) :
    a ^ 2 *
        (∫ θ in (0 : ℝ)..Real.pi / 2,
          16 * Real.cos θ ^ 6 -
            24 * Real.cos θ ^ 4 +
              9 * Real.cos θ ^ 2) =
      Real.pi * a ^ 2 / 4 := by
  have h2 :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.cos θ ^ 2) =
        Real.pi / 4 := by
    simp [integral_cos_sq]
    ring
  have h4 :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.cos θ ^ 4) =
        3 * Real.pi / 16 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num,
      integral_cos_pow]
    rw [h2]
    simp
    ring
  have h6 :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.cos θ ^ 6) =
        5 * Real.pi / 32 := by
    rw [show (6 : ℕ) = 4 + 2 by norm_num,
      integral_cos_pow]
    rw [h4]
    simp
    ring
  have hpoly :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        16 * Real.cos θ ^ 6 -
          24 * Real.cos θ ^ 4 +
            9 * Real.cos θ ^ 2) =
        Real.pi / 4 := by
    have hi6 :
        IntervalIntegrable
          (fun θ : ℝ => Real.cos θ ^ 6)
          volume 0 (Real.pi / 2) :=
      (Real.continuous_cos.pow 6).intervalIntegrable
        _ _
    have hi4 :
        IntervalIntegrable
          (fun θ : ℝ => Real.cos θ ^ 4)
          volume 0 (Real.pi / 2) :=
      (Real.continuous_cos.pow 4).intervalIntegrable
        _ _
    have hi2 :
        IntervalIntegrable
          (fun θ : ℝ => Real.cos θ ^ 2)
          volume 0 (Real.pi / 2) :=
      (Real.continuous_cos.pow 2).intervalIntegrable
        _ _
    rw [intervalIntegral.integral_add
        ((hi6.const_mul 16).sub
          (hi4.const_mul 24))
        (hi2.const_mul 9),
      intervalIntegral.integral_sub
        (hi6.const_mul 16) (hi4.const_mul 24),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rw [h6, h4, h2]
    ring
  rw [hpoly]
  ring

theorem gap9 (a : ℝ) (ha : 0 < a) :
    regionArea a = Real.pi * a ^ 2 / 4 := by
  rw [gap6 a ha, gap7 a, gap8 a]

end

end ProofGap.Exercise3989
