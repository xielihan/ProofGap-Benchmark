import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4027

noncomputable section

open MeasureTheory
open scoped Interval

def baseRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ a ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ b}

def upperSurface (x y : ℝ) : ℝ :=
  Real.sqrt (x * y)

def lowerSurface (x y : ℝ) : ℝ :=
  -Real.sqrt (x * y)

def volume (a b : ℝ) : ℝ :=
  ∫ p in baseRegion a b, 2 * Real.sqrt (p.1 * p.2)

theorem gap1 (x y : ℝ) :
    upperSurface x y = Real.sqrt (x * y) ∧
      lowerSurface x y = -Real.sqrt (x * y) := by
  exact ⟨rfl, rfl⟩

private theorem base_closed (a b : ℝ) : IsClosed (baseRegion a b) := by
  change IsClosed
    ({p : ℝ × ℝ | 0 ≤ p.1} ∩
      ({p : ℝ × ℝ | 0 ≤ p.2} ∩
        ({p : ℝ × ℝ | a ≤ p.1 + p.2} ∩
          {p : ℝ × ℝ | p.1 + p.2 ≤ b})))
  exact
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        ((isClosed_le continuous_const (continuous_fst.add continuous_snd)).inter
          (isClosed_le (continuous_fst.add continuous_snd) continuous_const)))

private theorem base_compact (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    IsCompact (baseRegion a b) := by
  have hb : 0 < b := ha.trans hab
  have hsub :
      baseRegion a b ⊆
        Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) b := by
    rintro ⟨x, y⟩ hp
    exact ⟨⟨hp.1, by linarith [hp.2.1, hp.2.2.2]⟩,
      ⟨hp.2.1, by linarith [hp.1, hp.2.2.2]⟩⟩
  exact
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      (base_closed a b) hsub

private def leftRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  baseRegion a b ∩ {p | p.1 ≤ a}

private def rightRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  baseRegion a b ∩ {p | a < p.1}

private theorem left_meas (a b : ℝ) : MeasurableSet (leftRegion a b) := by
  unfold leftRegion
  exact (base_closed a b).measurableSet.inter
    (measurableSet_le measurable_fst measurable_const)

private theorem right_meas (a b : ℝ) : MeasurableSet (rightRegion a b) := by
  unfold rightRegion
  exact (base_closed a b).measurableSet.inter
    (measurableSet_lt measurable_const measurable_fst)

private theorem split_base (a b : ℝ) :
    leftRegion a b ∪ rightRegion a b = baseRegion a b := by
  ext p
  simp only [leftRegion, rightRegion, Set.mem_union, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    exact (le_total p.1 a).elim (fun hx => Or.inl ⟨h, hx⟩)
      (fun hx => if heq : p.1 = a then Or.inl ⟨h, heq.le⟩
        else Or.inr ⟨h, lt_of_le_of_ne hx (Ne.symm heq)⟩)

private theorem split_disjoint (a b : ℝ) :
    Disjoint (leftRegion a b) (rightRegion a b) := by
  rw [Set.disjoint_left]
  rintro p ⟨_, hle⟩ ⟨_, hlt⟩
  change p.1 ≤ a at hle
  change a < p.1 at hlt
  exact (not_lt_of_ge hle) hlt

private theorem left_fubini (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∫ p in leftRegion a b, 2 * Real.sqrt (p.1 * p.2)) =
      ∫ x in (0 : ℝ)..a,
        ∫ y in a - x..b - x, 2 * Real.sqrt (x * y) := by
  let f : ℝ × ℝ → ℝ := fun p => 2 * Real.sqrt (p.1 * p.2)
  have hleftSub :
      leftRegion a b ⊆
        Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) b := by
    rintro ⟨x, y⟩ hp
    exact ⟨⟨hp.1.1, hp.2⟩,
      ⟨hp.1.2.1, by linarith [hp.1.1, hp.1.2.2.2]⟩⟩
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfintOn : IntegrableOn f (leftRegion a b) :=
    (hfcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hleftSub
  have hfint : Integrable ((leftRegion a b).indicator f) :=
    (integrable_indicator_iff (left_meas a b)).2 hfintOn
  have hsection : ∀ x ∈ Set.Icc (0 : ℝ) a,
      (∫ y : ℝ, (leftRegion a b).indicator f (x, y)) =
        ∫ y in a - x..b - x, 2 * Real.sqrt (x * y) := by
    intro x hx
    have hlow : 0 ≤ a - x := sub_nonneg.mpr hx.2
    have hbounds : a - x ≤ b - x := by linarith
    have hmem : ∀ y : ℝ,
        (x, y) ∈ leftRegion a b ↔
          y ∈ Set.Icc (a - x) (b - x) := by
      intro y
      simp only [leftRegion, baseRegion, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_Icc, Prod.fst, Prod.snd]
      constructor
      · rintro ⟨⟨hx0, hy0, hal, hbu⟩, hxa⟩
        exact ⟨by linarith, by linarith⟩
      · intro hy
        refine ⟨⟨hx.1, hlow.trans hy.1, ?_, ?_⟩, hx.2⟩
        · linarith
        · linarith
    have hind :
        (fun y : ℝ => (leftRegion a b).indicator f (x, y)) =
          (Set.Icc (a - x) (b - x)).indicator
            (fun y => 2 * Real.sqrt (x * y)) := by
      funext y
      by_cases hy : y ∈ Set.Icc (a - x) (b - x)
      · rw [Set.indicator_of_mem hy,
          Set.indicator_of_mem ((hmem y).mpr hy)]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (fun hp => hy ((hmem y).mp hp))]
    rw [hind, MeasureTheory.integral_indicator measurableSet_Icc]
    rw [← Measure.restrict_congr_set
      (Ioc_ae_eq_Icc :
        Set.Ioc (a - x) (b - x) =ᵐ[MeasureTheory.volume]
          Set.Icc (a - x) (b - x))]
    rw [← intervalIntegral.integral_of_le hbounds]
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, (leftRegion a b).indicator f (x, y)) =
        (Set.Icc (0 : ℝ) a).indicator
          (fun x =>
            ∫ y in a - x..b - x, 2 * Real.sqrt (x * y)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) a
    · rw [Set.indicator_of_mem hx]
      exact hsection x hx
    · rw [Set.indicator_of_notMem hx]
      have hnone : ∀ y : ℝ, (x, y) ∉ leftRegion a b := by
        intro y hp
        exact hx (hleftSub hp).1
      simp [hnone]
  calc
    (∫ p in leftRegion a b, 2 * Real.sqrt (p.1 * p.2)) =
        ∫ p : ℝ × ℝ, (leftRegion a b).indicator f p := by
          rw [MeasureTheory.integral_indicator (left_meas a b)]
    _ = ∫ x : ℝ, ∫ y : ℝ,
          (leftRegion a b).indicator f (x, y) := by
          exact MeasureTheory.integral_prod _ hfint
    _ = ∫ x : ℝ,
          (Set.Icc (0 : ℝ) a).indicator
            (fun x =>
              ∫ y in a - x..b - x,
                2 * Real.sqrt (x * y)) x := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = ∫ x in Set.Icc (0 : ℝ) a,
          ∫ y in a - x..b - x,
            2 * Real.sqrt (x * y) := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ x in Set.Ioc (0 : ℝ) a,
          ∫ y in a - x..b - x,
            2 * Real.sqrt (x * y) := by
          rw [Measure.restrict_congr_set
            (Ioc_ae_eq_Icc :
              Set.Ioc (0 : ℝ) a =ᵐ[MeasureTheory.volume]
                Set.Icc 0 a)]
    _ = ∫ x in (0 : ℝ)..a,
          ∫ y in a - x..b - x,
            2 * Real.sqrt (x * y) := by
          rw [intervalIntegral.integral_of_le ha.le]

private theorem right_fubini (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∫ p in rightRegion a b, 2 * Real.sqrt (p.1 * p.2)) =
      ∫ x in a..b,
        ∫ y in (0 : ℝ)..b - x, 2 * Real.sqrt (x * y) := by
  let f : ℝ × ℝ → ℝ := fun p => 2 * Real.sqrt (p.1 * p.2)
  have hrightSub :
      rightRegion a b ⊆
        Set.Ioc a b ×ˢ Set.Icc (0 : ℝ) b := by
    rintro ⟨x, y⟩ hp
    exact ⟨⟨hp.2, by linarith [hp.1.2.1, hp.1.2.2.2]⟩,
      ⟨hp.1.2.1, by linarith [hp.1.1, hp.1.2.2.2]⟩⟩
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfintOn : IntegrableOn f (rightRegion a b) :=
    (hfcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (fun p hp => ⟨⟨(hrightSub hp).1.1.le, (hrightSub hp).1.2⟩,
          (hrightSub hp).2⟩)
  have hfint : Integrable ((rightRegion a b).indicator f) :=
    (integrable_indicator_iff (right_meas a b)).2 hfintOn
  have hsection : ∀ x ∈ Set.Ioc a b,
      (∫ y : ℝ, (rightRegion a b).indicator f (x, y)) =
        ∫ y in (0 : ℝ)..b - x, 2 * Real.sqrt (x * y) := by
    intro x hx
    have hu : 0 ≤ b - x := sub_nonneg.mpr hx.2
    have hmem : ∀ y : ℝ,
        (x, y) ∈ rightRegion a b ↔
          y ∈ Set.Icc (0 : ℝ) (b - x) := by
      intro y
      simp only [rightRegion, baseRegion, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_Icc, Prod.fst, Prod.snd]
      constructor
      · rintro ⟨⟨hx0, hy0, hal, hbu⟩, hxa⟩
        exact ⟨hy0, by linarith⟩
      · intro hy
        refine ⟨⟨ha.le.trans hx.1.le, hy.1, ?_, ?_⟩, hx.1⟩
        · exact hx.1.le.trans (le_add_of_nonneg_right hy.1)
        · linarith
    have hind :
        (fun y : ℝ => (rightRegion a b).indicator f (x, y)) =
          (Set.Icc (0 : ℝ) (b - x)).indicator
            (fun y => 2 * Real.sqrt (x * y)) := by
      funext y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) (b - x)
      · rw [Set.indicator_of_mem hy,
          Set.indicator_of_mem ((hmem y).mpr hy)]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (fun hp => hy ((hmem y).mp hp))]
    rw [hind, MeasureTheory.integral_indicator measurableSet_Icc]
    rw [← Measure.restrict_congr_set
      (Ioc_ae_eq_Icc :
        Set.Ioc (0 : ℝ) (b - x) =ᵐ[MeasureTheory.volume]
          Set.Icc 0 (b - x))]
    rw [← intervalIntegral.integral_of_le hu]
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, (rightRegion a b).indicator f (x, y)) =
        (Set.Ioc a b).indicator
          (fun x =>
            ∫ y in (0 : ℝ)..b - x, 2 * Real.sqrt (x * y)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hx]
      exact hsection x hx
    · rw [Set.indicator_of_notMem hx]
      have hnone : ∀ y : ℝ, (x, y) ∉ rightRegion a b := by
        intro y hp
        exact hx (hrightSub hp).1
      simp [hnone]
  calc
    (∫ p in rightRegion a b, 2 * Real.sqrt (p.1 * p.2)) =
        ∫ p : ℝ × ℝ, (rightRegion a b).indicator f p := by
          rw [MeasureTheory.integral_indicator (right_meas a b)]
    _ = ∫ x : ℝ, ∫ y : ℝ,
          (rightRegion a b).indicator f (x, y) := by
          exact MeasureTheory.integral_prod _ hfint
    _ = ∫ x : ℝ,
          (Set.Ioc a b).indicator
            (fun x =>
              ∫ y in (0 : ℝ)..b - x,
                2 * Real.sqrt (x * y)) x := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = ∫ x in Set.Ioc a b,
          ∫ y in (0 : ℝ)..b - x,
            2 * Real.sqrt (x * y) := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ x in a..b,
          ∫ y in (0 : ℝ)..b - x,
            2 * Real.sqrt (x * y) := by
          rw [intervalIntegral.integral_of_le hab.le]

theorem gap2 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    volume a b =
      2 *
        ((∫ x in (0 : ℝ)..a,
            ∫ y in a - x..b - x, Real.sqrt (x * y)) +
          ∫ x in a..b,
            ∫ y in (0 : ℝ)..b - x, Real.sqrt (x * y)) := by
  let f : ℝ × ℝ → ℝ := fun p => 2 * Real.sqrt (p.1 * p.2)
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hint : IntegrableOn f (baseRegion a b) :=
    hcont.continuousOn.integrableOn_compact (base_compact a b ha hab)
  have hleftInt : IntegrableOn f (leftRegion a b) :=
    hint.mono_set (by intro p hp; exact hp.1)
  have hrightInt : IntegrableOn f (rightRegion a b) :=
    hint.mono_set (by intro p hp; exact hp.1)
  have hsplit :
      volume a b =
        (∫ p in leftRegion a b, 2 * Real.sqrt (p.1 * p.2)) +
          ∫ p in rightRegion a b, 2 * Real.sqrt (p.1 * p.2) := by
    rw [volume, ← split_base a b,
      MeasureTheory.setIntegral_union (split_disjoint a b)
        (right_meas a b) hleftInt hrightInt]
  rw [hsplit, left_fubini a b ha hab, right_fubini a b ha hab]
  have hleftFactor :
      (∫ x in (0 : ℝ)..a,
        ∫ y in a - x..b - x, 2 * Real.sqrt (x * y)) =
        2 * ∫ x in (0 : ℝ)..a,
          ∫ y in a - x..b - x, Real.sqrt (x * y) := by
    calc
      _ = ∫ x in (0 : ℝ)..a,
          2 * (∫ y in a - x..b - x, Real.sqrt (x * y)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change (∫ y in a - x..b - x,
              2 * Real.sqrt (x * y)) =
                2 * ∫ y in a - x..b - x, Real.sqrt (x * y)
            rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hrightFactor :
      (∫ x in a..b,
        ∫ y in (0 : ℝ)..b - x, 2 * Real.sqrt (x * y)) =
        2 * ∫ x in a..b,
          ∫ y in (0 : ℝ)..b - x, Real.sqrt (x * y) := by
    calc
      _ = ∫ x in a..b,
          2 * (∫ y in (0 : ℝ)..b - x, Real.sqrt (x * y)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change (∫ y in (0 : ℝ)..b - x,
              2 * Real.sqrt (x * y)) =
                2 * ∫ y in (0 : ℝ)..b - x, Real.sqrt (x * y)
            rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hleftFactor, hrightFactor]
  ring

private theorem sqrt_cube (u : ℝ) (hu : 0 ≤ u) :
    Real.sqrt (u ^ 3) = u * Real.sqrt u := by
  have hleft : 0 ≤ Real.sqrt (u ^ 3) := Real.sqrt_nonneg _
  have hright : 0 ≤ u * Real.sqrt u :=
    mul_nonneg hu (Real.sqrt_nonneg _)
  have hsqLeft : Real.sqrt (u ^ 3) ^ 2 = u ^ 3 :=
    Real.sq_sqrt (pow_nonneg hu 3)
  have hsqU : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  apply (sq_eq_sq₀ hleft hright).mp
  rw [hsqLeft, mul_pow, hsqU]
  ring

private theorem sqrt_mul_cube (x u : ℝ) (hx : 0 ≤ x) (hu : 0 ≤ u) :
    Real.sqrt (x * u ^ 3) = u * Real.sqrt (x * u) := by
  calc
    Real.sqrt (x * u ^ 3) =
        Real.sqrt x * Real.sqrt (u ^ 3) := by
          rw [Real.sqrt_mul hx]
    _ = Real.sqrt x * (u * Real.sqrt u) := by
          rw [sqrt_cube u hu]
    _ = u * (Real.sqrt x * Real.sqrt u) := by ring
    _ = u * Real.sqrt (x * u) := by
          rw [Real.sqrt_mul hx]

private theorem integral_sqrt_interval (l u : ℝ)
    (hl : 0 ≤ l) (hlu : l ≤ u) :
    (∫ y in l..u, Real.sqrt y) =
      2 / 3 * (u * Real.sqrt u - l * Real.sqrt l) := by
  let F : ℝ → ℝ := fun y => 2 / 3 * (y * Real.sqrt y)
  have hu0 : 0 ≤ u := hl.trans hlu
  have hcont : ContinuousOn F (Set.Icc l u) :=
    (by fun_prop : Continuous F).continuousOn
  have hd : ∀ y ∈ Set.Ioo l u, HasDerivAt F (Real.sqrt y) y := by
    intro y hy
    have hypos : 0 < y := hl.trans_lt hy.1
    have hsqrt :
        HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y)) y :=
      Real.hasDerivAt_sqrt (ne_of_gt hypos)
    have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hypos.le
    dsimp [F]
    convert
      (hasDerivAt_const y (2 / 3 : ℝ)).mul
        ((hasDerivAt_id y).mul hsqrt) using 1
    simp only [id_eq]
    field_simp [Real.sqrt_ne_zero'.mpr hypos]
    rw [hsq]
    ring
  have hi : IntervalIntegrable Real.sqrt MeasureTheory.volume l u :=
    Real.continuous_sqrt.intervalIntegrable _ _
  calc
    _ = F u - F l := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        hlu hcont hd hi
    _ = _ := by dsimp [F]; ring

private theorem inner_sqrt (x l u : ℝ)
    (hx : 0 ≤ x) (hl : 0 ≤ l) (hlu : l ≤ u) :
    (∫ y in l..u, Real.sqrt (x * y)) =
      2 / 3 *
        (Real.sqrt (x * u ^ 3) - Real.sqrt (x * l ^ 3)) := by
  have hu : 0 ≤ u := hl.trans hlu
  calc
    _ = ∫ y in l..u, Real.sqrt x * Real.sqrt y := by
      apply intervalIntegral.integral_congr
      intro y hy
      change Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y
      rw [Real.sqrt_mul hx]
    _ = Real.sqrt x * ∫ y in l..u, Real.sqrt y := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.sqrt x *
        (2 / 3 * (u * Real.sqrt u - l * Real.sqrt l)) := by
      rw [integral_sqrt_interval l u hl hlu]
    _ = _ := by
      rw [sqrt_mul_cube x u hx hu, sqrt_mul_cube x l hx hl]
      have hxu : Real.sqrt (x * u) = Real.sqrt x * Real.sqrt u := by
        rw [Real.sqrt_mul hx]
      have hxl : Real.sqrt (x * l) = Real.sqrt x * Real.sqrt l := by
        rw [Real.sqrt_mul hx]
      rw [hxu, hxl]
      ring

theorem gap3 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    volume a b =
      4 / 3 *
          (∫ x in (0 : ℝ)..a,
            Real.sqrt (x * (b - x) ^ 3) -
              Real.sqrt (x * (a - x) ^ 3)) +
        4 / 3 *
          ∫ x in a..b, Real.sqrt (x * (b - x) ^ 3) := by
  rw [gap2 a b ha hab]
  have hleft : ∀ x ∈ Set.uIcc (0 : ℝ) a,
      (∫ y in a - x..b - x, Real.sqrt (x * y)) =
        2 / 3 *
          (Real.sqrt (x * (b - x) ^ 3) -
            Real.sqrt (x * (a - x) ^ 3)) := by
    intro x hx
    rw [Set.uIcc_of_le ha.le] at hx
    exact inner_sqrt x (a - x) (b - x) hx.1
      (sub_nonneg.mpr hx.2) (by linarith)
  have hright : ∀ x ∈ Set.uIcc a b,
      (∫ y in (0 : ℝ)..b - x, Real.sqrt (x * y)) =
        2 / 3 * Real.sqrt (x * (b - x) ^ 3) := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    rw [inner_sqrt x 0 (b - x) (ha.le.trans hx.1)
      (by norm_num) (sub_nonneg.mpr hx.2)]
    norm_num
  calc
    2 * ((∫ x in (0 : ℝ)..a,
        ∫ y in a - x..b - x, Real.sqrt (x * y)) +
      ∫ x in a..b,
        ∫ y in (0 : ℝ)..b - x, Real.sqrt (x * y)) =
        2 * ((∫ x in (0 : ℝ)..a,
          2 / 3 * (Real.sqrt (x * (b - x) ^ 3) -
            Real.sqrt (x * (a - x) ^ 3))) +
          ∫ x in a..b,
            2 / 3 * Real.sqrt (x * (b - x) ^ 3)) := by
          congr 2
          · apply intervalIntegral.integral_congr
            exact hleft
          · apply intervalIntegral.integral_congr
            exact hright
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring

theorem gap4 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    volume a b =
      4 / 3 *
          (∫ x in (0 : ℝ)..b,
            (b - x) * Real.sqrt (x * (b - x))) -
        4 / 3 *
          ∫ x in (0 : ℝ)..a,
            (a - x) * Real.sqrt (x * (a - x)) := by
  rw [gap3 a b ha hab]
  let fb : ℝ → ℝ := fun x => (b - x) * Real.sqrt (x * (b - x))
  let fa : ℝ → ℝ := fun x => (a - x) * Real.sqrt (x * (a - x))
  have hfb0a : ∀ x ∈ Set.uIcc (0 : ℝ) a,
      Real.sqrt (x * (b - x) ^ 3) = fb x := by
    intro x hx
    rw [Set.uIcc_of_le ha.le] at hx
    exact sqrt_mul_cube x (b - x) hx.1
      (by linarith [hx.2, hab]) 
  have hfbab : ∀ x ∈ Set.uIcc a b,
      Real.sqrt (x * (b - x) ^ 3) = fb x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact sqrt_mul_cube x (b - x) (ha.le.trans hx.1)
      (sub_nonneg.mpr hx.2)
  have hfa0a : ∀ x ∈ Set.uIcc (0 : ℝ) a,
      Real.sqrt (x * (a - x) ^ 3) = fa x := by
    intro x hx
    rw [Set.uIcc_of_le ha.le] at hx
    exact sqrt_mul_cube x (a - x) hx.1
      (sub_nonneg.mpr hx.2)
  have hfbcont : Continuous fb := by dsimp [fb]; fun_prop
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hfbcont.intervalIntegrable 0 a)
      (hfbcont.intervalIntegrable a b)
  calc
    4 / 3 *
        (∫ x in (0 : ℝ)..a,
          Real.sqrt (x * (b - x) ^ 3) -
            Real.sqrt (x * (a - x) ^ 3)) +
      4 / 3 *
        ∫ x in a..b, Real.sqrt (x * (b - x) ^ 3) =
        4 / 3 *
          ((∫ x in (0 : ℝ)..a, fb x) -
            ∫ x in (0 : ℝ)..a, fa x) +
          4 / 3 * ∫ x in a..b, fb x := by
            congr 2
            · rw [← intervalIntegral.integral_sub
                (hfbcont.intervalIntegrable 0 a)
                ((by dsimp [fa]; fun_prop : Continuous fa).intervalIntegrable 0 a)]
              apply intervalIntegral.integral_congr
              intro x hx
              change
                Real.sqrt (x * (b - x) ^ 3) -
                    Real.sqrt (x * (a - x) ^ 3) =
                  fb x - fa x
              rw [hfb0a x hx, hfa0a x hx]
            · apply intervalIntegral.integral_congr
              exact hfbab
    _ = 4 / 3 * (∫ x in (0 : ℝ)..b, fb x) -
        4 / 3 * ∫ x in (0 : ℝ)..a, fa x := by
          rw [← hadd]
          ring
    _ = _ := rfl

theorem gap5 (b : ℝ) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b,
        (b - x) * Real.sqrt (x * (b - x))) =
      2 * b ^ 3 *
        ∫ t in (0 : ℝ)..Real.pi / 2,
          Real.cos t ^ 4 * Real.sin t ^ 2 := by
  let f : ℝ → ℝ := fun t => b * Real.sin t ^ 2
  let f' : ℝ → ℝ := fun t => 2 * b * Real.sin t * Real.cos t
  let g : ℝ → ℝ := fun x => (b - x) * Real.sqrt (x * (b - x))
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt f (f' t) t := by
    intro t ht
    dsimp [f, f']
    convert (hasDerivAt_const t b).mul ((Real.hasDerivAt_sin t).pow 2)
      using 1 <;> ring
  have hf'cont : ContinuousOn f' (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    exact (by dsimp [f']; fun_prop : Continuous f').continuousOn
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := f) (f' := f') (g := g)
      hderiv hf'cont hgcont
  have hf0 : f 0 = 0 := by simp [f]
  have hfpi : f (Real.pi / 2) = b := by simp [f]
  rw [hf0, hfpi] at hsub
  have hpoint : ∀ t ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      (g ∘ f) t * f' t =
        2 * b ^ 3 * (Real.cos t ^ 4 * Real.sin t ^ 2) := by
    intro t ht
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at ht
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1
        (ht.2.trans (by linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc
        ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans ht.1,
          ht.2⟩
    have htrig : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    have hrad :
        Real.sqrt
          ((b * Real.sin t ^ 2) *
            (b - b * Real.sin t ^ 2)) =
          b * Real.sin t * Real.cos t := by
      have hinside :
          (b * Real.sin t ^ 2) *
            (b - b * Real.sin t ^ 2) =
            (b * Real.sin t * Real.cos t) ^ 2 := by
        calc
          _ = b ^ 2 * Real.sin t ^ 2 *
              (1 - Real.sin t ^ 2) := by ring
          _ = _ := by rw [htrig]; ring
      rw [hinside, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hb.le hsin) hcos)]
    dsimp [g, f, f', Function.comp_def]
    rw [hrad]
    have hdiff :
        b - b * Real.sin t ^ 2 = b * Real.cos t ^ 2 := by
      calc
        _ = b * (1 - Real.sin t ^ 2) := by ring
        _ = _ := by rw [htrig]
    rw [hdiff]
    ring
  calc
    (∫ x in (0 : ℝ)..b,
      (b - x) * Real.sqrt (x * (b - x))) =
        ∫ t in (0 : ℝ)..Real.pi / 2, (g ∘ f) t * f' t := by
          exact hsub.symm
    _ = ∫ t in (0 : ℝ)..Real.pi / 2,
        2 * b ^ 3 * (Real.cos t ^ 4 * Real.sin t ^ 2) := by
          apply intervalIntegral.integral_congr
          exact hpoint
    _ = _ := by rw [intervalIntegral.integral_const_mul]

theorem gap6 (b : ℝ) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b,
        (b - x) * Real.sqrt (x * (b - x))) =
      2 * b ^ 3 *
        ((∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 4) -
          ∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 6) := by
  rw [gap5 b hb]
  congr 1
  rw [← intervalIntegral.integral_sub
    ((Real.continuous_cos.pow 4).intervalIntegrable _ _)
    ((Real.continuous_cos.pow 6).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro t ht
  change
    Real.cos t ^ 4 * Real.sin t ^ 2 =
      Real.cos t ^ 4 - Real.cos t ^ 6
  rw [show Real.cos t ^ 4 * Real.sin t ^ 2 =
    Real.cos t ^ 4 - Real.cos t ^ 6 by
      rw [Real.sin_sq]
      ring]

private theorem cos4_value :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 4) =
      3 * Real.pi / 16 := by
  rw [show (4 : ℕ) = 2 + 2 by norm_num, integral_cos_pow]
  simp
  ring

private theorem cos6_value :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 6) =
      5 * Real.pi / 32 := by
  rw [show (6 : ℕ) = 4 + 2 by norm_num, integral_cos_pow,
    cos4_value]
  simp
  ring

theorem gap7 (b : ℝ) (hb : 0 < b) :
    2 * b ^ 3 *
        ((∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 4) -
          ∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 6) =
      Real.pi * b ^ 3 / 16 := by
  rw [cos4_value, cos6_value]
  ring

theorem gap8 (b : ℝ) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b,
        (b - x) * Real.sqrt (x * (b - x))) =
      Real.pi * b ^ 3 / 16 := by
  rw [gap6 b hb, gap7 b hb]

theorem gap9 (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a,
        (a - x) * Real.sqrt (x * (a - x))) =
      Real.pi * a ^ 3 / 16 := by
  exact gap8 a ha

theorem gap10 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    volume a b =
      4 / 3 * (Real.pi * b ^ 3 / 16 - Real.pi * a ^ 3 / 16) := by
  rw [gap4 a b ha hab, gap8 b (ha.trans hab), gap9 a ha]
  ring

theorem gap11 (a b : ℝ) :
    4 / 3 * (Real.pi * b ^ 3 / 16 - Real.pi * a ^ 3 / 16) =
      Real.pi / 12 * (b ^ 3 - a ^ 3) := by
  ring

theorem gap12 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    volume a b = Real.pi / 12 * (b ^ 3 - a ^ 3) := by
  rw [gap10 a b ha hab, gap11]

end

end ProofGap.Exercise4027
