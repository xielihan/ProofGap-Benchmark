import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4205

noncomputable section

open MeasureTheory
open scoped Interval

def simplex (n : ℕ) (a : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ a}

def simplexVolume (n : ℕ) (a : ℝ) : ℝ :=
  ∫ _x in simplex n a, (1 : ℝ)

def iteratedSimplexVolume : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, a =>
      ∫ x in (0 : ℝ)..a, iteratedSimplexVolume n (a - x)

private abbrev Vec (n : ℕ) := Fin n → ℝ

private def splitSimplex (n : ℕ) (a : ℝ) :
    Set (ℝ × Vec n) :=
  {z | 0 ≤ z.1 ∧
    (∀ i, 0 ≤ z.2 i) ∧
    z.1 + ∑ i, z.2 i ≤ a}

private theorem measurableSet_splitSimplex
    (n : ℕ) (a : ℝ) :
    MeasurableSet (splitSimplex n a) := by
  unfold splitSimplex
  measurability

private theorem splitSimplex_preimage
    (n : ℕ) (a : ℝ) :
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
        splitSimplex n a =
      simplex (n + 1) a := by
  ext v
  simp only [splitSimplex, simplex, Set.mem_preimage,
    Set.mem_setOf_eq, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.sum_univ_succ]
  constructor
  · rintro ⟨hzero, htail, hsum⟩
    refine ⟨?_, hsum⟩
    intro i
    refine Fin.cases hzero (fun j => ?_) i
    simpa using htail j
  · rintro ⟨hall, hsum⟩
    exact ⟨hall 0, fun i => hall i.succ, hsum⟩

private theorem splitSimplex_fiber
    (n : ℕ) (a x : ℝ) :
    Prod.mk x ⁻¹' splitSimplex n a =
      if 0 ≤ x then simplex n (a - x) else ∅ := by
  ext v
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    simp only [splitSimplex, simplex,
      Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, hv, hsum⟩
      exact ⟨hv, by linarith⟩
    · rintro ⟨hv, hsum⟩
      exact ⟨hx, hv, by linarith⟩
  · simp [splitSimplex, hx]

private theorem simplex_eq_empty_of_neg
    (n : ℕ) {a : ℝ} (ha : a < 0) :
    simplex n a = ∅ := by
  ext v
  simp only [simplex, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨hv, hsum⟩
  have hnonneg :
      0 ≤ ∑ i, v i :=
    Finset.sum_nonneg fun i _ => hv i
  linarith

private theorem power_slice_integral
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) a,
        (a - x) ^ n / (n.factorial : ℝ)) =
      a ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ha]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => x ^ n) a]
  simp only [sub_self, sub_zero, integral_pow,
    zero_pow (Nat.succ_ne_zero n)]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

private theorem power_slice_integrable
    (n : ℕ) (a : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        (a - x) ^ n / (n.factorial : ℝ))
      (Set.Icc (0 : ℝ) a) volume := by
  apply Continuous.integrableOn_Icc
  fun_prop

private theorem simplex_volume_ennreal :
    ∀ (n : ℕ) (a : ℝ), 0 ≤ a →
      volume (simplex n a) =
        ENNReal.ofReal
          (a ^ n / (n.factorial : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro a ha
      have hs : simplex 0 a = Set.univ := by
        ext v
        simp [simplex, ha]
      rw [hs]
      simp [MeasureTheory.volume_pi]
  | succ n ih =>
      intro a ha
      let e :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0
      have he :
          MeasurePreserving e :=
        volume_preserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0
      have hsplit :
          volume (simplex (n + 1) a) =
            ((volume : Measure ℝ).prod
              (volume : Measure (Vec n)))
              (splitSimplex n a) := by
        rw [← splitSimplex_preimage]
        exact he.measure_preimage
          (measurableSet_splitSimplex n a).nullMeasurableSet
      rw [hsplit,
        Measure.prod_apply
          (measurableSet_splitSimplex n a)]
      have hpoint (x : ℝ) :
          volume
              (Prod.mk x ⁻¹'
                splitSimplex n a) =
            (Set.Icc (0 : ℝ) a).indicator
              (fun x =>
                ENNReal.ofReal
                  ((a - x) ^ n /
                    (n.factorial : ℝ))) x := by
        rw [splitSimplex_fiber]
        by_cases hx : x ∈ Set.Icc (0 : ℝ) a
        · rw [if_pos hx.1, Set.indicator_of_mem hx,
            ih (a - x) (sub_nonneg.mpr hx.2)]
        · rw [Set.indicator_of_notMem hx]
          by_cases hx0 : 0 ≤ x
          · rw [if_pos hx0]
            have hxa : a < x := by
              by_contra h
              exact hx ⟨hx0, le_of_not_gt h⟩
            rw [simplex_eq_empty_of_neg n
              (sub_neg.mpr hxa)]
            simp
          · rw [if_neg hx0]
            simp
      simp_rw [hpoint]
      rw [lintegral_indicator measurableSet_Icc]
      have hnonneg :
          0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) a)]
            (fun x : ℝ =>
              (a - x) ^ n /
                (n.factorial : ℝ)) := by
        filter_upwards [
          ae_restrict_mem measurableSet_Icc] with x hx
        exact div_nonneg
          (pow_nonneg (sub_nonneg.mpr hx.2) n)
          (Nat.cast_nonneg _)
      rw [← ofReal_integral_eq_lintegral_ofReal
        (power_slice_integrable n a) hnonneg]
      rw [power_slice_integral n a ha]

private theorem simplexVolume_formula
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    simplexVolume n a =
      a ^ n / (Nat.factorial n : ℝ) := by
  unfold simplexVolume
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [Measure.real_def, simplex_volume_ennreal n a ha]
  rw [ENNReal.toReal_ofReal]
  exact div_nonneg (pow_nonneg ha n) (Nat.cast_nonneg _)

private theorem power_interval_integral
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (0 : ℝ)..a,
        (a - x) ^ n / (Nat.factorial n : ℝ)) =
      a ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  have h := power_slice_integral n a ha
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ha] at h
  exact h

private theorem iteratedSimplexVolume_formula :
    ∀ (n : ℕ) (a : ℝ), 0 ≤ a →
      iteratedSimplexVolume n a =
        a ^ n / (Nat.factorial n : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro a ha
      simp [iteratedSimplexVolume]
  | succ n ih =>
      intro a ha
      rw [iteratedSimplexVolume]
      calc
        (∫ x in (0 : ℝ)..a,
            iteratedSimplexVolume n (a - x)) =
            ∫ x in (0 : ℝ)..a,
              (a - x) ^ n / (Nat.factorial n : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le ha] at hx
          exact ih (a - x) (sub_nonneg.mpr hx.2)
        _ = a ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
          power_interval_integral n a ha

theorem gap1 (n : ℕ) (a : ℝ) :
    simplexVolume n a =
      ∫ x in simplex n a, (1 : ℝ) := by
  rfl

theorem gap2 (n : ℕ) (a : ℝ) (ha : 0 < a) :
    simplexVolume n a = iteratedSimplexVolume n a := by
  rw [simplexVolume_formula n a ha.le,
    iteratedSimplexVolume_formula n a ha.le]

theorem gap3 (b : ℝ) (hb : 0 ≤ b) :
    iteratedSimplexVolume 2 b = (1 / 2 : ℝ) * b ^ 2 := by
  rw [iteratedSimplexVolume_formula 2 b hb]
  norm_num [Nat.factorial]
  ring

theorem gap4 (b : ℝ) (hb : 0 ≤ b) :
    iteratedSimplexVolume 3 b =
      (1 / (Nat.factorial 3 : ℝ)) * b ^ 3 := by
  rw [iteratedSimplexVolume_formula 3 b hb]
  ring

theorem gap5
    (n : ℕ) (hn : 1 ≤ n) (a x : ℝ)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    iteratedSimplexVolume (n - 1) (a - x) =
      (a - x) ^ (n - 1) /
        (Nat.factorial (n - 1) : ℝ) := by
  exact iteratedSimplexVolume_formula (n - 1) (a - x)
    (sub_nonneg.mpr hxa)

theorem gap6 (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) :
    iteratedSimplexVolume n a =
      ∫ x in (0 : ℝ)..a,
        (a - x) ^ (n - 1) /
          (Nat.factorial (n - 1) : ℝ) := by
  cases n with
  | zero =>
      exact (Nat.not_succ_le_zero 0 hn).elim
  | succ m =>
      rw [iteratedSimplexVolume]
      apply intervalIntegral.integral_congr
      intro x hxmem
      rw [Set.uIcc_of_le ha.le] at hxmem
      simpa using gap5 (m + 1) (by simp) a x hxmem.1 hxmem.2

theorem gap7 (n : ℕ) (a : ℝ) (ha : 0 < a) :
    simplexVolume n a =
      a ^ n / (Nat.factorial n : ℝ) := by
  exact simplexVolume_formula n a ha.le

end

end ProofGap.Exercise4205
