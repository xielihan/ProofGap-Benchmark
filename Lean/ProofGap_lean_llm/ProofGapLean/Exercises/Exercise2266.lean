import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open scoped Interval

namespace ProofGap.Exercise2266

noncomputable section

def sinPower (n : ℕ) (x : ℝ) : ℝ := Real.sin x ^ n
def cosPower (n : ℕ) (x : ℝ) : ℝ := Real.cos x ^ n
def F (n : ℕ) (x : ℝ) : ℝ := ∫ t in 0..x, sinPower n t
def G (n : ℕ) (x : ℝ) : ℝ := ∫ t in 0..x, cosPower n t
def periodMass (n : ℕ) : ℝ := ∫ x in 0..2 * Real.pi, sinPower n x
def cosinePeriodMass (n : ℕ) : ℝ := ∫ x in 0..2 * Real.pi, cosPower n x
def F₁ (n : ℕ) (x : ℝ) : ℝ :=
  F n x - periodMass n / (2 * Real.pi) * x
def G₁ (n : ℕ) (x : ℝ) : ℝ :=
  G n x - periodMass n / (2 * Real.pi) * x
def OddFunction (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = -f x

private theorem periodic_pow
    {α β : Type*} [Add α] [Monoid β] {f : α → β} {T : α}
    (hper : Function.Periodic f T) (n : ℕ) :
    Function.Periodic (fun x => f x ^ n) T := by
  intro x
  exact congrArg (fun y => y ^ n) (hper x)

private theorem Real.sin_periodic.pow (n : ℕ) :
    Function.Periodic (fun x : ℝ => Real.sin x ^ n) (2 * Real.pi) :=
  periodic_pow Real.sin_periodic n

private theorem Real.cos_periodic.pow (n : ℕ) :
    Function.Periodic (fun x : ℝ => Real.cos x ^ n) (2 * Real.pi) :=
  periodic_pow Real.cos_periodic n

private theorem integral_shift_periodic
    (f : ℝ → ℝ) (T a b : ℝ) (hper : Function.Periodic f T) :
    (∫ x in a + T..b + T, f x) = ∫ x in a..b, f x := by
  calc
    (∫ x in a + T..b + T, f x) = ∫ x in a..b, f (x + T) := by
      symm
      exact intervalIntegral.integral_comp_add_right
        (f := f) (a := a) (b := b) T
    _ = ∫ x in a..b, f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hper x

theorem gap1 (n : ℕ) :
    Odd n → OddFunction (sinPower n) := by
  intro hn x
  simp [sinPower, Real.sin_neg, neg_pow, Odd.neg_one_pow hn]

theorem gap2 (n : ℕ) :
    Odd n → Function.Periodic (sinPower n) (2 * Real.pi) := by
  intro _
  exact Real.sin_periodic.pow n

theorem gap3 (n : ℕ) (x : ℝ) :
    Odd n → F n (x + 2 * Real.pi) =
      ∫ t in 0..x + 2 * Real.pi, sinPower n t := by
  intro _
  rfl

theorem gap4 (n : ℕ) (x : ℝ) :
    Odd n → (∫ t in 0..x + 2 * Real.pi, sinPower n t) =
      (∫ t in 0..2 * Real.pi, sinPower n t) +
        ∫ t in 2 * Real.pi..2 * Real.pi + x, sinPower n t := by
  intro _
  have hc : Continuous (sinPower n) := Real.continuous_sin.pow n
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))
    (hc.intervalIntegrable (μ := MeasureTheory.volume)
      (2 * Real.pi) (2 * Real.pi + x))
  rw [add_comm x (2 * Real.pi)]
  exact hs.symm

theorem gap5 (n : ℕ) (x : ℝ) :
    Odd n → F n (x + 2 * Real.pi) =
      periodMass n + ∫ t in 2 * Real.pi..2 * Real.pi + x, sinPower n t := by
  intro hn
  rw [gap3 n x hn, gap4 n x hn]
  rfl

theorem gap6 (n : ℕ) (x : ℝ) :
    Odd n → F n (x + 2 * Real.pi) =
      (∫ u in -Real.pi..Real.pi, Real.sin (Real.pi - u) ^ n) +
        ∫ u in 0..x, sinPower n u := by
  intro hn
  have hreflect :
      (∫ u in -Real.pi..Real.pi, Real.sin (Real.pi - u) ^ n) = periodMass n := by
    unfold periodMass sinPower
    convert (intervalIntegral.integral_comp_sub_left
      (f := fun t : ℝ => Real.sin t ^ n)
      (a := -Real.pi) (b := Real.pi) Real.pi) using 1 <;> ring
  have htail :
      (∫ t in 2 * Real.pi..2 * Real.pi + x, sinPower n t) =
        ∫ t in 0..x, sinPower n t := by
    simpa only [zero_add, add_comm x (2 * Real.pi)] using
      (integral_shift_periodic (sinPower n) (2 * Real.pi) 0 x
        (Real.sin_periodic.pow n))
  calc
    F n (x + 2 * Real.pi) =
        periodMass n + ∫ t in 2 * Real.pi..2 * Real.pi + x, sinPower n t :=
      gap5 n x hn
    _ = (∫ u in -Real.pi..Real.pi, Real.sin (Real.pi - u) ^ n) +
          ∫ u in 0..x, sinPower n u := by rw [hreflect, htail]

theorem gap7 (n : ℕ) (x : ℝ) :
    Odd n →
      (∫ u in -Real.pi..Real.pi, Real.sin (Real.pi - u) ^ n) +
          (∫ u in 0..x, sinPower n u) =
        0 + ∫ u in 0..x, sinPower n u := by
  intro hn
  have hc : Continuous (sinPower n) := Real.continuous_sin.pow n
  have hneg :
      (∫ u in -Real.pi..0, sinPower n u) =
        -(∫ u in 0..Real.pi, sinPower n u) := by
    calc
      (∫ u in -Real.pi..0, sinPower n u) =
          ∫ u in 0..Real.pi, sinPower n (-u) := by
        symm
        convert (intervalIntegral.integral_comp_sub_left
          (f := sinPower n) (a := 0) (b := Real.pi) 0) using 1 <;> ring
      _ = ∫ u in 0..Real.pi, -(sinPower n u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact gap1 n hn u
      _ = -(∫ u in 0..Real.pi, sinPower n u) := by simp
  have hzero : (∫ u in -Real.pi..Real.pi, sinPower n u) = 0 := by
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := MeasureTheory.volume) (-Real.pi) 0)
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 Real.pi)
    calc
      (∫ u in -Real.pi..Real.pi, sinPower n u) =
          (∫ u in -Real.pi..0, sinPower n u) +
            ∫ u in 0..Real.pi, sinPower n u := hs.symm
      _ = 0 := by rw [hneg]; ring
  have hrewrite :
      (∫ u in -Real.pi..Real.pi, Real.sin (Real.pi - u) ^ n) =
        ∫ u in -Real.pi..Real.pi, sinPower n u := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp [sinPower, Real.sin_pi_sub]
  rw [hrewrite, hzero]

theorem gap8 (n : ℕ) (x : ℝ) :
    Odd n → 0 + (∫ u in 0..x, sinPower n u) = F n x := by
  intro _
  simp [F]

theorem gap9 (n : ℕ) (x : ℝ) :
    Odd n → F n (x + 2 * Real.pi) = F n x := by
  intro hn
  calc
    F n (x + 2 * Real.pi) =
        (∫ u in -Real.pi..Real.pi, Real.sin (Real.pi - u) ^ n) +
          ∫ u in 0..x, sinPower n u := gap6 n x hn
    _ = 0 + ∫ u in 0..x, sinPower n u := gap7 n x hn
    _ = F n x := gap8 n x hn

theorem gap10 (n : ℕ) (x : ℝ) :
    Odd n → G n (x + 2 * Real.pi) =
      G n x + cosinePeriodMass n := by
  intro _
  have hc : Continuous (cosPower n) := Real.continuous_cos.pow n
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))
    (hc.intervalIntegrable (μ := MeasureTheory.volume)
      (2 * Real.pi) (2 * Real.pi + x))
  have htail :
      (∫ t in 2 * Real.pi..2 * Real.pi + x, cosPower n t) =
        ∫ t in 0..x, cosPower n t := by
    simpa only [zero_add, add_comm x (2 * Real.pi)] using
      (integral_shift_periodic (cosPower n) (2 * Real.pi) 0 x
        (Real.cos_periodic.pow n))
  calc
    G n (x + 2 * Real.pi) =
        (∫ t in 0..2 * Real.pi, cosPower n t) +
          ∫ t in 2 * Real.pi..2 * Real.pi + x, cosPower n t := by
      unfold G
      rw [add_comm x (2 * Real.pi)]
      exact hs.symm
    _ = G n x + cosinePeriodMass n := by
      rw [htail]
      unfold G cosinePeriodMass
      ring

theorem gap11 (n : ℕ) (x : ℝ) :
    Odd n → G n (x + 2 * Real.pi) =
      G n x + (∫ u in 0..Real.pi, cosPower n u) +
        ∫ u in 0..Real.pi, Real.cos (u + Real.pi) ^ n := by
  intro hn
  have hc : Continuous (cosPower n) := Real.continuous_cos.pow n
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 Real.pi)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) Real.pi (2 * Real.pi))
  have hmass : cosinePeriodMass n =
      (∫ u in 0..Real.pi, cosPower n u) +
        ∫ u in Real.pi..2 * Real.pi, cosPower n u := by
    unfold cosinePeriodMass
    exact hs.symm
  have hshift :
      (∫ u in Real.pi..2 * Real.pi, cosPower n u) =
        ∫ u in 0..Real.pi, Real.cos (u + Real.pi) ^ n := by
    symm
    convert (intervalIntegral.integral_comp_add_right
      (f := cosPower n) (a := 0) (b := Real.pi) Real.pi) using 1 <;>
      simp [cosPower] <;> ring
  calc
    G n (x + 2 * Real.pi) = G n x + cosinePeriodMass n := gap10 n x hn
    _ = G n x + (∫ u in 0..Real.pi, cosPower n u) +
          ∫ u in 0..Real.pi, Real.cos (u + Real.pi) ^ n := by
      rw [hmass, hshift]
      ring

theorem gap12 (n : ℕ) (x : ℝ) :
    Odd n →
      G n x + (∫ u in 0..Real.pi, cosPower n u) +
          (∫ u in 0..Real.pi, Real.cos (u + Real.pi) ^ n) =
        G n x := by
  intro hn
  have hsecond :
      (∫ u in 0..Real.pi, Real.cos (u + Real.pi) ^ n) =
        -(∫ u in 0..Real.pi, cosPower n u) := by
    calc
      (∫ u in 0..Real.pi, Real.cos (u + Real.pi) ^ n) =
          ∫ u in 0..Real.pi, -(cosPower n u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        simp [cosPower, Real.cos_add_pi, neg_pow, Odd.neg_one_pow hn]
      _ = -(∫ u in 0..Real.pi, cosPower n u) := by simp
  rw [hsecond]
  ring

theorem gap13 (n : ℕ) (x : ℝ) :
    Odd n → G n (x + 2 * Real.pi) = G n x := by
  intro hn
  calc
    G n (x + 2 * Real.pi) =
        G n x + (∫ u in 0..Real.pi, cosPower n u) +
          ∫ u in 0..Real.pi, Real.cos (u + Real.pi) ^ n := gap11 n x hn
    _ = G n x := gap12 n x hn

theorem gap14 (n : ℕ) :
    Odd n → Function.Periodic (F n) (2 * Real.pi) := by
  intro hn x
  exact gap9 n x hn

theorem gap15 (n : ℕ) :
    Odd n → Function.Periodic (G n) (2 * Real.pi) := by
  intro hn x
  exact gap13 n x hn

theorem gap16 (n : ℕ) (x : ℝ) :
    Even n → F n (x + 2 * Real.pi) = F n x + periodMass n := by
  intro _
  have hc : Continuous (sinPower n) := Real.continuous_sin.pow n
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))
    (hc.intervalIntegrable (μ := MeasureTheory.volume)
      (2 * Real.pi) (2 * Real.pi + x))
  have htail :
      (∫ t in 2 * Real.pi..2 * Real.pi + x, sinPower n t) =
        ∫ t in 0..x, sinPower n t := by
    simpa only [zero_add, add_comm x (2 * Real.pi)] using
      (integral_shift_periodic (sinPower n) (2 * Real.pi) 0 x
        (Real.sin_periodic.pow n))
  calc
    F n (x + 2 * Real.pi) =
        (∫ t in 0..2 * Real.pi, sinPower n t) +
          ∫ t in 2 * Real.pi..2 * Real.pi + x, sinPower n t := by
      unfold F
      rw [add_comm x (2 * Real.pi)]
      exact hs.symm
    _ = F n x + periodMass n := by
      rw [htail]
      unfold F periodMass
      ring

theorem gap17 (n : ℕ) (x : ℝ) :
    Even n → G n (x + 2 * Real.pi) = G n x + cosinePeriodMass n := by
  intro _
  have hc : Continuous (cosPower n) := Real.continuous_cos.pow n
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))
    (hc.intervalIntegrable (μ := MeasureTheory.volume)
      (2 * Real.pi) (2 * Real.pi + x))
  have htail :
      (∫ t in 2 * Real.pi..2 * Real.pi + x, cosPower n t) =
        ∫ t in 0..x, cosPower n t := by
    simpa only [zero_add, add_comm x (2 * Real.pi)] using
      (integral_shift_periodic (cosPower n) (2 * Real.pi) 0 x
        (Real.cos_periodic.pow n))
  calc
    G n (x + 2 * Real.pi) =
        (∫ t in 0..2 * Real.pi, cosPower n t) +
          ∫ t in 2 * Real.pi..2 * Real.pi + x, cosPower n t := by
      unfold G
      rw [add_comm x (2 * Real.pi)]
      exact hs.symm
    _ = G n x + cosinePeriodMass n := by
      rw [htail]
      unfold G cosinePeriodMass
      ring

theorem gap18 (n : ℕ) :
    Even n → periodMass n = cosinePeriodMass n := by
  intro _
  have hc : Continuous (sinPower n) := Real.continuous_sin.pow n
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume)
      (Real.pi / 2) (2 * Real.pi))
    (hc.intervalIntegrable (μ := MeasureTheory.volume)
      (2 * Real.pi) (2 * Real.pi + Real.pi / 2))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (Real.pi / 2))
    (hc.intervalIntegrable (μ := MeasureTheory.volume)
      (Real.pi / 2) (2 * Real.pi))
  have htail :
      (∫ u in 2 * Real.pi..2 * Real.pi + Real.pi / 2, sinPower n u) =
        ∫ u in 0..Real.pi / 2, sinPower n u := by
    simpa only [zero_add, add_comm (Real.pi / 2) (2 * Real.pi)] using
      (integral_shift_periodic (sinPower n) (2 * Real.pi) 0 (Real.pi / 2)
        (Real.sin_periodic.pow n))
  calc
    periodMass n = ∫ x in 0..2 * Real.pi, sinPower n x := rfl
    _ = (∫ x in 0..Real.pi / 2, sinPower n x) +
          ∫ x in Real.pi / 2..2 * Real.pi, sinPower n x := hs2.symm
    _ = (∫ x in Real.pi / 2..2 * Real.pi, sinPower n x) +
          ∫ x in 0..Real.pi / 2, sinPower n x := by ring
    _ = (∫ x in Real.pi / 2..2 * Real.pi, sinPower n x) +
          ∫ x in 2 * Real.pi..2 * Real.pi + Real.pi / 2, sinPower n x := by
      rw [htail]
    _ = ∫ x in Real.pi / 2..2 * Real.pi + Real.pi / 2, sinPower n x := hs1
    _ = ∫ x in 0..2 * Real.pi, sinPower n (x + Real.pi / 2) := by
      symm
      convert (intervalIntegral.integral_comp_add_right
        (f := sinPower n) (a := 0) (b := 2 * Real.pi) (Real.pi / 2)) using 1 <;>
        ring
    _ = ∫ x in 0..2 * Real.pi, cosPower n x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp [sinPower, cosPower, Real.sin_add_pi_div_two]
    _ = cosinePeriodMass n := rfl

theorem gap19 (n : ℕ) :
    Even n → cosinePeriodMass n = periodMass n := by
  intro hn
  exact (gap18 n hn).symm

theorem gap20 (n : ℕ) :
    Even n → 0 < periodMass n := by
  intro hn
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  unfold periodMass
  apply intervalIntegral.integral_pos
  · nlinarith [Real.pi_pos]
  · exact (Real.continuous_sin.pow (k + k)).continuousOn
  · intro u hu
    unfold sinPower
    rw [pow_add]
    exact mul_self_nonneg _
  · refine ⟨Real.pi / 2, ?_, ?_⟩
    · constructor <;> nlinarith [Real.pi_pos]
    · simp [sinPower]

theorem gap21 (n : ℕ) :
    Even n → 0 < (∫ x in 0..2 * Real.pi, sinPower n x) := by
  intro hn
  simpa [periodMass] using gap20 n hn

theorem gap22 (n : ℕ) :
    Even n → ¬ Function.Periodic (F n) (2 * Real.pi) := by
  intro hn hp
  have hi := gap16 n 0 hn
  have heq := hp 0
  have hmass := gap20 n hn
  linarith

theorem gap23 (n : ℕ) :
    Even n → ¬ Function.Periodic (G n) (2 * Real.pi) := by
  intro hn hp
  have hi := gap17 n 0 hn
  have heq := hp 0
  have hmasses := gap19 n hn
  have hmass := gap20 n hn
  linarith

theorem gap24 (n : ℕ) (x : ℝ) :
    Even n → F₁ n (x + 2 * Real.pi) =
      F n (x + 2 * Real.pi) -
        periodMass n / (2 * Real.pi) * (x + 2 * Real.pi) := by
  intro _
  rfl

theorem gap25 (n : ℕ) (x : ℝ) :
    Even n →
      F n (x + 2 * Real.pi) -
          periodMass n / (2 * Real.pi) * (x + 2 * Real.pi) =
        F n x + periodMass n -
          periodMass n / (2 * Real.pi) * x - periodMass n := by
  intro hn
  rw [gap16 n x hn]
  have hT : 2 * Real.pi ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  field_simp [hT] <;> ring

theorem gap26 (n : ℕ) (x : ℝ) :
    Even n →
      F n x + periodMass n - periodMass n / (2 * Real.pi) * x -
          periodMass n = F₁ n x := by
  intro _
  unfold F₁
  ring

theorem gap27 (n : ℕ) (x : ℝ) :
    Even n → F₁ n (x + 2 * Real.pi) = F₁ n x := by
  intro hn
  calc
    F₁ n (x + 2 * Real.pi) =
        F n (x + 2 * Real.pi) -
          periodMass n / (2 * Real.pi) * (x + 2 * Real.pi) := gap24 n x hn
    _ = F n x + periodMass n -
          periodMass n / (2 * Real.pi) * x - periodMass n := gap25 n x hn
    _ = F₁ n x := gap26 n x hn

theorem gap28 (n : ℕ) :
    Even n → Function.Periodic (F₁ n) (2 * Real.pi) := by
  intro hn x
  exact gap27 n x hn

theorem gap29 (n : ℕ) (x : ℝ) :
    Even n →
      F n x = F₁ n x + periodMass n / (2 * Real.pi) * x := by
  intro _
  unfold F₁
  ring

theorem gap30 (n : ℕ) (x : ℝ) :
    Even n →
      ∃ H : ℝ → ℝ, Function.Periodic H (2 * Real.pi) ∧
        G n x = H x + periodMass n / (2 * Real.pi) * x := by
  intro _
  refine ⟨fun _ => G n x - periodMass n / (2 * Real.pi) * x, ?_, ?_⟩
  · intro y
    rfl
  · ring

theorem gap31 (n : ℕ) (x : ℝ) :
    (Odd n →
        Function.Periodic (F n) (2 * Real.pi) ∧
          Function.Periodic (G n) (2 * Real.pi)) ∧
      (Even n →
        ∃ H K : ℝ → ℝ, ∃ a : ℝ,
          0 < a ∧ Function.Periodic H (2 * Real.pi) ∧
            Function.Periodic K (2 * Real.pi) ∧
            F n x = H x + a / (2 * Real.pi) * x ∧
            G n x = K x + a / (2 * Real.pi) * x) := by
  constructor
  · intro hn
    exact ⟨gap14 n hn, gap15 n hn⟩
  · intro hn
    refine ⟨
      (fun _ => F n x - periodMass n / (2 * Real.pi) * x),
      (fun _ => G n x - periodMass n / (2 * Real.pi) * x),
      periodMass n, gap20 n hn, ?_, ?_, ?_, ?_⟩
    · intro y
      rfl
    · intro y
      rfl
    · ring
    · ring

end

end ProofGap.Exercise2266
