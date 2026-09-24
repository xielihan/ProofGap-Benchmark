import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2981

noncomputable section

open scoped Interval

def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.cos ((n : ℝ) * x)

def sineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in -Real.pi..Real.pi, f x * Real.sin ((n : ℝ) * x)

def splitCosine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ((∫ x in -Real.pi..0, f x * Real.cos ((n : ℝ) * x)) +
      ∫ x in 0..Real.pi, f x * Real.cos ((n : ℝ) * x))

def reversedCosine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ((∫ x in 0..Real.pi, f x * Real.cos ((n : ℝ) * x)) +
      ∫ x in -Real.pi..0, f x * Real.cos ((n : ℝ) * x))

def splitSine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ((∫ x in -Real.pi..0, f x * Real.sin ((n : ℝ) * x)) +
      ∫ x in 0..Real.pi, f x * Real.sin ((n : ℝ) * x))

def reversedSine (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    (-(∫ x in 0..Real.pi, f x * Real.sin ((n : ℝ) * x)) -
      ∫ x in -Real.pi..0, f x * Real.sin ((n : ℝ) * x))

private theorem cosineIntegral_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x) (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, φ x * Real.cos ((n : ℝ) * x)) =
      ∫ x in -b..-a, ψ x * Real.cos ((n : ℝ) * x) := by
  calc
    (∫ x in a..b, φ x * Real.cos ((n : ℝ) * x)) =
        ∫ x in a..b,
          (fun y => ψ y * Real.cos ((n : ℝ) * y)) (-x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxrel : φ x = ψ (-x) := by
        simpa only [neg_neg] using hrel (-x)
      change φ x * Real.cos ((n : ℝ) * x) =
        ψ (-x) * Real.cos ((n : ℝ) * (-x))
      rw [← hxrel, mul_neg, Real.cos_neg]
    _ = ∫ x in -b..-a, ψ x * Real.cos ((n : ℝ) * x) := by
      exact intervalIntegral.integral_comp_neg
        (fun x => ψ x * Real.cos ((n : ℝ) * x))

private theorem sineIntegral_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x) (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, φ x * Real.sin ((n : ℝ) * x)) =
      -(∫ x in -b..-a, ψ x * Real.sin ((n : ℝ) * x)) := by
  apply neg_injective
  simp only [neg_neg]
  rw [← intervalIntegral.integral_neg]
  calc
    (∫ x in a..b, -(φ x * Real.sin ((n : ℝ) * x))) =
        ∫ x in a..b,
          (fun y => ψ y * Real.sin ((n : ℝ) * y)) (-x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxrel : φ x = ψ (-x) := by
        simpa only [neg_neg] using hrel (-x)
      change -(φ x * Real.sin ((n : ℝ) * x)) =
        ψ (-x) * Real.sin ((n : ℝ) * (-x))
      rw [← hxrel, mul_neg, Real.sin_neg]
      ring
    _ = ∫ x in -b..-a, ψ x * Real.sin ((n : ℝ) * x) := by
      exact intervalIntegral.integral_comp_neg
        (fun x => ψ x * Real.sin ((n : ℝ) * x))

private theorem cosineCoefficient_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x) (n : ℕ) :
    cosineCoefficient φ n = cosineCoefficient ψ n := by
  unfold cosineCoefficient
  rw [cosineIntegral_reflect φ ψ hrel n (-Real.pi) Real.pi]
  simp

private theorem sineCoefficient_reflect (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x) (n : ℕ) :
    sineCoefficient φ n = -sineCoefficient ψ n := by
  unfold sineCoefficient
  rw [sineIntegral_reflect φ ψ hrel n (-Real.pi) Real.pi]
  simp

theorem gap1 (φ : ℝ → ℝ) (c : ℕ → ℝ)
    (hc : ∀ n, c n = cosineCoefficient φ n) :
    ∀ n, c n = cosineCoefficient φ n := by
  exact hc

theorem gap2 (φ : ℝ → ℝ) (s : ℕ → ℝ)
    (hs : ∀ n, s n = sineCoefficient φ n) :
    ∀ n, 1 ≤ n → s n = sineCoefficient φ n := by
  intro n hn
  exact hs n

theorem gap3 (ψ : ℝ → ℝ) (α : ℕ → ℝ)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, α n = cosineCoefficient ψ n := by
  exact hα

theorem gap4 (ψ : ℝ → ℝ) (β : ℕ → ℝ)
    (hβ : ∀ n, β n = sineCoefficient ψ n) :
    ∀ n, 1 ≤ n → β n = sineCoefficient ψ n := by
  intro n hn
  exact hβ n

theorem gap5 (φ : ℝ → ℝ) (c : ℕ → ℝ)
    (hφ : IntervalIntegrable φ MeasureTheory.volume (-Real.pi) Real.pi)
    (hc : ∀ n, c n = cosineCoefficient φ n) :
    ∀ n, c n = splitCosine φ n := by
  intro n
  rw [hc n]
  have hint : IntervalIntegrable
      (fun x => φ x * Real.cos ((n : ℝ) * x)) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    hφ.mul_continuousOn (by fun_prop)
  have hzero : (0 : ℝ) ∈ [[-Real.pi, Real.pi]] :=
    Set.mem_uIcc_of_le (neg_nonpos.mpr Real.pi_pos.le) Real.pi_pos.le
  have hsplits := (IntervalIntegrable.trans_iff hzero).mp hint
  unfold cosineCoefficient splitCosine
  rw [intervalIntegral.integral_add_adjacent_intervals hsplits.1 hsplits.2]

theorem gap6 (φ ψ : ℝ → ℝ) (c : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x)
    (hψ : IntervalIntegrable ψ MeasureTheory.volume (-Real.pi) Real.pi)
    (hc : ∀ n, c n = cosineCoefficient φ n) :
    ∀ n, c n = reversedCosine ψ n := by
  intro n
  rw [hc n, cosineCoefficient_reflect φ ψ hrel n]
  have hint : IntervalIntegrable
      (fun x => ψ x * Real.cos ((n : ℝ) * x)) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    hψ.mul_continuousOn (by fun_prop)
  have hzero : (0 : ℝ) ∈ [[-Real.pi, Real.pi]] :=
    Set.mem_uIcc_of_le (neg_nonpos.mpr Real.pi_pos.le) Real.pi_pos.le
  have hsplits := (IntervalIntegrable.trans_iff hzero).mp hint
  unfold cosineCoefficient reversedCosine
  rw [add_comm,
    intervalIntegral.integral_add_adjacent_intervals hsplits.1 hsplits.2]

theorem gap7 (ψ : ℝ → ℝ)
    (hψ : IntervalIntegrable ψ MeasureTheory.volume (-Real.pi) Real.pi) :
    ∀ n, reversedCosine ψ n = cosineCoefficient ψ n := by
  intro n
  have hint : IntervalIntegrable
      (fun x => ψ x * Real.cos ((n : ℝ) * x)) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    hψ.mul_continuousOn (by fun_prop)
  have hzero : (0 : ℝ) ∈ [[-Real.pi, Real.pi]] :=
    Set.mem_uIcc_of_le (neg_nonpos.mpr Real.pi_pos.le) Real.pi_pos.le
  have hsplits := (IntervalIntegrable.trans_iff hzero).mp hint
  unfold reversedCosine cosineCoefficient
  rw [add_comm,
    intervalIntegral.integral_add_adjacent_intervals hsplits.1 hsplits.2]

theorem gap8 (ψ : ℝ → ℝ) (α : ℕ → ℝ)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, cosineCoefficient ψ n = α n := by
  intro n
  exact (hα n).symm

theorem gap9 (φ ψ : ℝ → ℝ) (c α : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x)
    (hc : ∀ n, c n = cosineCoefficient φ n)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, c n = α n := by
  intro n
  rw [hc n, hα n]
  exact cosineCoefficient_reflect φ ψ hrel n

theorem gap10 (φ : ℝ → ℝ) (s : ℕ → ℝ)
    (hφ : IntervalIntegrable φ MeasureTheory.volume (-Real.pi) Real.pi)
    (hs : ∀ n, s n = sineCoefficient φ n) :
    ∀ n, 1 ≤ n → s n = splitSine φ n := by
  intro n hn
  rw [hs n]
  have hint : IntervalIntegrable
      (fun x => φ x * Real.sin ((n : ℝ) * x)) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    hφ.mul_continuousOn (by fun_prop)
  have hzero : (0 : ℝ) ∈ [[-Real.pi, Real.pi]] :=
    Set.mem_uIcc_of_le (neg_nonpos.mpr Real.pi_pos.le) Real.pi_pos.le
  have hsplits := (IntervalIntegrable.trans_iff hzero).mp hint
  unfold sineCoefficient splitSine
  rw [intervalIntegral.integral_add_adjacent_intervals hsplits.1 hsplits.2]

theorem gap11 (φ ψ : ℝ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x) :
    ∀ n, 1 ≤ n → splitSine φ n = reversedSine ψ n := by
  intro n hn
  have hneg := sineIntegral_reflect φ ψ hrel n (-Real.pi) 0
  have hpos := sineIntegral_reflect φ ψ hrel n 0 Real.pi
  simp only [neg_zero, neg_neg] at hneg hpos
  unfold splitSine reversedSine
  rw [hneg, hpos]
  ring

theorem gap12 (ψ : ℝ → ℝ)
    (hψ : IntervalIntegrable ψ MeasureTheory.volume (-Real.pi) Real.pi) :
    ∀ n, 1 ≤ n →
      reversedSine ψ n = -sineCoefficient ψ n := by
  intro n hn
  have hint : IntervalIntegrable
      (fun x => ψ x * Real.sin ((n : ℝ) * x)) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    hψ.mul_continuousOn (by fun_prop)
  have hzero : (0 : ℝ) ∈ [[-Real.pi, Real.pi]] :=
    Set.mem_uIcc_of_le (neg_nonpos.mpr Real.pi_pos.le) Real.pi_pos.le
  have hsplits := (IntervalIntegrable.trans_iff hzero).mp hint
  unfold reversedSine sineCoefficient
  rw [← intervalIntegral.integral_add_adjacent_intervals hsplits.1 hsplits.2]
  ring

theorem gap13 (ψ : ℝ → ℝ) (β : ℕ → ℝ)
    (hβ : ∀ n, β n = sineCoefficient ψ n) :
    ∀ n, 1 ≤ n → -sineCoefficient ψ n = -β n := by
  intro n hn
  rw [hβ n]

theorem gap14 (φ ψ : ℝ → ℝ) (s β : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x)
    (hs : ∀ n, s n = sineCoefficient φ n)
    (hβ : ∀ n, β n = sineCoefficient ψ n) :
    ∀ n, 1 ≤ n → s n = -β n := by
  intro n hn
  rw [hs n, hβ n]
  exact sineCoefficient_reflect φ ψ hrel n

theorem gap15 (φ ψ : ℝ → ℝ) (c α : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x)
    (hc : ∀ n, c n = cosineCoefficient φ n)
    (hα : ∀ n, α n = cosineCoefficient ψ n) :
    ∀ n, c n = α n := by
  exact gap9 φ ψ c α hrel hc hα

theorem gap16 (φ ψ : ℝ → ℝ) (s β : ℕ → ℝ)
    (hrel : ∀ x, φ (-x) = ψ x)
    (hs : ∀ n, s n = sineCoefficient φ n)
    (hβ : ∀ n, β n = sineCoefficient ψ n) :
    ∀ n, 1 ≤ n → s n = -β n := by
  exact gap14 φ ψ s β hrel hs hβ

end

end ProofGap.Exercise2981
