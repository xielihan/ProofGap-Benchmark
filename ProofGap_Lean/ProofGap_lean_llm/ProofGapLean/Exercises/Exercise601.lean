import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise601

noncomputable section

def f (x : ℝ) : ℝ := Real.sign (Real.sin (Real.pi * x))
def paritySign (n : ℤ) : ℝ := if Even n then 1 else -1
def leftFilter (n : ℤ) : Filter ℝ := nhdsWithin (n : ℝ) (Set.Iio n)
def rightFilter (n : ℤ) : Filter ℝ := nhdsWithin (n : ℝ) (Set.Ioi n)

/-- Exercise 601, gap 1. -/
private theorem oneSidedSignLimits (n : ℤ) :
    Filter.Tendsto (fun x => Real.sign (Real.sin (Real.pi * x)))
        (leftFilter n) (nhds (paritySign (n - 1))) ∧
      Filter.Tendsto (fun x => Real.sign (Real.sin (Real.pi * x)))
        (rightFilter n) (nhds (paritySign n)) := by
  have parityCos (m : ℤ) :
      Real.cos ((m : ℝ) * Real.pi) = paritySign m := by
    rw [Real.cos_int_mul_pi]
    obtain hm | hm := Int.even_or_odd m
    · rw [paritySign, if_pos hm]
      rcases hm with ⟨k, hk⟩
      have hk' : m = k + k := by
        simpa [two_mul] using hk
      calc
        (-1 : ℝ) ^ m = (-1 : ℝ) ^ (k + k) := by rw [hk']
        _ = (-1 : ℝ) ^ k * (-1 : ℝ) ^ k := by
          rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
        _ = ((-1 : ℝ) * -1) ^ k := by
          rw [mul_zpow]
        _ = 1 := by norm_num
    · have hne : ¬Even m := by
        intro he
        rcases he with ⟨a, ha⟩
        rcases hm with ⟨b, hb⟩
        omega
      rw [paritySign, if_neg hne]
      rcases hm with ⟨k, hk⟩
      have hk' : m = k + k + 1 := by
        simpa [two_mul] using hk
      calc
        (-1 : ℝ) ^ m = (-1 : ℝ) ^ (k + k + 1) := by rw [hk']
        _ = (-1 : ℝ) ^ (k + k) * (-1 : ℝ) ^ (1 : ℤ) := by
          rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
        _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
              (-1 : ℝ) ^ (1 : ℤ) := by
          rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
        _ = ((-1 : ℝ) * -1) ^ k * (-1 : ℝ) ^ (1 : ℤ) := by
          rw [mul_zpow]
        _ = -1 := by norm_num
  have hsinInt : Real.sin ((n : ℝ) * Real.pi) = 0 := by
    exact Real.sin_int_mul_pi n
  have hshift (x : ℝ) :
      Real.sin (Real.pi * x) =
        paritySign n * Real.sin (Real.pi * (x - (n : ℝ))) := by
    calc
      Real.sin (Real.pi * x) =
          Real.sin ((n : ℝ) * Real.pi + Real.pi * (x - (n : ℝ))) := by
            congr 1
            ring
      _ = Real.sin ((n : ℝ) * Real.pi) *
            Real.cos (Real.pi * (x - (n : ℝ))) +
          Real.cos ((n : ℝ) * Real.pi) *
            Real.sin (Real.pi * (x - (n : ℝ))) := by
            rw [Real.sin_add]
      _ = paritySign n * Real.sin (Real.pi * (x - (n : ℝ))) := by
            rw [hsinInt, parityCos]
            ring
  have hprev : paritySign (n - 1) = -paritySign n := by
    have hrel :
        Real.cos (((n - 1 : ℤ) : ℝ) * Real.pi) =
          -Real.cos ((n : ℝ) * Real.pi) := by
      calc
        Real.cos (((n - 1 : ℤ) : ℝ) * Real.pi) =
            Real.cos ((n : ℝ) * Real.pi - Real.pi) := by
              congr 1
              rw [Int.cast_sub, Int.cast_one]
              ring
        _ = Real.cos ((n : ℝ) * Real.pi) * Real.cos Real.pi +
              Real.sin ((n : ℝ) * Real.pi) * Real.sin Real.pi := by
              rw [Real.cos_sub]
        _ = -Real.cos ((n : ℝ) * Real.pi) := by
              rw [Real.cos_pi, Real.sin_pi]
              ring
    rw [parityCos (n - 1), parityCos n] at hrel
    exact hrel
  have hleft :
      (fun x : ℝ => Real.sign (Real.sin (Real.pi * x))) =ᶠ[leftFilter n]
        (fun _ : ℝ => paritySign (n - 1)) := by
    have hlower : ∀ᶠ x : ℝ in leftFilter n, (n : ℝ) - 1 < x := by
      have h : ∀ᶠ x : ℝ in nhds (n : ℝ), (n : ℝ) - 1 < x :=
        Ioi_mem_nhds (by linarith)
      exact h.filter_mono (by
        rw [leftFilter]
        exact inf_le_left)
    have hupper : ∀ᶠ x : ℝ in leftFilter n, x < (n : ℝ) := by
      simpa [leftFilter] using
        (self_mem_nhdsWithin :
          Set.Iio (n : ℝ) ∈ nhdsWithin (n : ℝ) (Set.Iio (n : ℝ)))
    filter_upwards [hlower, hupper] with x hxLower hxUpper
    have htPos : 0 < Real.pi * ((n : ℝ) - x) :=
      mul_pos Real.pi_pos (sub_pos.mpr hxUpper)
    have htLt : Real.pi * ((n : ℝ) - x) < Real.pi := by
      nlinarith [Real.pi_pos]
    have hsPos : 0 < Real.sin (Real.pi * ((n : ℝ) - x)) :=
      Real.sin_pos_of_pos_of_lt_pi htPos htLt
    have hsNeg : Real.sin (Real.pi * (x - (n : ℝ))) < 0 := by
      have harg : Real.pi * (x - (n : ℝ)) =
          -(Real.pi * ((n : ℝ) - x)) := by ring
      rw [harg, Real.sin_neg]
      exact neg_neg_of_pos hsPos
    rw [hshift x, hprev]
    by_cases hn : Even n
    · rw [paritySign, if_pos hn, one_mul]
      exact Real.sign_of_neg hsNeg
    · rw [paritySign, if_neg hn, neg_one_mul]
      simpa using Real.sign_of_pos (neg_pos.mpr hsNeg)
  have hright :
      (fun x : ℝ => Real.sign (Real.sin (Real.pi * x))) =ᶠ[rightFilter n]
        (fun _ : ℝ => paritySign n) := by
    have hlower : ∀ᶠ x : ℝ in rightFilter n, (n : ℝ) < x := by
      simpa [rightFilter] using
        (self_mem_nhdsWithin :
          Set.Ioi (n : ℝ) ∈ nhdsWithin (n : ℝ) (Set.Ioi (n : ℝ)))
    have hupper : ∀ᶠ x : ℝ in rightFilter n, x < (n : ℝ) + 1 := by
      have h : ∀ᶠ x : ℝ in nhds (n : ℝ), x < (n : ℝ) + 1 :=
        Iio_mem_nhds (by linarith)
      exact h.filter_mono (by
        rw [rightFilter]
        exact inf_le_left)
    filter_upwards [hlower, hupper] with x hxLower hxUpper
    have htPos : 0 < Real.pi * (x - (n : ℝ)) :=
      mul_pos Real.pi_pos (sub_pos.mpr hxLower)
    have htLt : Real.pi * (x - (n : ℝ)) < Real.pi := by
      nlinarith [Real.pi_pos]
    have hsPos : 0 < Real.sin (Real.pi * (x - (n : ℝ))) :=
      Real.sin_pos_of_pos_of_lt_pi htPos htLt
    rw [hshift x]
    by_cases hn : Even n
    · rw [paritySign, if_pos hn, one_mul]
      exact Real.sign_of_pos hsPos
    · rw [paritySign, if_neg hn, neg_one_mul]
      exact Real.sign_of_neg (neg_neg_of_pos hsPos)
  constructor
  · exact tendsto_const_nhds.congr' hleft.symm
  · exact tendsto_const_nhds.congr' hright.symm

theorem gap1 (n : ℤ) : f n = 0 := by
  rw [f, show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring,
    Real.sin_int_mul_pi, Real.sign_zero]

/-- Exercise 601, gap 2. -/
theorem gap2 (n : ℤ) (L : ℝ) :
    Filter.Tendsto f (leftFilter n) (nhds L) ↔
      Filter.Tendsto (fun x => Real.sign (Real.sin (Real.pi * x)))
        (leftFilter n) (nhds L) := by
  rfl

/-- Exercise 601, gap 3. -/
theorem gap3 (n : ℤ) :
    Filter.Tendsto (fun x => Real.sign (Real.sin (Real.pi * x)))
      (leftFilter n) (nhds (paritySign (n - 1))) := by
  exact (oneSidedSignLimits n).1

/-- Exercise 601, gap 4. -/
theorem gap4 (n : ℤ) :
    Filter.Tendsto f (leftFilter n) (nhds (paritySign (n - 1))) := by
  simpa [f] using gap3 n

/-- Exercise 601, gap 5. -/
theorem gap5 (n : ℤ) (L : ℝ) :
    Filter.Tendsto f (rightFilter n) (nhds L) ↔
      Filter.Tendsto (fun x => Real.sign (Real.sin (Real.pi * x)))
        (rightFilter n) (nhds L) := by
  rfl

/-- Exercise 601, gap 6. -/
theorem gap6 (n : ℤ) :
    Filter.Tendsto (fun x => Real.sign (Real.sin (Real.pi * x)))
      (rightFilter n) (nhds (paritySign n)) := by
  exact (oneSidedSignLimits n).2

/-- Exercise 601, gap 7. -/
theorem gap7 (n : ℤ) :
    Filter.Tendsto f (rightFilter n) (nhds (paritySign n)) := by
  simpa [f] using gap6 n

end

end ProofGap.Exercise601
