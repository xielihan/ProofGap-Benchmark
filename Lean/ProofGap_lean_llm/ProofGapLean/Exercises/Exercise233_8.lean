import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise233_8

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x + Real.sin (x * Real.sqrt 2)

/-- Source: `proof_gap/exercise_233_8/1.txt`. -/
theorem gap1 : ¬∃ T : ℝ, 0 < T ∧ Function.Periodic f T := by
  rintro ⟨T, hT, hper⟩
  let s : ℝ := Real.sqrt 2
  have hfun : (fun x : ℝ => f (x + T)) = f := funext hper
  have hfirst (x : ℝ) :
      Real.cos (x + T) + s * Real.cos ((x + T) * s) =
        Real.cos x + s * Real.cos (x * s) := by
    have hleft : HasDerivAt (fun y : ℝ => f (y + T))
        (Real.cos (x + T) + s * Real.cos ((x + T) * s)) x := by
      simpa [f, s, mul_comm] using
        (((Real.hasDerivAt_sin (x + T)).comp x
            ((hasDerivAt_id x).add_const T)).add
          ((Real.hasDerivAt_sin ((x + T) * Real.sqrt 2)).comp x
            (((hasDerivAt_id x).add_const T).mul_const (Real.sqrt 2))))
    have hright : HasDerivAt f
        (Real.cos x + s * Real.cos (x * s)) x := by
      simpa [f, s, mul_comm] using
        ((Real.hasDerivAt_sin x).add
          ((Real.hasDerivAt_sin (x * Real.sqrt 2)).comp x
            ((hasDerivAt_id x).mul_const (Real.sqrt 2))))
    rw [hfun] at hleft
    exact hleft.unique hright
  have hsecond (x : ℝ) :
      -Real.sin (x + T) - 2 * Real.sin ((x + T) * s) =
        -Real.sin x - 2 * Real.sin (x * s) := by
    have hleft : HasDerivAt
        (fun y : ℝ => Real.cos (y + T) + s * Real.cos ((y + T) * s))
        (-Real.sin (x + T) - (s * s) * Real.sin ((x + T) * s)) x := by
      convert
        (((Real.hasDerivAt_cos (x + T)).comp x
            ((hasDerivAt_id x).add_const T)).add
          (((Real.hasDerivAt_cos ((x + T) * s)).comp x
            (((hasDerivAt_id x).add_const T).mul_const s)).const_mul s)) using 1 <;> ring
    have hright : HasDerivAt
        (fun y : ℝ => Real.cos y + s * Real.cos (y * s))
        (-Real.sin x - (s * s) * Real.sin (x * s)) x := by
      convert
        ((Real.hasDerivAt_cos x).add
          (((Real.hasDerivAt_cos (x * s)).comp x
            ((hasDerivAt_id x).mul_const s)).const_mul s)) using 1 <;> ring
    have hderivfun :
        (fun y : ℝ => Real.cos (y + T) + s * Real.cos ((y + T) * s)) =
          fun y : ℝ => Real.cos y + s * Real.cos (y * s) :=
      funext hfirst
    rw [hderivfun] at hleft
    have hraw := hleft.unique hright
    have hsqrt : s * s = (2 : ℝ) := by
      dsimp [s]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [hsqrt] at hraw
    exact hraw
  have hzero (x : ℝ) :
      Real.sin (x + T) + Real.sin ((x + T) * s) =
        Real.sin x + Real.sin (x * s) := by
    simpa [f, s] using hper x
  have hsinScaled (x : ℝ) :
      Real.sin ((x + T) * s) = Real.sin (x * s) := by
    nlinarith [hzero x, hsecond x]
  have hsinBase (x : ℝ) : Real.sin (x + T) = Real.sin x := by
    nlinarith [hzero x, hsecond x]
  have hTsin : Real.sin T = 0 := by
    simpa using hsinBase 0
  have hTssin : Real.sin (T * s) = 0 := by
    simpa using hsinScaled 0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hTsin
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hTssin
  have hnR0 : (n : ℝ) ≠ 0 := by
    intro hn0
    have hT0 : T = 0 := by
      rw [← hn, hn0, zero_mul]
    linarith
  have hnZ0 : n ≠ 0 := by
    exact_mod_cast hnR0
  have hrel :
      (m : ℝ) * Real.pi = ((n : ℝ) * s) * Real.pi := by
    calc
      (m : ℝ) * Real.pi = T * s := hm
      _ = ((n : ℝ) * Real.pi) * s := by rw [← hn]
      _ = ((n : ℝ) * s) * Real.pi := by ring
  have hmn : (m : ℝ) = (n : ℝ) * s :=
    mul_right_cancel₀ (ne_of_gt Real.pi_pos) hrel
  have hs : s = (m : ℝ) / (n : ℝ) := by
    apply (eq_div_iff hnR0).2
    calc
      s * (n : ℝ) = (n : ℝ) * s := mul_comm _ _
      _ = (m : ℝ) := hmn.symm
  have hsrat :
      Real.sqrt 2 = (↑((m : ℚ) / (n : ℚ)) : ℝ) := by
    change s = (↑((m : ℚ) / (n : ℚ)) : ℝ)
    calc
      s = (m : ℝ) / (n : ℝ) := hs
      _ = (↑((m : ℚ) / (n : ℚ)) : ℝ) := by norm_cast
  exact irrational_sqrt_two ⟨(m : ℚ) / (n : ℚ), hsrat.symm⟩

/-- Source: `proof_gap/exercise_233_8/2.txt`. -/
theorem gap2 : {T : ℝ | 0 < T ∧ Function.Periodic f T} = ∅ := by
  ext T
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  exact gap1 ⟨T, h⟩

end

end ProofGap.Exercise233_8
