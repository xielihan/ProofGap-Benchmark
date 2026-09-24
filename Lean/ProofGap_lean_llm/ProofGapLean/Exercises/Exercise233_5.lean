import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise233_5

noncomputable section

def f (x : ℝ) : ℝ := Real.sin (x ^ 2)

/-- Exercise 233_5, gap 1. -/
theorem gap1 : ∀ a x, Function.Periodic f a →
    Real.sin ((x + a) ^ 2) = Real.sin (x ^ 2) := by
  intro a x h
  simpa [f] using h x

/-- Exercise 233_5, gap 2; replace the source's unsupported square-root witness by the valid specialization at zero. -/
theorem gap2 : ∀ a, Function.Periodic f a →
    Real.sin (a ^ 2) = 0 := by
  intro a h
  simpa using gap1 a 0 h

/-- Exercise 233_5, gap 3; retain the full translated identity needed to rule out a nonzero shift. -/
theorem gap3 : ∀ a, Function.Periodic f a →
    ∀ x, Real.sin (x ^ 2 + 2 * a * x + a ^ 2) = Real.sin (x ^ 2) := by
  intro a h x
  convert gap1 a x h using 1 <;> ring

/-- Exercise 233_5, gap 4; state the valid conclusion of the nonperiodicity argument. -/
theorem gap4 : ∀ a, Function.Periodic f a → a = 0 := by
  intro a h
  by_contra ha
  have ha_sin : Real.sin (a ^ 2) = 0 := gap2 a h
  let q : ℝ := Real.pi / (4 * a)
  have hq : 2 * a * q = Real.pi / 2 := by
    dsimp [q]
    field_simp [ha] <;> ring
  have hqneg : 2 * a * (-q) = -(Real.pi / 2) := by
    calc
      2 * a * (-q) = -(2 * a * q) := by ring
      _ = -(Real.pi / 2) := by rw [hq]
  have hp : Real.sin (q ^ 2 + Real.pi / 2 + a ^ 2) =
      Real.sin (q ^ 2) := by
    simpa only [hq] using gap3 a h q
  have hm0 := gap3 a h (-q)
  rw [hqneg] at hm0
  have hm : Real.sin (q ^ 2 - Real.pi / 2 + a ^ 2) =
      Real.sin (q ^ 2) := by
    convert hm0 using 1 <;> ring
  have hp' : Real.cos (q ^ 2 + a ^ 2) = Real.sin (q ^ 2) := by
    calc
      Real.cos (q ^ 2 + a ^ 2) =
          Real.sin ((q ^ 2 + a ^ 2) + Real.pi / 2) := by
            rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
            ring
      _ = Real.sin (q ^ 2 + Real.pi / 2 + a ^ 2) := by
            congr 1 <;> ring
      _ = Real.sin (q ^ 2) := hp
  have hm' : -Real.cos (q ^ 2 + a ^ 2) = Real.sin (q ^ 2) := by
    calc
      -Real.cos (q ^ 2 + a ^ 2) =
          Real.sin ((q ^ 2 + a ^ 2) - Real.pi / 2) := by
            rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
            ring
      _ = Real.sin (q ^ 2 - Real.pi / 2 + a ^ 2) := by
            congr 1 <;> ring
      _ = Real.sin (q ^ 2) := hm
  have hsu : Real.sin (q ^ 2) = 0 := by
    linarith
  have hcv : Real.cos (q ^ 2 + a ^ 2) = 0 := by
    linarith
  have hsv : Real.sin (q ^ 2 + a ^ 2) = 0 := by
    rw [Real.sin_add, hsu, ha_sin]
    ring
  have htrig := Real.sin_sq_add_cos_sq (q ^ 2 + a ^ 2)
  rw [hsv, hcv] at htrig
  norm_num at htrig

/-- Exercise 233_5, gap 5; zero is always a period, so exclude it. -/
theorem gap5 : ∀ a, a ≠ 0 → ¬ Function.Periodic f a := by
  intro a ha h
  exact ha (gap4 a h)

/-- Exercise 233_5, gap 6. -/
theorem gap6 : {T : ℝ | 0 < T ∧ Function.Periodic f T} = ∅ := by
  ext T
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hT, hper⟩
  exact (gap5 T (ne_of_gt hT)) hper

end

end ProofGap.Exercise233_5
