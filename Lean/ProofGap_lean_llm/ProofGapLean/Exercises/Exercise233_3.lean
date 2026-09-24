import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise233_3

noncomputable section

def f (x : ℝ) : ℝ :=
  2 * Real.tan (x / 2) - 3 * Real.tan (x / 3)

def IsLeastPositivePeriod (g : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ Function.Periodic g T ∧
    ∀ T', 0 < T' → Function.Periodic g T' → T ≤ T'

/-- Source: `proof_gap/exercise_233_3/1.txt`. -/
theorem gap1 : Function.Periodic f (6 * Real.pi) := by
  intro x
  unfold f
  have hhalf : (x + 6 * Real.pi) / 2 = x / 2 + (3 : ℕ) * Real.pi := by
    norm_num
    ring
  have hthird : (x + 6 * Real.pi) / 3 = x / 3 + (2 : ℕ) * Real.pi := by
    norm_num
    ring
  rw [hhalf, hthird, Real.tan_add_nat_mul_pi,
    Real.tan_add_nat_mul_pi]

private theorem zero_in_first_period {x : ℝ}
    (hxpos : 0 < x) (hxlt : x < 6 * Real.pi) (hzero : f x = 0) :
    x = 3 * Real.pi := by
  by_cases hcos2 : Real.cos (x / 2) = 0
  · have htan2 : Real.tan (x / 2) = 0 := by
      rw [Real.tan_eq_sin_div_cos, hcos2, div_zero]
    have htan3 : Real.tan (x / 3) = 0 := by
      unfold f at hzero
      rw [htan2] at hzero
      linarith
    rw [Real.tan_eq_sin_div_cos] at htan3
    rcases div_eq_zero_iff.mp htan3 with hsin3 | hcos3
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin3
      have hxn : x = 3 * (n : ℝ) * Real.pi := by
        linarith
      have hscale : 0 < 3 * Real.pi := by positivity
      have hxn' : x = (n : ℝ) * (3 * Real.pi) := by
        calc
          x = 3 * (n : ℝ) * Real.pi := hxn
          _ = (n : ℝ) * (3 * Real.pi) := by ring
      have hnposR : 0 < (n : ℝ) := by
        apply (mul_lt_mul_iff_right₀ hscale).mp
        simpa [hxn', mul_comm] using hxpos
      have hnltR : (n : ℝ) < 2 := by
        apply (mul_lt_mul_iff_right₀ hscale).mp
        calc
          (3 * Real.pi) * (n : ℝ) = x := by
            rw [mul_comm]
            exact hxn'.symm
          _ < 6 * Real.pi := hxlt
          _ = (3 * Real.pi) * 2 := by ring
      have hnposZ : (0 : ℤ) < n := by exact_mod_cast hnposR
      have hnltZ : n < (2 : ℤ) := by exact_mod_cast hnltR
      have hn1 : n = 1 := by omega
      rw [hn1] at hxn
      norm_num at hxn
      exact hxn
    · obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos2
      obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.mp hcos3
      have hxk : x = (2 * (k : ℝ) + 1) * Real.pi := by
        linarith
      have hxm : x = 3 * (2 * (m : ℝ) + 1) * Real.pi / 2 := by
        linarith
      have hmul :
          (2 * (2 * (k : ℝ) + 1)) * Real.pi =
            (3 * (2 * (m : ℝ) + 1)) * Real.pi := by
        calc
          (2 * (2 * (k : ℝ) + 1)) * Real.pi = 2 * x := by
            rw [hxk]
            ring
          _ = (3 * (2 * (m : ℝ) + 1)) * Real.pi := by
            rw [hxm]
            ring
      have hcoeff :
          (2 * (2 * (k : ℝ) + 1)) =
            3 * (2 * (m : ℝ) + 1) :=
        mul_right_cancel₀ Real.pi_ne_zero hmul
      have hcoeffZ : 2 * (2 * k + 1) = 3 * (2 * m + 1) := by
        exact_mod_cast hcoeff
      omega
  · by_cases hcos3 : Real.cos (x / 3) = 0
    · have htan3 : Real.tan (x / 3) = 0 := by
        rw [Real.tan_eq_sin_div_cos, hcos3, div_zero]
      have htan2 : Real.tan (x / 2) = 0 := by
        unfold f at hzero
        rw [htan3] at hzero
        linarith
      rw [Real.tan_eq_sin_div_cos] at htan2
      rcases div_eq_zero_iff.mp htan2 with hsin2 | hcos2'
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin2
        obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.mp hcos3
        have hxn : x = 2 * (n : ℝ) * Real.pi := by
          linarith
        have hxm : x = 3 * (2 * (m : ℝ) + 1) * Real.pi / 2 := by
          linarith
        have hmul :
            (4 * (n : ℝ)) * Real.pi =
              (3 * (2 * (m : ℝ) + 1)) * Real.pi := by
          calc
            (4 * (n : ℝ)) * Real.pi = 2 * x := by
              rw [hxn]
              ring
            _ = (3 * (2 * (m : ℝ) + 1)) * Real.pi := by
              rw [hxm]
              ring
        have hcoeff :
            (4 * (n : ℝ)) = 3 * (2 * (m : ℝ) + 1) :=
          mul_right_cancel₀ Real.pi_ne_zero hmul
        have hcoeffZ : 4 * n = 3 * (2 * m + 1) := by
          exact_mod_cast hcoeff
        omega
      · exact (hcos2 hcos2').elim
    · have hcross :
          2 * Real.sin (x / 2) * Real.cos (x / 3) -
              3 * Real.sin (x / 3) * Real.cos (x / 2) = 0 := by
        unfold f at hzero
        rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos] at hzero
        field_simp [hcos2, hcos3] at hzero
        nlinarith
      let u : ℝ := x / 6
      have hxhalf : x / 2 = 3 * u := by
        dsimp [u]
        ring
      have hxthird : x / 3 = 2 * u := by
        dsimp [u]
        ring
      have hfactor :
          2 * Real.sin (x / 2) * Real.cos (x / 3) -
              3 * Real.sin (x / 3) * Real.cos (x / 2) =
            2 * Real.sin u ^ 3 * (5 - 4 * Real.sin u ^ 2) := by
        rw [hxhalf, hxthird, Real.sin_three_mul, Real.cos_two_mul,
          Real.sin_two_mul, Real.cos_three_mul]
        have htrig := Real.sin_sq_add_cos_sq u
        have hc2 : Real.cos u ^ 2 = 1 - Real.sin u ^ 2 := by
          nlinarith
        have hc4 : Real.cos u ^ 4 = (1 - Real.sin u ^ 2) ^ 2 := by
          calc
            Real.cos u ^ 4 = (Real.cos u ^ 2) ^ 2 := by ring
            _ = (1 - Real.sin u ^ 2) ^ 2 := by rw [hc2]
        ring_nf
        rw [hc4, hc2]
        ring
      have hupos : 0 < u := by
        dsimp [u]
        linarith
      have hult : u < Real.pi := by
        dsimp [u]
        linarith
      have hsinu : 0 < Real.sin u :=
        Real.sin_pos_of_pos_of_lt_pi hupos hult
      have hsinle : Real.sin u ^ 2 ≤ 1 := by
        nlinarith [Real.sin_sq_add_cos_sq u, sq_nonneg (Real.cos u)]
      have hlast : 0 < 5 - 4 * Real.sin u ^ 2 := by linarith
      have hpositive :
          0 < 2 * Real.sin u ^ 3 * (5 - 4 * Real.sin u ^ 2) := by
        positivity
      rw [hfactor] at hcross
      linarith

/-- Source: `proof_gap/exercise_233_3/2.txt`; represent `min` by the least-positive-period predicate. -/
theorem gap2 : IsLeastPositivePeriod f (6 * Real.pi) := by
  refine ⟨by positivity, gap1, ?_⟩
  intro T hT hper
  apply le_of_not_gt
  intro hlt
  have hzero : f T = 0 := by
    simpa [f] using hper 0
  have hT3 : T = 3 * Real.pi :=
    zero_in_first_period hT hlt hzero
  have hspecial := hper (Real.pi / 2)
  rw [hT3] at hspecial
  unfold f at hspecial
  have hhalf :
      (Real.pi / 2 + 3 * Real.pi) / 2 =
        -(Real.pi / 4) + (2 : ℕ) * Real.pi := by
    norm_num
    ring
  have hthird :
      (Real.pi / 2 + 3 * Real.pi) / 3 =
        Real.pi / 6 + (1 : ℕ) * Real.pi := by
    norm_num
    ring
  have hhalf0 : Real.pi / 2 / 2 = Real.pi / 4 := by ring
  have hthird0 : Real.pi / 2 / 3 = Real.pi / 6 := by ring
  rw [hhalf, hthird, Real.tan_add_nat_mul_pi,
    Real.tan_add_nat_mul_pi, Real.tan_neg, hhalf0, hthird0,
    Real.tan_pi_div_four] at hspecial
  norm_num at hspecial

end

end ProofGap.Exercise233_3
