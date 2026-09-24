import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise605

noncomputable section

def seq (n : ℕ) : ℝ := Real.sin (Real.pi * Real.sqrt (n ^ 2 + n)) ^ 2
def halfAngle (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 - Real.cos (2 * Real.pi * Real.sqrt (n ^ 2 + n)))
def shifted (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 - Real.cos (2 * Real.pi * (Real.sqrt (n ^ 2 + n) - n)))

/-- Exercise 605, gap 1. -/
private theorem trig_nat_mul_two_pi (n : ℕ) :
    Real.cos (2 * Real.pi * (n : ℝ)) = 1 ∧
      Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have harg :
          2 * Real.pi * ((n.succ : ℕ) : ℝ) =
            2 * Real.pi * (n : ℝ) + 2 * Real.pi := by
        rw [Nat.cast_succ]
        ring
      constructor
      · rw [harg, Real.cos_add, ih.1, ih.2, Real.cos_two_pi,
          Real.sin_two_pi]
        norm_num
      · rw [harg, Real.sin_add, ih.1, ih.2, Real.cos_two_pi,
          Real.sin_two_pi]
        norm_num

private theorem tendsto_root_offset :
    Filter.Tendsto
      (fun n : ℕ => Real.sqrt (n ^ 2 + n) - n)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hnat :
      Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹))
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hbase :
      Filter.Tendsto
        (fun n : ℕ => 1 + ((n : ℝ)⁻¹))
        Filter.atTop (nhds 1) := by
    convert tendsto_const_nhds.add hinv using 1 <;> norm_num
  have hsqrt :
      Filter.Tendsto
        (fun n : ℕ => Real.sqrt (1 + ((n : ℝ)⁻¹)))
        Filter.atTop (nhds 1) := by
    simpa using
      Real.continuous_sqrt.continuousAt.tendsto.comp hbase
  have hden :
      Filter.Tendsto
        (fun n : ℕ => Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1)
        Filter.atTop (nhds 2) := by
    convert hsqrt.add tendsto_const_nhds using 1 <;> norm_num
  have hrecip :
      Filter.Tendsto
        (fun n : ℕ =>
          (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1)⁻¹)
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    convert hden.inv₀ (by norm_num : (2 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have heq :
      (fun n : ℕ => Real.sqrt (n ^ 2 + n) - n) =ᶠ[Filter.atTop]
        (fun n : ℕ =>
          (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1)⁻¹) :=
    Filter.eventually_atTop.2 ⟨1, by
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
      have hx : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
      have hs_sq :
          Real.sqrt ((n : ℝ) ^ 2 + (n : ℝ)) ^ 2 =
            (n : ℝ) ^ 2 + (n : ℝ) :=
        Real.sq_sqrt (by positivity)
      have ht_sq :
          Real.sqrt (1 + ((n : ℝ)⁻¹)) ^ 2 =
            1 + ((n : ℝ)⁻¹) :=
        Real.sq_sqrt (by positivity)
      have hscale_sq :
          ((n : ℝ) * Real.sqrt (1 + ((n : ℝ)⁻¹))) ^ 2 =
            (n : ℝ) ^ 2 + (n : ℝ) := by
        calc
          ((n : ℝ) * Real.sqrt (1 + ((n : ℝ)⁻¹))) ^ 2 =
              (n : ℝ) ^ 2 *
                Real.sqrt (1 + ((n : ℝ)⁻¹)) ^ 2 := by ring
          _ = (n : ℝ) ^ 2 * (1 + ((n : ℝ)⁻¹)) := by
            rw [ht_sq]
          _ = (n : ℝ) ^ 2 + (n : ℝ) := by
            field_simp [hx.ne'] <;> ring
      have hscale :
          Real.sqrt ((n : ℝ) ^ 2 + (n : ℝ)) =
            (n : ℝ) * Real.sqrt (1 + ((n : ℝ)⁻¹)) := by
        have hs_nonneg :=
          Real.sqrt_nonneg ((n : ℝ) ^ 2 + (n : ℝ))
        have ht_nonneg :
            0 ≤ (n : ℝ) * Real.sqrt (1 + ((n : ℝ)⁻¹)) :=
          mul_nonneg hx.le (Real.sqrt_nonneg _)
        nlinarith [hs_sq, hscale_sq]
      have halg :
          (n : ℝ) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) ^ 2 - 1) = 1 := by
        calc
          (n : ℝ) *
                (Real.sqrt (1 + ((n : ℝ)⁻¹)) ^ 2 - 1) =
              (n : ℝ) * (1 + ((n : ℝ)⁻¹) - 1) := by
                rw [ht_sq]
          _ = 1 := by
            field_simp [hx.ne'] <;> ring
      have htplus :
          Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1 ≠ 0 := by
        positivity
      have hprod :
          ((n : ℝ) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) - 1)) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1) = 1 := by
        calc
          ((n : ℝ) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) - 1)) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1) =
            (n : ℝ) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) ^ 2 - 1) := by
                ring
          _ = 1 := halg
      have hdiv :
          (n : ℝ) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) - 1) =
            1 / (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1) :=
        (eq_div_iff htplus).2 hprod
      change
        Real.sqrt ((n : ℝ) ^ 2 + (n : ℝ)) - (n : ℝ) =
          (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1)⁻¹
      rw [hscale]
      calc
        (n : ℝ) * Real.sqrt (1 + ((n : ℝ)⁻¹)) - (n : ℝ) =
            (n : ℝ) *
              (Real.sqrt (1 + ((n : ℝ)⁻¹)) - 1) := by ring
        _ = 1 / (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1) := hdiv
        _ = (Real.sqrt (1 + ((n : ℝ)⁻¹)) + 1)⁻¹ := by
          rw [one_div]
    ⟩
  exact (Filter.tendsto_congr' heq).2 hrecip

theorem gap1 (L : ℝ) :
    Filter.Tendsto seq Filter.atTop (nhds L) ↔
      Filter.Tendsto halfAngle Filter.atTop (nhds L) := by
  have h : seq = halfAngle := by
    funext n
    unfold seq halfAngle
    rw [Real.sin_sq]
    have harg :
        2 * (Real.pi * Real.sqrt (n ^ 2 + n)) =
          2 * Real.pi * Real.sqrt (n ^ 2 + n) := by
      ring
    rw [← harg, Real.cos_two_mul]
    ring
  rw [h]

/-- Exercise 605, gap 2. -/
theorem gap2 (L : ℝ) :
    Filter.Tendsto halfAngle Filter.atTop (nhds L) ↔
      Filter.Tendsto shifted Filter.atTop (nhds L) := by
  have h : halfAngle = shifted := by
    funext n
    unfold halfAngle shifted
    have ht := trig_nat_mul_two_pi n
    have hc :
        Real.cos
            (2 * Real.pi *
              (Real.sqrt (n ^ 2 + n) - (n : ℝ))) =
          Real.cos (2 * Real.pi * Real.sqrt (n ^ 2 + n)) := by
      have harg :
          2 * Real.pi *
              (Real.sqrt (n ^ 2 + n) - (n : ℝ)) =
            2 * Real.pi * Real.sqrt (n ^ 2 + n) -
              2 * Real.pi * (n : ℝ) := by
        ring
      rw [harg, Real.cos_sub, ht.1, ht.2]
      ring
    exact
      congrArg (fun y : ℝ => (1 / 2 : ℝ) * (1 - y)) hc.symm
  rw [h]

/-- Exercise 605, gap 3. -/
theorem gap3 : Filter.Tendsto shifted Filter.atTop (nhds 1) := by
  have hcont :
      Continuous
        (fun x : ℝ =>
          (1 / 2 : ℝ) * (1 - Real.cos (2 * Real.pi * x))) :=
    continuous_const.mul
      (continuous_const.sub
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))
  have hlim :=
    hcont.continuousAt.tendsto.comp tendsto_root_offset
  have hvalue :
      (1 / 2 : ℝ) *
          (1 - Real.cos (2 * Real.pi * (1 / 2 : ℝ))) = 1 := by
    rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring,
      Real.cos_pi]
    ring
  simpa only [shifted, hvalue] using hlim

/-- Exercise 605, gap 4. -/
theorem gap4 : Filter.Tendsto seq Filter.atTop (nhds 1) := by
  exact (gap1 1).2 ((gap2 1).2 gap3)

end

end ProofGap.Exercise605
