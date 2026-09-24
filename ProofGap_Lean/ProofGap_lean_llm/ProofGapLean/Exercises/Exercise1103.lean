import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1103

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10
def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private theorem exercise1103_sq_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx hy)]

private theorem exercise1103_log_lower {x : ℝ} (hx : 0 < x) :
    (x - 1) / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x⁻¹ by positivity)
  rw [Real.log_inv] at h
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp [mul_sub, hx0] at hm
  apply (div_le_iff₀ hx).2
  nlinarith

private theorem exercise1103_numeric_bounds :
    ((19 / 201 : ℝ) ≤ Real.log (11 / 10 : ℝ) ∧
      Real.log (11 / 10 : ℝ) ≤ (1 / 10 : ℝ)) ∧
    ((23021 / 10000 : ℝ) < Real.log 10 ∧
      Real.log 10 < (23031 / 10000 : ℝ)) := by
  set_option maxHeartbeats 2000000 in
  set_option maxRecDepth 4096 in
    constructor
    · constructor
      · have hpow : (201 / 200 : ℝ) ^ 19 ≤ (11 / 10 : ℝ) := by
          norm_num
        have hmono :
            Real.log ((201 / 200 : ℝ) ^ 19) ≤ Real.log (11 / 10 : ℝ) :=
          Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) hpow
        rw [Real.log_pow] at hmono
        have hq : (1 / 201 : ℝ) ≤ Real.log (201 / 200 : ℝ) := by
          convert exercise1103_log_lower
            (show 0 < (201 / 200 : ℝ) by norm_num) using 1 <;> norm_num
        nlinarith
      · have h := Real.log_le_sub_one_of_pos
            (show 0 < (11 / 10 : ℝ) by norm_num)
        norm_num at h ⊢
        exact h
    · have hExpLow : Real.exp (23021 / 10000 : ℝ) < 10 := by
        let t : ℝ := (23021 / 10000 : ℝ) / 1048576
        let q : ℝ := 1 / (1 - t)
        have htBound : Real.exp t ≤ q := by
          dsimp [q]
          apply Real.exp_bound_div_one_sub_of_interval
          · dsimp [t]
            norm_num
          · dsimp [t]
            norm_num
        have hq0 : q ≤ (10000021955 / 10000000000 : ℝ) := by
          dsimp [q, t]
          norm_num
        have hqnonneg : 0 ≤ q := by
          dsimp [q, t]
          positivity
        have hp1 : q ^ 2 ≤ (10000043911 / 10000000000 : ℝ) := calc
          q ^ 2 ≤ (10000021955 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono hqnonneg hq0
          _ ≤ (10000043911 / 10000000000 : ℝ) := by norm_num
        have hp2 : q ^ 4 ≤ (10000087823 / 10000000000 : ℝ) := calc
          q ^ 4 = (q ^ 2) ^ 2 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
          _ ≤ (10000043911 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp1
          _ ≤ (10000087823 / 10000000000 : ℝ) := by norm_num
        have hp3 : q ^ 8 ≤ (10000175648 / 10000000000 : ℝ) := calc
          q ^ 8 = (q ^ 4) ^ 2 := by
            rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
          _ ≤ (10000087823 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp2
          _ ≤ (10000175648 / 10000000000 : ℝ) := by norm_num
        have hp4 : q ^ 16 ≤ (10000351300 / 10000000000 : ℝ) := calc
          q ^ 16 = (q ^ 8) ^ 2 := by
            rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul]
          _ ≤ (10000175648 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp3
          _ ≤ (10000351300 / 10000000000 : ℝ) := by norm_num
        have hp5 : q ^ 32 ≤ (10000702613 / 10000000000 : ℝ) := calc
          q ^ 32 = (q ^ 16) ^ 2 := by
            rw [show (32 : ℕ) = 16 * 2 by norm_num, pow_mul]
          _ ≤ (10000351300 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp4
          _ ≤ (10000702613 / 10000000000 : ℝ) := by norm_num
        have hp6 : q ^ 64 ≤ (10001405276 / 10000000000 : ℝ) := calc
          q ^ 64 = (q ^ 32) ^ 2 := by
            rw [show (64 : ℕ) = 32 * 2 by norm_num, pow_mul]
          _ ≤ (10000702613 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp5
          _ ≤ (10001405276 / 10000000000 : ℝ) := by norm_num
        have hp7 : q ^ 128 ≤ (10002810750 / 10000000000 : ℝ) := calc
          q ^ 128 = (q ^ 64) ^ 2 := by
            rw [show (128 : ℕ) = 64 * 2 by norm_num, pow_mul]
          _ ≤ (10001405276 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp6
          _ ≤ (10002810750 / 10000000000 : ℝ) := by norm_num
        have hp8 : q ^ 256 ≤ (10005622291 / 10000000000 : ℝ) := calc
          q ^ 256 = (q ^ 128) ^ 2 := by
            rw [show (256 : ℕ) = 128 * 2 by norm_num, pow_mul]
          _ ≤ (10002810750 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp7
          _ ≤ (10005622291 / 10000000000 : ℝ) := by norm_num
        have hp9 : q ^ 512 ≤ (10011247744 / 10000000000 : ℝ) := calc
          q ^ 512 = (q ^ 256) ^ 2 := by
            rw [show (512 : ℕ) = 256 * 2 by norm_num, pow_mul]
          _ ≤ (10005622291 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp8
          _ ≤ (10011247744 / 10000000000 : ℝ) := by norm_num
        have hp10 : q ^ 1024 ≤ (10022511000 / 10000000000 : ℝ) := calc
          q ^ 1024 = (q ^ 512) ^ 2 := by
            rw [show (1024 : ℕ) = 512 * 2 by norm_num, pow_mul]
          _ ≤ (10011247744 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hp9
          _ ≤ (10022508140 / 10000000000 : ℝ) := by norm_num
          _ ≤ (10022511000 / 10000000000 : ℝ) := by norm_num
        have hb1 : (10022511000 / 10000000000 : ℝ) ^ 2 ≤
            (10045072675 / 10000000000 : ℝ) := by norm_num
        have hb2 : (10022511000 / 10000000000 : ℝ) ^ 4 ≤
            (10090348505 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 2) ^ 2 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
          _ ≤ (10045072675 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb1
          _ ≤ (10090348505 / 10000000000 : ℝ) := by norm_num
        have hb3 : (10022511000 / 10000000000 : ℝ) ^ 8 ≤
            (10181513296 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 4) ^ 2 := by
            rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
          _ ≤ (10090348505 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb2
          _ ≤ (10181513296 / 10000000000 : ℝ) := by norm_num
        have hb4 : (10022511000 / 10000000000 : ℝ) ^ 16 ≤
            (10366321300 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 8) ^ 2 := by
            rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul]
          _ ≤ (10181513296 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb3
          _ ≤ (10366321300 / 10000000000 : ℝ) := by norm_num
        have hb5 : (10022511000 / 10000000000 : ℝ) ^ 32 ≤
            (10746061730 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 16) ^ 2 := by
            rw [show (32 : ℕ) = 16 * 2 by norm_num, pow_mul]
          _ ≤ (10366321300 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb4
          _ ≤ (10746061730 / 10000000000 : ℝ) := by norm_num
        have hb6 : (10022511000 / 10000000000 : ℝ) ^ 64 ≤
            (11547784271 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 32) ^ 2 := by
            rw [show (64 : ℕ) = 32 * 2 by norm_num, pow_mul]
          _ ≤ (10746061730 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb5
          _ ≤ (11547784271 / 10000000000 : ℝ) := by norm_num
        have hb7 : (10022511000 / 10000000000 : ℝ) ^ 128 ≤
            (13335132157 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 64) ^ 2 := by
            rw [show (128 : ℕ) = 64 * 2 by norm_num, pow_mul]
          _ ≤ (11547784271 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb6
          _ ≤ (13335132157 / 10000000000 : ℝ) := by norm_num
        have hb8 : (10022511000 / 10000000000 : ℝ) ^ 256 ≤
            (17782574965 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 128) ^ 2 := by
            rw [show (256 : ℕ) = 128 * 2 by norm_num, pow_mul]
          _ ≤ (13335132157 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb7
          _ ≤ (17782574965 / 10000000000 : ℝ) := by norm_num
        have hb9 : (10022511000 / 10000000000 : ℝ) ^ 512 ≤
            (31621997240 / 10000000000 : ℝ) := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 256) ^ 2 := by
            rw [show (512 : ℕ) = 256 * 2 by norm_num, pow_mul]
          _ ≤ (17782574965 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb8
          _ ≤ (31621997240 / 10000000000 : ℝ) := by norm_num
        have hb10 : (10022511000 / 10000000000 : ℝ) ^ 1024 < 10 := calc
          _ = ((10022511000 / 10000000000 : ℝ) ^ 512) ^ 2 := by
            rw [show (1024 : ℕ) = 512 * 2 by norm_num, pow_mul]
          _ ≤ (31621997240 / 10000000000 : ℝ) ^ 2 :=
            exercise1103_sq_mono (by positivity) hb9
          _ < 10 := by norm_num
        have hexp : Real.exp (23021 / 10000 : ℝ) =
            (Real.exp t) ^ 1048576 := by
          rw [← Real.exp_nat_mul]
          congr 1
          dsimp [t]
          ring
        calc
          Real.exp (23021 / 10000 : ℝ) = (Real.exp t) ^ 1048576 := hexp
          _ ≤ q ^ 1048576 := by gcongr
          _ = (q ^ 1024) ^ 1024 := by
            rw [show (1048576 : ℕ) = 1024 * 1024 by norm_num, pow_mul]
          _ ≤ (10022511000 / 10000000000 : ℝ) ^ 1024 := by gcongr
          _ < 10 := hb10
      have hExpHigh : 10 < Real.exp (23031 / 10000 : ℝ) := by
        let t : ℝ := (23031 / 10000 : ℝ) / 1048576
        have htBound : 1 + t ≤ Real.exp t := by
          simpa [add_comm] using Real.add_one_le_exp t
        have ha0 : (10000021964 / 10000000000 : ℝ) ≤ 1 + t := by
          dsimp [t]
          norm_num
        have ha1 : (10000043928 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 2 := by norm_num
        have ha2 : (10000087856 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 4 := calc
          _ ≤ (10000043928 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 2) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha1
          _ = (10000021964 / 10000000000 : ℝ) ^ 4 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        have ha3 : (10000175712 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 8 := calc
          _ ≤ (10000087856 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 4) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha2
          _ = (10000021964 / 10000000000 : ℝ) ^ 8 := by
            rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
        have ha4 : (10000351427 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 16 := calc
          _ ≤ (10000175712 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 8) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha3
          _ = (10000021964 / 10000000000 : ℝ) ^ 16 := by
            rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul]
        have ha5 : (10000702866 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 32 := calc
          _ ≤ (10000351427 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 16) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha4
          _ = (10000021964 / 10000000000 : ℝ) ^ 32 := by
            rw [show (32 : ℕ) = 16 * 2 by norm_num, pow_mul]
        have ha6 : (10001405781 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 64 := calc
          _ ≤ (10000702866 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 32) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha5
          _ = (10000021964 / 10000000000 : ℝ) ^ 64 := by
            rw [show (64 : ℕ) = 32 * 2 by norm_num, pow_mul]
        have ha7 : (10002811759 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 128 := calc
          _ ≤ (10001405781 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 64) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha6
          _ = (10000021964 / 10000000000 : ℝ) ^ 128 := by
            rw [show (128 : ℕ) = 64 * 2 by norm_num, pow_mul]
        have ha8 : (10005624308 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 256 := calc
          _ ≤ (10002811759 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 128) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha7
          _ = (10000021964 / 10000000000 : ℝ) ^ 256 := by
            rw [show (256 : ℕ) = 128 * 2 by norm_num, pow_mul]
        have ha9 : (10011251779 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 512 := calc
          _ ≤ (10005624308 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 256) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha8
          _ = (10000021964 / 10000000000 : ℝ) ^ 512 := by
            rw [show (512 : ℕ) = 256 * 2 by norm_num, pow_mul]
        have ha10 : (10022516217 / 10000000000 : ℝ) ≤
            (10000021964 / 10000000000 : ℝ) ^ 1024 := calc
          _ ≤ (10011251779 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 512) ^ 2 :=
            exercise1103_sq_mono (by positivity) ha9
          _ = (10000021964 / 10000000000 : ℝ) ^ 1024 := by
            rw [show (1024 : ℕ) = 512 * 2 by norm_num, pow_mul]
        have hc1 : (10045083000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 2 := by norm_num
        have hc2 : (10090369000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 4 := calc
          _ ≤ (10045083000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 2) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc1
          _ = (10022516217 / 10000000000 : ℝ) ^ 4 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        have hc3 : (10181554000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 8 := calc
          _ ≤ (10090369000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 4) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc2
          _ = (10022516217 / 10000000000 : ℝ) ^ 8 := by
            rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
        have hc4 : (10366404000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 16 := calc
          _ ≤ (10181554000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 8) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc3
          _ = (10022516217 / 10000000000 : ℝ) ^ 16 := by
            rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul]
        have hc5 : (10746233000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 32 := calc
          _ ≤ (10366404000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 16) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc4
          _ = (10022516217 / 10000000000 : ℝ) ^ 32 := by
            rw [show (32 : ℕ) = 16 * 2 by norm_num, pow_mul]
        have hc6 : (11548152000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 64 := calc
          _ ≤ (10746233000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 32) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc5
          _ = (10022516217 / 10000000000 : ℝ) ^ 64 := by
            rw [show (64 : ℕ) = 32 * 2 by norm_num, pow_mul]
        have hc7 : (13335981000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 128 := calc
          _ ≤ (11548152000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 64) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc6
          _ = (10022516217 / 10000000000 : ℝ) ^ 128 := by
            rw [show (128 : ℕ) = 64 * 2 by norm_num, pow_mul]
        have hc8 : (17784838000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 256 := calc
          _ ≤ (13335981000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 128) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc7
          _ = (10022516217 / 10000000000 : ℝ) ^ 256 := by
            rw [show (256 : ℕ) = 128 * 2 by norm_num, pow_mul]
        have hc9 : (31630046000 / 10000000000 : ℝ) ≤
            (10022516217 / 10000000000 : ℝ) ^ 512 := calc
          _ ≤ (17784838000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 256) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc8
          _ = (10022516217 / 10000000000 : ℝ) ^ 512 := by
            rw [show (512 : ℕ) = 256 * 2 by norm_num, pow_mul]
        have hc10 : 10 < (10022516217 / 10000000000 : ℝ) ^ 1024 := calc
          10 < (31630046000 / 10000000000 : ℝ) ^ 2 := by norm_num
          _ ≤ ((10022516217 / 10000000000 : ℝ) ^ 512) ^ 2 :=
            exercise1103_sq_mono (by positivity) hc9
          _ = (10022516217 / 10000000000 : ℝ) ^ 1024 := by
            rw [show (1024 : ℕ) = 512 * 2 by norm_num, pow_mul]
        have hexp : Real.exp (23031 / 10000 : ℝ) =
            (Real.exp t) ^ 1048576 := by
          rw [← Real.exp_nat_mul]
          congr 1
          dsimp [t]
          ring
        calc
          10 < (10022516217 / 10000000000 : ℝ) ^ 1024 := hc10
          _ ≤ ((10000021964 / 10000000000 : ℝ) ^ 1024) ^ 1024 := by
            gcongr
          _ = (10000021964 / 10000000000 : ℝ) ^ 1048576 := by
            rw [show (1048576 : ℕ) = 1024 * 1024 by norm_num, pow_mul]
          _ ≤ (1 + t) ^ 1048576 := by gcongr
          _ ≤ (Real.exp t) ^ 1048576 := by gcongr
          _ = Real.exp (23031 / 10000 : ℝ) := hexp.symm
      constructor
      · rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
        exact hExpLow
      · rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
        exact hExpHigh

theorem gap1 :
    lg 11 = lg 10 + lg (11 / 10 : ℝ) := by
  unfold lg
  have h10pos : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have h10ne : Real.log (10 : ℝ) ≠ 0 := ne_of_gt h10pos
  rw [show (11 : ℝ) = 10 * (11 / 10 : ℝ) by norm_num]
  rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0)
    (by norm_num : (11 / 10 : ℝ) ≠ 0)]
  field_simp [h10ne]

theorem gap2 :
    lg 10 + lg (11 / 10 : ℝ) = 1 + lg (11 / 10 : ℝ) := by
  have h10pos : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have h10ne : Real.log (10 : ℝ) ≠ 0 := ne_of_gt h10pos
  simp [lg, h10ne]

theorem gap3 :
    lg 11 = 1 + lg (11 / 10 : ℝ) := by
  exact gap1.trans gap2

theorem gap4 :
    Approx (lg (11 / 10 : ℝ))
      (lg 1 + (1 / 10 : ℝ) / Real.log 10)
      (3 / 1000 : ℝ) := by
  rcases exercise1103_numeric_bounds with
    ⟨⟨hLlow, hLhigh⟩, ⟨hDlow, hDhigh⟩⟩
  have hDpos : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  unfold Approx lg
  simp only [Real.log_one, zero_div, zero_add]
  rw [← sub_div]
  have hnum : Real.log (11 / 10 : ℝ) - (1 / 10 : ℝ) ≤ 0 := by
    linarith
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hDpos.le)]
  rw [← neg_div]
  apply (div_lt_iff₀ hDpos).2
  nlinarith

theorem gap5 :
    Approx (lg 1 + (1 / 10 : ℝ) / Real.log 10)
      ((1 / 10 : ℝ) / (23026 / 10000 : ℝ))
      (1 / 100000 : ℝ) := by
  rcases exercise1103_numeric_bounds with
    ⟨⟨hLlow, hLhigh⟩, ⟨hDlow, hDhigh⟩⟩
  have hDpos : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hcpos : 0 < (23026 / 10000 : ℝ) := by norm_num
  unfold Approx lg
  simp only [Real.log_one, zero_div, zero_add]
  have heq :
      (1 / 10 : ℝ) / Real.log 10 - (1 / 10 : ℝ) / (23026 / 10000 : ℝ) =
        ((23026 / 10000 : ℝ) - Real.log 10) /
          (10 * Real.log 10 * (23026 / 10000 : ℝ)) := by
    field_simp [ne_of_gt hDpos, ne_of_gt hcpos]
  rw [heq, abs_div, abs_of_pos (mul_pos (mul_pos (by norm_num) hDpos) hcpos)]
  apply (div_lt_iff₀ (mul_pos (mul_pos (by norm_num) hDpos) hcpos)).2
  have habs :
      |(23026 / 10000 : ℝ) - Real.log 10| < (1 / 2000 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hden :
      50 < 10 * Real.log 10 * (23026 / 10000 : ℝ) := by
    nlinarith
  nlinarith

theorem gap6 :
    Approx ((1 / 10 : ℝ) / (23026 / 10000 : ℝ))
      (434 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  norm_num [Approx, abs_lt]

theorem gap7 :
    Approx (lg (11 / 10 : ℝ))
      (434 / 10000 : ℝ) (3 / 1000 : ℝ) := by
  rcases exercise1103_numeric_bounds with
    ⟨⟨hLlow, hLhigh⟩, ⟨hDlow, hDhigh⟩⟩
  have hDpos : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hratioLow :
      (404 / 10000 : ℝ) < Real.log (11 / 10 : ℝ) / Real.log 10 := by
    apply (lt_div_iff₀ hDpos).2
    nlinarith
  have hratioHigh :
      Real.log (11 / 10 : ℝ) / Real.log 10 < (464 / 10000 : ℝ) := by
    apply (div_lt_iff₀ hDpos).2
    nlinarith
  unfold Approx lg
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap8 :
    Approx (lg 11) (10434 / 10000 : ℝ) (3 / 1000 : ℝ) := by
  have h := gap7
  unfold Approx at h ⊢
  rw [gap3]
  convert h using 1 <;> ring

end

end ProofGap.Exercise1103
