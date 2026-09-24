import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1444

noncomputable section

def y (x : ℝ) : ℝ := |x| * Real.exp (-|x - 1|)
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem topologyScopeMarker : True := by
  trivial

open scoped Topology

theorem gap1 (x : ℝ) (hx : x < 0) :
    y x = -x * Real.exp (x - 1) := by
  have hx₁ : x - 1 < 0 := by linarith
  simp [y, abs_of_neg hx, abs_of_neg hx₁]

theorem gap2 (x : ℝ) (hx : x < 0) :
    deriv y x = -(x + 1) * Real.exp (x - 1) := by
  have hfun : y =ᶠ[𝓝 x] (fun z : ℝ => -z * Real.exp (z - 1)) := by
    filter_upwards [eventually_lt_nhds hx] with z hz
    exact gap1 z hz
  have hder :
      HasDerivAt (fun z : ℝ => -z * Real.exp (z - 1))
        (-(x + 1) * Real.exp (x - 1)) x := by
    convert (hasDerivAt_id x).neg.mul
      ((Real.hasDerivAt_exp (x - 1)).comp x
        ((hasDerivAt_id x).sub_const 1)) using 1 <;>
      simp [Function.comp_apply] <;> ring
  calc
    deriv y x = deriv (fun z : ℝ => -z * Real.exp (z - 1)) x := hfun.deriv_eq
    _ = -(x + 1) * Real.exp (x - 1) := hder.deriv

theorem gap3 : deriv y (-1) = 0 := by
  rw [gap2 (-1) (by norm_num)]
  ring

theorem gap4 (x : ℝ) (hx : x < -1) : 0 < deriv y x := by
  rw [gap2 x (by linarith)]
  exact mul_pos (by linarith) (Real.exp_pos _)

theorem gap5 (x : ℝ) (h₁ : -1 < x) (h₂ : x < 0) :
    deriv y x < 0 := by
  rw [gap2 x h₂]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)

theorem gap6 : IsLocalMax y (-1) := by
  filter_upwards [eventually_lt_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
  have hyx : y x = -x * Real.exp (x - 1) := gap1 x hx
  have hym : y (-1) = Real.exp (-2) := by
    norm_num [y]
  rw [hyx, hym]
  have hcore : -x * Real.exp (x + 1) ≤ 1 := by
    calc
      -x * Real.exp (x + 1) =
          (1 + -(x + 1)) * Real.exp (x + 1) := by ring
      _ ≤ Real.exp (-(x + 1)) * Real.exp (x + 1) :=
        mul_le_mul_of_nonneg_right
          (by simpa [add_comm] using Real.add_one_le_exp (-(x + 1)))
          (Real.exp_nonneg _)
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        norm_num
  calc
    -x * Real.exp (x - 1) =
        -x * (Real.exp (-2) * Real.exp (x + 1)) := by
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-2) * (-x * Real.exp (x + 1)) := by ring
    _ ≤ Real.exp (-2) * 1 :=
      mul_le_mul_of_nonneg_left hcore (Real.exp_nonneg _)
    _ = Real.exp (-2) := by ring

theorem gap7 : y (-1) = Real.exp (-2) := by
  norm_num [y]

theorem gap8 : Approx (Real.exp (-2)) 0.135 0.001 := by
  unfold Approx
  have hminus : (249 / 250 : ℝ) ≤ Real.exp (-(1 / 250 : ℝ)) := by
    convert Real.add_one_le_exp (-(1 / 250 : ℝ)) using 1 <;> norm_num
  have hplus : (251 / 250 : ℝ) ≤ Real.exp (1 / 250 : ℝ) := by
    convert Real.add_one_le_exp (1 / 250 : ℝ) using 1 <;> norm_num
  have hprod :
      Real.exp (-(1 / 250 : ℝ)) * Real.exp (1 / 250 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hupperBase :
      Real.exp (-(1 / 250 : ℝ)) ≤ (250 / 251 : ℝ) := by
    have hm :
        Real.exp (-(1 / 250 : ℝ)) * (251 / 250 : ℝ) ≤ 1 := by
      calc
        Real.exp (-(1 / 250 : ℝ)) * (251 / 250 : ℝ) ≤
            Real.exp (-(1 / 250 : ℝ)) * Real.exp (1 / 250 : ℝ) :=
          mul_le_mul_of_nonneg_left hplus (Real.exp_nonneg _)
        _ = 1 := hprod
    nlinarith
  have pow_mono : ∀ (a b : ℝ), 0 ≤ a → a ≤ b → ∀ n : ℕ, a ^ n ≤ b ^ n := by
    intro a b ha hab n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) n)
  have pow_strict :
      ∀ (a b : ℝ), 0 ≤ a → a < b → ∀ n : ℕ, 0 < n → a ^ n < b ^ n := by
    intro a b ha hab n hn
    cases n with
    | zero => norm_num at hn
    | succ n =>
        rw [pow_succ, pow_succ]
        have hp : a ^ n ≤ b ^ n := pow_mono a b ha hab.le n
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hp ha)
          (mul_lt_mul_of_pos_left hab (pow_pos (lt_of_le_of_lt ha hab) n))
  have hlpow :
      (249 / 250 : ℝ) ^ (500 : ℕ) ≤
        Real.exp (-(1 / 250 : ℝ)) ^ (500 : ℕ) :=
    pow_mono _ _ (by norm_num) hminus 500
  have hupow :
      Real.exp (-(1 / 250 : ℝ)) ^ (500 : ℕ) ≤
        (250 / 251 : ℝ) ^ (500 : ℕ) :=
    pow_mono _ _ (Real.exp_nonneg _) hupperBase 500
  have hid :
      Real.exp (-(1 / 250 : ℝ)) ^ (500 : ℕ) = Real.exp (-2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hsmallLo :
      (409 / 500 : ℝ) < (249 / 250 : ℝ) ^ (50 : ℕ) := by
    set_option maxRecDepth 4096 in
      norm_num [div_pow]
  have hsmallHi :
      (250 / 251 : ℝ) ^ (50 : ℕ) < (8191 / 10000 : ℝ) := by
    set_option maxRecDepth 4096 in
      norm_num [div_pow]
  have hgroupLo :
      (409 / 500 : ℝ) ^ (10 : ℕ) < (249 / 250 : ℝ) ^ (500 : ℕ) := by
    calc
      (409 / 500 : ℝ) ^ (10 : ℕ) <
          ((249 / 250 : ℝ) ^ (50 : ℕ)) ^ (10 : ℕ) :=
        pow_strict _ _ (by norm_num) hsmallLo 10 (by norm_num)
      _ = (249 / 250 : ℝ) ^ (500 : ℕ) := by
        rw [← pow_mul]
  have hgroupHi :
      (250 / 251 : ℝ) ^ (500 : ℕ) <
        (8191 / 10000 : ℝ) ^ (10 : ℕ) := by
    calc
      (250 / 251 : ℝ) ^ (500 : ℕ) =
          ((250 / 251 : ℝ) ^ (50 : ℕ)) ^ (10 : ℕ) := by
        rw [← pow_mul]
      _ < (8191 / 10000 : ℝ) ^ (10 : ℕ) :=
        pow_strict _ _ (pow_nonneg (by norm_num) 50) hsmallHi 10 (by norm_num)
  have hratLo :
      (67 / 500 : ℝ) < (409 / 500 : ℝ) ^ (10 : ℕ) := by
    norm_num [div_pow]
  have hratHi :
      (8191 / 10000 : ℝ) ^ (10 : ℕ) < (17 / 125 : ℝ) := by
    norm_num [div_pow]
  have hlower : (67 / 500 : ℝ) < Real.exp (-2) := by
    rw [← hid]
    exact hratLo.trans (hgroupLo.trans_le hlpow)
  have hupper : Real.exp (-2) < (17 / 125 : ℝ) := by
    rw [← hid]
    exact hupow.trans_lt (hgroupHi.trans hratHi)
  rw [abs_lt]
  constructor
  · norm_num
    linarith
  · norm_num
    linarith

theorem gap9 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1) :
    y x = x * Real.exp (x - 1) := by
  have hx₁ : x - 1 < 0 := by linarith
  simp [y, abs_of_pos h₁, abs_of_neg hx₁]

theorem gap10 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1) :
    deriv y x = (x + 1) * Real.exp (x - 1) := by
  have hfun : y =ᶠ[𝓝 x] (fun z : ℝ => z * Real.exp (z - 1)) := by
    filter_upwards [eventually_gt_nhds h₁, eventually_lt_nhds h₂] with z hz₁ hz₂
    exact gap9 z hz₁ hz₂
  have hder :
      HasDerivAt (fun z : ℝ => z * Real.exp (z - 1))
        ((x + 1) * Real.exp (x - 1)) x := by
    convert (hasDerivAt_id x).mul
      ((Real.hasDerivAt_exp (x - 1)).comp x
        ((hasDerivAt_id x).sub_const 1)) using 1 <;>
      simp [Function.comp_apply] <;> ring
  calc
    deriv y x = deriv (fun z : ℝ => z * Real.exp (z - 1)) x := hfun.deriv_eq
    _ = (x + 1) * Real.exp (x - 1) := hder.deriv

theorem gap11 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1) :
    0 < (x + 1) * Real.exp (x - 1) := by
  exact mul_pos (by linarith) (Real.exp_pos _)

theorem gap12 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1) :
    0 < deriv y x := by
  rw [gap10 x h₁ h₂]
  exact gap11 x h₁ h₂

theorem gap13 : IsMinOn y Set.univ 0 := by
  intro x hx
  have hy0 : y 0 = 0 := by
    norm_num [y]
  rw [hy0]
  exact mul_nonneg (abs_nonneg x) (Real.exp_nonneg _)

theorem gap14 : y 0 = 0 := by
  norm_num [y]

theorem gap15 (x : ℝ) (hx : 1 < x) :
    y x = x * Real.exp (1 - x) := by
  have hx₀ : 0 < x := by linarith
  have hx₁ : 0 < x - 1 := by linarith
  simp [y, abs_of_pos hx₀, abs_of_pos hx₁]

theorem gap16 (x : ℝ) (hx : 1 < x) :
    deriv y x = (1 - x) * Real.exp (1 - x) := by
  have hfun : y =ᶠ[𝓝 x] (fun z : ℝ => z * Real.exp (1 - z)) := by
    filter_upwards [eventually_gt_nhds hx] with z hz
    exact gap15 z hz
  have hinner : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hder :
      HasDerivAt (fun z : ℝ => z * Real.exp (1 - z))
        ((1 - x) * Real.exp (1 - x)) x := by
    convert (hasDerivAt_id x).mul
      ((Real.hasDerivAt_exp (1 - x)).comp x hinner) using 1 <;>
      simp [Function.comp_apply] <;> ring
  calc
    deriv y x = deriv (fun z : ℝ => z * Real.exp (1 - z)) x := hfun.deriv_eq
    _ = (1 - x) * Real.exp (1 - x) := hder.deriv

theorem gap17 (x : ℝ) (hx : 1 < x) :
    (1 - x) * Real.exp (1 - x) < 0 := by
  exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)

theorem gap18 (x : ℝ) (hx : 1 < x) : deriv y x < 0 := by
  rw [gap16 x hx]
  exact gap17 x hx

theorem gap19 : IsMaxOn y Set.univ 1 := by
  intro x hx
  have hy1 : y 1 = 1 := by
    norm_num [y]
  rw [hy1]
  unfold y
  have habs : |x| ≤ |x - 1| + 1 := by
    calc
      |x| = |(x - 1) + 1| := by
        congr 1
        ring
      _ ≤ |x - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |x - 1| + 1 := by norm_num
  have hexp : |x| ≤ Real.exp |x - 1| := by
    exact habs.trans (by
      simpa [add_comm] using Real.add_one_le_exp |x - 1|)
  calc
    |x| * Real.exp (-|x - 1|) ≤
        Real.exp |x - 1| * Real.exp (-|x - 1|) :=
      mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)
    _ = 1 := by
      rw [← Real.exp_add]
      simp

theorem gap20 : y 1 = 1 := by
  norm_num [y]

end
end ProofGap.Exercise1444
