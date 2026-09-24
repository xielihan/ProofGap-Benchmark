import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise447

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3 : ℝ)
  else -Real.rpow (-x) (1 / 3 : ℝ)
def original (x : ℝ) : ℝ :=
  (signedCbrt (27 + x) - signedCbrt (27 - x)) /
    (x + 2 * signedCbrt (x ^ 4))
def cancelled (x : ℝ) : ℝ :=
  2 / ((1 + 2 * signedCbrt x) *
    (signedCbrt ((27 + x) ^ 2) + signedCbrt (27 ^ 2 - x ^ 2) +
      signedCbrt ((27 - x) ^ 2)))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_447/1.txt`; use signed cube roots around zero. -/
private lemma cube_strict {a b : ℝ} (h : a < b) : a ^ 3 < b ^ 3 := by
  have hs : 0 < (b - a) ^ 2 := pow_pos (sub_pos.mpr h) 2
  have hq : 0 < b ^ 2 + b * a + a ^ 2 := by
    nlinarith [sq_nonneg (a + b), hs]
  calc
    a ^ 3 < a ^ 3 + (b - a) * (b ^ 2 + b * a + a ^ 2) := by
      exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr h) hq)
    _ = b ^ 3 := by ring

private lemma cube_injective {a b : ℝ} (h : a ^ 3 = b ^ 3) : a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hc := cube_strict hlt
    linarith
  · have hc := cube_strict hgt
    linarith

private lemma signedCbrt_cubed (x : ℝ) : signedCbrt x ^ 3 = x := by
  unfold signedCbrt
  split_ifs with hx
  · calc
      (Real.rpow x (1 / 3 : ℝ)) ^ 3 =
          Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
            exact (Real.rpow_natCast _ 3).symm
      _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
            exact (Real.rpow_mul hx (1 / 3 : ℝ) (3 : ℝ)).symm
      _ = x := by norm_num
  · have hx' : 0 ≤ -x := by linarith
    have hp : (Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 = -x := by
      calc
        (Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
            Real.rpow (Real.rpow (-x) (1 / 3 : ℝ)) (3 : ℝ) := by
              exact (Real.rpow_natCast _ 3).symm
        _ = Real.rpow (-x) ((1 / 3 : ℝ) * 3) := by
              exact (Real.rpow_mul hx' (1 / 3 : ℝ) (3 : ℝ)).symm
        _ = -x := by norm_num
    calc
      (-Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
          -(Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 := by ring
      _ = -(-x) := by rw [hp]
      _ = x := by ring

private lemma signedCbrt_zero : signedCbrt 0 = 0 := by
  apply cube_injective
  rw [signedCbrt_cubed]
  norm_num

private lemma signedCbrt_729 : signedCbrt (729 : ℝ) = 9 := by
  apply cube_injective
  rw [signedCbrt_cubed]
  norm_num

private lemma signedCbrt_continuousAt (a : ℝ) : ContinuousAt signedCbrt a := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hlo : (signedCbrt a - ε) ^ 3 < a := by
    calc
      (signedCbrt a - ε) ^ 3 < signedCbrt a ^ 3 :=
        cube_strict (sub_lt_self _ hε)
      _ = a := signedCbrt_cubed a
  have hhi : a < (signedCbrt a + ε) ^ 3 := by
    calc
      a = signedCbrt a ^ 3 := (signedCbrt_cubed a).symm
      _ < (signedCbrt a + ε) ^ 3 :=
        cube_strict (lt_add_of_pos_right _ hε)
  refine ⟨min (a - (signedCbrt a - ε) ^ 3)
      ((signedCbrt a + ε) ^ 3 - a), ?_, ?_⟩
  · exact lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  · intro x hx
    rw [Real.dist_eq] at hx ⊢
    rw [abs_lt] at hx ⊢
    have hlcube :
        (signedCbrt a - ε) ^ 3 < signedCbrt x ^ 3 := by
      rw [signedCbrt_cubed]
      nlinarith [min_le_left
        (a - (signedCbrt a - ε) ^ 3)
        ((signedCbrt a + ε) ^ 3 - a)]
    have hucube :
        signedCbrt x ^ 3 < (signedCbrt a + ε) ^ 3 := by
      rw [signedCbrt_cubed]
      nlinarith [min_le_right
        (a - (signedCbrt a - ε) ^ 3)
        ((signedCbrt a + ε) ^ 3 - a)]
    have hlroot : signedCbrt a - ε < signedCbrt x := by
      by_contra hnot
      have hle : signedCbrt x ≤ signedCbrt a - ε := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hc := cube_strict hlt
        linarith
      · rw [heq] at hlcube
        exact (lt_irrefl _ hlcube)
    have huroot : signedCbrt x < signedCbrt a + ε := by
      by_contra hnot
      have hle : signedCbrt a + ε ≤ signedCbrt x := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hc := cube_strict hlt
        linarith
      · rw [← heq] at hucube
        exact (lt_irrefl _ hucube)
    constructor <;> linarith

private lemma original_eq_cancelled_of_ne {x : ℝ} (hx : x ≠ 0) :
    original x = cancelled x := by
  let A : ℝ := signedCbrt (27 + x)
  let B : ℝ := signedCbrt (27 - x)
  have hA : A ^ 3 = 27 + x := by
    dsimp [A]
    exact signedCbrt_cubed (27 + x)
  have hB : B ^ 3 = 27 - x := by
    dsimp [B]
    exact signedCbrt_cubed (27 - x)
  have hsquarePlus : signedCbrt ((27 + x) ^ 2) = A ^ 2 := by
    apply cube_injective
    rw [signedCbrt_cubed]
    calc
      (27 + x) ^ 2 = (A ^ 3) ^ 2 := by rw [hA]
      _ = (A ^ 2) ^ 3 := by ring
  have hsquareMinus : signedCbrt ((27 - x) ^ 2) = B ^ 2 := by
    apply cube_injective
    rw [signedCbrt_cubed]
    calc
      (27 - x) ^ 2 = (B ^ 3) ^ 2 := by rw [hB]
      _ = (B ^ 2) ^ 3 := by ring
  have hmiddle : signedCbrt (27 ^ 2 - x ^ 2) = A * B := by
    apply cube_injective
    rw [signedCbrt_cubed]
    calc
      (27 : ℝ) ^ 2 - x ^ 2 = (27 + x) * (27 - x) := by ring
      _ = A ^ 3 * B ^ 3 := by rw [hA, hB]
      _ = (A * B) ^ 3 := by ring
  let S : ℝ :=
    signedCbrt ((27 + x) ^ 2) + signedCbrt (27 ^ 2 - x ^ 2) +
      signedCbrt ((27 - x) ^ 2)
  have hnum : (A - B) * S = 2 * x := by
    dsimp [S]
    rw [hsquarePlus, hmiddle, hsquareMinus]
    nlinarith [hA, hB]
  have hS : S ≠ 0 := by
    intro hzero
    have hxzero : x = 0 := by
      rw [hzero, mul_zero] at hnum
      linarith
    exact hx hxzero
  have hx4 : signedCbrt (x ^ 4) = x * signedCbrt x := by
    apply cube_injective
    rw [signedCbrt_cubed, mul_pow, signedCbrt_cubed]
    ring
  have hratio : (A - B) / x = 2 / S :=
    (div_eq_div_iff hx hS).2 hnum
  unfold original cancelled
  change
    (A - B) / (x + 2 * signedCbrt (x ^ 4)) =
      2 / ((1 + 2 * signedCbrt x) * S)
  rw [hx4]
  have hden : x + 2 * (x * signedCbrt x) =
      x * (1 + 2 * signedCbrt x) := by ring
  rw [hden]
  calc
    (A - B) / (x * (1 + 2 * signedCbrt x)) =
        ((A - B) / x) / (1 + 2 * signedCbrt x) := by
          rw [div_div]
    _ = (2 / S) / (1 + 2 * signedCbrt x) := by rw [hratio]
    _ = 2 / (S * (1 + 2 * signedCbrt x)) := by rw [div_div]
    _ = 2 / ((1 + 2 * signedCbrt x) * S) := by
      rw [mul_comm S]

private lemma original_eventuallyEq_cancelled :
    original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] cancelled := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  apply original_eq_cancelled_of_ne
  simpa using hx

private lemma cancelled_continuousAt_zero : ContinuousAt cancelled 0 := by
  have hplusInner : ContinuousAt (fun x : ℝ => (27 + x) ^ 2) 0 :=
    (continuousAt_const.add continuousAt_id).pow 2
  have hminusInner : ContinuousAt (fun x : ℝ => (27 - x) ^ 2) 0 :=
    (continuousAt_const.sub continuousAt_id).pow 2
  have hmiddleInner : ContinuousAt (fun x : ℝ => 27 ^ 2 - x ^ 2) 0 :=
    continuousAt_const.sub (continuousAt_id.pow 2)
  have hplusComp : ContinuousAt
      (signedCbrt ∘ fun x : ℝ => (27 + x) ^ 2) 0 :=
    Filter.Tendsto.comp
      (signedCbrt_continuousAt ((27 + (0 : ℝ)) ^ 2)) hplusInner
  have hminusComp : ContinuousAt
      (signedCbrt ∘ fun x : ℝ => (27 - x) ^ 2) 0 :=
    Filter.Tendsto.comp
      (signedCbrt_continuousAt ((27 - (0 : ℝ)) ^ 2)) hminusInner
  have hmiddleComp : ContinuousAt
      (signedCbrt ∘ fun x : ℝ => 27 ^ 2 - x ^ 2) 0 :=
    Filter.Tendsto.comp
      (signedCbrt_continuousAt ((27 : ℝ) ^ 2 - (0 : ℝ) ^ 2)) hmiddleInner
  have hplus : ContinuousAt (fun x : ℝ => signedCbrt ((27 + x) ^ 2)) 0 := by
    simpa only [Function.comp_apply] using hplusComp
  have hminus : ContinuousAt (fun x : ℝ => signedCbrt ((27 - x) ^ 2)) 0 := by
    simpa only [Function.comp_apply] using hminusComp
  have hmiddle : ContinuousAt (fun x : ℝ => signedCbrt (27 ^ 2 - x ^ 2)) 0 := by
    simpa only [Function.comp_apply] using hmiddleComp
  have hfactor : ContinuousAt (fun x : ℝ => 1 + 2 * signedCbrt x) 0 :=
    continuousAt_const.add
      (continuousAt_const.mul (signedCbrt_continuousAt 0))
  have hsum : ContinuousAt
      (fun x : ℝ => signedCbrt ((27 + x) ^ 2) +
        signedCbrt (27 ^ 2 - x ^ 2) + signedCbrt ((27 - x) ^ 2)) 0 :=
    (hplus.add hmiddle).add hminus
  have hden := hfactor.mul hsum
  unfold cancelled
  apply continuousAt_const.div hden
  norm_num [signedCbrt_zero, signedCbrt_729]

theorem gap1 : HasLimitAt original 0 (2 / 27) ↔
    HasLimitAt cancelled 0 (2 / 27) := by
  unfold HasLimitAt
  constructor
  · intro h
    rw [Filter.tendsto_def] at h ⊢
    intro s hs
    have hpre := h s hs
    filter_upwards [original_eventuallyEq_cancelled, hpre] with x heq hx
    change cancelled x ∈ s
    change original x ∈ s at hx
    simpa [heq] using hx
  · intro h
    rw [Filter.tendsto_def] at h ⊢
    intro s hs
    have hpre := h s hs
    filter_upwards [original_eventuallyEq_cancelled, hpre] with x heq hx
    change original x ∈ s
    change cancelled x ∈ s at hx
    simpa [heq] using hx

/-- Source: `proof_gap/exercise_447/2.txt`. -/
theorem gap2 : HasLimitAt original 0 (2 / 27) ↔
    HasLimitAt cancelled 0 (2 / 27) := by
  exact gap1

/-- Source: `proof_gap/exercise_447/3.txt`. -/
theorem gap3 : HasLimitAt cancelled 0 (2 / 27) := by
  unfold HasLimitAt
  have hvalue : cancelled 0 = (2 / 27 : ℝ) := by
    norm_num [cancelled, signedCbrt_zero, signedCbrt_729]
  rw [← hvalue]
  exact cancelled_continuousAt_zero.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_447/4.txt`. -/
theorem gap4 : HasLimitAt original 0 (2 / 27) := by
  exact gap1.mpr gap3

end

end ProofGap.Exercise447
