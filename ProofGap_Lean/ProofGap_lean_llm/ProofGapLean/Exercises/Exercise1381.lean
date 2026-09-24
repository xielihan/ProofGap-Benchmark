import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise1381

noncomputable section

open Filter

def f (x : ℝ) : ℝ := Real.exp (2 * x - x ^ 2)

def rawPolynomial (x : ℝ) : ℝ :=
  1 + (2 * x - x ^ 2) +
    (2 * x - x ^ 2) ^ 2 / (Nat.factorial 2 : ℝ) +
    (2 * x - x ^ 2) ^ 3 / (Nat.factorial 3 : ℝ) +
    (2 * x - x ^ 2) ^ 4 / (Nat.factorial 4 : ℝ) +
    (2 * x - x ^ 2) ^ 5 / (Nat.factorial 5 : ℝ)

def collectedPolynomial (x : ℝ) : ℝ :=
  1 + 2 * x + x ^ 2 - (2 / 3 : ℝ) * x ^ 3 -
    (5 / 6 : ℝ) * x ^ 4 - (1 / 15 : ℝ) * x ^ 5

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

theorem gap1 :
    AgreesToOrderAt f rawPolynomial 0 5 := by
  have hy : Tendsto (fun x : ℝ => 2 * x - x ^ 2)
      (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => 2 * x - x ^ 2) 0 := by
      fun_prop
    convert hc.tendsto using 1 <;> norm_num
  have hexp :=
    (Real.exp_sub_sum_range_succ_isLittleO_pow 5).comp_tendsto hy
  have hlin : (fun x : ℝ => 2 * x - x ^ 2) =O[nhds 0]
      (fun x : ℝ => x) := by
    have hb : (fun x : ℝ => 2 - x) =O[nhds 0]
        (fun _ : ℝ => (1 : ℝ)) := by
      have ht : Tendsto (fun x : ℝ => 2 - x) (nhds 0) (nhds 2) := by
        have hc : ContinuousAt (fun x : ℝ => 2 - x) 0 := by fun_prop
        convert hc.tendsto using 1 <;> norm_num
      exact ht.isBigO_one ℝ
    have hm :=
      (Asymptotics.isBigO_refl (fun x : ℝ => x) (nhds 0)).mul hb
    exact hm.congr (fun x => by ring) (fun x => by ring)
  have hp := hlin.pow 5
  unfold AgreesToOrderAt
  have h := hexp.trans_isBigO hp
  refine h.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
  · intro x
    unfold f rawPolynomial
    norm_num [Finset.sum_range_succ]
  · intro x
    simp

theorem gap2 :
    AgreesToOrderAt rawPolynomial collectedPolynomial 0 5 := by
  let r : ℝ → ℝ := fun x =>
    -x ^ 4 / 120 + x ^ 3 / 12 - 7 * x ^ 2 / 24 + x / 3 + 1 / 6
  have hr_tend : Tendsto r (nhds 0) (nhds (1 / 6 : ℝ)) := by
    have hc : ContinuousAt r 0 := by
      dsimp [r]
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [r]
  have hr : r =O[nhds 0] (fun _ : ℝ => (1 : ℝ)) :=
    hr_tend.isBigO_one ℝ
  have hp : (fun x : ℝ => x ^ 6) =o[nhds 0]
      (fun x : ℝ => x ^ 5) :=
    Asymptotics.isLittleO_pow_pow (by norm_num)
  have h := hp.mul_isBigO hr
  unfold AgreesToOrderAt
  refine h.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
  · intro x
    dsimp [r]
    unfold rawPolynomial collectedPolynomial
    norm_num
    ring
  · intro x
    simp

theorem gap3 :
    AgreesToOrderAt f collectedPolynomial 0 5 := by
  have h1 := gap1
  have h2 := gap2
  unfold AgreesToOrderAt at h1 h2 ⊢
  have h := h1.add h2
  refine h.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
  · intro x
    ring
  · intro x
    ring

end

end ProofGap.Exercise1381
