import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1617

noncomputable section

def f (x : ℝ) := x ^ 3 - 6 * x + 2
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def smallApproximant : ℕ → ℝ
  | 1 => 0.4
  | 2 => 0.342
  | 3 => 0.340
  | _ => 0
def middleApproximant : ℕ → ℝ
  | 1 => 2.15
  | 2 => 2.22
  | 3 => 2.245
  | 4 => 2.256
  | 5 => 2.260
  | 6 => 2.261
  | 7 => 2.262
  | _ => 0
def negativeApproximant : ℕ → ℝ
  | 1 => -2.461
  | 2 => -2.574
  | 3 => -2.596
  | 4 => -2.601
  | 5 => -2.602
  | _ => 0
def reportedRoots : Set ℝ := {0.340, 2.262, -2.602}
def ApproxRootSet (samples : Set ℝ) (tolerance : ℝ) : Prop :=
  (∀ s ∈ samples, ∃ r, f r = 0 ∧ |s - r| < tolerance) ∧
    (∀ r, f r = 0 → ∃ s ∈ samples, |r - s| < tolerance)

private theorem hasDerivAt_f (x : ℝ) : HasDerivAt f (3 * x ^ 2 - 6) x := by
  unfold f
  convert (((((hasDerivAt_id x).mul (hasDerivAt_id x)).mul (hasDerivAt_id x)).sub ((hasDerivAt_id x).const_mul 6)).add_const 2) using 1
  · funext y
    dsimp [id]
    ring
  · dsimp [id]
    ring

private theorem deriv_f (x : ℝ) : deriv f x = 3 * x ^ 2 - 6 :=
  (hasDerivAt_f x).deriv

private theorem continuous_f : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hasDerivAt_f x).continuousAt

private theorem f_sub_f (x y : ℝ) :
    f x - f y = (x - y) * (x ^ 2 + x * y + y ^ 2 - 6) := by
  unfold f
  ring

private theorem root_error_bound {s r m : ℝ} (hr : f r = 0) (hm : 0 < m)
    (hq : m ≤ |s ^ 2 + s * r + r ^ 2 - 6|) :
    |s - r| ≤ |f s| / m := by
  have hfac : f s = (s - r) * (s ^ 2 + s * r + r ^ 2 - 6) := by
    calc
      f s = f s - f r := by rw [hr]; ring
      _ = (s - r) * (s ^ 2 + s * r + r ^ 2 - 6) := f_sub_f s r
  have habs : |f s| = |s - r| * |s ^ 2 + s * r + r ^ 2 - 6| := by
    rw [hfac, abs_mul]
  apply (le_div_iff₀ hm).2
  have hmul := mul_nonneg (abs_nonneg (s - r)) (sub_nonneg.mpr hq)
  nlinarith

theorem gap1 : f 0 = 2 := by
  norm_num [f]
theorem gap2 : f 1 = -3 := by
  norm_num [f]
theorem gap3 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv f x = 3 * x ^ 2 - 6 ∧ deriv f x ≠ 0 := by
  constructor
  · exact deriv_f x
  · rw [deriv_f]
    have hx2 : x ^ 2 < 1 := by
      have hp := mul_pos hx.1 (sub_pos.mpr hx.2)
      nlinarith
    nlinarith
theorem gap4 : ∃! ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 ∧ f ξ = 0 := by
  have hz : (0 : ℝ) ∈ Set.Icc (-f 0) (-f 1) := by
    rw [gap1, gap2]
    norm_num
  have himg : (0 : ℝ) ∈ (fun x : ℝ => -f x) '' Set.Icc 0 1 :=
    intermediate_value_Icc (by norm_num) continuous_f.neg.continuousOn hz
  rcases himg with ⟨ξ, hξ, hval⟩
  have hfξ : f ξ = 0 := by linarith
  have hξ0 : ξ ≠ 0 := by
    intro h
    subst ξ
    norm_num [f] at hfξ
  have hξ1 : ξ ≠ 1 := by
    intro h
    subst ξ
    norm_num [f] at hfξ
  have hξoo : ξ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hξ.1 (Ne.symm hξ0), lt_of_le_of_ne hξ.2 hξ1⟩
  refine ⟨ξ, ⟨hξoo, hfξ⟩, ?_⟩
  intro y hy
  have hy2 : y ^ 2 < 1 := by
    have hp := mul_pos hy.1.1 (sub_pos.mpr hy.1.2)
    nlinarith
  have hξ2 : ξ ^ 2 < 1 := by
    have hp := mul_pos hξoo.1 (sub_pos.mpr hξoo.2)
    nlinarith
  have hyξ : y * ξ < 1 := by
    have hp := mul_pos (sub_pos.mpr hy.1.2) (sub_pos.mpr hξoo.2)
    nlinarith
  have hq : y ^ 2 + y * ξ + ξ ^ 2 - 6 < 0 := by nlinarith
  have hp : (y - ξ) * (y ^ 2 + y * ξ + ξ ^ 2 - 6) = 0 := by
    calc
      (y - ξ) * (y ^ 2 + y * ξ + ξ ^ 2 - 6) = f y - f ξ := (f_sub_f y ξ).symm
      _ = 0 := by rw [hy.2, hfξ]; ring
  rcases mul_eq_zero.mp hp with h | h
  · linarith
  · exact (ne_of_lt hq h).elim
theorem gap5 : smallApproximant 1 = 0.4 := by
  rfl
theorem gap6 : f 0.4 = -0.336 := by
  norm_num [f]
theorem gap7 : smallApproximant 2 = 0.342 := by
  rfl
theorem gap8 : Approx (f 0.342) (-0.012) (1 / 100000) := by
  norm_num [Approx, f, abs_lt]
theorem gap9 : smallApproximant 3 = 0.340 := by
  rfl
theorem gap10 : Approx (f 0.340) (-0.001) (1 / 2000) := by
  norm_num [Approx, f, abs_lt]
theorem gap11 : ∃ m₁ : ℝ, m₁ = 3 := by
  exact ⟨3, rfl⟩
theorem gap12 :
    sInf ((fun x : ℝ => |deriv f x|) '' Set.Ioo (0 : ℝ) 1) = 3 := by
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo (0 : ℝ) 1
  change sInf S = 3
  have hne : S.Nonempty := by
    refine ⟨|deriv f (1 / 2)|, ?_⟩
    exact ⟨1 / 2, by norm_num, rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro b ⟨x, hx, rfl⟩
    exact abs_nonneg _
  apply le_antisymm
  · by_contra hnot
    have hgt : 3 < sInf S := lt_of_not_ge hnot
    have hmem : |deriv f (1 / 2)| ∈ S := ⟨1 / 2, by norm_num, rfl⟩
    have hup := csInf_le hbdd hmem
    rw [deriv_f] at hup
    norm_num at hup
    let d : ℝ := sInf S - 3
    let x : ℝ := 1 - d / 12
    have hd : 0 < d := by dsimp [d]; linarith
    have hx : x ∈ Set.Ioo (0 : ℝ) 1 := by
      dsimp [x, d]
      constructor <;> nlinarith
    have hx2 : x ^ 2 < 1 := by
      have hp := mul_pos hx.1 (sub_pos.mpr hx.2)
      nlinarith
    have hneg : 3 * x ^ 2 - 6 < 0 := by nlinarith
    have hnear : |deriv f x| ∈ S := ⟨x, hx, rfl⟩
    have hle := csInf_le hbdd hnear
    have hlt : |deriv f x| < sInf S := by
      rw [deriv_f, abs_of_neg hneg]
      dsimp [x, d]
      nlinarith [sq_nonneg d]
    linarith
  · apply le_csInf hne
    intro b hb
    rcases hb with ⟨x, hx, rfl⟩
    change 3 ≤ |deriv f x|
    rw [deriv_f]
    have hx2 : x ^ 2 < 1 := by
      have hp := mul_pos hx.1 (sub_pos.mpr hx.2)
      nlinarith
    rw [abs_of_neg (by nlinarith)]
    nlinarith
theorem gap13 :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ f ξ₁ = 0 ∧
      |0.340 - ξ₁| ≤ |f 0.340| / 3 := by
  rcases gap4 with ⟨ξ, hξ, huniq⟩
  refine ⟨ξ, hξ.1, hξ.2, ?_⟩
  have hξ2 : ξ ^ 2 < 1 := by
    have hp := mul_pos hξ.1.1 (sub_pos.mpr hξ.1.2)
    nlinarith
  have hq : (0.340 : ℝ) ^ 2 + 0.340 * ξ + ξ ^ 2 - 6 < -3 := by
    nlinarith
  have habsq : 3 ≤ |(0.340 : ℝ) ^ 2 + 0.340 * ξ + ξ ^ 2 - 6| := by
    rw [abs_of_neg (by linarith)]
    linarith
  exact root_error_bound hξ.2 (by norm_num) habsq
theorem gap14 : |f 0.340| / 3 < 0.001 := by
  norm_num [f, abs_of_nonneg, abs_of_neg]
theorem gap15 :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ f ξ₁ = 0 ∧
      |0.340 - ξ₁| < 0.001 := by
  rcases gap13 with ⟨ξ, hξ, hfξ, herr⟩
  exact ⟨ξ, hξ, hfξ, lt_of_le_of_lt herr gap14⟩
theorem gap16 : f 2 = -2 := by
  norm_num [f]
theorem gap17 : f 3 = 11 := by
  norm_num [f]
theorem gap18 (x : ℝ) (hx : x ∈ Set.Ioo (2 : ℝ) 3) :
    deriv f x ≠ 0 := by
  rw [deriv_f]
  have hxplus : 0 < x + 2 := by linarith [hx.1]
  have hp := mul_pos (sub_pos.mpr hx.1) hxplus
  have hx2 : 4 < x ^ 2 := by nlinarith
  nlinarith
theorem gap19 : ∃! ξ : ℝ, ξ ∈ Set.Ioo (2 : ℝ) 3 ∧ f ξ = 0 := by
  have hz : (0 : ℝ) ∈ Set.Icc (f 2) (f 3) := by
    rw [gap16, gap17]
    norm_num
  have himg : (0 : ℝ) ∈ f '' Set.Icc 2 3 :=
    intermediate_value_Icc (by norm_num) continuous_f.continuousOn hz
  rcases himg with ⟨ξ, hξ, hfξ⟩
  have hξ2 : ξ ≠ 2 := by
    intro h
    subst ξ
    norm_num [f] at hfξ
  have hξ3 : ξ ≠ 3 := by
    intro h
    subst ξ
    norm_num [f] at hfξ
  have hξoo : ξ ∈ Set.Ioo (2 : ℝ) 3 :=
    ⟨lt_of_le_of_ne hξ.1 (Ne.symm hξ2), lt_of_le_of_ne hξ.2 hξ3⟩
  refine ⟨ξ, ⟨hξoo, hfξ⟩, ?_⟩
  intro y hy
  have hyplus : 0 < y + 2 := by linarith [hy.1.1]
  have hξplus : 0 < ξ + 2 := by linarith [hξoo.1]
  have hy2 : 4 < y ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hy.1.1) hyplus
    nlinarith
  have hξsq : 4 < ξ ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hξoo.1) hξplus
    nlinarith
  have hyξ : 4 < y * ξ := by
    have hp := mul_pos (sub_pos.mpr hy.1.1) (sub_pos.mpr hξoo.1)
    nlinarith [hy.1.1, hξoo.1]
  have hq : 0 < y ^ 2 + y * ξ + ξ ^ 2 - 6 := by nlinarith
  have hp : (y - ξ) * (y ^ 2 + y * ξ + ξ ^ 2 - 6) = 0 := by
    calc
      (y - ξ) * (y ^ 2 + y * ξ + ξ ^ 2 - 6) = f y - f ξ := (f_sub_f y ξ).symm
      _ = 0 := by rw [hy.2, hfξ]; ring
  rcases mul_eq_zero.mp hp with h | h
  · linarith
  · exact (ne_of_gt hq h).elim
theorem gap20 : middleApproximant 1 = 2.15 := by
  rfl
theorem gap21 : middleApproximant 2 = 2.22 := by
  rfl
theorem gap22 : middleApproximant 3 = 2.245 := by
  rfl
theorem gap23 : middleApproximant 4 = 2.256 := by
  rfl
theorem gap24 : middleApproximant 5 = 2.260 := by
  rfl
theorem gap25 : middleApproximant 6 = 2.261 := by
  rfl
theorem gap26 : middleApproximant 7 = 2.262 := by
  rfl
theorem gap27 : Approx (f 2.262) 0.003 (1 / 500) := by
  norm_num [Approx, f, abs_lt]
theorem gap28 : ∃ m₂ : ℝ, m₂ = 6 := by
  exact ⟨6, rfl⟩
theorem gap29 :
    sInf ((fun x : ℝ => |deriv f x|) '' Set.Ioo (2 : ℝ) 3) = 6 := by
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo (2 : ℝ) 3
  change sInf S = 6
  have hne : S.Nonempty := by
    refine ⟨|deriv f (5 / 2)|, ?_⟩
    exact ⟨5 / 2, by norm_num, rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro b ⟨x, hx, rfl⟩
    exact abs_nonneg _
  apply le_antisymm
  · by_contra hnot
    have hgt : 6 < sInf S := lt_of_not_ge hnot
    have hmem : |deriv f (5 / 2)| ∈ S := ⟨5 / 2, by norm_num, rfl⟩
    have hup := csInf_le hbdd hmem
    rw [deriv_f] at hup
    norm_num at hup
    let d : ℝ := sInf S - 6
    let x : ℝ := 2 + d / 100
    have hd : 0 < d := by dsimp [d]; linarith
    have hdtop : d ≤ 27 / 4 := by dsimp [d]; linarith
    have hdprod : 0 ≤ d * (27 / 4 - d) :=
      mul_nonneg (le_of_lt hd) (sub_nonneg.mpr hdtop)
    have hx : x ∈ Set.Ioo (2 : ℝ) 3 := by
      dsimp [x]
      constructor <;> nlinarith
    have hxplus : 0 < x + 2 := by linarith [hx.1]
    have hpos : 0 < 3 * x ^ 2 - 6 := by
      have hp := mul_pos (sub_pos.mpr hx.1) hxplus
      nlinarith
    have hnear : |deriv f x| ∈ S := ⟨x, hx, rfl⟩
    have hle := csInf_le hbdd hnear
    have hlt : |deriv f x| < sInf S := by
      rw [deriv_f, abs_of_pos hpos]
      dsimp [x, d]
      nlinarith [hdprod]
    linarith
  · apply le_csInf hne
    intro b hb
    rcases hb with ⟨x, hx, rfl⟩
    change 6 ≤ |deriv f x|
    rw [deriv_f]
    have hxplus : 0 < x + 2 := by linarith [hx.1]
    have hx2 : 4 < x ^ 2 := by
      have hp := mul_pos (sub_pos.mpr hx.1) hxplus
      nlinarith
    rw [abs_of_pos (by nlinarith)]
    nlinarith
theorem gap30 :
    ∃ ξ₂ : ℝ, ξ₂ ∈ Set.Ioo (2 : ℝ) 3 ∧ f ξ₂ = 0 ∧
      |2.262 - ξ₂| ≤ |f 2.262| / 6 := by
  rcases gap19 with ⟨ξ, hξ, huniq⟩
  refine ⟨ξ, hξ.1, hξ.2, ?_⟩
  have hξplus : 0 < ξ + 2 := by linarith [hξ.1.1]
  have hξ2 : 4 < ξ ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hξ.1.1) hξplus
    nlinarith
  have hq : 6 ≤ (2.262 : ℝ) ^ 2 + 2.262 * ξ + ξ ^ 2 - 6 := by
    nlinarith [hξ.1.1]
  have habsq : 6 ≤ |(2.262 : ℝ) ^ 2 + 2.262 * ξ + ξ ^ 2 - 6| := by
    rw [abs_of_nonneg (by linarith)]
    exact hq
  exact root_error_bound hξ.2 (by norm_num) habsq
theorem gap31 : |f 2.262| / 6 < 0.001 := by
  norm_num [f, abs_of_nonneg, abs_of_neg]
theorem gap32 :
    ∃ ξ₂ : ℝ, ξ₂ ∈ Set.Ioo (2 : ℝ) 3 ∧ f ξ₂ = 0 ∧
      |2.262 - ξ₂| < 0.001 := by
  rcases gap30 with ⟨ξ, hξ, hfξ, herr⟩
  exact ⟨ξ, hξ, hfξ, lt_of_le_of_lt herr gap31⟩
theorem gap33 : f (-2) = 6 := by
  norm_num [f]
theorem gap34 : f (-3) = -7 := by
  norm_num [f]
theorem gap35 (x : ℝ) (hx : x ∈ Set.Ioo (-3 : ℝ) (-2)) :
    deriv f x ≠ 0 := by
  rw [deriv_f]
  have hxplus : x + 2 < 0 := by linarith [hx.2]
  have hxminus : x - 2 < 0 := by linarith [hx.2]
  have hp := mul_pos_of_neg_of_neg hxplus hxminus
  have hx2 : 4 < x ^ 2 := by nlinarith
  nlinarith
theorem gap36 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (-3 : ℝ) (-2) ∧ f ξ = 0 := by
  have hz : (0 : ℝ) ∈ Set.Icc (f (-3)) (f (-2)) := by
    rw [gap34, gap33]
    norm_num
  have himg : (0 : ℝ) ∈ f '' Set.Icc (-3) (-2) :=
    intermediate_value_Icc (by norm_num) continuous_f.continuousOn hz
  rcases himg with ⟨ξ, hξ, hfξ⟩
  have hξ3 : ξ ≠ -3 := by
    intro h
    subst ξ
    norm_num [f] at hfξ
  have hξ2 : ξ ≠ -2 := by
    intro h
    subst ξ
    norm_num [f] at hfξ
  have hξoo : ξ ∈ Set.Ioo (-3 : ℝ) (-2) :=
    ⟨lt_of_le_of_ne hξ.1 (Ne.symm hξ3), lt_of_le_of_ne hξ.2 hξ2⟩
  refine ⟨ξ, ⟨hξoo, hfξ⟩, ?_⟩
  intro y hy
  have hyplus : y + 2 < 0 := by linarith [hy.1.2]
  have hyminus : y - 2 < 0 := by linarith [hy.1.2]
  have hξplus : ξ + 2 < 0 := by linarith [hξoo.2]
  have hξminus : ξ - 2 < 0 := by linarith [hξoo.2]
  have hy2 : 4 < y ^ 2 := by
    have hp := mul_pos_of_neg_of_neg hyplus hyminus
    nlinarith
  have hξsq : 4 < ξ ^ 2 := by
    have hp := mul_pos_of_neg_of_neg hξplus hξminus
    nlinarith
  have hyξ : 4 < y * ξ := by
    have hp := mul_pos_of_neg_of_neg hyplus hξplus
    nlinarith [hy.1.2, hξoo.2]
  have hq : 0 < y ^ 2 + y * ξ + ξ ^ 2 - 6 := by nlinarith
  have hp : (y - ξ) * (y ^ 2 + y * ξ + ξ ^ 2 - 6) = 0 := by
    calc
      (y - ξ) * (y ^ 2 + y * ξ + ξ ^ 2 - 6) = f y - f ξ := (f_sub_f y ξ).symm
      _ = 0 := by rw [hy.2, hfξ]; ring
  rcases mul_eq_zero.mp hp with h | h
  · linarith
  · exact (ne_of_gt hq h).elim
theorem gap37 : negativeApproximant 1 = -2.461 := by
  rfl
theorem gap38 : negativeApproximant 2 = -2.574 := by
  rfl
theorem gap39 : negativeApproximant 3 = -2.596 := by
  rfl
theorem gap40 : negativeApproximant 4 = -2.601 := by
  rfl
theorem gap41 : negativeApproximant 5 = -2.602 := by
  rfl
theorem gap42 : Approx (f (-2.602)) (-0.004) (1 / 1000) := by
  norm_num [Approx, f, abs_lt]
theorem gap43 : ∃ m₃ : ℝ, m₃ = 6 := by
  exact ⟨6, rfl⟩
theorem gap44 :
    sInf ((fun x : ℝ => |deriv f x|) '' Set.Ioo (-3 : ℝ) (-2)) = 6 := by
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo (-3 : ℝ) (-2)
  change sInf S = 6
  have hne : S.Nonempty := by
    refine ⟨|deriv f (-5 / 2)|, ?_⟩
    exact ⟨-5 / 2, by norm_num, rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro b ⟨x, hx, rfl⟩
    exact abs_nonneg _
  apply le_antisymm
  · by_contra hnot
    have hgt : 6 < sInf S := lt_of_not_ge hnot
    have hmem : |deriv f (-5 / 2)| ∈ S := ⟨-5 / 2, by norm_num, rfl⟩
    have hup := csInf_le hbdd hmem
    rw [deriv_f] at hup
    norm_num at hup
    let d : ℝ := sInf S - 6
    let x : ℝ := -2 - d / 100
    have hd : 0 < d := by dsimp [d]; linarith
    have hdtop : d ≤ 27 / 4 := by dsimp [d]; linarith
    have hdprod : 0 ≤ d * (27 / 4 - d) :=
      mul_nonneg (le_of_lt hd) (sub_nonneg.mpr hdtop)
    have hx : x ∈ Set.Ioo (-3 : ℝ) (-2) := by
      dsimp [x]
      constructor <;> nlinarith
    have hxplus : x + 2 < 0 := by linarith [hx.2]
    have hxminus : x - 2 < 0 := by linarith [hx.2]
    have hpos : 0 < 3 * x ^ 2 - 6 := by
      have hp := mul_pos_of_neg_of_neg hxplus hxminus
      nlinarith
    have hnear : |deriv f x| ∈ S := ⟨x, hx, rfl⟩
    have hle := csInf_le hbdd hnear
    have hlt : |deriv f x| < sInf S := by
      rw [deriv_f, abs_of_pos hpos]
      dsimp [x, d]
      nlinarith [hdprod]
    linarith
  · apply le_csInf hne
    intro b hb
    rcases hb with ⟨x, hx, rfl⟩
    change 6 ≤ |deriv f x|
    rw [deriv_f]
    have hxplus : x + 2 < 0 := by linarith [hx.2]
    have hxminus : x - 2 < 0 := by linarith [hx.2]
    have hx2 : 4 < x ^ 2 := by
      have hp := mul_pos_of_neg_of_neg hxplus hxminus
      nlinarith
    rw [abs_of_pos (by nlinarith)]
    nlinarith
theorem gap45 :
    ∃ ξ₃ : ℝ, ξ₃ ∈ Set.Ioo (-3 : ℝ) (-2) ∧ f ξ₃ = 0 ∧
      |-2.602 - ξ₃| ≤ |f (-2.602)| / 6 := by
  rcases gap36 with ⟨ξ, hξ, huniq⟩
  refine ⟨ξ, hξ.1, hξ.2, ?_⟩
  have hξplus : ξ + 2 < 0 := by linarith [hξ.1.2]
  have hξminus : ξ - 2 < 0 := by linarith [hξ.1.2]
  have hξ2 : 4 < ξ ^ 2 := by
    have hp := mul_pos_of_neg_of_neg hξplus hξminus
    nlinarith
  have hq : 6 ≤ (-2.602 : ℝ) ^ 2 + (-2.602) * ξ + ξ ^ 2 - 6 := by
    nlinarith [hξ.1.2]
  have habsq : 6 ≤ |(-2.602 : ℝ) ^ 2 + (-2.602) * ξ + ξ ^ 2 - 6| := by
    rw [abs_of_nonneg (by linarith)]
    exact hq
  exact root_error_bound hξ.2 (by norm_num) habsq
theorem gap46 : |f (-2.602)| / 6 < 0.001 := by
  norm_num [f, abs_of_nonneg, abs_of_neg]
theorem gap47 :
    ∃ ξ₃ : ℝ, ξ₃ ∈ Set.Ioo (-3 : ℝ) (-2) ∧ f ξ₃ = 0 ∧
      |-2.602 - ξ₃| < 0.001 := by
  rcases gap45 with ⟨ξ, hξ, hfξ, herr⟩
  exact ⟨ξ, hξ, hfξ, lt_of_le_of_lt herr gap46⟩
theorem gap48 : ApproxRootSet reportedRoots 0.001 := by
  unfold ApproxRootSet
  constructor
  · intro s hs
    simp only [reportedRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with hs | hs | hs
    · subst s
      rcases gap15 with ⟨r, hr, hfr, hclose⟩
      exact ⟨r, hfr, hclose⟩
    · subst s
      rcases gap32 with ⟨r, hr, hfr, hclose⟩
      exact ⟨r, hfr, hclose⟩
    · subst s
      rcases gap47 with ⟨r, hr, hfr, hclose⟩
      exact ⟨r, hfr, hclose⟩
  · intro r hr
    have hpoly : r ^ 3 - 6 * r + 2 = 0 := by simpa [f] using hr
    have hlow : -3 < r := by
      by_contra h
      have hrle : r ≤ -3 := le_of_not_gt h
      have hq : 0 < r ^ 2 - 3 * r + 3 := by
        nlinarith [sq_nonneg (r - 3 / 2)]
      have hm : (r + 3) * (r ^ 2 - 3 * r + 3) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hq)
      nlinarith
    have hupp : r < 3 := by
      by_contra h
      have hrge : 3 ≤ r := le_of_not_gt h
      have hq : 0 < r ^ 2 + 3 * r + 3 := by
        nlinarith [sq_nonneg r]
      have hm : 0 ≤ (r - 3) * (r ^ 2 + 3 * r + 3) :=
        mul_nonneg (by linarith) (le_of_lt hq)
      nlinarith
    have hloc : r ∈ Set.Ioo (-3 : ℝ) (-2) ∨
        r ∈ Set.Ioo (0 : ℝ) 1 ∨ r ∈ Set.Ioo (2 : ℝ) 3 := by
      by_cases hm2 : r < -2
      · exact Or.inl ⟨hlow, hm2⟩
      · have hrm2 : -2 ≤ r := le_of_not_gt hm2
        by_cases hzero : r < 0
        · have hsquare : r ^ 2 ≤ 4 := by
            have hp := mul_nonneg (by linarith : 0 ≤ r + 2) (by linarith : 0 ≤ 2 - r)
            nlinarith
          have hprod : 0 < r * (r ^ 2 - 6) :=
            mul_pos_of_neg_of_neg hzero (by nlinarith)
          exfalso
          nlinarith
        · have hr0 : 0 ≤ r := le_of_not_gt hzero
          by_cases hone : r < 1
          · have hrne : r ≠ 0 := by
              intro heq
              subst r
              norm_num at hpoly
            exact Or.inr (Or.inl ⟨lt_of_le_of_ne hr0 (Ne.symm hrne), hone⟩)
          · have hr1 : 1 ≤ r := le_of_not_gt hone
            by_cases htwo : r < 2
            · have hfour : 0 < 4 - r ^ 2 := by
                have hp := mul_pos (by linarith : 0 < 2 - r) (by linarith : 0 < 2 + r)
                nlinarith
              have hp : 0 < r * (4 - r ^ 2) :=
                mul_pos (by linarith) hfour
              exfalso
              nlinarith
            · have hr2 : 2 ≤ r := le_of_not_gt htwo
              have hrne : r ≠ 2 := by
                intro heq
                subst r
                norm_num at hpoly
              exact Or.inr (Or.inr ⟨lt_of_le_of_ne hr2 (Ne.symm hrne), hupp⟩)
    rcases hloc with hneg | hsmall | hmiddle
    · rcases gap47 with ⟨ξ, hξ, hfξ, hclose⟩
      rcases gap36 with ⟨u, hu, huniq⟩
      have hru : r = u := huniq r ⟨hneg, hr⟩
      have hξu : ξ = u := huniq ξ ⟨hξ, hfξ⟩
      have hrξ : r = ξ := hru.trans hξu.symm
      refine ⟨-2.602, ?_, ?_⟩
      · simp [reportedRoots]
      · simpa [hrξ, abs_sub_comm] using hclose
    · rcases gap15 with ⟨ξ, hξ, hfξ, hclose⟩
      rcases gap4 with ⟨u, hu, huniq⟩
      have hru : r = u := huniq r ⟨hsmall, hr⟩
      have hξu : ξ = u := huniq ξ ⟨hξ, hfξ⟩
      have hrξ : r = ξ := hru.trans hξu.symm
      refine ⟨0.340, ?_, ?_⟩
      · simp [reportedRoots]
      · simpa [hrξ, abs_sub_comm] using hclose
    · rcases gap32 with ⟨ξ, hξ, hfξ, hclose⟩
      rcases gap19 with ⟨u, hu, huniq⟩
      have hru : r = u := huniq r ⟨hmiddle, hr⟩
      have hξu : ξ = u := huniq ξ ⟨hξ, hfξ⟩
      have hrξ : r = ξ := hru.trans hξu.symm
      refine ⟨2.262, ?_, ?_⟩
      · simp [reportedRoots]
      · simpa [hrξ, abs_sub_comm] using hclose

end
end ProofGap.Exercise1617
