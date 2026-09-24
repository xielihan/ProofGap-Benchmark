import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1618

noncomputable section

def f (x : ℝ) := x ^ 4 - x - 1
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def positiveApproximant : ℕ → ℝ
  | 1 => 1.07
  | 2 => 1.12
  | 3 => 1.156
  | 4 => 1.180
  | 5 => 1.196
  | 6 => 1.205
  | 7 => 1.217
  | 8 => 1.220
  | 9 => 1.221
  | _ => 0
def negativeApproximant : ℕ → ℝ
  | 1 => -0.652
  | 2 => -0.789
  | 3 => -0.706
  | 4 => -0.719
  | 5 => -0.723
  | 6 => -0.724
  | _ => 0
def reportedRoots : Set ℝ := {1.221, -0.724}
def ApproxRootSet (samples : Set ℝ) (tolerance : ℝ) : Prop :=
  (∀ s ∈ samples, ∃ r, f r = 0 ∧ |s - r| < tolerance) ∧
    (∀ r, f r = 0 → ∃ s ∈ samples, |r - s| < tolerance)

private theorem deriv_f_formula (x : ℝ) : deriv f x = 4 * x ^ 3 - 1 := by
  unfold f
  have h2 := (hasDerivAt_id x).mul (hasDerivAt_id x)
  have h4 := h2.mul h2
  have hraw := (h4.sub (hasDerivAt_id x)).sub_const (1 : ℝ)
  have h : HasDerivAt (fun y : ℝ => y ^ 4 - y - 1)
      (4 * x ^ 3 - 1) x := by
    convert hraw using 1
    · funext y
      simp [id_eq] <;> ring
    · simp [id_eq] <;> ring
  exact h.deriv

private theorem second_deriv_f_formula (x : ℝ) :
    deriv (deriv f) x = 12 * x ^ 2 := by
  have hfun : deriv f = fun y : ℝ => 4 * y ^ 3 - 1 :=
    funext deriv_f_formula
  rw [hfun]
  have h2 := (hasDerivAt_id x).mul (hasDerivAt_id x)
  have h3 := h2.mul (hasDerivAt_id x)
  have hraw := ((hasDerivAt_const x (4 : ℝ)).mul h3).sub_const (1 : ℝ)
  have h : HasDerivAt (fun y : ℝ => 4 * y ^ 3 - 1)
      (12 * x ^ 2) x := by
    convert hraw using 1
    · funext y
      simp [id_eq] <;> ring
    · simp [id_eq] <;> ring
  exact h.deriv

private theorem continuous_f : Continuous f := by
  unfold f
  exact ((continuous_id.pow 4).sub continuous_id).sub continuous_const

private theorem deriv_f_gt_three {x : ℝ} (hx : 1 < x) :
    3 < deriv f x := by
  have hq : 0 < x ^ 2 + x + 1 := by
    nlinarith [sq_nonneg x]
  have hm : 0 < (x - 1) * (x ^ 2 + x + 1) :=
    mul_pos (sub_pos.mpr hx) hq
  rw [deriv_f_formula]
  nlinarith

private theorem three_halves_lt_abs_deriv {x : ℝ} (hx : x < -1 / 2) :
    3 / 2 < |deriv f x| := by
  have hlin : x + 1 / 2 < 0 := by linarith
  have hquad : 0 < x ^ 2 - x / 2 + 1 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 4)]
  have hm : (x + 1 / 2) * (x ^ 2 - x / 2 + 1 / 4) < 0 :=
    mul_neg_of_neg_of_pos hlin hquad
  have hcub : x ^ 3 < -1 / 8 := by
    nlinarith
  rw [deriv_f_formula, abs_of_neg (by nlinarith)]
  nlinarith

private theorem positive_roots_eq {x y : ℝ}
    (hxI : x ∈ Set.Ioo (1 : ℝ) 2) (hyI : y ∈ Set.Ioo (1 : ℝ) 2)
    (hfx : f x = 0) (hfy : f y = 0) : x = y := by
  have hxpos : 0 < x := lt_trans (by norm_num) hxI.1
  have hypos : 0 < y := lt_trans (by norm_num) hyI.1
  have hx2 : 0 < x ^ 2 := by nlinarith [sq_nonneg x]
  have hy2 : 0 < y ^ 2 := by nlinarith [sq_nonneg y]
  have hxq : 0 < x ^ 2 + x + 1 := by nlinarith [sq_nonneg x]
  have hxcube : 1 < x ^ 3 := by
    have hm := mul_pos (sub_pos.mpr hxI.1) hxq
    nlinarith
  have hxyy : 0 < x ^ 2 * y := mul_pos hx2 hypos
  have hxy2 : 0 < x * y ^ 2 := mul_pos hxpos hy2
  have hy3 : 0 < y ^ 3 := by
    have hm := mul_pos hy2 hypos
    nlinarith
  have hcoef : 0 < x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1 := by
    nlinarith
  have hfactor :
      (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1) = 0 := by
    calc
      (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1) =
          f x - f y := by unfold f; ring
      _ = 0 := by rw [hfx, hfy]; ring
  rcases mul_eq_zero.mp hfactor with hxy | hc
  · linarith
  · exact (ne_of_gt hcoef hc).elim

private theorem negative_roots_eq {x y : ℝ}
    (hxI : x ∈ Set.Ioo (-1 : ℝ) (-0.5))
    (hyI : y ∈ Set.Ioo (-1 : ℝ) (-0.5))
    (hfx : f x = 0) (hfy : f y = 0) : x = y := by
  have hxneg : x < 0 := lt_trans hxI.2 (by norm_num)
  have hyneg : y < 0 := lt_trans hyI.2 (by norm_num)
  have hx2 : 0 < x ^ 2 := by nlinarith [sq_nonneg x]
  have hy2 : 0 < y ^ 2 := by nlinarith [sq_nonneg y]
  have hx3 : x ^ 3 < 0 := by
    have hm := mul_neg_of_pos_of_neg hx2 hxneg
    nlinarith
  have hx2y : x ^ 2 * y < 0 := mul_neg_of_pos_of_neg hx2 hyneg
  have hxy2 : x * y ^ 2 < 0 := mul_neg_of_neg_of_pos hxneg hy2
  have hy3 : y ^ 3 < 0 := by
    have hm := mul_neg_of_pos_of_neg hy2 hyneg
    nlinarith
  have hcoef : x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1 < 0 := by
    nlinarith
  have hfactor :
      (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1) = 0 := by
    calc
      (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1) =
          f x - f y := by unfold f; ring
      _ = 0 := by rw [hfx, hfy]; ring
  rcases mul_eq_zero.mp hfactor with hxy | hc
  · linarith
  · exact (ne_of_lt hcoef hc).elim

private theorem root_location (x : ℝ) (hx : f x = 0) :
    x ∈ Set.Ioo (-1 : ℝ) (-0.5) ∨ x ∈ Set.Ioo (1 : ℝ) 2 := by
  have hxeq : x ^ 4 - x - 1 = 0 := by simpa [f] using hx
  have hx4 : 0 ≤ x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2)]
  have hxminle : -1 ≤ x := by nlinarith
  have hxne1 : x ≠ -1 := by
    intro h
    subst x
    norm_num at hxeq
  have hxmin : -1 < x := lt_of_le_of_ne hxminle (Ne.symm hxne1)
  have hxmax : x < 2 := by
    by_contra hnot
    have h2x : 2 ≤ x := le_of_not_gt hnot
    have hxnonneg : 0 ≤ x := by linarith
    have hp1 : 0 ≤ x * (x - 2) :=
      mul_nonneg hxnonneg (sub_nonneg.mpr h2x)
    have hx2ge : 4 ≤ x ^ 2 := by nlinarith
    have hp2 : 0 ≤ x ^ 2 * (x ^ 2 - 4) :=
      mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2ge)
    nlinarith
  by_cases hleft : x < -0.5
  · exact Or.inl ⟨hxmin, hleft⟩
  · have hxhalf : -1 / 2 ≤ x := by
      norm_num at hleft ⊢
      exact hleft
    have hxgt1 : 1 < x := by
      by_contra hnot
      have hxle1 : x ≤ 1 := le_of_not_gt hnot
      by_cases hxneg : x < 0
      · have hp1 : 0 ≤ (x + 1 / 2) * (1 / 2 - x) :=
          mul_nonneg (by linarith) (by linarith)
        have hx2le : x ^ 2 ≤ 1 / 4 := by nlinarith
        have hp2 : 0 ≤ x ^ 2 * (1 / 4 - x ^ 2) :=
          mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2le)
        nlinarith
      · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
        have hp1 : 0 ≤ x * (1 - x) :=
          mul_nonneg hxnonneg (sub_nonneg.mpr hxle1)
        have hx2le : x ^ 2 ≤ 1 := by nlinarith
        have hp2 : 0 ≤ x ^ 2 * (1 - x ^ 2) :=
          mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2le)
        nlinarith
    exact Or.inr ⟨hxgt1, hxmax⟩

theorem gap1 : f 1 = -1 := by
  norm_num [f]
theorem gap2 : f 2 = 13 := by
  norm_num [f]
theorem gap3 (x : ℝ) (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    deriv f x ≠ 0 := by
  have h := deriv_f_gt_three hx.1
  nlinarith
theorem gap4 : ∃! ξ : ℝ, ξ ∈ Set.Ioo (1 : ℝ) 2 ∧ f ξ = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (f 1) (f 2) := by
    constructor <;> norm_num [f]
  have himg : (0 : ℝ) ∈ f '' Set.Icc (1 : ℝ) 2 :=
    (intermediate_value_Icc (f := f) (a := (1 : ℝ)) (b := 2)
      (by norm_num) continuous_f.continuousOn) hzero
  rcases himg with ⟨x, hx, hfx⟩
  have hxne1 : x ≠ 1 := by
    intro h
    subst x
    norm_num [f] at hfx
  have hxne2 : x ≠ 2 := by
    intro h
    subst x
    norm_num [f] at hfx
  have hxI : x ∈ Set.Ioo (1 : ℝ) 2 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxne1), lt_of_le_of_ne hx.2 hxne2⟩
  refine ⟨x, ⟨hxI, hfx⟩, ?_⟩
  intro y hy
  exact positive_roots_eq hy.1 hxI hy.2 hfx
theorem gap5 : positiveApproximant 1 = 1.07 := by
  rfl
theorem gap6 : positiveApproximant 2 = 1.12 := by
  rfl
theorem gap7 : positiveApproximant 3 = 1.156 := by
  rfl
theorem gap8 : positiveApproximant 4 = 1.180 := by
  rfl
theorem gap9 : positiveApproximant 5 = 1.196 := by
  rfl
theorem gap10 : positiveApproximant 6 = 1.205 := by
  rfl
theorem gap11 : positiveApproximant 7 = 1.217 := by
  rfl
theorem gap12 : positiveApproximant 8 = 1.220 := by
  rfl
theorem gap13 : positiveApproximant 9 = 1.221 := by
  rfl
theorem gap14 : Approx (f 1.221) 0.002 (1 / 2000) := by
  norm_num [Approx, f, abs_lt]
theorem gap15 : ∃ m₁ : ℝ, m₁ = 3 := by
  exact ⟨3, rfl⟩
theorem gap16 :
    sInf ((fun x : ℝ => |deriv f x|) '' Set.Ioo (1 : ℝ) 2) = 3 := by
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo (1 : ℝ) 2
  change sInf S = 3
  have hbelow : BddBelow S := by
    refine ⟨3, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    change 3 ≤ |deriv f x|
    have hd := deriv_f_gt_three hx.1
    rw [abs_of_pos (by linarith : 0 < deriv f x)]
    exact le_of_lt hd
  have hne : S.Nonempty := by
    refine ⟨|deriv f (3 / 2)|, ?_⟩
    exact ⟨3 / 2, by constructor <;> norm_num, rfl⟩
  apply le_antisymm
  · by_contra hnot
    have hs : 3 < sInf S := lt_of_not_ge hnot
    have hmem15 : |deriv f (3 / 2)| ∈ S :=
      ⟨3 / 2, by constructor <;> norm_num, rfl⟩
    have hupper := csInf_le hbelow hmem15
    rw [deriv_f_formula] at hupper
    norm_num at hupper
    let d : ℝ := (sInf S - 3) / 100
    have hdpos : 0 < d := by
      dsimp [d]
      linarith
    have hdlt : d < 1 := by
      dsimp [d]
      linarith
    have hd2 : d ^ 2 < d := by
      have hm := mul_lt_mul_of_pos_left hdlt hdpos
      nlinarith
    have hd3 : d ^ 3 < d := by
      have hm := mul_lt_mul_of_pos_left hd2 hdpos
      nlinarith [hd2]
    have hddef : 100 * d = sInf S - 3 := by
      dsimp [d]
      ring
    have hdx : 1 + d ∈ Set.Ioo (1 : ℝ) 2 := by
      constructor <;> linarith
    have hmem : |deriv f (1 + d)| ∈ S := ⟨1 + d, hdx, rfl⟩
    have hinf := csInf_le hbelow hmem
    have hderpos : 0 < deriv f (1 + d) := by
      have := deriv_f_gt_three hdx.1
      linarith
    rw [abs_of_pos hderpos, deriv_f_formula] at hinf
    have hval : 4 * (1 + d) ^ 3 - 1 < sInf S := by
      nlinarith [hd2, hd3, hddef]
    exact (not_lt_of_ge hinf) hval
  · refine le_csInf hne ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    change 3 ≤ |deriv f x|
    have hd := deriv_f_gt_three hx.1
    rw [abs_of_pos (by linarith : 0 < deriv f x)]
    exact le_of_lt hd
theorem gap17 :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (1 : ℝ) 2 ∧ f ξ₁ = 0 ∧
      |1.221 - ξ₁| ≤ |f 1.221| / 3 := by
  rcases gap4 with ⟨r, hr, _⟩
  refine ⟨r, hr.1, hr.2, ?_⟩
  have hrlo : 1 < r := hr.1.1
  have hrpos : 0 < r := lt_trans (by norm_num) hrlo
  have hr2 : 1 < r ^ 2 := by
    have hm : 0 < (r - 1) * (r + 1) :=
      mul_pos (sub_pos.mpr hrlo) (by linarith)
    nlinarith
  have hr3 : 1 < r ^ 3 := by
    have hm : 0 < (r - 1) * (r ^ 2 + r + 1) :=
      mul_pos (sub_pos.mpr hrlo) (by nlinarith [sq_nonneg r])
    nlinarith
  have h1 : 1 < (1.221 : ℝ) ^ 3 := by norm_num
  have h2 : 1 < (1.221 : ℝ) ^ 2 * r := by nlinarith
  have h3 : 1 < (1.221 : ℝ) * r ^ 2 := by nlinarith
  let q : ℝ := (1.221 : ℝ) ^ 3 + (1.221 : ℝ) ^ 2 * r +
    (1.221 : ℝ) * r ^ 2 + r ^ 3 - 1
  have hq : 3 < q := by
    dsimp [q]
    nlinarith
  have hsec : f 1.221 = (1.221 - r) * q := by
    rw [show f 1.221 = f 1.221 - f r by rw [hr.2, sub_zero]]
    dsimp [q]
    unfold f
    ring
  have habsq : |q| = q := abs_of_pos (lt_trans (by norm_num) hq)
  have habs : |f 1.221| = |1.221 - r| * q := by
    calc
      |f 1.221| = |1.221 - r| * |q| := by rw [hsec, abs_mul]
      _ = |1.221 - r| * q := by rw [habsq]
  rw [habs]
  nlinarith [abs_nonneg (1.221 - r)]
theorem gap18 : |f 1.221| / 3 < 0.001 := by
  norm_num [f, abs_lt]
theorem gap19 :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (1 : ℝ) 2 ∧ f ξ₁ = 0 ∧
      |1.221 - ξ₁| < 0.001 := by
  rcases gap17 with ⟨r, hrI, hr0, hrb⟩
  exact ⟨r, hrI, hr0, lt_of_le_of_lt hrb gap18⟩
theorem gap20 : f (-1) = 1 := by
  norm_num [f]
theorem gap21 : f (-0.5) = -0.4375 := by
  norm_num [f]
theorem gap22 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) (-0.5)) :
    deriv f x ≠ 0 := by
  have hx' : x < -1 / 2 := by
    linarith [hx.2]
  have h := three_halves_lt_abs_deriv hx'
  intro hz
  rw [hz, abs_zero] at h
  norm_num at h
theorem gap23 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (-1 : ℝ) (-0.5) ∧ f ξ = 0 := by
  have hcontneg : Continuous (fun x : ℝ => -f x) := continuous_f.neg
  have hzero : (0 : ℝ) ∈ Set.Icc (-f (-1)) (-f (-0.5)) := by
    constructor <;> norm_num [f]
  have himg : (0 : ℝ) ∈ (fun x : ℝ => -f x) '' Set.Icc (-1 : ℝ) (-0.5) :=
    (intermediate_value_Icc (f := fun x : ℝ => -f x)
      (a := (-1 : ℝ)) (b := (-0.5 : ℝ)) (by norm_num)
      hcontneg.continuousOn) hzero
  rcases himg with ⟨x, hx, hnegfx⟩
  have hfx : f x = 0 := by linarith
  have hxne1 : x ≠ -1 := by
    intro h
    subst x
    norm_num [f] at hfx
  have hxne2 : x ≠ -0.5 := by
    intro h
    subst x
    norm_num [f] at hfx
  have hxI : x ∈ Set.Ioo (-1 : ℝ) (-0.5) :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxne1), lt_of_le_of_ne hx.2 hxne2⟩
  refine ⟨x, ⟨hxI, hfx⟩, ?_⟩
  intro y hy
  exact negative_roots_eq hy.1 hxI hy.2 hfx
theorem gap24 : negativeApproximant 1 = -0.652 := by
  rfl
theorem gap25 : negativeApproximant 2 = -0.789 := by
  rfl
theorem gap26 : negativeApproximant 3 = -0.706 := by
  rfl
theorem gap27 : negativeApproximant 4 = -0.719 := by
  rfl
theorem gap28 : negativeApproximant 5 = -0.723 := by
  rfl
theorem gap29 : negativeApproximant 6 = -0.724 := by
  rfl
theorem gap30 : Approx (f (-0.724)) (-0.001) (1 / 2000) := by
  norm_num [Approx, f, abs_lt]
theorem gap31 : ∃ m₂ : ℝ, m₂ = 3 / 2 := by
  exact ⟨3 / 2, rfl⟩
theorem gap32 :
    sInf ((fun x : ℝ => |deriv f x|) '' Set.Ioo (-1 : ℝ) (-0.5)) = 3 / 2 := by
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo (-1 : ℝ) (-0.5)
  change sInf S = 3 / 2
  have hbelow : BddBelow S := by
    refine ⟨3 / 2, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hx' : x < -1 / 2 := by linarith [hx.2]
    exact le_of_lt (three_halves_lt_abs_deriv hx')
  have hne : S.Nonempty := by
    refine ⟨|deriv f (-3 / 4)|, ?_⟩
    exact ⟨-3 / 4, by constructor <;> norm_num, rfl⟩
  apply le_antisymm
  · by_contra hnot
    have hs : 3 / 2 < sInf S := lt_of_not_ge hnot
    have hmem34 : |deriv f (-3 / 4)| ∈ S :=
      ⟨-3 / 4, by constructor <;> norm_num, rfl⟩
    have hupper := csInf_le hbelow hmem34
    rw [deriv_f_formula] at hupper
    norm_num at hupper
    let d : ℝ := (sInf S - 3 / 2) / 100
    have hdpos : 0 < d := by
      dsimp [d]
      linarith
    have hdhalf : d < 1 / 2 := by
      dsimp [d]
      linarith
    have hdlt : d < 1 := by linarith
    have hd2 : d ^ 2 < d := by
      have hm := mul_lt_mul_of_pos_left hdlt hdpos
      nlinarith
    have hd3 : d ^ 3 < d := by
      have hm := mul_lt_mul_of_pos_left hd2 hdpos
      nlinarith [hd2]
    have hddef : 100 * d = sInf S - 3 / 2 := by
      dsimp [d]
      ring
    let z : ℝ := -1 / 2 - d
    have hzI : z ∈ Set.Ioo (-1 : ℝ) (-0.5) := by
      dsimp [z]
      constructor <;> linarith
    have hmem : |deriv f z| ∈ S := ⟨z, hzI, rfl⟩
    have hinf := csInf_le hbelow hmem
    have hzneg : z < 0 := by linarith [hzI.2]
    have hz2 : 0 < z ^ 2 := by nlinarith [sq_nonneg z]
    have hz3 : z ^ 3 < 0 := by
      have hm := mul_neg_of_pos_of_neg hz2 hzneg
      nlinarith
    have hderneg : deriv f z < 0 := by
      rw [deriv_f_formula]
      nlinarith
    rw [abs_of_neg hderneg, deriv_f_formula] at hinf
    have hval : -(4 * z ^ 3 - 1) < sInf S := by
      dsimp [z]
      nlinarith [hd2, hd3, hddef]
    exact (not_lt_of_ge hinf) hval
  · refine le_csInf hne ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx' : x < -1 / 2 := by linarith [hx.2]
    exact le_of_lt (three_halves_lt_abs_deriv hx')
theorem gap33 :
    ∃ ξ₂ : ℝ, ξ₂ ∈ Set.Ioo (-1 : ℝ) (-0.5) ∧ f ξ₂ = 0 ∧
      |-0.724 - ξ₂| ≤ |f (-0.724)| / (3 / 2) := by
  rcases gap23 with ⟨r, hr, _⟩
  refine ⟨r, hr.1, hr.2, ?_⟩
  have hrhi : r < -1 / 2 := by norm_num at hr ⊢; exact hr.1.2
  have hr2 : 1 / 4 < r ^ 2 := by
    have hm : 0 < (r - 1 / 2) * (r + 1 / 2) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    nlinarith
  have hquad : 0 < r ^ 2 - r / 2 + 1 / 4 := by
    nlinarith [sq_nonneg (r - 1 / 4)]
  have hr3 : r ^ 3 < -1 / 8 := by
    have hm : (r + 1 / 2) * (r ^ 2 - r / 2 + 1 / 4) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hquad
    nlinarith
  have h1 : (-0.724 : ℝ) ^ 3 < -1 / 8 := by norm_num
  have h2 : (-0.724 : ℝ) ^ 2 * r < -1 / 8 := by nlinarith
  have h3 : (-0.724 : ℝ) * r ^ 2 < -1 / 8 := by nlinarith
  let q : ℝ := (-0.724 : ℝ) ^ 3 + (-0.724 : ℝ) ^ 2 * r +
    (-0.724 : ℝ) * r ^ 2 + r ^ 3 - 1
  have hq : q < -(3 / 2) := by
    dsimp [q]
    nlinarith
  have hsec : f (-0.724) = (-0.724 - r) * q := by
    rw [show f (-0.724) = f (-0.724) - f r by rw [hr.2, sub_zero]]
    dsimp [q]
    unfold f
    ring
  have hqneg : q < 0 := by linarith
  have habsq : |q| = -q := abs_of_neg hqneg
  have habs : |f (-0.724)| = |-0.724 - r| * (-q) := by
    calc
      |f (-0.724)| = |-0.724 - r| * |q| := by rw [hsec, abs_mul]
      _ = |-0.724 - r| * (-q) := by rw [habsq]
  rw [habs]
  nlinarith [abs_nonneg (-0.724 - r)]
theorem gap34 : |f (-0.724)| / (3 / 2) < 0.001 := by
  norm_num [f, abs_lt]
theorem gap35 :
    ∃ ξ₂ : ℝ, ξ₂ ∈ Set.Ioo (-1 : ℝ) (-0.5) ∧ f ξ₂ = 0 ∧
      |-0.724 - ξ₂| < 0.001 := by
  rcases gap33 with ⟨r, hrI, hr0, hrb⟩
  exact ⟨r, hrI, hr0, lt_of_le_of_lt hrb gap34⟩
theorem gap36 (x : ℝ) : deriv f x = 4 * x ^ 3 - 1 := by
  exact deriv_f_formula x
theorem gap37 (x : ℝ) : deriv (deriv f) x = 12 * x ^ 2 := by
  exact second_deriv_f_formula x
theorem gap38 (x : ℝ) (hx : f x = 0) : 12 * x ^ 2 > 0 := by
  have hxne : x ≠ 0 := by
    intro h
    subst x
    norm_num [f] at hx
  by_cases hpos : 0 < x
  · nlinarith [sq_nonneg x]
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hxne
    nlinarith [sq_nonneg x]
theorem gap39 (x : ℝ) (hx : f x = 0) : deriv (deriv f) x > 0 := by
  rw [second_deriv_f_formula]
  exact gap38 x hx
theorem gap40 : ApproxRootSet reportedRoots 0.001 := by
  constructor
  · intro s hs
    simp only [reportedRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rcases gap19 with ⟨r, hrI, hr0, hrclose⟩
      exact ⟨r, hr0, hrclose⟩
    · rcases gap35 with ⟨r, hrI, hr0, hrclose⟩
      exact ⟨r, hr0, hrclose⟩
  · intro r hr
    rcases root_location r hr with hrneg | hrpos
    · rcases gap35 with ⟨z, hzI, hz0, hzclose⟩
      have herz : r = z := negative_roots_eq hrneg hzI hr hz0
      refine ⟨-0.724, by simp [reportedRoots], ?_⟩
      rw [herz]
      simpa [abs_sub_comm] using hzclose
    · rcases gap19 with ⟨z, hzI, hz0, hzclose⟩
      have herz : r = z := positive_roots_eq hrpos hzI hr hz0
      refine ⟨1.221, by simp [reportedRoots], ?_⟩
      rw [herz]
      simpa [abs_sub_comm] using hzclose

end
end ProofGap.Exercise1618
