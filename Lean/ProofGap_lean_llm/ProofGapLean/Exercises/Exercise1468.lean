import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1468

noncomputable section

def base (x : ℝ) : ℝ := Real.sin x ^ 3 * Real.cos x
def f (a x : ℝ) : ℝ := base x - a
def threshold : ℝ := 3 * Real.sqrt 3 / 16

private theorem derivative_factor_identity (x : ℝ) :
    3 * Real.sin x ^ 2 * Real.cos x ^ 2 - Real.sin x ^ 4 =
      Real.sin x ^ 2 * (4 * Real.cos x ^ 2 - 1) := by
  calc
    3 * Real.sin x ^ 2 * Real.cos x ^ 2 - Real.sin x ^ 4 =
        Real.sin x ^ 2 *
          (4 * Real.cos x ^ 2 -
            (Real.sin x ^ 2 + Real.cos x ^ 2)) := by ring
    _ = Real.sin x ^ 2 * (4 * Real.cos x ^ 2 - 1) := by
      rw [Real.sin_sq_add_cos_sq]

private theorem abs_base_le_threshold (x : ℝ) :
    |base x| ≤ threshold := by
  let u : ℝ := Real.sin x ^ 2
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have htrig := Real.sin_sq_add_cos_sq x
  have hcos : Real.cos x ^ 2 = 1 - u := by
    dsimp [u]
    nlinarith
  have hbase_sq : (base x) ^ 2 = u ^ 3 * (1 - u) := by
    calc
      (base x) ^ 2 = (Real.sin x ^ 2) ^ 3 * Real.cos x ^ 2 := by
        unfold base
        ring
      _ = u ^ 3 * (1 - u) := by rw [hcos]
  have hquad : 0 ≤ 16 * u ^ 2 + 8 * u + 3 := by
    nlinarith [sq_nonneg u]
  have hproduct :
      0 ≤ (4 * u - 3) ^ 2 * (16 * u ^ 2 + 8 * u + 3) :=
    mul_nonneg (sq_nonneg (4 * u - 3)) hquad
  have hpoly : 256 * (u ^ 3 * (1 - u)) ≤ 27 := by
    nlinarith [hproduct]
  have hbase_bound : 256 * (base x) ^ 2 ≤ 27 := by
    nlinarith [hbase_sq, hpoly]
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hthreshold_nonneg : 0 ≤ threshold := by
    unfold threshold
    positivity
  have hthreshold_sq : 256 * threshold ^ 2 = 27 := by
    unfold threshold
    nlinarith [hsqrt]
  have habs_sq : |base x| ^ 2 = (base x) ^ 2 := by
    exact sq_abs (base x)
  nlinarith [abs_nonneg (base x)]

theorem gap1 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi)
    (hzero : base x = 0) :
    x ∈ ({0, Real.pi / 2, Real.pi} : Set ℝ) := by
  rw [base] at hzero
  rcases mul_eq_zero.mp hzero with hsin | hcos
  · have hsin0 : Real.sin x = 0 := pow_eq_zero hsin
    by_cases hx0 : x = 0
    · subst x
      simp
    by_cases hxpi : x = Real.pi
    · subst x
      simp
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxlt : x < Real.pi := lt_of_le_of_ne hx.2 hxpi
    have hpos := Real.sin_pos_of_pos_of_lt_pi hxpos hxlt
    rw [hsin0] at hpos
    exact (lt_irrefl 0 hpos).elim
  · have hmid : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    have hxeq : x = Real.pi / 2 :=
      Real.strictAntiOn_cos.injOn hx hmid (by simpa using hcos)
    subst x
    simp

theorem gap2 (a x : ℝ) :
    deriv (f a) x =
      3 * Real.sin x ^ 2 * Real.cos x ^ 2 - Real.sin x ^ 4 := by
  have h := (((Real.hasDerivAt_sin x).pow 3).mul
    (Real.hasDerivAt_cos x)).sub_const a
  convert h.deriv using 1 <;> simp [f, base] <;> ring

theorem gap3 (a x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hzero : deriv (f a) x = 0) :
    x = Real.pi / 3 ∨ x = 2 * Real.pi / 3 := by
  rw [gap2, derivative_factor_identity] at hzero
  have hxclosed : x ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hsinpos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsinne : Real.sin x ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt hsinpos)
  have hcore : 4 * Real.cos x ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hsinne
  have hfactor :
      (2 * Real.cos x - 1) * (2 * Real.cos x + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · have hcosx : Real.cos x = 1 / 2 := by nlinarith
    have hp : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    left
    apply Real.strictAntiOn_cos.injOn hxclosed hp
    rw [hcosx, Real.cos_pi_div_three]
  · have hcosx : Real.cos x = -(1 / 2) := by nlinarith
    have hp : 2 * Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    have hp_cos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
      rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring,
        Real.cos_two_mul, Real.cos_pi_div_three]
      ring
    right
    apply Real.strictAntiOn_cos.injOn hxclosed hp
    rw [hcosx, hp_cos]

theorem gap4 (a : ℝ) :
    f a (Real.pi / 3) = threshold - a := by
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hcub : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt]
  rw [f, base, Real.sin_pi_div_three, Real.cos_pi_div_three]
  unfold threshold
  nlinarith [hcub]

theorem gap5 (a : ℝ) :
    f a (2 * Real.pi / 3) = -threshold - a := by
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hcub : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt]
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring,
      Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring,
      Real.cos_two_mul, Real.cos_pi_div_three]
    ring
  rw [f, base, hsin, hcos]
  unfold threshold
  nlinarith [hcub]

theorem gap6 (a : ℝ) :
    f a 0 = f a Real.pi := by
  simp [f, base]

theorem gap7 (a : ℝ) :
    f a Real.pi = -a := by
  simp [f, base]

theorem gap8 (a x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 3)) :
    deriv (f a) x > 0 := by
  rw [gap2, derivative_factor_identity]
  have hxclosed : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [hx.1, hx.2, Real.pi_pos]
  have hp : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcos : 1 / 2 < Real.cos x := by
    have h := Real.strictAntiOn_cos hxclosed hp hx.2
    rwa [Real.cos_pi_div_three] at h
  have hsin : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi hx.1
    nlinarith [hx.2, Real.pi_pos]
  have hsquare : 0 < Real.sin x ^ 2 := by positivity
  have hleft : 0 < 2 * Real.cos x - 1 := by linarith
  have hright : 0 < 2 * Real.cos x + 1 := by linarith
  have hcore : 0 < 4 * Real.cos x ^ 2 - 1 := by
    calc
      0 < (2 * Real.cos x - 1) * (2 * Real.cos x + 1) :=
        mul_pos hleft hright
      _ = 4 * Real.cos x ^ 2 - 1 := by ring
  exact mul_pos hsquare hcore

theorem gap9 (a x : ℝ) (hx : x ∈ Set.Ioo (2 * Real.pi / 3) Real.pi) :
    deriv (f a) x > 0 := by
  rw [gap2, derivative_factor_identity]
  have hxclosed : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [hx.1, hx.2, Real.pi_pos]
  have hp : 2 * Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hp_cos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring,
      Real.cos_two_mul, Real.cos_pi_div_three]
    ring
  have hcos : Real.cos x < -(1 / 2) := by
    have h := Real.strictAntiOn_cos hp hxclosed hx.1
    rwa [hp_cos] at h
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hx.1, Real.pi_pos]) hx.2
  have hsquare : 0 < Real.sin x ^ 2 := by positivity
  have hleft : 2 * Real.cos x - 1 < 0 := by linarith
  have hright : 2 * Real.cos x + 1 < 0 := by linarith
  have hcore : 0 < 4 * Real.cos x ^ 2 - 1 := by
    calc
      0 < (2 * Real.cos x - 1) * (2 * Real.cos x + 1) :=
        mul_pos_of_neg_of_neg hleft hright
      _ = 4 * Real.cos x ^ 2 - 1 := by ring
  exact mul_pos hsquare hcore

theorem gap10 (a x : ℝ) (hx : x ∈ Set.Ioo (Real.pi / 3) (2 * Real.pi / 3)) :
    deriv (f a) x < 0 := by
  rw [gap2, derivative_factor_identity]
  have hxclosed : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [hx.1, hx.2, Real.pi_pos]
  have hp₁ : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hp₂ : 2 * Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hp₂cos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring,
      Real.cos_two_mul, Real.cos_pi_div_three]
    ring
  have hcos_upper : Real.cos x < 1 / 2 := by
    have h := Real.strictAntiOn_cos hp₁ hxclosed hx.1
    rwa [Real.cos_pi_div_three] at h
  have hcos_lower : -(1 / 2) < Real.cos x := by
    have h := Real.strictAntiOn_cos hxclosed hp₂ hx.2
    rwa [hp₂cos] at h
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hx.1, Real.pi_pos])
      (by nlinarith [hx.2, Real.pi_pos])
  have hsquare : 0 < Real.sin x ^ 2 := by positivity
  have hleft : 2 * Real.cos x - 1 < 0 := by linarith
  have hright : 0 < 2 * Real.cos x + 1 := by linarith
  have hcore : 4 * Real.cos x ^ 2 - 1 < 0 := by
    calc
      4 * Real.cos x ^ 2 - 1 =
          (2 * Real.cos x - 1) * (2 * Real.cos x + 1) := by ring
      _ < 0 := mul_neg_of_neg_of_pos hleft hright
  exact mul_neg_of_pos_of_neg hsquare hcore

theorem gap11 (a : ℝ) (ha0 : a ≠ 0) (ha : |a| < threshold) :
    ∃ x₁ x₂, x₁ ∈ Set.Ioo (0 : ℝ) Real.pi ∧
      x₂ ∈ Set.Ioo (0 : ℝ) Real.pi ∧ x₁ ≠ x₂ ∧
      f a x₁ = 0 ∧ f a x₂ = 0 := by
  have hcont : Continuous (f a) := by
    change Continuous (fun x : ℝ => Real.sin x ^ 3 * Real.cos x - a)
    fun_prop
  have hthreshold : 0 < threshold := by
    unfold threshold
    have : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    positivity
  have hp₁pos : 0 < Real.pi / 3 := by nlinarith [Real.pi_pos]
  have hp₁mid : Real.pi / 3 < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hmidp₂ : Real.pi / 2 < 2 * Real.pi / 3 := by
    nlinarith [Real.pi_pos]
  have hp₂pi : 2 * Real.pi / 3 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hmidpi : Real.pi / 2 < Real.pi := by nlinarith [Real.pi_pos]
  have hf0 : f a 0 = -a := by simp [f, base]
  have hfmid : f a (Real.pi / 2) = -a := by simp [f, base]
  have hfpi : f a Real.pi = -a := gap7 a
  have hfp₁ : f a (Real.pi / 3) = threshold - a := gap4 a
  have hfp₂ : f a (2 * Real.pi / 3) = -threshold - a := gap5 a
  rcases lt_or_gt_of_ne ha0 with ha_neg | ha_pos
  · have haT : -a < threshold := by
      simpa [abs_of_neg ha_neg] using ha
    let g : ℝ → ℝ := fun x => -f a x
    have hgcont : Continuous g := by
      dsimp [g]
      exact hcont.neg
    have hz₁ : (0 : ℝ) ∈ Set.Icc (g (Real.pi / 2))
        (g (2 * Real.pi / 3)) := by
      dsimp [g]
      constructor <;> nlinarith [hfmid, hfp₂]
    rcases (intermediate_value_Icc (le_of_lt hmidp₂)
      hgcont.continuousOn) hz₁ with ⟨x₁, hx₁, hgx₁⟩
    have hfx₁ : f a x₁ = 0 := by
      dsimp [g] at hgx₁
      linarith
    have hx₁open : x₁ ∈ Set.Ioo (Real.pi / 2)
        (2 * Real.pi / 3) := by
      constructor
      · apply lt_of_le_of_ne hx₁.1
        intro heq
        have : x₁ = Real.pi / 2 := heq.symm
        subst x₁
        nlinarith [hfx₁, hfmid]
      · apply lt_of_le_of_ne hx₁.2
        intro heq
        subst x₁
        nlinarith [hfx₁, hfp₂, haT]
    have hz₂ : (0 : ℝ) ∈ Set.Icc (f a (2 * Real.pi / 3))
        (f a Real.pi) := by
      constructor <;> nlinarith [hfp₂, hfpi, haT]
    rcases (intermediate_value_Icc (le_of_lt hp₂pi)
      hcont.continuousOn) hz₂ with ⟨x₂, hx₂, hfx₂⟩
    have hx₂open : x₂ ∈ Set.Ioo (2 * Real.pi / 3) Real.pi := by
      constructor
      · apply lt_of_le_of_ne hx₂.1
        intro heq
        have : x₂ = 2 * Real.pi / 3 := heq.symm
        subst x₂
        nlinarith [hfx₂, hfp₂, haT]
      · apply lt_of_le_of_ne hx₂.2
        intro heq
        subst x₂
        nlinarith [hfx₂, hfpi, ha_neg]
    refine ⟨x₁, x₂, ?_, ?_, ?_, hfx₁, hfx₂⟩
    · exact ⟨by nlinarith [hx₁open.1, Real.pi_pos],
        by nlinarith [hx₁open.2, hp₂pi]⟩
    · exact ⟨by nlinarith [hx₂open.1, Real.pi_pos], hx₂open.2⟩
    · nlinarith [hx₁open.2, hx₂open.1]
  · have haT : a < threshold := by
      simpa [abs_of_pos ha_pos] using ha
    have hz₁ : (0 : ℝ) ∈ Set.Icc (f a 0) (f a (Real.pi / 3)) := by
      constructor <;> nlinarith [hf0, hfp₁]
    rcases (intermediate_value_Icc (le_of_lt hp₁pos)
      hcont.continuousOn) hz₁ with ⟨x₁, hx₁, hfx₁⟩
    have hx₁open : x₁ ∈ Set.Ioo 0 (Real.pi / 3) := by
      constructor
      · apply lt_of_le_of_ne hx₁.1
        intro heq
        have : x₁ = 0 := heq.symm
        subst x₁
        nlinarith [hfx₁, hf0, ha_pos]
      · apply lt_of_le_of_ne hx₁.2
        intro heq
        subst x₁
        nlinarith [hfx₁, hfp₁, haT]
    let g : ℝ → ℝ := fun x => -f a x
    have hgcont : Continuous g := by
      dsimp [g]
      exact hcont.neg
    have hz₂ : (0 : ℝ) ∈ Set.Icc (g (Real.pi / 3))
        (g (Real.pi / 2)) := by
      dsimp [g]
      constructor <;> nlinarith [hfp₁, hfmid]
    rcases (intermediate_value_Icc (le_of_lt hp₁mid)
      hgcont.continuousOn) hz₂ with ⟨x₂, hx₂, hgx₂⟩
    have hfx₂ : f a x₂ = 0 := by
      dsimp [g] at hgx₂
      linarith
    have hx₂open : x₂ ∈ Set.Ioo (Real.pi / 3)
        (Real.pi / 2) := by
      constructor
      · apply lt_of_le_of_ne hx₂.1
        intro heq
        have : x₂ = Real.pi / 3 := heq.symm
        subst x₂
        nlinarith [hfx₂, hfp₁, haT]
      · apply lt_of_le_of_ne hx₂.2
        intro heq
        subst x₂
        nlinarith [hfx₂, hfmid, ha_pos]
    refine ⟨x₁, x₂, ?_, ?_, ?_, hfx₁, hfx₂⟩
    · exact ⟨hx₁open.1, by nlinarith [hx₁open.2, Real.pi_pos]⟩
    · exact ⟨by nlinarith [hx₂open.1, Real.pi_pos],
        by nlinarith [hx₂open.2, hmidpi]⟩
    · nlinarith [hx₁open.2, hx₂open.1]

theorem gap12 (a : ℝ) (ha0 : a ≠ 0) (ha : threshold < |a|) :
    ¬ ∃ x ∈ Set.Icc (0 : ℝ) Real.pi, f a x = 0 := by
  rintro ⟨x, hx, hfx⟩
  have hbase : base x = a := by
    unfold f at hfx
    linarith
  have hbound := abs_base_le_threshold x
  rw [hbase] at hbound
  linarith

theorem gap13 (a x : ℝ) :
    x ∈ {y : ℝ | y ∈ Set.Icc 0 Real.pi ∧ base y = a} ↔
      x ∈ Set.Icc 0 Real.pi ∧ base x = a := by
  rfl

end

end ProofGap.Exercise1468
