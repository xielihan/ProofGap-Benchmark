import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1576

noncomputable section

def ellipse (a b x y : ℝ) : Prop :=
  x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1

def distanceSquared (a b y : ℝ) : ℝ :=
  (1 - a ^ 2 / b ^ 2) * y ^ 2 + 2 * b * y + a ^ 2 + b ^ 2

def focalC (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 - b ^ 2)
def criticalY (a b : ℝ) : ℝ := b ^ 3 / (a ^ 2 - b ^ 2)
def criticalX (a b : ℝ) : ℝ :=
  a ^ 2 / (a ^ 2 - b ^ 2) * Real.sqrt (a ^ 2 - 2 * b ^ 2)

def pointDistance (b x y : ℝ) : ℝ := Real.sqrt (x ^ 2 + (y + b) ^ 2)

def IsFarthest (a b x y : ℝ) : Prop :=
  ellipse a b x y ∧ ∀ x₁ y₁, ellipse a b x₁ y₁ →
    pointDistance b x₁ y₁ ≤ pointDistance b x y

private theorem smallAxisFacts (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsmall : b < a / Real.sqrt 2) :
    b < a ∧ 0 < a ^ 2 - b ^ 2 ∧ 0 < a ^ 2 - 2 * b ^ 2 := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsone : 1 < Real.sqrt 2 := by nlinarith
  have hm : b * Real.sqrt 2 < a :=
    (lt_div_iff₀ hspos).mp hsmall
  have hbg : b < b * Real.sqrt 2 := by
    have hp := mul_pos hb (sub_pos.mpr hsone)
    nlinarith
  have hab : b < a := hbg.trans hm
  have hbs : 0 < b * Real.sqrt 2 := mul_pos hb hspos
  have hp : 0 < (a - b * Real.sqrt 2) *
      (a + b * Real.sqrt 2) :=
    mul_pos (sub_pos.mpr hm) (by linarith)
  have hsq : (b * Real.sqrt 2) ^ 2 < a ^ 2 := by
    nlinarith [hp]
  rw [mul_pow, hssq] at hsq
  have hdiff : 0 < a ^ 2 - b ^ 2 := by
    have hp' : 0 < (a - b) * (a + b) :=
      mul_pos (sub_pos.mpr hab) (by linarith)
    nlinarith [hp']
  refine ⟨hab, hdiff, ?_⟩
  nlinarith

private theorem largeAxisFacts (a b : ℝ) (ha : 0 < a)
    (hlarge : a / Real.sqrt 2 < b) :
    0 < b ∧ a ^ 2 < 2 * b ^ 2 := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hb : 0 < b := by
    have hadiv : 0 < a / Real.sqrt 2 := div_pos ha hspos
    linarith
  have hm : a < b * Real.sqrt 2 :=
    (div_lt_iff₀ hspos).mp hlarge
  have hbs : 0 < b * Real.sqrt 2 := mul_pos hb hspos
  have hp : 0 < (b * Real.sqrt 2 - a) *
      (b * Real.sqrt 2 + a) :=
    mul_pos (sub_pos.mpr hm) (by linarith)
  have hsq : a ^ 2 < (b * Real.sqrt 2) ^ 2 := by
    nlinarith [hp]
  rw [mul_pow, hssq] at hsq
  exact ⟨hb, by nlinarith⟩

theorem gap1 (b x y : ℝ) :
    x ^ 2 + (y + b) ^ 2 = x ^ 2 + y ^ 2 + 2 * b * y + b ^ 2 := by
  ring

theorem gap2 (a b x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hell : ellipse a b x y) :
    x ^ 2 + y ^ 2 + 2 * b * y + b ^ 2 =
      a ^ 2 - a ^ 2 / b ^ 2 * y ^ 2 + y ^ 2 + 2 * b * y + b ^ 2 := by
  unfold ellipse at hell
  field_simp [ha, hb] at hell ⊢
  nlinarith [hell]

theorem gap3 (a b y : ℝ) :
    a ^ 2 - a ^ 2 / b ^ 2 * y ^ 2 + y ^ 2 + 2 * b * y + b ^ 2 =
      distanceSquared a b y := by
  unfold distanceSquared
  ring

theorem gap4 (a b y : ℝ) :
    distanceSquared a b y =
      (1 - a ^ 2 / b ^ 2) * y ^ 2 + 2 * b * y + a ^ 2 + b ^ 2 := by
  rfl

theorem gap5 (a b x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hell : ellipse a b x y) :
    x ^ 2 + (y + b) ^ 2 = distanceSquared a b y := by
  rw [gap1, gap2 a b x y ha hb hell, gap3]

theorem gap6 (a b y : ℝ) (hb : b ≠ 0) :
    deriv (distanceSquared a b) y =
      2 * (1 - a ^ 2 / b ^ 2) * y + 2 * b := by
  unfold distanceSquared
  have hid : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
  have hsq : HasDerivAt (fun z : ℝ => z * z) (1 * y + y * 1) y :=
    hid.mul hid
  have hquad : HasDerivAt
      (fun z : ℝ => (1 - a ^ 2 / b ^ 2) * (z * z))
      ((1 - a ^ 2 / b ^ 2) * (1 * y + y * 1)) y :=
    hsq.const_mul (1 - a ^ 2 / b ^ 2)
  have hlin : HasDerivAt (fun z : ℝ => 2 * b * z) (2 * b * 1) y :=
    hid.const_mul (2 * b)
  have hconst : HasDerivAt (fun _ : ℝ => a ^ 2 + b ^ 2) 0 y :=
    hasDerivAt_const y (a ^ 2 + b ^ 2)
  have hall : HasDerivAt
      (fun z : ℝ =>
        (1 - a ^ 2 / b ^ 2) * (z * z) + 2 * b * z +
          (a ^ 2 + b ^ 2))
      (((1 - a ^ 2 / b ^ 2) * (1 * y + y * 1)) + 2 * b * 1 + 0) y :=
    (hquad.add hlin).add hconst
  convert hall.deriv using 1 <;> ring

theorem gap7 (a b y : ℝ) (ha : b < a) (hb : 0 < b)
    (hcrit : deriv (distanceSquared a b) y = 0) :
    y = criticalY a b := by
  rw [gap6 a b y (ne_of_gt hb)] at hcrit
  unfold criticalY
  have hba : 0 < a ^ 2 - b ^ 2 := by nlinarith
  have hb0 : b ≠ 0 := ne_of_gt hb
  field_simp [hb0]
  field_simp [hb0] at hcrit
  nlinarith

theorem gap8 (a b : ℝ) (hb : 0 < b) (hab : b ≤ a) :
    focalC a b ^ 2 = a ^ 2 - b ^ 2 := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hp : 0 ≤ (a - b) * (a + b) :=
    mul_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hnon : 0 ≤ a ^ 2 - b ^ 2 := by
    nlinarith [hp]
  unfold focalC
  exact Real.sq_sqrt hnon

theorem gap9 (a b : ℝ) (hab : b < a) (hb : 0 < b) :
    criticalY a b = b ^ 3 / focalC a b ^ 2 := by
  unfold criticalY
  rw [← gap8 a b hb hab.le]

theorem gap10 (a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hell : ellipse a b x (criticalY a b)) :
    x ^ 2 = a ^ 2 - a ^ 2 / b ^ 2 * (criticalY a b) ^ 2 := by
  unfold ellipse at hell
  field_simp [ha, hb] at hell ⊢
  nlinarith [hell]

theorem gap11 (a b : ℝ) (hab : b < a) (hb : 0 < b) :
    a ^ 2 - a ^ 2 / b ^ 2 * (criticalY a b) ^ 2 =
      a ^ 2 * (1 - b ^ 4 / focalC a b ^ 4) := by
  have hfc : focalC a b ^ 2 = a ^ 2 - b ^ 2 :=
    gap8 a b hb hab.le
  have hpos : 0 < a ^ 2 - b ^ 2 := by nlinarith
  have hfcpos : 0 < focalC a b := by
    unfold focalC
    exact Real.sqrt_pos.2 hpos
  unfold criticalY
  rw [← hfc]
  field_simp [ne_of_gt hb, ne_of_gt hfcpos] <;> ring

theorem gap12 (a b x : ℝ) (ha : a ≠ 0) (hb : 0 < b) (hab : b < a)
    (hell : ellipse a b x (criticalY a b)) :
    x ^ 2 = a ^ 2 * (1 - b ^ 4 / focalC a b ^ 4) := by
  rw [gap10 a b x ha (ne_of_gt hb) hell]
  exact gap11 a b hab hb

theorem gap13 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsmall : b < a / Real.sqrt 2)
    (hell : ellipse a b x (criticalY a b)) :
    x = criticalX a b ∨ x = -criticalX a b := by
  rcases smallAxisFacts a b ha hb hsmall with ⟨hab, hdiff, htwo⟩
  have hx2 := gap12 a b x (ne_of_gt ha) hb hab hell
  have hfc2 := gap8 a b hb hab.le
  have hc4 : focalC a b ^ 4 = (a ^ 2 - b ^ 2) ^ 2 := by
    calc
      focalC a b ^ 4 = (focalC a b ^ 2) ^ 2 := by ring
      _ = (a ^ 2 - b ^ 2) ^ 2 := by rw [hfc2]
  have hsqrt : (Real.sqrt (a ^ 2 - 2 * b ^ 2)) ^ 2 =
      a ^ 2 - 2 * b ^ 2 := Real.sq_sqrt htwo.le
  have hden : a ^ 2 - b ^ 2 ≠ 0 := ne_of_gt hdiff
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [hx2, hc4]
  unfold criticalX
  simp only [mul_pow, hsqrt, div_pow]
  field_simp [hden]
  ring

theorem gap14 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsmall : b < a / Real.sqrt 2) :
    a / focalC a b ^ 2 * Real.sqrt (focalC a b ^ 4 - b ^ 4) =
      criticalX a b := by
  rcases smallAxisFacts a b ha hb hsmall with ⟨hab, hdiff, htwo⟩
  have hfc2 := gap8 a b hb hab.le
  have hc4 : focalC a b ^ 4 = (a ^ 2 - b ^ 2) ^ 2 := by
    calc
      focalC a b ^ 4 = (focalC a b ^ 2) ^ 2 := by ring
      _ = (a ^ 2 - b ^ 2) ^ 2 := by rw [hfc2]
  have hrad : focalC a b ^ 4 - b ^ 4 =
      a ^ 2 * (a ^ 2 - 2 * b ^ 2) := by
    rw [hc4]
    ring
  have hroot : Real.sqrt (focalC a b ^ 4 - b ^ 4) =
      a * Real.sqrt (a ^ 2 - 2 * b ^ 2) := by
    rw [hrad, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
      abs_of_pos ha]
  unfold criticalX
  rw [hroot, hfc2]
  field_simp [ne_of_gt hdiff] <;> ring

theorem gap15 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsmall : b < a / Real.sqrt 2)
    (hell : ellipse a b x (criticalY a b)) :
    |x| = criticalX a b := by
  rcases smallAxisFacts a b ha hb hsmall with ⟨hab, hdiff, htwo⟩
  have hcrit : 0 ≤ criticalX a b := by
    unfold criticalX
    exact mul_nonneg
      (div_nonneg (sq_nonneg a) hdiff.le)
      (Real.sqrt_nonneg _)
  rcases gap13 a b x ha hb hsmall hell with hx | hx
  · rw [hx, abs_of_nonneg hcrit]
  · rw [hx, abs_neg, abs_of_nonneg hcrit]

theorem gap16 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsmall : b < a / Real.sqrt 2) :
    pointDistance b (criticalX a b) (criticalY a b) =
      a ^ 2 / focalC a b := by
  rcases smallAxisFacts a b ha hb hsmall with ⟨hab, hdiff, htwo⟩
  have hfc2 := gap8 a b hb hab.le
  have hfcpos : 0 < focalC a b := by
    unfold focalC
    exact Real.sqrt_pos.2 hdiff
  have hsqrt : (Real.sqrt (a ^ 2 - 2 * b ^ 2)) ^ 2 =
      a ^ 2 - 2 * b ^ 2 := Real.sq_sqrt htwo.le
  have hden : a ^ 2 - b ^ 2 ≠ 0 := ne_of_gt hdiff
  have hrhs : 0 < a ^ 2 / focalC a b :=
    div_pos (sq_pos_of_pos ha) hfcpos
  unfold pointDistance criticalX criticalY
  have hins :
      (a ^ 2 / (a ^ 2 - b ^ 2) *
          Real.sqrt (a ^ 2 - 2 * b ^ 2)) ^ 2 +
        (b ^ 3 / (a ^ 2 - b ^ 2) + b) ^ 2 =
          (a ^ 2 / focalC a b) ^ 2 := by
    simp only [mul_pow, hsqrt, div_pow, hfc2]
    field_simp [hden] <;> ring
  rw [hins, Real.sqrt_sq_eq_abs, abs_of_pos hrhs]

theorem gap17 (a b y : ℝ) (hb : 0 < b) :
    deriv (distanceSquared a b) y =
      2 * (1 - a ^ 2 / b ^ 2) * y + 2 * b := by
  exact gap6 a b y (ne_of_gt hb)

theorem gap18 (a b y : ℝ) (ha : 0 < a)
    (hba : b ≤ a) (hlarge : a / Real.sqrt 2 < b)
    (hy : y ∈ Set.Icc (-b) b) :
    deriv (distanceSquared a b) b ≤ deriv (distanceSquared a b) y := by
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hb : 0 < b := by
    have : 0 < a / Real.sqrt 2 := div_pos ha hs2pos
    linarith
  rw [gap17 a b b hb, gap17 a b y hb]
  have hcoef : 1 - a ^ 2 / b ^ 2 ≤ 0 := by
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    apply (sub_nonpos.mpr)
    apply (le_div_iff₀ hb2).2
    nlinarith
  have hyb : y ≤ b := hy.2
  nlinarith

theorem gap19 (a b : ℝ) (hb : b ≠ 0) :
    deriv (distanceSquared a b) b = 4 * b - 2 * a ^ 2 / b := by
  rw [gap6 a b b hb]
  field_simp [hb]
  ring

theorem gap20 (a b : ℝ) (ha : 0 < a) (hlarge : a / Real.sqrt 2 < b) :
    0 < 4 * b - 2 * a ^ 2 / b := by
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hb : 0 < b := by
    have : 0 < a / Real.sqrt 2 := div_pos ha hs2pos
    linarith
  have hm := (mul_lt_mul_of_pos_right hlarge hs2pos)
  have hb0 : b ≠ 0 := ne_of_gt hb
  field_simp at hm
  field_simp [hb0]
  nlinarith

theorem gap21 (a b y : ℝ) (ha : 0 < a)
    (hlarge : a / Real.sqrt 2 < b) (hy : y ∈ Set.Icc (-b) b) :
    0 < deriv (distanceSquared a b) y := by
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hb : 0 < b := by
    have : 0 < a / Real.sqrt 2 := div_pos ha hs2pos
    linarith
  rw [gap17 a b y hb]
  have hylo : -b ≤ y := hy.1
  have hyhi : y ≤ b := hy.2
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hlarge2 : a ^ 2 < 2 * b ^ 2 := by
    have hm := (mul_lt_mul_of_pos_right hlarge hs2pos)
    have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    field_simp at hm
    nlinarith
  by_cases hcoef : 0 ≤ 1 - a ^ 2 / b ^ 2
  · have : 0 < 2 * (1 - a ^ 2 / b ^ 2) * y + 2 * b := by
      have hamin : 0 < 2 * (1 - a ^ 2 / b ^ 2) * (-b) + 2 * b := by
        field_simp [ne_of_gt hb]
        nlinarith
      nlinarith
    exact this
  · have hcoef' : 1 - a ^ 2 / b ^ 2 < 0 := lt_of_not_ge hcoef
    have : 0 < 2 * (1 - a ^ 2 / b ^ 2) * b + 2 * b := by
      field_simp [ne_of_gt hb]
      nlinarith
    nlinarith

theorem gap22 (a b : ℝ) (ha : 0 < a) (hlarge : a / Real.sqrt 2 < b) :
    ∀ y ∈ Set.Icc (-b) b, distanceSquared a b y ≤ distanceSquared a b b := by
  intro y hy
  rcases largeAxisFacts a b ha hlarge with ⟨hb, hlarge2⟩
  have hylo : -b ≤ y := hy.1
  have hyhi : y ≤ b := hy.2
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hfrac : a ^ 2 / b ^ 2 < 2 :=
    (div_lt_iff₀ hb2).2 hlarge2
  have hfac : distanceSquared a b b - distanceSquared a b y =
      (b - y) * ((1 - a ^ 2 / b ^ 2) * (b + y) + 2 * b) := by
    unfold distanceSquared
    ring
  have hbr : 0 ≤ (1 - a ^ 2 / b ^ 2) * (b + y) + 2 * b := by
    by_cases hc : 0 ≤ 1 - a ^ 2 / b ^ 2
    · have hm : 0 ≤ (1 - a ^ 2 / b ^ 2) * (b + y) :=
        mul_nonneg hc (by linarith)
      linarith
    · have hc' : 1 - a ^ 2 / b ^ 2 < 0 := lt_of_not_ge hc
      have hm : (1 - a ^ 2 / b ^ 2) * (2 * b) ≤
          (1 - a ^ 2 / b ^ 2) * (b + y) :=
        mul_le_mul_of_nonpos_left (by linarith) hc'.le
      have hend : 0 < (1 - a ^ 2 / b ^ 2) * (2 * b) + 2 * b := by
        calc
          0 < 2 * b * (2 - a ^ 2 / b ^ 2) :=
            mul_pos (by positivity) (sub_pos.mpr hfrac)
          _ = (1 - a ^ 2 / b ^ 2) * (2 * b) + 2 * b := by ring
      linarith
  apply sub_nonneg.mp
  rw [hfac]
  exact mul_nonneg (sub_nonneg.mpr hyhi) hbr

theorem gap23 (a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hell : ellipse a b x b) :
    x = 0 := by
  unfold ellipse at hell
  field_simp [ha, hb] at hell
  nlinarith

theorem gap24 (a b : ℝ) (ha : 0 < a) (hlarge : a / Real.sqrt 2 < b) :
    IsFarthest a b 0 b ∧ pointDistance b 0 b = 2 * b := by
  rcases largeAxisFacts a b ha hlarge with ⟨hb, hlarge2⟩
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  constructor
  · constructor
    · unfold ellipse
      field_simp [ha0, hb0]
      ring
    · intro x₁ y₁ hell
      have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
      have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
      have hxnon : 0 ≤ x₁ ^ 2 / a ^ 2 :=
        div_nonneg (sq_nonneg _) ha2.le
      have hydiv : y₁ ^ 2 / b ^ 2 ≤ 1 := by
        unfold ellipse at hell
        nlinarith
      have hy2 : y₁ ^ 2 ≤ b ^ 2 :=
        (div_le_one hb2).mp hydiv
      have hy : y₁ ∈ Set.Icc (-b) b := by
        constructor <;> nlinarith
      have hds := gap22 a b ha hlarge y₁ hy
      have hsq : x₁ ^ 2 + (y₁ + b) ^ 2 = distanceSquared a b y₁ :=
        gap5 a b x₁ y₁ ha0 hb0 hell
      have hend : distanceSquared a b b = 4 * b ^ 2 := by
        unfold distanceSquared
        field_simp [hb0]
        ring
      unfold pointDistance
      rw [hsq, show 0 ^ 2 + (b + b) ^ 2 = 4 * b ^ 2 by ring, ← hend]
      exact Real.sqrt_le_sqrt hds
  · unfold pointDistance
    rw [show 0 ^ 2 + (b + b) ^ 2 = (2 * b) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

end

end ProofGap.Exercise1576
