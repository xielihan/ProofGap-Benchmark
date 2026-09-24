import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise2822

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (a b : ℝ) (n : ℕ) : ℝ :=
  1 / (a ^ n + b ^ n)

def powerTerm (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient a b n * x ^ n

def SeriesConvergesAt (a b x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm a b (k + 1) x)

def radius (a b : ℝ) : ℝ :=
  max a b

def theta (a b : ℝ) : ℝ :=
  min a b / max a b

def ratioFormula (a b : ℝ) (n : ℕ) : ℝ :=
  max a b * (1 + theta a b ^ (n + 1)) / (1 + theta a b ^ n)

def boundaryLimit (a b : ℝ) : ℝ :=
  if a = b then 1 / 2 else 1

def HasConvergenceRadius (a b : ℝ) : Prop :=
  (∀ x : ℝ, |x| < radius a b → SeriesConvergesAt a b x) ∧
    (∀ x : ℝ, radius a b < |x| → ¬ SeriesConvergesAt a b x)

private theorem coefficient_pos (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hb : 0 < b) : 0 < coefficient a b n := by
  unfold coefficient
  positivity

private theorem coefficient_ne_zero (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hb : 0 < b) : coefficient a b n ≠ 0 :=
  (coefficient_pos a b n ha hb).ne'

private theorem theta_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < theta a b := by
  unfold theta
  exact div_pos (lt_min ha hb) (ha.trans_le (le_max_left _ _))

private theorem theta_le_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    theta a b ≤ 1 := by
  unfold theta
  exact (div_le_one (ha.trans_le (le_max_left _ _))).2 min_le_max

private theorem boundary_term_formula (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    |powerTerm a b n (radius a b)| =
      1 / (1 + theta a b ^ n) := by
  by_cases hab : a ≤ b
  · simp only [powerTerm, coefficient, radius, theta, max_eq_right hab,
      min_eq_left hab, abs_mul, abs_pow]
    rw [abs_of_pos (one_div_pos.mpr (add_pos (pow_pos ha _) (pow_pos hb _)))]
    rw [abs_of_pos hb]
    simp only [div_pow]
    field_simp [ha.ne', hb.ne']
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    simp only [powerTerm, coefficient, radius, theta, max_eq_left hba,
      min_eq_right hba, abs_mul, abs_pow]
    rw [abs_of_pos (one_div_pos.mpr (add_pos (pow_pos ha _) (pow_pos hb _)))]
    rw [abs_of_pos ha]
    simp only [div_pow]
    field_simp [ha.ne', hb.ne']

theorem gap1 :
    ∀ (a b : ℝ), 0 < a → 0 < b →
      (fun n : ℕ => |coefficient a b (n + 1) / coefficient a b (n + 2)|) =
        fun n : ℕ => ratioFormula a b (n + 1) := by
  intro a b ha hb
  funext n
  rw [abs_of_pos (div_pos (coefficient_pos _ _ _ ha hb)
    (coefficient_pos _ _ _ ha hb))]
  by_cases hab : a ≤ b
  · simp only [coefficient, ratioFormula, theta, max_eq_right hab, min_eq_left hab]
    have ha0 : a ≠ 0 := ha.ne'
    have hb0 : b ≠ 0 := hb.ne'
    simp only [div_pow]
    field_simp [ha0, hb0]
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    simp only [coefficient, ratioFormula, theta, max_eq_left hba, min_eq_right hba]
    have ha0 : a ≠ 0 := ha.ne'
    have hb0 : b ≠ 0 := hb.ne'
    simp only [div_pow]
    field_simp [ha0, hb0]
    ring

theorem gap2 :
    ∀ (a b : ℝ), 0 < a → 0 < b →
      Tendsto (ratioFormula a b) atTop (𝓝 (max a b)) := by
  intro a b ha hb
  have htpos := theta_pos a b ha hb
  have htle := theta_le_one a b ha hb
  by_cases ht : theta a b = 1
  · have hfun : ratioFormula a b = fun _ : ℕ => max a b := by
      funext n
      simp [ratioFormula, ht]
    rw [hfun]
    exact tendsto_const_nhds
  · have htlt : theta a b < 1 := lt_of_le_of_ne htle ht
    have hp :
        Tendsto (fun n : ℕ => theta a b ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one htpos.le htlt
    have hp₁ := hp.comp (tendsto_add_atTop_nat 1)
    have hnum :
        Tendsto (fun n : ℕ => 1 + theta a b ^ (n + 1))
          atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hp₁
    have hden :
        Tendsto (fun n : ℕ => 1 + theta a b ^ n)
          atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hp
    have hratio :
        Tendsto (fun n : ℕ =>
          (1 + theta a b ^ (n + 1)) / (1 + theta a b ^ n))
          atTop (𝓝 1) := by
      simpa only [Pi.div_apply, div_one] using hnum.div hden (by norm_num)
    convert
      (tendsto_const_nhds.mul hratio :
        Tendsto
          (fun n : ℕ =>
            max a b * ((1 + theta a b ^ (n + 1)) /
              (1 + theta a b ^ n)))
          atTop (𝓝 (max a b * 1))) using 1
    · funext n
      unfold ratioFormula
      ring
    · ring

theorem gap3 :
    ∀ (a b : ℝ), 0 < a → 0 < b →
      Tendsto
        (fun n : ℕ => |coefficient a b (n + 1) / coefficient a b (n + 2)|)
        atTop (𝓝 (max a b)) := by
  intro a b ha hb
  rw [gap1 a b ha hb]
  exact (gap2 a b ha hb).comp (tendsto_add_atTop_nat 1)

private theorem tendsto_coefficient_ratio_inv (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ => |coefficient a b (n + 2) / coefficient a b (n + 1)|)
      atTop (𝓝 (1 / max a b)) := by
  have hmax : 0 < max a b := ha.trans_le (le_max_left _ _)
  have hinv := (gap3 a b ha hb).inv₀ hmax.ne'
  convert hinv using 1
  · funext n
    rw [abs_of_pos (div_pos (coefficient_pos _ _ _ ha hb)
      (coefficient_pos _ _ _ ha hb))]
    rw [abs_of_pos (div_pos (coefficient_pos _ _ _ ha hb)
      (coefficient_pos _ _ _ ha hb))]
    field_simp [coefficient_ne_zero a b _ ha hb]
  · simp [one_div]

private theorem tendsto_power_ratio (a b x : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        ‖powerTerm a b (n + 2) x‖ /
          ‖powerTerm a b (n + 1) x‖)
      atTop (𝓝 (|x| / max a b)) := by
  by_cases hx : x = 0
  · subst x
    simp [powerTerm]
  · have hmul :=
      (tendsto_const_nhds (x := |x|)).mul
        (tendsto_coefficient_ratio_inv a b ha hb)
    convert hmul using 1
    · funext n
      simp only [powerTerm, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos (coefficient_pos _ _ _ ha hb)]
      rw [abs_of_pos (div_pos (coefficient_pos _ _ _ ha hb)
        (coefficient_pos _ _ _ ha hb))]
      have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
      field_simp [coefficient_ne_zero a b _ ha hb, hxabs]
      ring
    · ring

theorem gap4 :
    ∀ (a b : ℝ), 0 < a → 0 < b → 0 < theta a b := by
  exact fun a b ha hb => theta_pos a b ha hb

theorem gap5 :
    ∀ (a b : ℝ), 0 < a → 0 < b → theta a b ≤ 1 := by
  exact fun a b ha hb => theta_le_one a b ha hb

theorem gap6 :
    (0 : ℝ) < 1 := by
  norm_num

theorem gap7 :
    ∀ (a b : ℝ), 0 < a → 0 < b → HasConvergenceRadius a b := by
  intro a b ha hb
  have hmax : 0 < max a b := ha.trans_le (le_max_left _ _)
  constructor
  · intro x hx
    unfold SeriesConvergesAt
    by_cases hx0 : x = 0
    · subst x
      simp [powerTerm]
    · apply summable_of_ratio_test_tendsto_lt_one
        (l := |x| / max a b)
      · exact (div_lt_one hmax).2 hx
      · filter_upwards [] with n
        exact mul_ne_zero (coefficient_ne_zero _ _ _ ha hb)
          (pow_ne_zero _ hx0)
      · simpa [Nat.add_assoc] using tendsto_power_ratio a b x ha hb
  · intro x hx
    unfold SeriesConvergesAt
    apply not_summable_of_ratio_test_tendsto_gt_one
      (l := |x| / max a b)
    · exact (one_lt_div hmax).2 hx
    · simpa [Nat.add_assoc] using tendsto_power_ratio a b x ha hb

theorem gap8 :
    ∀ (a b x : ℝ), 0 < a → 0 < b → |x| < radius a b →
      SeriesConvergesAt a b x := by
  intro a b x ha hb hx
  exact (gap7 a b ha hb).1 x hx

theorem gap9 :
    ∀ (a b : ℝ), 0 < a → 0 < b →
      Tendsto
        (fun n : ℕ =>
          |powerTerm a b (n + 1) (radius a b)|)
        atTop (𝓝 (boundaryLimit a b)) := by
  intro a b ha hb
  by_cases heq : a = b
  · subst b
    have hfun :
        (fun n : ℕ => |powerTerm a a (n + 1) (radius a a)|) =
          fun _ : ℕ => (1 / 2 : ℝ) := by
      funext n
      rw [boundary_term_formula a a (n + 1) ha ha]
      simp [theta, ha.ne']
      norm_num
    rw [hfun]
    simp [boundaryLimit]
  · have htpos := theta_pos a b ha hb
    have htlt : theta a b < 1 := by
      by_cases hab : a ≤ b
      · have hablt : a < b := lt_of_le_of_ne hab heq
        simp only [theta, min_eq_left hab, max_eq_right hab]
        exact (div_lt_one hb).2 hablt
      · have hbalt : b < a := lt_of_not_ge hab
        have hba : b ≤ a := hbalt.le
        simp only [theta, min_eq_right hba, max_eq_left hba]
        exact (div_lt_one ha).2 hbalt
    have hp :
        Tendsto (fun n : ℕ => theta a b ^ (n + 1))
          atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one htpos.le htlt).comp
        (tendsto_add_atTop_nat 1)
    have hden :
        Tendsto (fun n : ℕ => 1 + theta a b ^ (n + 1))
          atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hp
    have hinv :
        Tendsto (fun n : ℕ => 1 / (1 + theta a b ^ (n + 1)))
          atTop (𝓝 1) := by
      simpa only [Pi.div_apply, div_one] using
        tendsto_const_nhds.div hden (by norm_num)
    simpa only [boundary_term_formula a b _ ha hb, boundaryLimit, if_neg heq] using hinv

theorem gap10 :
    ∀ (a b : ℝ), 0 < a → 0 < b → boundaryLimit a b ≠ 0 := by
  intro a b ha hb
  by_cases heq : a = b
  · simp [boundaryLimit, heq]
  · simp [boundaryLimit, heq]

theorem gap11 :
    ∀ (a b : ℝ), 0 < a → 0 < b →
      ¬ Tendsto
          (fun n : ℕ => |powerTerm a b (n + 1) (radius a b)|)
          atTop (𝓝 0) := by
  intro a b ha hb hzero
  have heq : boundaryLimit a b = 0 :=
    tendsto_nhds_unique (gap9 a b ha hb) hzero
  exact (gap10 a b ha hb) heq

theorem gap12 :
    ∀ (a b x : ℝ), 0 < a → 0 < b → |x| = radius a b →
      ¬ SeriesConvergesAt a b x := by
  intro a b x ha hb hx hsum
  have hzeroX :
      Tendsto (fun n : ℕ => |powerTerm a b (n + 1) x|)
        atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using
      (tendsto_norm_zero.comp hsum.tendsto_atTop_zero)
  have heq :
      (fun n : ℕ => |powerTerm a b (n + 1) x|) =
        fun n : ℕ => |powerTerm a b (n + 1) (radius a b)| := by
    funext n
    unfold powerTerm
    rw [abs_mul, abs_mul, abs_pow, abs_pow, hx]
    have hrpos : 0 < radius a b := by
      unfold radius
      exact ha.trans_le (le_max_left a b)
    rw [abs_of_pos hrpos]
  rw [heq] at hzeroX
  exact gap11 a b ha hb hzeroX

theorem gap13 :
    ∀ (a b x : ℝ), 0 < a → 0 < b →
      (x ∈ Set.Ioo (-(max a b)) (max a b) ↔
        SeriesConvergesAt a b x) := by
  intro a b x ha hb
  constructor
  · intro hx
    exact gap8 a b x ha hb (abs_lt.mpr hx)
  · intro hsum
    have hle : |x| ≤ radius a b := by
      by_contra hle
      exact (gap7 a b ha hb).2 x (lt_of_not_ge hle) hsum
    have hne : |x| ≠ radius a b := by
      intro heq
      exact gap12 a b x ha hb heq hsum
    have hlt : |x| < radius a b := lt_of_le_of_ne hle hne
    exact abs_lt.mp (by simpa [radius] using hlt)

end

end ProofGap.Exercise2822
